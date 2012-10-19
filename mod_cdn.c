/*
  mod_cdn: cdn-ify a website
  Kris Beevers <kbeevers@voxel.net>
  http://www.voxel.net/labs/mod_cdn

  mod_cdn is an apache2 module developed at Voxel dot Net that makes
  VoxCAST and other CDNs easier to use by automatically "CDNifying"
  some HTML content and "originifying" the origin apache server to
  send proper headers, validate authentication tokens, etc.  mod_cdn
  is meant to be installed and configured on a CDN customer's origin
  server.

  Some parts of mod_cdn are based on code from mod_proxy_html
  (http://apache.webthing.com/mod_proxy_html/).
*/

/********************************************************************
 * mod_cdn Copyright (c) 2008-2010, Voxel dot Net, Inc. with parts
 * adapted from mod_proxy_html Copyright (c) 2003-8, WebThing Ltd
 * Authors: Kris Beevers <kbeevers@voxel.net>
 *          Reed Loden <reed@voxel.net>
 *          (mod_proxy_html: Nick Kew <nick@webthing.com>)
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * version 2 as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * Version 2 along with this program.  If not, see
 * <http://www.gnu.org/licenses/old-licenses/gpl-2.0.html>.
 *
 *
 * EXCEPTION TO THE ABOVE LICENSE:
 * The following license applies only to the matches_aliases() and
 * qs_to_table() functions used in this file. See COPYING for
 * more details.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this function except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 ********************************************************************/

#include <ctype.h>

#include <libxml/HTMLparser.h>

#include <openssl/sha.h>

#include <http_protocol.h>
#include <http_config.h>
#include <http_log.h>
#include <http_request.h>

#include <apr_strings.h>
#include <apr_hash.h>
#include <apr_tables.h>
#include <apr_time.h>
#include <apr_uri.h>

/* To support Apache 2.1/2.2, we need the ap_ forms of the regexp
 * stuff, and they're now used in the code.  To support 2.0 in the
 * same compile, * we #define the AP_ versions if necessary.
 */
#ifndef AP_REG_ICASE
/* it's 2.0, so we #define the ap_ versions */
#define ap_regex_t regex_t
#define ap_regmatch_t regmatch_t
#define AP_REG_EXTENDED REG_EXTENDED
#define AP_REG_ICASE REG_ICASE
#define AP_REG_NOSUB REG_NOSUB
#define AP_REG_NEWLINE REG_NEWLINE
#define APACHE20
#define ap_register_output_filter_protocol(a,b,c,d,e) ap_register_output_filter(a,b,c,d)
#else
#define APACHE22
#endif

#ifndef APR_ARRAY_IDX
#define APR_ARRAY_IDX(ary,i,type) (((type *)(ary)->elts)[i])
#endif

module AP_MODULE_DECLARE_DATA cdn_module;

static ap_filter_rec_t *cdn_html_filter_handle;

typedef struct
{
  const char *val;
} tattr;

#define REMAP_FLAG_AUTH           1
#define REMAP_FLAG_QSTRING_IGNORE 2
typedef struct
{
  ap_regex_t regex;
  int flags;
} server_remap_t;

#define ORIGINIFY_FLAG_EXPIRE 1
#define ORIGINIFY_FLAG_AUTH   2
typedef struct
{
  ap_regex_t regex;
  int flags;
  int exptime;
} act_as_origin_t;

/* ignore_token_direction */
#define BEFORE 0
#define AFTER  1

typedef struct
{
  size_t bufsz;
  const char *doctype;
  xmlCharEncoding default_encoding;
  apr_hash_t *links;
  apr_array_header_t *skipto;
  apr_array_header_t *content_types;
  apr_array_header_t *from_servers;
  const char *to_server;
  apr_array_header_t *map;
  apr_array_header_t *originify;
  const char *auth_key;
  const char *auth_header_text;
  int auth_exptime;
  const char *ignore_token;
  const char *ignore_token_arg_relative;
  int ignore_token_direction;
  int global_auth;
  int global_qstring_ignore;
  int default_exptime;
} cdn_conf;

typedef struct
{
  ap_filter_t *f;
  cdn_conf *cfg;
  htmlParserCtxtPtr parser;
  apr_bucket_brigade *bb;
  char *buf;
  size_t offset;
  size_t avail;
} saxctxt;

static htmlSAXHandler sax;

static const char* const fpi_html =
	"<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01//EN\">\n" ;
static const char* const fpi_html_legacy =
	"<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\">\n" ;
static const char* const fpi_xhtml =
	"<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\n" ;
static const char* const fpi_xhtml_legacy =
	"<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">\n" ;
static const char* const DEFAULT_DOCTYPE = "" ;

static ap_regex_t* seek_meta_ctype;
static ap_regex_t* seek_charset;

#define SHA1_STR_SIZE 40
#define TIME_STR_SIZE 25


/* returns 1 if auth is required, 0 otherwise */
static int add_origin_headers(cdn_conf *cfg, request_rec *r, act_as_origin_t *orig)
{
  if(orig->flags & ORIGINIFY_FLAG_EXPIRE) {
    char *exp_date_rfc822 = apr_palloc(r->pool, APR_RFC822_DATE_LEN);
    apr_time_t exp = apr_time_now() + apr_time_from_sec(orig->exptime);

    if(apr_rfc822_date(exp_date_rfc822, exp) == APR_SUCCESS)
      apr_table_setn(r->headers_out, "Expires", exp_date_rfc822);
  }

  if(orig->flags & ORIGINIFY_FLAG_AUTH) {
    apr_table_setn(r->headers_out, "Vox-Authorization", cfg->auth_header_text);
    return 1;
  }

  return 0;
}

static void consume_buffer(saxctxt * ctx, const char *inbuf, int bytes, int flag)
{
  htmlParseChunk(ctx->parser, inbuf, bytes, flag);
}

#define FLUSH ap_fwrite(ctx->f->next, ctx->bb, (chars+begin), (i-begin)) ; begin = i+1
static void pcharacters(void* ctxt, const xmlChar *uchars, int length) {
  const char* chars = (const char*) uchars;
  saxctxt* ctx = (saxctxt*) ctxt ;
  int i ;
  int begin ;
  for ( begin=i=0; i<length; i++ ) {
    switch (chars[i]) {
    case '&' : FLUSH ; ap_fputs(ctx->f->next, ctx->bb, "&amp;") ; break ;
    case '<' : FLUSH ; ap_fputs(ctx->f->next, ctx->bb, "&lt;") ; break ;
    case '>' : FLUSH ; ap_fputs(ctx->f->next, ctx->bb, "&gt;") ; break ;
    case '"' : FLUSH ; ap_fputs(ctx->f->next, ctx->bb, "&quot;") ; break ;
    default : break ;
    }
  }
  FLUSH ;
}

static void preserve(saxctxt * ctx, const size_t len)
{
  char *newbuf;
  if (len <= (ctx->avail - ctx->offset))
    return;
  else
    while (len > (ctx->avail - ctx->offset))
      ctx->avail += ctx->cfg->bufsz;

  newbuf = realloc(ctx->buf, ctx->avail);
  if (newbuf != ctx->buf) {
    if (ctx->buf)
      apr_pool_cleanup_kill(ctx->f->r->pool, ctx->buf, (int(*)(void*))free);
    apr_pool_cleanup_register
      (ctx->f->r->pool, newbuf, (int(*)(void*))free, apr_pool_cleanup_null);
    ctx->buf = newbuf;
  }
}

static void pappend(saxctxt * ctx, const char *buf, const size_t len)
{
  preserve(ctx, len);
  memcpy(ctx->buf + ctx->offset, buf, len);
  ctx->offset += len;
}

static void dump_content(saxctxt * ctx)
{
  char c = 0;
  pappend(ctx, &c, 1);        /* append null byte */
  ap_fwrite(ctx->f->next, ctx->bb, ctx->buf, strlen(ctx->buf));
}

static void pcdata(void *ctxt, const xmlChar * uchars, int length)
{
  const char *chars = (const char *) uchars;
  saxctxt *ctx = (saxctxt *) ctxt;
  ap_fwrite(ctx->f->next, ctx->bb, chars, length);
}

static void pcomment(void *ctxt, const xmlChar * uchars)
{
  const char *chars = (const char *) uchars;
  saxctxt *ctx = (saxctxt *) ctxt;

  ap_fputs(ctx->f->next, ctx->bb, "<!--");
  ap_fwrite(ctx->f->next, ctx->bb, chars, strlen(chars));
  ap_fputs(ctx->f->next, ctx->bb, "-->");
}

static void pendElement(void *ctxt, const xmlChar * uname)
{
  saxctxt *ctx = (saxctxt *) ctxt;
  const char *name = (const char *) uname;
  const htmlElemDesc *desc = htmlTagLookup(uname);

#if 0 /* for now, err on the side of leaving stuff alone */
  if ((ctx->cfg->doctype == fpi_html) || (ctx->cfg->doctype == fpi_xhtml)) {
    /* enforce html */
    if (!desc || desc->depr)
      return;

  } else if ((ctx->cfg->doctype == fpi_html)
		|| (ctx->cfg->doctype == fpi_xhtml)) {
    /* enforce html legacy */
    if (!desc)
      return;
  }
#endif

  if (ctx->offset > 0) {
    dump_content(ctx);
    ctx->offset = 0;        /* having dumped it, we can re-use the memory */
  }
  if (!desc || !desc->empty) {
    ap_fprintf(ctx->f->next, ctx->bb, "</%s>", name);
  }
}

/**
 * Copied from httpd/trunk/server/vhost.c.
 *
 * Copyright 2009 The Apache Software Foundation.
 *
 * The following function is licensed under the Apache
 * License, Version 2.0. See COPYING for more details.
 */
/* return 1 if host matches ServerName or ServerAliases */
static int matches_aliases(server_rec *s, const char *host)
{
    int i;
    apr_array_header_t *names;

    /* match ServerName */
    if (!strcasecmp(host, s->server_hostname)) {
        return 1;
    }

    /* search all the aliases from ServerAlias directive */
    names = s->names;
    if (names) {
        char **name = (char **) names->elts;
        for (i = 0; i < names->nelts; ++i) {
            if(!name[i]) continue;
            if (!strcasecmp(host, name[i]))
                return 1;
        }
    }
    names = s->wild_names;
    if (names) {
        char **name = (char **) names->elts;
        for (i = 0; i < names->nelts; ++i) {
            if(!name[i]) continue;
            if (!ap_strcasecmp_match(host, name[i]))
                return 1;
        }
    }
    return 0;
}

/**
 * Copied from httpd/trunk/modules/cluster/mod_heartbeat.c.
 *
 * Copyright 2009 The Apache Software Foundation.
 *
 * The following function is licensed under the Apache
 * License, Version 2.0. See COPYING for more details.
 */
static void qs_to_table(const char *input, apr_table_t *parms,
                        apr_pool_t *p)
{
    char *key;
    char *value;
    char *query_string;
    char *strtok_state;

    if (input == NULL) {
        return;
    }

    query_string = apr_pstrdup(p, input);

    key = apr_strtok(query_string, "&", &strtok_state);
    while (key) {
        value = strchr(key, '=');
        if (value) {
            *value = '\0';      /* Split the string in two */
            value++;            /* Skip passed the = */
        }
        else {
            value = "1";
        }
        ap_unescape_url(key);
        ap_unescape_url(value);
        apr_table_set(parms, key, value);
        /*
           ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,
           "Found query arg: %s = %s", key, value);
         */
        key = apr_strtok(NULL, "&", &strtok_state);
    }
}

/* comparison function used for qsort() */
static int compare_params(const void *a, const void *b)
{
  return strcmp(((apr_table_entry_t*)a)->key, ((apr_table_entry_t*)b)->key);
}

/*
  generate a voxcast-compatible authentication token for a link
  assuming the object will be requested from the same IP making this
  request.
*/
static const char * make_auth_token
  (request_rec *r, const char *ip, const char *uri,
   const apr_table_t *params, const char *key)
{
  char *flat_args, *to_encrypt, *token;
  unsigned char enc[20];
  int i;
  const apr_array_header_t *params_arr;

  /* Sort the table alphabetically */
  params_arr = apr_table_elts(params);
  qsort(params_arr->elts, params_arr->nelts, params_arr->elt_size, compare_params);

  /* Flatten the table into one string */
  flat_args = "";
  for (i = 0; i < params_arr->nelts; ++i) {
    flat_args = apr_pstrcat(r->pool, flat_args,
                  APR_ARRAY_IDX(params_arr, i, apr_table_entry_t).key,
                  APR_ARRAY_IDX(params_arr, i, apr_table_entry_t).val,
                  NULL);
  }

  /* Format string to be hashed */
  to_encrypt = apr_pstrcat(r->pool, ip, uri, flat_args, key, NULL);

  /* Hash the string into the new token */
  SHA1((unsigned char *)to_encrypt, strlen(to_encrypt), enc);
  token = apr_palloc(r->pool, SHA1_STR_SIZE + 1);
  for (i = 0; i < 20; i += 4)
    sprintf(token + (i*2), "%02x%02x%02x%02x", enc[i], enc[i+1], enc[i+2], enc[i+3]);
  token[SHA1_STR_SIZE] = '\0';

  return token;
}

static int verify_auth_token(cdn_conf *cfg, request_rec *r)
{
  char *last, *uri_base, *query_string, *vox_timestamp_decoded, *forwarded_list;
  const char *token, *vox_sig, *vox_timestamp, *ip;
  apr_table_t *params;
  struct tm ctime;
  long remote_east_of_utc, local_east_of_utc;
  time_t raw;
  apr_time_t vox_ts;

  /* URI must have '?' in it */
  if (!strchr(r->unparsed_uri, '?')) {
    ap_log_error(APLOG_MARK, APLOG_DEBUG, 0, r->server,
                 "verify_auth_token: URI %s missing '?'",
                 r->unparsed_uri);
    return DECLINED;
  }

  /* The base URL of the request, without the query arguments. */
  uri_base = apr_strtok(r->unparsed_uri, "?", &last);
  uri_base = apr_pstrcat(r->pool, cfg->to_server, uri_base, NULL);

  /* All of the query string parameters */
  query_string = apr_strtok(NULL, "", &last);

  /* Convert the query string to a table */
  params = apr_table_make(r->pool, 1);
  qs_to_table(query_string, params, r->pool);

  /* Get vox_sig from the parameters */
  vox_sig = apr_table_get(params, "vox_sig");
  if (!vox_sig) {
    ap_log_error(APLOG_MARK, APLOG_DEBUG, 0, r->server,
                 "verify_auth_token: vox_sig missing");
    return DECLINED;
  }

  /* Remove vox_sig from params so it can be regenerated */
  apr_table_unset(params, "vox_sig");

  /* Get vox_timestamp from the parameters */
  vox_timestamp = apr_table_get(params, "vox_timestamp");
  if (!vox_timestamp) {
    ap_log_error(APLOG_MARK, APLOG_DEBUG, 0, r->server,
                 "verify_auth_token: vox_timestamp missing");
    return DECLINED;
  }

  /* Parse vox_timestamp, which must be in ISO 8601 format */
  memset(&ctime, 0, sizeof(struct tm));
  vox_timestamp_decoded = apr_pstrdup(r->pool, vox_timestamp);
  ap_unescape_url(vox_timestamp_decoded);
  strptime(vox_timestamp_decoded, "%FT%T%z", &ctime);
  remote_east_of_utc = ctime.tm_gmtoff; /* have to save because mktime overwrites */
  ctime.tm_isdst = -1; /* mktime needs to auto-determine DST */
  raw = mktime(&ctime);
  local_east_of_utc = ctime.tm_gmtoff;
  apr_time_ansi_put(&vox_ts, raw - remote_east_of_utc + local_east_of_utc);

  /* verify vox_timestamp is in the future; if not, authentication has failed */
  if (vox_ts < apr_time_now()) {
    ap_log_error(APLOG_MARK, APLOG_DEBUG, 0, r->server,
                 "Authenticated URL %s is expired (expired %ld, now %ld, raw %ld, "
                 "remote_east_of_utc %ld, local_east_of_utc %ld)",
                 r->uri,
                 apr_time_sec(vox_ts),
                 apr_time_sec(apr_time_now()),
                 raw, remote_east_of_utc, local_east_of_utc);
    return DECLINED;
  }

  /* compute the correct auth token using the connection's remote IP */
  token = make_auth_token(r, r->connection->remote_ip, uri_base, params,
                          cfg->auth_key);

  ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
               "verify_auth_token: comparing vox_sig %s with token %s "
               "using remote_ip %s", vox_sig, token, r->connection->remote_ip);

  if (!strncasecmp(token, vox_sig, SHA1_STR_SIZE))
    return OK;

  /* if that IP didn't work, try every IP in the X-Forwarded-For header in order */
  forwarded_list = (char *)apr_table_get(r->headers_in, "X-Forwarded-For");
  if (forwarded_list && (forwarded_list = apr_pstrdup(r->pool, forwarded_list))) {
    last = NULL;
    if (!(ip = apr_strtok(forwarded_list, ", \t", &last)))
      return DECLINED;
    do {
      token = make_auth_token(r, ip, uri_base, params, cfg->auth_key);

      ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
                   "verify_auth_token: comparing vox_sig %s with token %s "
                   "using X-Forwarded-For ip %s", vox_sig, token, ip);

      if (!strncasecmp(token, vox_sig, SHA1_STR_SIZE))
        return OK;
    } while ((ip = apr_strtok(NULL, ", \t", &last)));
  }

  return DECLINED;
}

static char * add_auth_token(apr_pool_t *pool, saxctxt *ctx, apr_uri_t *u)
{
  apr_uri_t u2 = *u;
  const char *unparsed_uri, *auth_token, *ip;
  char *timestamp, *forwarded_list, *last;
  apr_status_t rv;
  apr_time_exp_t xt;
  apr_size_t sz;
  apr_table_t *params;

  unparsed_uri = apr_uri_unparse(pool, &u2, APR_URI_UNP_OMITQUERY);

  rv = apr_time_exp_lt(&xt, apr_time_now() + apr_time_from_sec(ctx->cfg->auth_exptime));
  timestamp = apr_palloc(pool, TIME_STR_SIZE + 1);
  rv = apr_strftime(timestamp, &sz, TIME_STR_SIZE, "%FT%T%z", &xt);

  if (u2.query)
    u2.query = apr_pstrcat(pool, u2.query, "&vox_timestamp=", timestamp, NULL);
  else
    u2.query = apr_pstrcat(pool, "vox_timestamp=", timestamp, NULL);

  /* Convert the query string to a table */
  params = apr_table_make(pool, 1);
  qs_to_table(u2.query, params, pool);

  /* Generate the auth token */
  forwarded_list = (char *)apr_table_get(ctx->f->r->headers_in, "X-Forwarded-For");
  /* If X-Forwarded-For header exists, use first IP in it */
  if (forwarded_list &&
      (forwarded_list = apr_pstrdup(pool, forwarded_list)) &&
      (ip = apr_strtok(forwarded_list, ", \t", &last)))
    auth_token = make_auth_token(ctx->f->r, ip, unparsed_uri, params,
                                 ctx->cfg->auth_key);
  else /* Otherwise, use the normal remote_ip */
    auth_token = make_auth_token(ctx->f->r, ctx->f->r->connection->remote_ip,
                                 unparsed_uri, params, ctx->cfg->auth_key);

  if (auth_token) {
    u2.query = apr_pstrcat(pool, u2.query, "&vox_sig=", auth_token, NULL);
    ap_log_error(APLOG_MARK, APLOG_INFO, APR_SUCCESS, ctx->f->r->server,
                 "add_auth_token: new query string is %s", u2.query);
  }

  return u2.query;
}

static char * add_qstring_ignore_token(apr_pool_t *pool, saxctxt *ctx, apr_uri_t *u)
{
  char *where;
  const char *arg = ctx->cfg->ignore_token_arg_relative;

  if(!u->query || !ctx->cfg->ignore_token || !arg)
    return u->query;

  ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, ctx->f->r->server,
               "add_qstring_ignore_token: adding ignore token %s to %s relative to %s",
               ctx->cfg->ignore_token, u->query, arg);

  /*
   * doing this rather than just a basic strstr for arg makes sure we
   * find an argument name, and not the string within a value
   */
  where = (!strncmp(u->query, arg, strlen(arg))) ? u->query :
    strstr(u->query, apr_pstrcat(pool, "&", arg, 0));

  if(!where) { /* give up, can't find the argument */
    ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, ctx->f->r->server,
                 "add_qstring_ignore_token: can't find %s", arg);
    return u->query;
  }

  if(ctx->cfg->ignore_token_direction == BEFORE) {
    /* put the ignore_token before arg_relative in the query string */
    if(where == u->query) /* at the beginning of the qstring */
      return apr_pstrcat(pool, ctx->cfg->ignore_token, "&", u->query, 0);
    else {                /* somewhere in the middle */
      char *start = apr_pstrndup(pool, u->query, where - u->query);
      return apr_pstrcat(pool, start, "&", ctx->cfg->ignore_token, where, 0);
    }
  } else {
    /*
     * put the ignore_token after arg_relative in the query string
     * first find the end of the argument/value
     */
    char *end = strchr(where, '&');
    if(end) {
      char *start = apr_pstrndup(pool, u->query, end - u->query);
      return apr_pstrcat(pool, start, "&", ctx->cfg->ignore_token, end, 0);
    } else
      return apr_pstrcat(pool, u->query, "&", ctx->cfg->ignore_token, 0);
  }
}


/* compute a new uri based on the old one and the current request such
   that the uri maps to the same location on a different server.
   there are three cases:
     1. globally absolute: method://old-server(:port)/path/to/file
     2. locally absolute:  /path/to/file
     3. relative:          path/to/file

   we handle the cases as follows:

     1. check from_servers to ensure that old-server(:port) is listed;
        if not, we check if old-server is the current servername; if
        not, we _do not_ replace the server in the url; note that we
        _do not_ try to match urls of the form
        method://username:password@old-server(:port)/path/to/file
     2. just drop in to_server in the beginning
     3. figure out the current request_uri, and replace the most
        specific filename with path/to/file
*/
static char * remap_url(saxctxt *ctx, char *uri, int add_auth, int add_qstring_ignore)
{
  apr_uri_t u, u2;
  int i;
  char *s;
  apr_pool_t *pool = ctx->f->r->pool;

  ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, ctx->f->r->server,
               "remap_url: remapping %s (add_auth = %d, add_qstring_ignore = %d)",
               uri, add_auth, add_qstring_ignore);

  if(apr_uri_parse(pool, uri, &u) != APR_SUCCESS)
    return NULL;

  /* only CDNify HTTP and HTTPS requests for now */
  if(u.scheme && strcasecmp(u.scheme, "http") != 0 && strcasecmp(u.scheme, "https") != 0)
    return NULL;

  if(u.hostinfo) { /* case 1 */
    const char *hostinfo =
      (u.port_str && u.scheme && u.port != apr_uri_port_of_scheme(u.scheme)) ?
      u.hostinfo : u.hostname;

    /* does this hostinfo match the current ServerName or one of the ServerAliases? */
    if(matches_aliases(ctx->f->r->server, hostinfo))
      goto set_hostname_and_return;

    /* if not, cycle through from_servers and see if one of them matches */
    if(ctx->cfg->from_servers) {
      tattr *from = (tattr *)ctx->cfg->from_servers->elts;
      for(i = 0; i < ctx->cfg->from_servers->nelts; ++i)
        if(!strcasecmp(hostinfo, from[i].val))
          goto set_hostname_and_return;
    }

  } else if(u.path && u.path[0] == '/') { /* case 2 */
    goto set_hostname_and_return;

  } else if(u.path) { /* case 3 */

    /*
     * first figure out the local absolute path, minus the filename,
     * from r->uri; then, tack the relative uri onto the end
     */
    char *my_uri = apr_pstrdup(pool, ctx->f->r->uri);
    s = strrchr(my_uri, '/');
    if(s) {
      *(s+1) = '\0';
      u.path = apr_pstrcat(pool, my_uri, u.path, NULL);
    }
    goto set_hostname_and_return;
  }

  return NULL;

 set_hostname_and_return:
  if(apr_uri_parse(pool, (char *)ctx->cfg->to_server, &u2) != APR_SUCCESS)
    return NULL;
  u.scheme = u2.scheme;
  u.hostname = u2.hostname;
  u.port_str = u2.port_str;
  u.port = u2.port;

  if(add_qstring_ignore)
    u.query = add_qstring_ignore_token(pool, ctx, &u);

  if(add_auth)
    u.query = add_auth_token(pool, ctx, &u);

  return apr_uri_unparse(pool, &u, 0);
}

static void pstartElement(void *ctxt, const xmlChar * uname, const xmlChar ** uattrs)
{
  int num_match;
  char *subs;
  int is_uri;
  const char **a;
  size_t s_to, s_from;
  saxctxt *ctx = (saxctxt *) ctxt;
  apr_array_header_t *linkattrs;
  int i;
  const char *name = (const char *) uname;
  const char **attrs = (const char **) uattrs;
  const htmlElemDesc *desc = htmlTagLookup(uname);

  /* VoxCDN FIXME: rewrite this, it's ridiculously bad */

#if 0 /* for now, err on the side of leaving stuff alone */
  int enforce = 0;
  if ((ctx->cfg->doctype == fpi_html) || (ctx->cfg->doctype == fpi_xhtml)) {
    /* enforce html */
    enforce = 2;
    if (!desc || desc->depr)
      return;

  } else if ((ctx->cfg->doctype == fpi_html)
		|| (ctx->cfg->doctype == fpi_xhtml)) {
    enforce = 1;
    /* enforce html legacy */
    if (!desc) {
      return;
    }
  }
  if (!desc && enforce) {
    ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, ctx->f->r,
		"Bogus HTML element %s dropped", name) ;
    return;
  }
  if (desc && desc->depr && (enforce == 2) ) {
    ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, ctx->f->r,
		"Deprecated HTML element %s dropped", name) ;
    return;
  }
#endif

  ap_fputc(ctx->f->next, ctx->bb, '<');
  ap_fputs(ctx->f->next, ctx->bb, name);

  if (attrs) {
    linkattrs =
      apr_hash_get(ctx->cfg->links, name, APR_HASH_KEY_STRING);
    for (a = attrs; *a; a += 2) {
      ctx->offset = 0;
      if (a[1]) {
        pappend(ctx, a[1], strlen(a[1]) + 1);
        is_uri = 0;
        if (linkattrs) {
          tattr *attrs = (tattr *) linkattrs->elts;
          for (i = 0; i < linkattrs->nelts; ++i) {
            if (!strcmp(*a, attrs[i].val)) {
              is_uri = 1;
              break;
            }
          }
        }

        if(is_uri) {
          /* first do the server replacements */
          if(ctx->cfg->map) {
            server_remap_t *remaps = (server_remap_t *)ctx->cfg->map->elts;
            for(i = 0; i < ctx->cfg->map->nelts; ++i) {
              if(!ap_regexec(&(remaps[i].regex), ctx->buf, 0, 0, 0)) {
                int add_auth = ctx->cfg->global_auth | (remaps[i].flags & REMAP_FLAG_AUTH);
                int add_qstring_ignore =
                  ctx->cfg->global_qstring_ignore | (remaps[i].flags & REMAP_FLAG_QSTRING_IGNORE);
                subs = remap_url(ctx, ctx->buf, add_auth, add_qstring_ignore);
                if(subs) {
                  ++num_match;
                  s_to = strlen(subs);
                  s_from = strlen(ctx->buf);
                  if(s_to > s_from)
                    preserve(ctx, s_to - s_from);
                  memcpy(ctx->buf, subs, s_to+1);
                  break; /* only do one substitution per link */
                }
              }
            }
          }
        }
      }
      if (!a[1])
        ap_fputstrs(ctx->f->next, ctx->bb, " ", a[0], NULL);
      else {
        /* write the attribute */
        ap_fputstrs(ctx->f->next, ctx->bb, " ", a[0], "=\"", NULL);
        pcharacters(ctx, (const xmlChar *) ctx->buf, strlen(ctx->buf));
        ap_fputc(ctx->f->next, ctx->bb, '"');
      }
    }
  }
  ctx->offset = 0;
  if(desc && desc->empty)
    ap_fputs(ctx->f->next, ctx->bb, "/>");
  else
    ap_fputc(ctx->f->next, ctx->bb, '>');
}

static saxctxt *check_html_filter_init(ap_filter_t * f)
{
  saxctxt *fctx;
  if (!f->ctx) {
    cdn_conf *cfg = ap_get_module_config(f->r->per_dir_config, &cdn_module);

    const char *errmsg = NULL;
    if(!f->r->content_type)
      errmsg = "check_html_filter_init: no content-type; bailing out of cdn filter";
    else if(cfg->content_types) {
      int i, found = 0;
      tattr *content_types = (tattr *)cfg->content_types->elts;
      for(i = 0; i < cfg->content_types->nelts; ++i) {
        if(!strncasecmp(content_types[i].val, f->r->content_type, strlen(content_types[i].val))) {
          found = 1;
          break;
        }
      }
      if(!found)
        errmsg = "check_html_filter_init: Content-type doesn't match any defined types; "
          "not inserting cdn filter";
    }

    if(errmsg) {
      ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, f->r->server, "%s", errmsg);
      ap_remove_output_filter(f);
      return NULL;
    }

    fctx = f->ctx = apr_pcalloc(f->r->pool, sizeof(saxctxt));
    fctx->f = f;
    fctx->bb =
      apr_brigade_create(f->r->pool, f->r->connection->bucket_alloc);
    fctx->cfg = cfg;
    apr_table_unset(f->r->headers_out, "Content-Length");
  }
  return f->ctx;
}

static xmlCharEncoding sniff_encoding(saxctxt* ctx, const char* cbuf, size_t bytes)
{
  request_rec* r = ctx->f->r;
  cdn_conf* cfg = ctx->cfg;
  xmlCharEncoding ret;
  char* p;
  ap_regmatch_t match[2];
  char* buf = (char*)cbuf;
  const char *encoding = 0;

  /* If we've got it in the HTTP headers, there's nothing to do */
  if(r->content_type && (p = ap_strcasestr(r->content_type, "charset=")) && p != NULL) {
    p += 8;
    if((encoding = apr_pstrndup(r->pool, p, strcspn(p, " ;")))) {
      ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
                   "sniff_encoding: found charset %s in Content-Type", encoding);
      ret = xmlParseCharEncoding(encoding);
      if(((ret != XML_CHAR_ENCODING_ERROR) && (ret != XML_CHAR_ENCODING_NONE)))
        return ret;
    }
  }

  /* to sniff, first we look for BOM */
  if(encoding == NULL) {

    if((ret = xmlDetectCharEncoding((const xmlChar*)buf, bytes)) != XML_CHAR_ENCODING_NONE) {
      ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
                   "sniff_encoding: got charset from XML rules");
      return ret;
    }

    /* If none of the above, look for a META-thingey */
    if(ap_regexec(seek_meta_ctype, buf, 1, match, 0) == 0) {
      p = apr_pstrndup(r->pool, buf + match[0].rm_so, match[0].rm_eo - match[0].rm_so);
      if(ap_regexec(seek_charset, p, 2, match, 0) == 0)
        encoding = apr_pstrndup(r->pool, p+match[1].rm_so, match[1].rm_eo - match[1].rm_so);
    }

  }

  /* either it's set to something we found or it's still the default */
  if(encoding) {
    ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
                 "sniff_encoding: got charset %s from HTML META", encoding);
    ret = xmlParseCharEncoding(encoding);
    if(ret != XML_CHAR_ENCODING_ERROR && ret != XML_CHAR_ENCODING_NONE)
      return ret;

    ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
                 "sniff_encoding: charset %s not supported", encoding);
  }

  /* Use configuration default as a last resort */
  ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
               "sniff_encoding: no suitable charset information");
  return (cfg->default_encoding == XML_CHAR_ENCODING_NONE)
    ? XML_CHAR_ENCODING_8859_1 : cfg->default_encoding ;
}


static const char * skip_to_start(saxctxt *ctxt, const char **bufp, apr_size_t *bytes)
{
  char *p = ap_strchr_c(*bufp, '<');
  tattr *starts = (tattr *) ctxt->cfg->skipto->elts;
  int found = 0;
  while (!found && *p) {
    int i;
    for (i = 0; i < ctxt->cfg->skipto->nelts; ++i) {
      if (!strncasecmp(p + 1, starts[i].val, strlen(starts[i].val))) {
        *bytes -= (p - *bufp);
        *bufp = p;
        found = 1;
        ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, ctxt->f->r->server,
                     "skip_to_start: skipped to first <%s> element", starts[i].val);
        break;
      }
    }
    p = ap_strchr_c(p + 1, '<');
  }
  if (p == NULL) {
    ap_log_error(APLOG_MARK, APLOG_WARNING, APR_SUCCESS, ctxt->f->r->server,
                 "skip_to_start: failed to find start of recognised HTML!");
  }
  return *bufp;
}

#define USE_OLD_LIBXML2
static int create_parser(saxctxt *ctxt, const char **bufp, apr_size_t *bytes)
{
  xmlCharEncoding enc;
#ifndef USE_OLD_LIBXML2
  int xmlopts = XML_PARSE_RECOVER | XML_PARSE_NONET |
    XML_PARSE_NOBLANKS | XML_PARSE_NOERROR | XML_PARSE_NOWARNING;
#endif
  enc = sniff_encoding(ctxt, *bufp, *bytes);
  ctxt->parser = htmlCreatePushParserCtxt(&sax, ctxt, *bufp, 0, 0, enc);
  if (ctxt->parser == NULL)
    return 0;
  apr_pool_cleanup_register
    (ctxt->f->r->pool, ctxt->parser, (int(*)(void*))htmlFreeParserCtxt,
     apr_pool_cleanup_null);
#ifndef USE_OLD_LIBXML2
  if (xmlopts = xmlCtxtUseOptions(ctxt->parser, xmlopts), xmlopts)
    ap_log_error(APLOG_MARK, APLOG_WARNING, APR_SUCCESS, ctxt->f->r,
                 "create_parser: unsupported parser opts %x", xmlopts);
#endif
  return 1;
}

static int initialize_parser(ap_filter_t *f, saxctxt *ctxt, const char **bufp, apr_size_t bytes)
{
  const char *buf = *bufp;

  /* initialize parser */
  if(buf[bytes] != 0) {
    /* make a string for parse routines to play with */
    char *buf1 = apr_palloc(ctxt->f->r->pool, bytes + 1);
    memcpy(buf1, buf, bytes);
    buf1[bytes] = 0;
    buf = *bufp = buf1;
  }

  if(ctxt->cfg->skipto != NULL)
    *bufp = skip_to_start(ctxt, bufp, &bytes);

  if(ctxt->cfg->skipto != NULL && buf != *bufp) {
    /* skip_to_start skipped some bytes, dump them directly */
    ap_fwrite(f->next, ctxt->bb, buf, *bufp - buf);
  }

  if(!create_parser(ctxt, bufp, &bytes))
    return 0;

  return 1;
}

static int cdn_html_filter(ap_filter_t * f, apr_bucket_brigade * bb)
{
  apr_bucket *b;
  const char *buf = 0;
  apr_size_t bytes = 0;

  /* now do HTML filtering if necessary, and pass the brigade onward */
  saxctxt *ctxt = check_html_filter_init(f);
  if (!ctxt)
    return ap_pass_brigade(f->next, bb);

  for(b = APR_BRIGADE_FIRST(bb); b != APR_BRIGADE_SENTINEL(bb); b = APR_BUCKET_NEXT(b)) {
    if(APR_BUCKET_IS_EOS(b) || APR_BUCKET_IS_FLUSH(b)) {
      consume_buffer(ctxt, buf, 0, 1);
      APR_BUCKET_REMOVE(b);
      APR_BRIGADE_INSERT_TAIL(ctxt->bb, b);
      ap_pass_brigade(ctxt->f->next, ctxt->bb);
      return APR_SUCCESS;
    }

    if(apr_bucket_read(b, &buf, &bytes, APR_BLOCK_READ) == APR_SUCCESS && buf) {
      if(ctxt->parser == NULL) {

        /*
         * for now, always output utf-8; we could incorporate
         * mod_proxy_html's output transcoding with little problem if
         * necessary
         */
        ap_set_content_type(f->r, "text/html;charset=utf-8");

        if(!initialize_parser(f, ctxt, &buf, bytes)) {
          apr_status_t rv = ap_pass_brigade(ctxt->f->next, bb);
          ap_remove_output_filter(f);
          return rv;
        } else
          ap_fputs(f->next, ctxt->bb, ctxt->cfg->doctype);
      }
      consume_buffer(ctxt, buf, bytes, 0);
    }

  }

  /*ap_fflush(ctxt->f->next, ctxt->bb) ; */      /* uncomment for debug */
  apr_brigade_cleanup(bb);
  return APR_SUCCESS;
}



static int cdn_post_config
  (apr_pool_t * p, apr_pool_t * p1, apr_pool_t * p2, server_rec * s)
{
  memset(&sax, 0, sizeof(htmlSAXHandler));
  sax.startElement = pstartElement;
  sax.endElement = pendElement;
  sax.characters = pcharacters;
  sax.comment = pcomment;
  sax.cdataBlock = pcdata;
  return OK;
}

static int cdn_request_handler(request_rec *r)
{
  cdn_conf *cfg = ap_get_module_config(r->per_dir_config, &cdn_module);

  /*
   * first, do originification, which only touches output headers, if
   * the object's request URL matches one of the CDNActAsOrigin
   * regexes
   */
  if(cfg->originify) {
    int i, verify_auth;
    act_as_origin_t *orig = (act_as_origin_t *)cfg->originify->elts;
    for(i = 0; i < cfg->originify->nelts; ++i) {
      if(!ap_regexec(&(orig[i].regex), r->uri, 0, 0, 0)) {
        ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
                     "cdn_request_handler: adding CDN origin headers for %s",
                     r->uri);
        verify_auth = add_origin_headers(cfg, r, &orig[i]);
        if(verify_auth && verify_auth_token(cfg, r) != OK)
          return HTTP_UNAUTHORIZED;
        break;
      }
    }
  }

  /* decide whether to install cdn_html_filter */
  if(cfg->content_types && cfg->links && cfg->map) {
    ap_log_error(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, r->server,
                 "cdn_request_handler: adding cdn_html_filter for %s",
                 r->uri);
    ap_add_output_filter_handle(cdn_html_filter_handle, NULL, r, r->connection);
  }

  return DECLINED;
}


static void *cdn_config(apr_pool_t * pool, char *x)
{
  cdn_conf *ret = apr_pcalloc(pool, sizeof(cdn_conf));
  ret->doctype = DEFAULT_DOCTYPE;
  ret->default_encoding = XML_CHAR_ENCODING_NONE;
  ret->bufsz = 8192;
  ret->auth_header_text = "required";
  ret->auth_exptime = 900;
  ret->default_exptime = 86400;

  seek_meta_ctype =
    ap_pregcomp(pool, "(<meta[^>]*http-equiv[ \t\r\n='\"]*content-type[^>]*>)",
                AP_REG_EXTENDED|AP_REG_ICASE);
  seek_charset = ap_pregcomp(pool, "charset=([A-Za-z0-9_-]+)", AP_REG_EXTENDED|AP_REG_ICASE);

  return ret;
}

#define MERGE_ARRAYS(a,b,c) if(a && b) { c = apr_array_append(pool, a, b); } \
  else { c = (a == NULL) ? b : a; }

static void *cdn_merge(apr_pool_t * pool, void *BASE, void *ADD)
{
  cdn_conf *base = (cdn_conf *) BASE;
  cdn_conf *add = (cdn_conf *) ADD;
  cdn_conf *conf = apr_palloc(pool, sizeof(cdn_conf));

  conf->doctype = ( add->doctype == DEFAULT_DOCTYPE )
		? base->doctype : add->doctype;
  conf->default_encoding = (add->default_encoding == XML_CHAR_ENCODING_NONE)
    ? base->default_encoding : add->default_encoding;
  conf->bufsz = add->bufsz;
  conf->skipto = add->skipto ? add->skipto : base->skipto;

  MERGE_ARRAYS(base->map, add->map, conf->map);
  MERGE_ARRAYS(base->originify, add->originify, conf->originify);
  MERGE_ARRAYS(base->from_servers, add->from_servers, conf->from_servers);

  /* don't merge declarations for the below - just use the most specific */
  conf->links = (add->links == NULL) ? base->links : add->links;
  conf->content_types = (add->content_types == NULL) ? base->content_types : add->content_types;
  conf->to_server = (add->to_server == NULL) ? base->to_server : add->to_server;
  conf->auth_key = (add->auth_key == NULL) ? base->auth_key : add->auth_key;
  conf->auth_header_text = (add->auth_header_text == NULL) ? base->auth_header_text : add->auth_header_text;
  conf->auth_exptime = add->auth_exptime ? add->auth_exptime : base->auth_exptime;
  conf->ignore_token = (add->ignore_token == NULL) ? base->ignore_token : add->ignore_token;
  conf->ignore_token_arg_relative = (add->ignore_token_arg_relative == NULL) ?
    base->ignore_token_arg_relative : add->ignore_token_arg_relative;
  conf->ignore_token_direction = add->ignore_token_direction != base->ignore_token_direction ?
    add->ignore_token_direction : base->ignore_token_direction;

  conf->default_exptime = add->default_exptime ? add->default_exptime : base->default_exptime;

  conf->global_auth = base->global_auth | add->global_auth;
  conf->global_qstring_ignore = base->global_qstring_ignore | add->global_qstring_ignore;

  return conf;
}

static const char *set_skipto(cmd_parms * cmd, void *CFG, const char *arg)
{
  tattr *attr;
  cdn_conf *cfg = CFG;
  if (cfg->skipto == NULL)
    cfg->skipto = apr_array_make(cmd->pool, 4, sizeof(tattr));
  attr = apr_array_push(cfg->skipto);
  attr->val = arg;
  return NULL;
}

static const char* set_doctype(cmd_parms* cmd, void* CFG, const char* t, const char* l)
{
  cdn_conf* cfg = (cdn_conf *)CFG ;
  if ( !strcasecmp(t, "xhtml") ) {
    if ( l && !strcasecmp(l, "legacy") )
      cfg->doctype = fpi_xhtml_legacy ;
    else
      cfg->doctype = fpi_xhtml ;
  } else if ( !strcasecmp(t, "html") ) {
    if ( l && !strcasecmp(l, "legacy") )
      cfg->doctype = fpi_html_legacy ;
    else
      cfg->doctype = fpi_html ;
  } else
    cfg->doctype = apr_pstrdup(cmd->pool, t) ;
  return NULL ;
}

static const char* set_charset_default(cmd_parms* cmd, void* CFG, const char* charset)
{
  cdn_conf* cfg = (cdn_conf *)CFG;
  cfg->default_encoding = xmlParseCharEncoding(charset);
  switch(cfg->default_encoding) {
  case XML_CHAR_ENCODING_NONE:
    return "Default charset not found";
  case XML_CHAR_ENCODING_ERROR:
    return "Invalid or unsupported default charset";
  default:
    return NULL;
  }
}

static const char *set_links
  (cmd_parms * cmd, void *CFG, const char *elt, const char *att)
{
  apr_array_header_t *attrs;
  tattr *attr;
  cdn_conf *cfg = CFG;

  if (cfg->links == NULL)
    cfg->links = apr_hash_make(cmd->pool);

  attrs = apr_hash_get(cfg->links, elt, APR_HASH_KEY_STRING);
  if (!attrs) {
    attrs = apr_array_make(cmd->pool, 2, sizeof(tattr *));
    apr_hash_set(cfg->links, elt, APR_HASH_KEY_STRING, attrs);
  }
  attr = apr_array_push(attrs);
  attr->val = att;
  return NULL;
}

static const char *set_content_type(cmd_parms * cmd, void *CFG, const char *arg)
{
  tattr *attr;
  cdn_conf *cfg = CFG;
  if(cfg->content_types == NULL)
    cfg->content_types = apr_array_make(cmd->pool, 4, sizeof(tattr));
  attr = apr_array_push(cfg->content_types);
  attr->val = arg;
  return NULL;
}

static const char * set_fromservers(cmd_parms * cmd, void *CFG, const char *arg)
{
  tattr *attr;
  cdn_conf *cfg = CFG;
  if(cfg->from_servers == NULL)
    cfg->from_servers = apr_array_make(cmd->pool, 4, sizeof(tattr));
  attr = apr_array_push(cfg->from_servers);
  attr->val = arg;
  return NULL;
}

#define FLAG(n,s,c) ( (s&&(ap_strchr_c((s),(c))!=NULL)) ? (n) : 0 )

static const char * set_serverremap(cmd_parms *cmd, void *CFG, const char *args)
{
  cdn_conf *cfg = (cdn_conf *)CFG;
  server_remap_t *remap;
  unsigned int regflags = 0;
  const char *pattern, *flags;
  const char *usage = "Usage: CDNHTMLRemapURLServer pattern [flags]";

  pattern = ap_getword_conf(cmd->pool, &args);
  if(!pattern)
    return usage;
  flags = ap_getword_conf(cmd->pool, &args);
  if(flags && !*flags)
    flags = NULL;

  if(cfg->map == NULL)
    cfg->map = apr_array_make(cmd->pool, 4, sizeof(server_remap_t));
  remap = apr_array_push(cfg->map);

  regflags = AP_REG_NOSUB | FLAG(AP_REG_EXTENDED, flags, 'x') |
    FLAG(AP_REG_ICASE, flags, 'i');
  if(ap_regcomp(&(remap->regex), pattern, regflags) != 0)
    return "CDNHTMLRemapURLServer: error compiling regex";

  remap->flags |= FLAG(REMAP_FLAG_AUTH, flags, 'a') |
    FLAG(REMAP_FLAG_QSTRING_IGNORE, flags, 'q');

  return NULL;
}

static const char * set_act_as_origin(cmd_parms *cmd, void *CFG, const char *args)
{
  cdn_conf *cfg = (cdn_conf *)CFG;
  act_as_origin_t *orig;
  unsigned int regflags = 0;
  const char *pattern, *flags, *exptime;
  const char *usage = "Usage: CDNActAsOrigin pattern [flags] [exptime]";

  pattern = ap_getword_conf(cmd->pool, &args);
  if(!pattern)
    return usage;
  flags = ap_getword_conf(cmd->pool, &args);
  if(flags && !*flags)
    flags = NULL;
  exptime = ap_getword_conf(cmd->pool, &args);
  if(exptime && !*exptime)
    exptime = NULL;

  if(cfg->originify == NULL)
    cfg->originify = apr_array_make(cmd->pool, 4, sizeof(act_as_origin_t));
  orig = apr_array_push(cfg->originify);

  regflags = AP_REG_NOSUB | FLAG(AP_REG_EXTENDED, flags, 'x') |
    FLAG(AP_REG_ICASE, flags, 'i');
  if(ap_regcomp(&(orig->regex), pattern, regflags) != 0)
    return "CDNActAsOrigin: error compiling regex";

  orig->flags |= FLAG(ORIGINIFY_FLAG_EXPIRE, flags, 'e') |
    FLAG(ORIGINIFY_FLAG_AUTH, flags, 'a');

  if(orig->flags & ORIGINIFY_FLAG_EXPIRE) {
    if(exptime) {
      errno = 0;
      orig->exptime = strtol(exptime, NULL, 10);
      if(errno)
        return "CDNActAsOrigin: error setting expiration time";
    } else if(cfg->default_exptime) {
      orig->exptime = cfg->default_exptime;
    } else
      return "CDNActAsOrigin: expiration flag set but no expiration time given";
  }

  return NULL;
}

static const char *set_auth_alt(cmd_parms * cmd, void *CFG, const char *arg)
{
  cdn_conf *cfg = CFG;
  cfg->auth_header_text = apr_pstrcat(cmd->pool, "required,alt=", arg, NULL);
  return NULL;
}

static const char *set_ignore_token(cmd_parms * cmd, void *CFG, const char *arg)
{
  cdn_conf *cfg = CFG;
  cfg->ignore_token = apr_pstrcat(cmd->pool, arg, "=ignore", NULL);
  return NULL;
}

static const char *set_ignore_token_location
  (cmd_parms * cmd, void *CFG, const char *where, const char *arg)
{
  cdn_conf *cfg = CFG;
  if(!strcasecmp(where, "before"))
    cfg->ignore_token_direction = BEFORE;
  else if(!strcasecmp(where, "after"))
    cfg->ignore_token_direction = AFTER;
  else
    return "CDNHTMLIgnoreTokenLocation: first argument must be \"before\" or \"after\"";
  cfg->ignore_token_arg_relative = apr_pstrdup(cmd->pool, arg);
  return NULL;
}

static const command_rec cdn_cmds[] = {
  AP_INIT_ITERATE("CDNHTMLFromServers", set_fromservers, NULL,
                  RSRC_CONF | ACCESS_CONF,
                  "Set server names that will be replaced by CDNHTMLMapServer"),
  AP_INIT_TAKE1("CDNHTMLToServer", ap_set_string_slot,
                (void *)APR_OFFSETOF(cdn_conf, to_server),
                RSRC_CONF | ACCESS_CONF,
                "Set destination server name for CDNHTMLRemapURLServer"),
  AP_INIT_RAW_ARGS("CDNHTMLRemapURLServer", set_serverremap, NULL,
                   RSRC_CONF | ACCESS_CONF,
                   "Convert matching URLs to come from a different server"),

  AP_INIT_ITERATE("CDNHTMLContentType", set_content_type, NULL,
                  RSRC_CONF | ACCESS_CONF,
                  "Declare content types that will be parsed for CDNification as HTML"),

  AP_INIT_TAKE12("CDNHTMLDocType", set_doctype, NULL,
                 RSRC_CONF|ACCESS_CONF, "(HTML|XHTML) [Legacy]"),

  AP_INIT_TAKE1("CDNHTMLCharsetDefault", set_charset_default, NULL,
                RSRC_CONF|ACCESS_CONF, "Set default input/output character set"),

  AP_INIT_ITERATE("CDNHTMLStartParse", set_skipto, NULL,
                  RSRC_CONF | ACCESS_CONF,
                  "Ignore anything in front of the first of these elements"),
  AP_INIT_ITERATE2("CDNHTMLLinks", set_links, NULL,
                   RSRC_CONF | ACCESS_CONF,
                   "Declare HTML Attributes"),
  AP_INIT_TAKE1("CDNHTMLBufSize", ap_set_int_slot,
                (void *) APR_OFFSETOF(cdn_conf, bufsz),
                RSRC_CONF | ACCESS_CONF, "Buffer size"),

  AP_INIT_TAKE1("CDNAuthKey", ap_set_string_slot,
                (void *)APR_OFFSETOF(cdn_conf, auth_key),
                RSRC_CONF | ACCESS_CONF,
                "Key for generating and validating authentication tokens of protected content"),
  AP_INIT_TAKE1("CDNAuthAlt", set_auth_alt, NULL,
                RSRC_CONF | ACCESS_CONF,
                "Alternate redirection URL for failed authentications"),
  AP_INIT_TAKE1("CDNAuthExpire", ap_set_int_slot,
                (void *) APR_OFFSETOF(cdn_conf, auth_exptime),
                RSRC_CONF | ACCESS_CONF, "Set default expiration time for generated authentication tokens"),
  AP_INIT_FLAG("CDNHTMLAddAuthTokens", ap_set_flag_slot,
               (void *)APR_OFFSETOF(cdn_conf, global_auth),
               RSRC_CONF | ACCESS_CONF,
               "Add authentication tokens to all matching URLs"),

  AP_INIT_TAKE1("CDNIgnoreTokenName", set_ignore_token, NULL,
                RSRC_CONF | ACCESS_CONF,
                "Set the name of the ignore token argument to be added to query strings"),
  AP_INIT_TAKE2("CDNHTMLIgnoreTokenLocation", set_ignore_token_location, NULL,
                RSRC_CONF | ACCESS_CONF,
                "Set the location in the query string to insert an ignore token"),
  AP_INIT_FLAG("CDNHTMLAddIgnoreTokens", ap_set_flag_slot,
               (void *)APR_OFFSETOF(cdn_conf, global_qstring_ignore),
               RSRC_CONF | ACCESS_CONF,
               "Add ignore tokens to the query strings of all matching URLs"),

  AP_INIT_RAW_ARGS("CDNActAsOrigin", set_act_as_origin, NULL,
                   RSRC_CONF | ACCESS_CONF,
                   "Set proper origin headers for matching requests"),

  AP_INIT_TAKE1("CDNDefaultExpire", ap_set_int_slot,
                (void *)APR_OFFSETOF(cdn_conf, default_exptime),
                RSRC_CONF | ACCESS_CONF,
                "Set default expiration time for originified responses"),
  {NULL}
};

static void cdn_hooks(apr_pool_t * p)
{
  ap_hook_fixups(cdn_request_handler, NULL, NULL, APR_HOOK_MIDDLE);

  cdn_html_filter_handle =
    ap_register_output_filter_protocol
      ("CDN_HTML",
       cdn_html_filter,
       NULL,
       AP_FTYPE_RESOURCE,
       AP_FILTER_PROTO_CHANGE | AP_FILTER_PROTO_CHANGE_LENGTH);

  ap_hook_post_config(cdn_post_config, NULL, NULL, APR_HOOK_MIDDLE);
}

module AP_MODULE_DECLARE_DATA cdn_module = {
  STANDARD20_MODULE_STUFF,
  cdn_config,
  cdn_merge,
  NULL,
  NULL,
  cdn_cmds,
  cdn_hooks
};
