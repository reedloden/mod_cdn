#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.61)
AC_INIT([mod_cdn], [1.1.1], [support@voxel.net], [mod_cdn], [http://www.voxel.net/labs/mod_cdn/])
AC_CONFIG_SRCDIR([mod_cdn.c])
AC_CONFIG_MACRO_DIR([m4])

AM_INIT_AUTOMAKE([-Wall -Werror foreign])

# Checks for programs.
AC_PROG_CC
AC_PROG_INSTALL
AC_PROG_LIBTOOL

# Checks for libraries.
AP_VERSION=2.0.0
AP_CHECK_APACHE([$AP_VERSION], [
   LIBTOOL="`$APR_CONFIG --apr-libtool`"
   AC_SUBST([LIBTOOL])

   MODULE_CFLAGS="$AP_CFLAGS"
   AC_SUBST([MODULE_CFLAGS])

   MODULE_LDFLAGS="`$APR_CONFIG --link-libtool` `$APU_CONFIG --link-libtool`"
   AC_SUBST([MODULE_LDFLAGS])

   BIN_LDFLAGS="`$APR_CONFIG --link-libtool` `$APU_CONFIG --link-libtool` `$APR_CONFIG --ldflags --libs` `$APU_CONFIG --ldflags --libs`"
   AC_SUBST([BIN_LDFLAGS])

   prefix="$AP_PREFIX"
], AC_MSG_ERROR([*** Apache version >= $AP_VERSION not found!]))

LIBXML_VERSION=2.5.10
AM_PATH_XML2([$LIBXML_VERSION], AC_SUBST([XML_CPPFLAGS]),
             AC_MSG_ERROR([missing program 'xml2-config'; is 'libxml2' or 'libxml2-devel' installed?]))

# Checks for header files.
AC_CHECK_HEADER([openssl/sha.h], [],
                AC_MSG_ERROR([missing header 'openssl/sha.h'; is 'openssl-devel' installed?]))

# Checks for typedefs, structures, and compiler characteristics.
AC_TYPE_SIZE_T

# Checks for library functions.
AC_FUNC_MKTIME
AC_FUNC_REALLOC

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
