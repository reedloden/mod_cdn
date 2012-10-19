#!/bin/sh

aclocal -I m4 \
  && libtoolize --copy \
  && automake --add-missing --foreign --copy \
  && autoconf \
  && ./configure $@
