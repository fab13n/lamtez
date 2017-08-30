#!/usr/bin/env bash
SRC_EXT="ltz"
DST_EXT="tz"
SRC="$1"
DST="$(basename $SRC .$SRC_EXT).$DST_EXT"
make debug && \
( rm $DST ; \
  ./main.d.byte -c $SRC -o $DST ) && \
echo -e '\n' && \
cat $DST && \
tezos-client typecheck program file:$DST
