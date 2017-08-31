#!/usr/bin/env bash
DIR=$(dirname $0)
SRC_EXT="ltz"
DST_EXT="tz"
SRC="$1"
DST="$DIR/michelson/$(basename $SRC .$SRC_EXT).$DST_EXT"
make debug && \
( rm $DST 2>/dev/null ; ./main.d.byte -c $SRC -o $DST ) && \
echo -e '\n' && \
cat $DST && \
tezos-client typecheck program file:$DST
