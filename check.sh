#!/usr/bin/env bash
SRC="$1"
DST="$(basename $SRC .lt).tz"
make debug && \
./main.d.byte -c $SRC -o $DST && \
echo -e '\n' && \
cat $DST && \
tezos-client typecheck program file:$DST
