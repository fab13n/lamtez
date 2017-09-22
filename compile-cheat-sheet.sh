#!/bin/bash

DIR="$(dirname $0)"
SRC="$DIR/CHEAT-SHEET.tex"
DST="$DIR/$(basename "$SRC" .tex).pdf"
POLL_DELAY=1
FAILURE_DELAY=10

while true; do
	  if [ "$SRC" -nt "$DST" ]; then
		  pdflatex -halt-on-error -output-directory="$DIR" "$SRC" || sleep $FAILURE_DELAY
		  echo "Compiled at $(date)"
	  fi
	  sleep $POLL_DELAY
done
