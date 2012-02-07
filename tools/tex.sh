#!/bin/bash

for FILE in "$@"
do
  /usr/bin/dot2tex -ftikz -c -t math --autosize "${FILE}" > "${FILE/%.dot/}.tex" && pdflatex "${FILE/%.dot/}.tex"
done
