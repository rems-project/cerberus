#!/usr/bin/env -S bash -euo pipefail

for FILE in "$@"
do
  dot2tex -ftikz -c -t math --autosize "${FILE}" > "${FILE/%.dot/}.tex" && pdflatex "${FILE/%.dot/}.tex"
done
