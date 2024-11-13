#!/usr/bin/env bash
set -euo pipefail -o noclobber

for file in "$(dirname $0)"/cn_vip_testsuite/*.json
do
    ./tests/diff-prog.py cn "$file" 2> "${file%.json}.patch" || (cat "${file%.json}.patch"; exit 1)
done || exit 1
