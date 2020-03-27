#!/bin/bash

set -e -o pipefail

# from https://stackoverflow.com/a/246128
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

for TEST in examples/*.c; do
    echo "$TEST"
    dune exec --no-print-directory -- ail_to_coq --no-spec "$TEST"
done
