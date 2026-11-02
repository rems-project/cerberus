#!/bin/bash
set -euo pipefail

# Run in the active opam switch. As in the other test runners, setting
# USE_OPAM selects installed CLI executables; otherwise build local ones.
TESTSDIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$TESTSDIR/.."

if [[ -n "${USE_OPAM+x}" ]]; then
  logging_prefix=${OPAM_SWITCH_PREFIX:?Activate an opam switch before setting USE_OPAM}
else
  logging_prefix=${DUNE_BUILD_DIR:-_build}/install/default
fi

make prelude-src
if [[ -z "${USE_OPAM+x}" ]]; then
  dune build --profile=release cerberus-lib.install cerberus.install
fi
dune runtest --profile=release tests/logging
python3 tests/logging/test_provers.py

for backend in cerberus cerberus-vip; do
  echo "Checking $backend logging"
  python3 tests/logging/test_cli.py \
    --binary "$logging_prefix/bin/$backend" --runtime "$logging_prefix"
done
