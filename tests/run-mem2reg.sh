#!/bin/bash
# run-mem2reg.sh — two-phase mem2reg validation
#   Phase 1: --sw mem2reg must not change output of existing CI tests
#   Phase 2: --sw mem2reg must identify the right promotable vars (tests/mem2reg/)

TESTSDIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)

bash "$TESTSDIR/run-mem2reg-phase1.sh" "$@" && bash "$TESTSDIR/run-mem2reg-phase2.sh" "$@"
