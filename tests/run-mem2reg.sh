#!/bin/bash
# run-mem2reg.sh — two-phase mem2reg validation
#   Phase 1: --sw mem2reg must not change output of existing tests (0001–0340)
#   Phase 2: --sw mem2reg must eliminate promotable vars from Core (0341–0350)

TESTSDIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)

bash "$TESTSDIR/run-mem2reg-phase1.sh" "$@" && bash "$TESTSDIR/run-mem2reg-phase2.sh" "$@"
