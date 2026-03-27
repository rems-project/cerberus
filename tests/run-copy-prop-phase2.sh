#!/bin/bash
# run-copy-prop-phase2.sh — elimination check
# Verifies that --sw copy_prop eliminates pure-sym aliases from Core IR.

TESTSDIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
cd "$TESTSDIR"

source ./common.sh  # set_cerberus_exec

mkdir -p tmp

pass=0
fail=0

function report {
  local label=$1
  local ret=$2

  if [[ "$((ret))" -eq "0" ]]; then
    echo -e "Test $label: \033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    echo -e "Test $label: \033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
  fi
}

set_cerberus_exec "cerberus"

echo "=== Phase 2: elimination (--sw copy_prop expected create() counts) ==="

# Expected create() counts in Core IR after copy_prop.
# Tests 0373 uses both switches, so count is compared for --sw copy_prop only.
declare -A elim_expected
elim_expected=(
  [0366-copy_prop_simple.c]=1
  [0367-copy_prop_chain.c]=2
  [0368-copy_prop_compound_lit.c]=2
  [0369-copy_prop_if.c]=3
  [0370-copy_prop_loop.c]=2
  [0371-copy_prop_no_elim_action.c]=2
  [0372-copy_prop_no_elim_literal.c]=1
  [0373-copy_prop_and_mem2reg.c]=2
)

for file in "${!elim_expected[@]}"; do
  expected_creates=${elim_expected[$file]}

  if [[ ! -f ./ci/$file ]]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m"
    fail=$((fail+1))
    continue
  fi

  $CERB --nolibc --pp core --sw copy_prop ci/$file > tmp/core_out 2>/dev/null
  actual=$(grep -c 'create(' tmp/core_out || true)

  if [[ "$actual" -eq "$expected_creates" ]]; then
    report "$file [create($actual)==$expected_creates]" 0
  else
    echo "  → got create($actual), want $expected_creates"
    report "$file [create($actual)!=$expected_creates]" 1
  fi
done

echo ""
echo "=== Integration: --sw copy_prop --sw mem2reg on 0373 ==="
# Verify that 0373 with both switches has fewer creates than mem2reg alone,
# confirming that copy_prop exposes the compound literal pointer to mem2reg.
$CERB --nolibc --pp core --sw mem2reg ci/0373-copy_prop_and_mem2reg.c > tmp/core_mem2reg 2>/dev/null
$CERB --nolibc --pp core --sw copy_prop --sw mem2reg ci/0373-copy_prop_and_mem2reg.c > tmp/core_both 2>/dev/null
n_mem2reg=$(grep -c 'create(' tmp/core_mem2reg || true)
n_both=$(grep -c 'create(' tmp/core_both || true)

echo "  mem2reg alone: create=$n_mem2reg"
echo "  copy_prop+mem2reg: create=$n_both"
if [[ "$n_both" -le "$n_mem2reg" ]]; then
  report "0373 integration [copy_prop+mem2reg creates($n_both) <= mem2reg($n_mem2reg)]" 0
else
  report "0373 integration [copy_prop+mem2reg creates($n_both) > mem2reg($n_mem2reg) — UNEXPECTED]" 1
fi

echo ""
echo "COPY_PROP PHASE 2 PASSED: $pass"
echo "COPY_PROP PHASE 2 FAILED: $fail"
[ $fail -eq 0 ]
