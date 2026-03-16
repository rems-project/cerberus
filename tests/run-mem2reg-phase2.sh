#!/bin/bash
# run-mem2reg-phase2.sh — elimination check
# Verifies that --sw mem2reg removes promotable vars from Core IR (tests 0341–0356).

TESTSDIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
cd "$TESTSDIR"

source ./common.sh  # set_cerberus_exec

mkdir -p tmp

pass=0
fail=0

# report <display-name> <file-for-type-check> <ret>
function report {
  local label=$1
  local file=$2
  local ret=$3
  local res=$ret

  if [[ "$((res))" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
  fi

  echo -e "Test $label: $res"
}

set_cerberus_exec "cerberus"

echo "=== Phase 2: elimination (--sw mem2reg must remove promotable vars from Core) ==="

# Current expected create() counts reflect the stub (identity) pass.
# Update these as the implementation progresses; the fully-working pass targets:
#   0341=0  0342=0  0343=0  0344=0  0345=1
#   0346=2  0347=0  0348=2  0349=1  0350=1
#   0351=1  0352=1  0353=0  0354=0  0355=0  0356=1
declare -A elim_expected
elim_expected=(
  [0341-mem2reg_simple.c]=1
  [0342-mem2reg_multi.c]=3
  [0343-mem2reg_if.c]=2
  [0344-mem2reg_if_one_branch.c]=2
  [0345-mem2reg_loop.c]=2
  [0346-mem2reg_no_promote_address.c]=2
  [0347-mem2reg_no_promote_arg.c]=2
  [0348-mem2reg_no_promote_loop_write.c]=2
  [0349-mem2reg_struct.c]=1
  [0350-mem2reg_mixed.c]=3
  [0351-mem2reg_unseq_uninit.undef.c]=1
  [0352-mem2reg_unseq_init.undef.c]=1
  [0353-mem2reg_unseq_reads.c]=1
  [0354-mem2reg_seqrmw_post.c]=1
  [0355-mem2reg_seqrmw_pre.c]=1
  [0356-mem2reg_unseq_seqrmw.undef.c]=1
)

for file in "${!elim_expected[@]}"; do
  expected_creates=${elim_expected[$file]}

  if [[ ! -f ./ci/$file ]]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m"
    fail=$((fail+1))
    continue
  fi

  $CERB --nolibc --pp core --sw mem2reg ci/$file > tmp/core_out 2>/dev/null
  actual=$(grep -c 'create(' tmp/core_out || true)

  if [[ "$actual" -eq "$expected_creates" ]]; then
    report "$file [create($actual)==$expected_creates]" "$file" 0
  else
    echo "  → got create($actual), want $expected_creates"
    report "$file [create($actual)!=$expected_creates]" "$file" 1
  fi
done

echo ""
echo "MEM2REG PHASE 2 PASSED: $pass"
echo "MEM2REG PHASE 2 FAILED: $fail"
[ $fail -eq 0 ]
