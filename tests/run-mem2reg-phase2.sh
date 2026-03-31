#!/bin/bash
# run-mem2reg-phase2.sh — promotable-symbol check
# Verifies that --sw copy_prop,mem2reg identifies the right promotable vars
# (checked via -d 3 debug output from core_mem2reg.ml).
#
# Usage:
#   bash run-mem2reg-phase2.sh            # run checks
#   bash run-mem2reg-phase2.sh --generate # print current promotable lines for all test files

TESTSDIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
cd "$TESTSDIR"

source ./common.sh  # set_cerberus_exec

mkdir -p tmp

pass=0
fail=0

# report <display-name> <ret>
function report {
  local label=$1
  local ret=$2
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

# extract_promotable_lines <debug_output_file>
# Strips ANSI codes + "(debug N): " prefix, keeps only [mem2reg].*promotable: lines.
function extract_promotable_lines {
  sed 's/\x1b\[[0-9;]*m//g; s/^(debug [0-9]*): //' "$1" \
    | grep '^\[mem2reg\].*promotable:' \
    | sort
}

set_cerberus_exec "cerberus"

# Ordered list of test files (same set as former elim_expected).
test_files=(
  0341-mem2reg_simple.c
  0342-mem2reg_multi.c
  0343-mem2reg_if.c
  0344-mem2reg_if_one_branch.c
  0345-mem2reg_loop.c
  0346-mem2reg_no_promote_address.c
  0347-mem2reg_no_promote_arg.c
  0348-mem2reg_no_promote_loop_write.c
  0349-mem2reg_struct.c
  0350-mem2reg_mixed.c
  0351-mem2reg_unseq_uninit.undef.c
  0352-mem2reg_unseq_init.undef.c
  0353-mem2reg_unseq_reads.c
  0354-mem2reg_seqrmw_post.c
  0355-mem2reg_seqrmw_pre.c
  0356-mem2reg_unseq_seqrmw.undef.c
  0361-mem2reg_loop_read_preinit.c
  0362-mem2reg_loop_escape.c
  0363-mem2reg_nested_loops.c
  0364-mem2reg_loop_uninit_load.undef.c
  0365-mem2reg_compound_lit.c
)

# --generate: print actual promotable lines for all test files and exit.
if [[ "${1:-}" == "--generate" ]]; then
  echo "promotable_expected=("
  for file in "${test_files[@]}"; do
    if [[ ! -f ./ci/$file ]]; then
      echo "  # $file: NOT FOUND" >&2
      continue
    fi
    $CERB --nolibc -d 3 --pp core --sw inner_arg_temps,copy_prop,mem2reg ci/$file >tmp/gen_stdout 2>tmp/gen_debug
    lines=$(extract_promotable_lines tmp/gen_debug)
    echo "  [$file]=\"$lines\""
  done
  echo ")"
  exit 0
fi

echo "=== Phase 2: promotable-symbol check (--sw copy_prop,mem2reg -d 3) ==="

# Hardcoded expected promotable lines per test file.
# Each value is the sorted, newline-joined set of [mem2reg] lines from -d 3 output.
# Regenerate with: bash run-mem2reg-phase2.sh --generate
declare -A promotable_expected
promotable_expected=(
  [0341-mem2reg_simple.c]="[mem2reg] main: 1 promotable: [x_423]"
  [0342-mem2reg_multi.c]="[mem2reg] main: 3 promotable: [x_423, y_424, z_425]"
  [0343-mem2reg_if.c]="[mem2reg] main: 2 promotable: [x_423, cond_424]"
  [0344-mem2reg_if_one_branch.c]="[mem2reg] main: 2 promotable: [x_423, cond_424]"
  [0345-mem2reg_loop.c]="[mem2reg] main: 2 promotable: [x_423, i_424]"
  [0346-mem2reg_no_promote_address.c]="[mem2reg] foo: 1 promotable: [p_421]
[mem2reg] main: 0 promotable: []"
  [0347-mem2reg_no_promote_arg.c]="[mem2reg] id: 1 promotable: [x_421]
[mem2reg] main: 1 promotable: [x_426]"
  [0348-mem2reg_no_promote_loop_write.c]="[mem2reg] main: 2 promotable: [x_423, i_424]"
  [0349-mem2reg_struct.c]="[mem2reg] main: 0 promotable: []"
  [0350-mem2reg_mixed.c]="[mem2reg] main: 1 promotable: [promotable_426]
[mem2reg] sink: 1 promotable: [p_421]"
  [0351-mem2reg_unseq_uninit.undef.c]="[mem2reg] main: 0 promotable: []"
  [0352-mem2reg_unseq_init.undef.c]="[mem2reg] main: 0 promotable: []"
  [0353-mem2reg_unseq_reads.c]="[mem2reg] main: 1 promotable: [x_423]"
  [0354-mem2reg_seqrmw_post.c]="[mem2reg] main: 1 promotable: [x_423]"
  [0355-mem2reg_seqrmw_pre.c]="[mem2reg] main: 1 promotable: [x_423]"
  [0356-mem2reg_unseq_seqrmw.undef.c]="[mem2reg] main: 0 promotable: []"
  [0361-mem2reg_loop_read_preinit.c]="[mem2reg] main: 1 promotable: [x_423]"
  [0362-mem2reg_loop_escape.c]="[mem2reg] fn: 1 promotable: [p_421]
[mem2reg] main: 0 promotable: []"
  [0363-mem2reg_nested_loops.c]="[mem2reg] main: 1 promotable: [x_423]"
  [0364-mem2reg_loop_uninit_load.undef.c]="[mem2reg] main: 1 promotable: [x_423]"
  [0365-mem2reg_compound_lit.c]="[mem2reg] main: 2 promotable: [a_427, x_423]"
)

for file in "${test_files[@]}"; do
  if [[ ! -f ./ci/$file ]]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m"
    fail=$((fail+1))
    continue
  fi

  if [[ -z "${promotable_expected[$file]+set}" ]]; then
    echo -e "Test $file: \033[1m\033[33mSKIP\033[0m (no expected value)"
    continue
  fi

  $CERB --nolibc -d 3 --pp core --sw inner_arg_temps,copy_prop,mem2reg ci/$file >/dev/null 2>tmp/debug_out
  actual_sorted=$(extract_promotable_lines tmp/debug_out)
  expected_sorted=$(printf '%s\n' "${promotable_expected[$file]}" | sort)

  if [[ "$actual_sorted" == "$expected_sorted" ]]; then
    report "$file" 0
  else
    echo "  → got:      $actual_sorted"
    echo "  → expected: $expected_sorted"
    report "$file" 1
  fi
done

echo ""
echo "MEM2REG PHASE 2 PASSED: $pass"
echo "MEM2REG PHASE 2 FAILED: $fail"
[ $fail -eq 0 ]
