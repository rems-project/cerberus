#!/bin/bash
# run-copy-prop-phase1.sh — regression check
# Verifies that --sw copy_prop does not change output of existing CI tests (0001–0365).

TESTSDIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
cd "$TESTSDIR"

source ./tests.sh   # citests, skip
source ./common.sh  # set_cerberus_exec

mkdir -p tmp

pass=0
fail=0

function doSkip {
  for f in "${skip[@]}"; do [[ $f == $1 ]] && return 0; done
  return 1
}

# report <display-name> <file-for-type-check> <ret>
function report {
  local label=$1
  local file=$2
  local ret=$3
  local res=$ret

  if [[ $file == *.error.c || $file == *.undef.c ]]; then
    res=$((1 - ret))
  fi

  if [[ $file == *.unsup.c ]]; then
    cat tmp/result tmp/stderr | grep -q "feature not yet supported"
    res=$?
  fi

  if [[ "$((res))" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
    cat tmp/result tmp/stderr
  fi

  echo -e "Test $label: $res"
}

if [[ $# == 1 ]]; then
  citests=("$(basename "$1")")
fi

set_cerberus_exec "cerberus"

echo "=== Phase 1: regression (--sw copy_prop must not change output of existing tests) ==="

for file in "${citests[@]}"; do
  if [[ ! -f ./ci/$file ]]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m"
    fail=$((fail+1))
    continue
  fi

  if doSkip "$file"; then
    echo -e "Test $file: \033[1m\033[33mSKIPPING\033[0m"
    continue
  fi

  if [[ $file == *.syntax-only.c ]]; then
    $CERB --nolibc --typecheck-core --sw copy_prop ci/$file > tmp/result 2> tmp/stderr
  else
    $CERB --nolibc --typecheck-core --exec --batch --sw copy_prop ci/$file > tmp/result 2> tmp/stderr
  fi
  ret=$?

  if [[ -f ./ci/expected/$file.expected ]]; then
    if [[ $file == *.error.c || $file == *.syntax-only.c ]]; then
      if [ "$(uname)" == "Linux" ]; then
        sed -i '$ d' tmp/stderr
      else
        sed -i '' -e '$ d' tmp/stderr
      fi
      if ! cmp --silent tmp/stderr ci/expected/$file.expected; then
        ret=0
      fi
    else
      if ! cmp --silent tmp/result ci/expected/$file.expected; then
        if [[ $file == *.undef.c ]]; then
          ret=0
        else
          ret=1
        fi
      fi
    fi
  else
    echo -e "Test $file: \033[1m\033[33mMISSING .expected FILE\033[0m"
    continue
  fi

  report "$file [+copy_prop]" "$file" "$ret"
done

echo ""
echo "COPY_PROP PHASE 1 PASSED: $pass"
echo "COPY_PROP PHASE 1 FAILED: $fail"
[ $fail -eq 0 ]
