#!/bin/bash

export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:`ocamlfind query z3`
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`ocamlfind query z3`

. ./tests.sh

mkdir -p tmp

pass=0
fail=0


# Arguments:
# 1: test case name
# 2: result (0 is success)
function report {
  #If the test should fail
  if [[ $1 == *.fail.c ]]; then
    res="1 - $2";
  else
    res=$2;
  fi

  #If the test is about undef
  if [[ $1 == *.undef.c ]]; then
    cat tmp/result tmp/stderr | grep -E "Undefined|UNDEFINED"
    res=$?
  fi

  # If the test is about something currently not supported
  # This can still test the parser
  if [[ $1 == *.unsup.c ]]; then
    cat tmp/result tmp/stderr | grep "feature not yet supported"
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

  echo -e "Test $1: $res"
}

# Running ci tests
for file in "${citests[@]}"
do
  ../cerberus --exec --batch ci/$file > tmp/result 2> tmp/stderr
  if [ -f ./ci/expected/$file.expected ]; then
    if [[ $file == *.error.c ]]; then 
      cmp --silent tmp/stderr ci/expected/$file.expected
    else
      cmp --silent tmp/result ci/expected/$file.expected
    fi
  fi
  report $file $?
done
echo "CI PASSED: $pass"
echo "CI FAILED: $fail"
