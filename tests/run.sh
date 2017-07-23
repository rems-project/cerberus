#!/bin/bash

export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:$HOME/Applications/usr/lib

source tests.sh

mkdir -p tmp

pass=0
fail=0

function test {
  ../cerberus --exec --batch $2/$1 > tmp/result 2> /dev/null
  cmp --silent tmp/result $2/expected/$1.expected
  if [[ "$?" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
    cat tmp/result
  fi

  echo -e "Test $1: $res"
}


# Running ci tests
for file in "${citests[@]}"
do
  test $file ci
done

echo "PASSED: $pass"
echo "FAILED: $fail"
