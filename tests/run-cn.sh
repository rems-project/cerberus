#! /bin/bash

# tests for the CN tool attached to cerberus

DIRNAME=$(dirname $0)

set -e

SUCC=$(find $DIRNAME/cn -name '*.c' | grep -v '\.error\.c' | grep -v '\.unknown\.c')

for TEST in $SUCC
do
  echo cn $TEST
  cn $TEST
done

FAIL=$(find $DIRNAME/cn -name '*.error.c')

for TEST in $FAIL
do
  echo cn --expect-fail $TEST
  cn --expect-failure $TEST
done

echo "All tests passed."

return 0

