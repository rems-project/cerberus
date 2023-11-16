#! /bin/bash

# tests for the CN tool attached to cerberus

DIRNAME=$(dirname $0)

SUCC=$(find $DIRNAME/cn -name '*.c' | grep -v '\.error\.c' | grep -v '\.unknown\.c' | grep -v '\-exec\.c')

NUM_FAILED=0
FAILED=''

mkdir -p $DIRNAME/cn/exec

for TEST in $SUCC
do
  mkdir -p $DIRNAME/cn/exec/$(basename $TEST .c)
  echo cn $TEST --output_decorated=$DIRNAME/cn/exec/$(basename $TEST .c)/$(basename $TEST .c)-exec.c
  if ! cn $TEST --output_decorated=$DIRNAME/cn/exec/$(basename $TEST .c)/$(basename $TEST .c)-exec.c
  then
    NUM_FAILED=$(( $NUM_FAILED + 1 ))
    FAILED="$FAILED $TEST"
  fi
done

FAIL=$(find $DIRNAME/cn -name '*.error.c')

for TEST in $FAIL
do
  echo cn --expect-fail $TEST
  if ! cn --expect-failure $TEST
  then
    NUM_FAILED=$(( $NUM_FAILED + 1 ))
    FAILED="$FAILED $TEST"
  fi
done

UNKNOWN=$(find $DIRNAME/cn -name '*.unknown.c')

echo $UNKNOWN | xargs -n 1 cn

echo
echo 'Done running tests.'
echo

if [ -z "$FAILED" ]
then
  echo "All tests passed."
  exit 0
else
  echo "$NUM_FAILED tests failed:"
  echo "  $FAILED"
  exit 1
fi


