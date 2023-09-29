#! /bin/bash

# tests for the CN tool attached to cerberus

DIRNAME=$(dirname $0)

SUCC=$(find $DIRNAME/cn -name '*.c' | grep -v '\.error\.c' | grep -v '\.unknown\.c')

NUM_FAILED=0
FAILED=''

for TEST in $SUCC
do
  echo cn $TEST
  if ! cn $TEST
  then
    NUM_FAILED=$(( $NUM_FAILED + 1 ))
    FAILED="$FAILED $TEST"
  fi
  echo
done

FAIL=$(find $DIRNAME/cn -name '*.error.c')

for TEST in $FAIL
do
  echo cn --expect-failure $TEST
  if ! cn --expect-failure $TEST
  then
    NUM_FAILED=$(( $NUM_FAILED + 1 ))
    FAILED="$FAILED $TEST"
  fi
  echo
done

UNKNOWN=$(find $DIRNAME/cn -name '*.unknown.c')

echo $UNKNOWN | xargs -n 1 cn

COQ_LEMMAS=$(find $DIRNAME/cn -name 'coq_lemmas' -type d)

for TEST in $COQ_LEMMAS
do
  if [ "$1" == "--coq" ]
  then
    echo make -C $TEST
    if ! make -C $TEST
    then
      NUM_FAILED=$(( $NUM_FAILED + 1 ))
      FAILED="$FAILED $TEST"
    fi
  fi
done

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


