#! /bin/bash

# tests for the CN executable spec tool attached to cerberus

DIRNAME=$1

SUCC=$(find $DIRNAME -maxdepth 1 -name '*.c' | grep -v '\.error\.c' | grep -v '\.unknown\.c' | grep -v '\-exec\.c')

NUM_FAILED=0
FAILED=''

mkdir -p $DIRNAME/exec

for TEST in $SUCC
do
  mkdir -p $DIRNAME/exec/$(basename $TEST .c)
  echo cn $TEST --output_decorated=$(basename $TEST .c)-exec.c --output_decorated_dir=$DIRNAME/exec/$(basename $TEST .c)/
  if ! ~/.opam/4.14.0/bin/cn $TEST --output_decorated=$(basename $TEST .c)-exec.c --output_decorated_dir=$DIRNAME/exec/$(basename $TEST .c)/
  then
    NUM_FAILED=$(( $NUM_FAILED + 1 ))
    FAILED="$FAILED $TEST"
  fi
done

FAIL=$(find $DIRNAME -name '*.error.c')

for TEST in $FAIL
do
  echo cn --expect-fail $TEST
  if ! cn --expect-failure $TEST
  then
    NUM_FAILED=$(( $NUM_FAILED + 1 ))
    FAILED="$FAILED $TEST"
  fi
done

UNKNOWN=$(find $DIRNAME -name '*.unknown.c')

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


