#!/bin/bash
set -euo pipefail -o noclobber

# copying from run-ci.sh
export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-}:`ocamlfind query z3`"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:`ocamlfind query z3`"
CN=$OPAM_SWITCH_PREFIX/bin/cn


DIRNAME=$(dirname $0)

SUCC=$(find $DIRNAME/cn -name '*.c' | grep -v '\.error\.c')
FAIL=$(find $DIRNAME/cn -name '*.error.c')

NUM_FAILED=0
FAILED=''


for TEST in $SUCC
do
  $CN verify $TEST
  RET=$?
  if [[ "$RET" = 0 ]]
  then
    echo "$TEST -- OK"
  else
    echo "$TEST -- Unexpected"
    NUM_FAILED=$(( $NUM_FAILED + 1 ))
    FAILED="$FAILED $TEST"
  fi
  echo
done

for TEST in $FAIL
do
  $CN verify $TEST
  RET=$?
  if [[ "$RET" = 1 || "$RET" = 2 ]]
  then
    echo "$TEST -- OK"
  else
    echo "$TEST -- Unexpected"
    NUM_FAILED=$(( $NUM_FAILED + 1 ))
    FAILED="$FAILED $TEST"
  fi
  echo
done

COQ_LEMMAS=$(find $DIRNAME/cn -name 'coq_lemmas' -type d)

for TEST in $COQ_LEMMAS
do
  if [ "${1:-}" == "--coq" ]
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


