#!/bin/bash

# set -xv

export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:`ocamlfind query z3`
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`ocamlfind query z3`
CN=$OPAM_SWITCH_PREFIX/bin/cn


DIRNAME=$(dirname $0)

SUCC=$(
    find $DIRNAME/cn_vip_testsuite -name '*.c' \
        \! -name '*.annot.c' \
        \! -name '*.error.c' \
        \! -name '*.unprovable.c' \
)
FAIL=$(find $DIRNAME/cn -name '*.error.c')
ANNOT=$(find $DIRNAME/cn -name '*.annot.c')
UNPROV=$(
    find $DIRNAME/cn -name '*.unprovable.c' \
        \! -name 'pointer_copy_user_ctrlflow_bytewise.unprovable.c'
)

NUM_FAILED=0
FAILED=''


for TEST in $SUCC $ANNOT
do
  # TODO add -D flags to CN for these ones
  $CN $TEST
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

for TEST in $FAIL $ANNOT $UNPROV
do
  $CN $TEST
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

if [ -z "$FAILED" ]
then
  echo "All tests passed."
  exit 0
else
  echo "$NUM_FAILED tests failed:"
  echo "  $FAILED"
  exit 1
fi


