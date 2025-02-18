#!/bin/bash

CN=$OPAM_SWITCH_PREFIX/bin/cn

DIRNAME=$(dirname "$0")
TEST=$1

# Clean directory
cd "$DIRNAME" || exit
if [[ $TEST == *.pass.c ]]; then
  DIR=passing-$(basename $TEST .pass.c)
else
  DIR=failing-$(basename $TEST .fail.c)
fi
rm -rf $DIR

# For UBSan
export UBSAN_OPTIONS=halt_on_error=1

# Track failures
NUM_FAILED=0
FAILED=''

function separator() {
  OUTPUT="${OUTPUT}\n"
  for i in {1..60}; do
    OUTPUT="${OUTPUT}="
  done
  OUTPUT="${OUTPUT}\n\n"
}

CONFIGS=("--sized-null --sizing-strategy=uniform" "--coverage --sizing-strategy=quartile" "--with-static-hack --coverage --sizing-strategy=quickcheck" "--random-size-splits" "--random-size-splits --allowed-size-split-backtracks=10")

OUTPUT=""

# For each configuration
for CONFIG in "${CONFIGS[@]}"; do
  separator
  OUTPUT="${OUTPUT}Running CI with CLI config \"$CONFIG\"\n"
  separator

  FULL_CONFIG="$CONFIG --input-timeout=1000 --progress-level=function --sanitize=undefined"

  if [[ $TEST == *.pass.c ]]; then
    CLEANUP="rm -rf ${DIR} run_tests.sh;separator"
    OUTPUT="${OUTPUT}$($CN test "$TEST" --output-dir="$DIR" $FULL_CONFIG 2>&1)"
    RET=$?
    if [[ "$RET" != 0 ]]; then
      OUTPUT="${OUTPUT}\n$TEST -- Tests failed unexpectedly\n"
      NUM_FAILED=$(($NUM_FAILED + 1))
      FAILED="$FAILED $CONFIG"
    else
      OUTPUT="${OUTPUT}\n$TEST -- Tests passed successfully\n"
    fi
  elif [[ $TEST == *.fail.c ]]; then
    CLEANUP="rm -rf ${DIR} run_tests.sh;separator"
    OUTPUT="${OUTPUT}$($CN test "$TEST" --output-dir="$DIR" $FULL_CONFIG 2>&1)"
    RET=$?
    if [[ "$RET" = 0 ]]; then
      OUTPUT="${OUTPUT}\n$TEST -- Tests passed unexpectedly\n"
      NUM_FAILED=$(($NUM_FAILED + 1))
      FAILED="$FAILED $CONFIG"
    else
      OUTPUT="${OUTPUT}\n$TEST -- Tests failed successfully"
    fi
  fi

  eval "$CLEANUP"
done

if [ -z "$FAILED" ]; then
  # echo "$TEST - all configs passed."
  exit 0
else
  OUTPUT="${OUTPUT}$TEST - $NUM_FAILED configs failed:\n  $FAILED"
  printf "%s\n" "${OUTPUT}"
  exit 1
fi
