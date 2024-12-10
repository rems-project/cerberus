#!/bin/bash

# copying from run-ci.sh
export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:$(ocamlfind query z3)
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$(ocamlfind query z3)
CN=$OPAM_SWITCH_PREFIX/bin/cn

DIRNAME=$(dirname "$0")

# Clean directory
cd "$DIRNAME"/cn-test-gen || exit
rm -rf build decorated test
mkdir build decorated test

# Get `*.c` files
FILES=$(find "$DIRNAME"/src -name '*.c')

# Track failures
NUM_FAILED=0
FAILED=''

function separator() {
  printf '\n'
  for i in {1..60}; do
    printf "="
  done
  printf '\n\n'
}

CONFIGS=("--coverage" "--sized-null" "--random-size-splits" "--random-size-splits --allowed-size-split-backtracks=10")

# For each configuration
for CONFIG in "${CONFIGS[@]}"; do
  separator
  echo "Running CI with CLI config \"$CONFIG\""
  separator

  FULL_CONFIG="$CONFIG --input-timeout=1000 --progress-level=1"

  # Test each `*.c` file
  for TEST in $FILES; do
    CLEANUP="rm -rf test/* run_tests.sh;separator"

    # Run passing tests
    if [[ $TEST == *.pass.c ]]; then
      $CN test "$TEST" --output-dir="test" $FULL_CONFIG
      RET=$?
      if [[ "$RET" != 0 ]]; then
        echo
        echo "$TEST -- Tests failed unexpectedly"
        NUM_FAILED=$(($NUM_FAILED + 1))
        FAILED="$FAILED $TEST($CONFIG)"
        eval "$CLEANUP"
        continue
      else
        echo
        echo "$TEST -- Tests passed successfully"
      fi
    fi

    # Run failing tests
    if [[ $TEST == *.fail.c ]]; then
      $CN test "$TEST" --output-dir="test" $FULL_CONFIG
      RET=$?
      if [[ "$RET" = 0 ]]; then
        echo
        echo "$TEST -- Tests passed unexpectedly"
        NUM_FAILED=$(($NUM_FAILED + 1))
        FAILED="$FAILED $TEST($CONFIG)"
        eval "$CLEANUP"
        continue
      else
        echo
        echo "$TEST -- Tests failed successfully"
      fi
    fi

    eval "$CLEANUP"
  done
done

echo 'Done running tests.'
echo

if [ -z "$FAILED" ]; then
  echo "All tests passed."
  exit 0
else
  echo "$NUM_FAILED tests failed:"
  echo "  $FAILED"
  exit 1
fi
