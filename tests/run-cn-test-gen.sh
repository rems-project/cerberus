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

# Test each `*.c` file
for TEST in $FILES; do
  CLEANUP="rm -rf decorated/*"

  # Instrument file
  $CN verify "$TEST" --output-decorated="$(basename "$TEST")" --output-decorated-dir=decorated/
  RET=$?
  if [[ "$RET" != 0 ]]; then
    echo "$TEST -- Error during executable spec decoration"
    NUM_FAILED=$(($NUM_FAILED + 1))
    FAILED="$FAILED $TEST"
    eval "$CLEANUP"
    continue
  else
    echo "$TEST -- Executable spec decorated successfully"
  fi

  CLEANUP="rm -rf test/*;$CLEANUP"

  # Generate tests
  $CN generate-tests "$TEST" --output-dir="test"
  RET=$?
  if [[ "$RET" != 0 ]]; then
    echo "$TEST -- Error during test generation"
    NUM_FAILED=$(($NUM_FAILED + 1))
    FAILED="$FAILED $TEST"
    eval "$CLEANUP"
    continue
  else
    echo "$TEST -- Tests generated successfully"
  fi

  CLEANUP="cd ..;$CLEANUP"

  # Run CMake
  cd build || exit
  cmake .. >/dev/null
  RET=$?
  if [[ "$RET" != 0 ]]; then
    echo "$TEST -- Error while running CMake"
    NUM_FAILED=$(($NUM_FAILED + 1))
    FAILED="$FAILED $TEST"
    eval "$CLEANUP"
    continue
  else
    echo "$TEST -- CMake run successfully"
  fi

  # Build tests
  make >/dev/null
  RET=$?
  if [[ "$RET" != 0 ]]; then
    echo "$TEST -- Error while building tests"
    NUM_FAILED=$(($NUM_FAILED + 1))
    FAILED="$FAILED $TEST"
    eval "$CLEANUP"
    continue
  else
    echo "$TEST -- Tests built successfully"
  fi

  # Run passing tests
  if [[ $TEST == *.pass.c ]]; then
    ./ci_tests >/dev/null
    RET=$?
    if [[ "$RET" != 0 ]]; then
      echo "$TEST -- Tests failed unexpectedly"
      NUM_FAILED=$(($NUM_FAILED + 1))
      FAILED="$FAILED $TEST"
      eval "$CLEANUP"
      continue
    else
      echo "$TEST -- Tests passed successfully"
    fi
  fi

  # Run failing tests
  if [[ $TEST == *.fail.c ]]; then
    ./ci_tests 2>/dev/null
    RET=$?
    if [[ "$RET" = 0 ]]; then
      echo "$TEST -- Tests passed unexpectedly"
      NUM_FAILED=$(($NUM_FAILED + 1))
      FAILED="$FAILED $TEST"
      eval "$CLEANUP"
      continue
    else
      echo "$TEST -- Tests failed successfully"
    fi
  fi

  eval "$CLEANUP"
done

echo
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
