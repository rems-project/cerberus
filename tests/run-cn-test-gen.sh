#!/bin/bash

# copying from run-ci.sh
export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:$(ocamlfind query z3)
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$(ocamlfind query z3)
CN=$OPAM_SWITCH_PREFIX/bin/cn

DIRNAME=$(dirname $0)

# Clean directory
cd $DIRNAME/cn-test-gen
rm -rf test build
mkdir test build

# Get `*.c` files
SUCC=$(find $DIRNAME/src -name '*.c')

# Track failures
NUM_FAILED=0
FAILED=''

# Test each `*.c` file
for TEST in $SUCC; do
  # Generate tests
  $CN generate-tests $TEST --output-dir="test"
  RET=$?
  if [[ "$RET" != 0 ]]; then
    echo "$TEST -- Error during test generation"
    NUM_FAILED=$(($NUM_FAILED + 1))
    FAILED="$FAILED $TEST"
  else
    echo "$TEST -- Tests generated successfully"

    # Run CMake
    cd build
    cmake .. >/dev/null
    RET=$?
    if [[ "$RET" != 0 ]]; then
      echo "$TEST -- Error while running CMake"
      NUM_FAILED=$(($NUM_FAILED + 1))
      FAILED="$FAILED $TEST"
    else
      echo "$TEST -- CMake run successfully"

      # Build tests
      make >/dev/null
      RET=$?
      if [[ "$RET" != 0 ]]; then
        echo "$TEST -- Error while building tests"
        NUM_FAILED=$(($NUM_FAILED + 1))
        FAILED="$FAILED $TEST"
      else
        echo "$TEST -- Tests built successfully"

        # Run tests
        ./ci_tests >/dev/null
        RET=$?
        if [[ "$RET" != 0 ]]; then
          echo "$TEST -- Error while running tests"
          NUM_FAILED=$(($NUM_FAILED + 1))
          FAILED="$FAILED $TEST"
        else
          echo "$TEST -- Tests run successfully"
        fi
      fi
    fi
    cd ..
  fi
  rm -rf test/*
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
