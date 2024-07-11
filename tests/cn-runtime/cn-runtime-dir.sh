#! /bin/bash

# tests for the CN executable spec tool attached to cerberus

DIRNAME=$1

SUCC=$(find $DIRNAME -maxdepth 1 -name '*.c' | grep -v '\.error\.c' | grep -v 'fixme_error' | grep -v '\.unknown\.c' | grep -v '\-exec\.c' | grep -v 'inconsistent*' | grep -v 'implies*')

NUM_GENERATION_FAILED=0
GENERATION_FAILED=''

NUM_COMPILATION_FAILED=0
COMPILATION_FAILED=''

NUM_RUNNING_BINARY_FAILED=0
RUNNING_BINARY_FAILED=''

NUM_SUCC=0
SUCC_FILES=''

mkdir -p $DIRNAME/exec

for TEST in $SUCC
do
  TEST_NAME=$TEST
  TEST_BASENAME=$(basename $TEST_NAME .c)
  EXEC_C_DIRECTORY=$DIRNAME/exec/$TEST_BASENAME
  EXEC_C_FILE=$EXEC_C_DIRECTORY/$TEST_BASENAME-exec.c
  mkdir -p $EXEC_C_DIRECTORY
  if grep -q "#define" "$INPUT_FN"; then
    echo Preprocessing due to presence of macros ...
    TEST_BASENAME=${TEST_BASENAME}_pp
    cpp -P -CC $TEST >! $DIRNAME/${TEST_BASENAME}.c  # macros present - need to preprocess
    TEST_NAME=$DIRNAME/${TEST_BASENAME}.c
    echo Done!
  fi
  echo Generating $EXEC_C_FILE ...
  if ! cn $TEST_NAME --output_decorated=$TEST_BASENAME-exec.c --output_decorated_dir=$EXEC_C_DIRECTORY/ --with_ownership_checking
  then
    echo Generation failed.
    NUM_GENERATION_FAILED=$(( $NUM_GENERATION_FAILED + 1 ))
    GENERATION_FAILED="$GENERATION_FAILED $TEST"
  else 
    echo Generation succeeded!
    echo Compiling and linking...
    if ! clang-18 -I$OPAM_SWITCH_PREFIX/lib/cn/runtime/include $EXEC_C_DIRECTORY/*.c $OPAM_SWITCH_PREFIX/lib/cn/runtime/libcn.a -o $TEST_BASENAME-output   
    then
      echo Compiling/linking failed.
      NUM_COMPILATION_FAILED=$(( $NUM_COMPILATION_FAILED + 1 ))
      COMPILATION_FAILED="$COMPILATION_FAILED $EXEC_C_FILE"
    else 
      echo Compiling and linking succeeded!
      cp $TEST_BASENAME-output $EXEC_C_DIRECTORY
      rm $TEST_BASENAME-output
      echo Running the $TEST_BASENAME-output binary ...
      if ! ./$EXEC_C_DIRECTORY/$TEST_BASENAME-output
      then 
          echo Running binary failed.
          NUM_RUNNING_BINARY_FAILED=$(( $NUM_RUNNING_BINARY_FAILED + 1 ))
          RUNNING_BINARY_FAILED="$RUNNING_BINARY_FAILED $EXEC_C_FILE"
      else 
          echo Running binary succeeded!
          NUM_SUCC=$(( $NUM_SUCC + 1 ))
          SUCC_FILES="$SUCC_FILES $EXEC_C_FILE"
      fi
    fi
  fi
  
done


echo
echo 'Done running tests.'
echo

if [ -z "$GENERATION_FAILED$COMPILATION_FAILED$LINKING_FAILED$RUNNING_BINARY_FAILED" ]
then
  echo "All tests passed."
  exit 0
else
  echo "$NUM_GENERATION_FAILED tests failed to have executable specs generated:"
  echo "  $GENERATION_FAILED"
  echo " "
  echo "$NUM_COMPILATION_FAILED tests failed to be compiled/linked:"
  echo "  $COMPILATION_FAILED"
  echo " "
  echo "$NUM_RUNNING_BINARY_FAILED tests failed to be run as binaries:"
  echo "  $RUNNING_BINARY_FAILED"
  echo " "
  echo "$NUM_SUCC tests passed:"
  echo "  $SUCC_FILES"
  exit 1
fi


