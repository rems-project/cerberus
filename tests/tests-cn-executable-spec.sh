#! /bin/bash

# tests for the CN executable spec tool attached to cerberus

DIRNAME=$1

SUCC=$(find $DIRNAME -maxdepth 1 -name '*.c' | grep -v '\.error\.c' | grep -v '\.unknown\.c' | grep -v '\-exec\.c')

NUM_GENERATION_FAILED=0
GENERATION_FAILED=''

NUM_COMPILATION_FAILED=0
COMPILATION_FAILED=''

NUM_LINKING_FAILED=0
LINKING_FAILED=''

NUM_RUNNING_BINARY_FAILED=0
RUNNING_BINARY_FAILED=''

NUM_SUCC=0
SUCC_FILES=''

EXECUTABLE_SPEC_DIR='../executable-spec'

mkdir -p $DIRNAME/exec
clang -fno-lto -c $EXECUTABLE_SPEC_DIR/hash_table.c $EXECUTABLE_SPEC_DIR/alloc.c $EXECUTABLE_SPEC_DIR/cn_utils.c

for TEST in $SUCC
do
  TEST_BASENAME=$(basename $TEST .c)
  EXEC_C_DIRECTORY=$DIRNAME/exec/$TEST_BASENAME
  EXEC_C_FILE=$EXEC_C_DIRECTORY/$TEST_BASENAME-exec.c
  mkdir -p $EXEC_C_DIRECTORY
  echo Generating $EXEC_C_FILE ...
  if ! ~/.opam/4.14.0/bin/cn $TEST --output_decorated=$TEST_BASENAME-exec.c --output_decorated_dir=$EXEC_C_DIRECTORY/
  then
    echo Generation failed.
    NUM_GENERATION_FAILED=$(( $NUM_GENERATION_FAILED + 1 ))
    GENERATION_FAILED="$GENERATION_FAILED $TEST"
  else 
    echo Generation succeeded!
    echo Compiling $EXEC_C_FILE ...
    if ! clang -fno-lto -c $EXEC_C_FILE $EXEC_C_DIRECTORY/cn.c   
    then
      echo Compilation failed.
      NUM_COMPILATION_FAILED=$(( $NUM_COMPILATION_FAILED + 1 ))
      COMPILATION_FAILED="$COMPILATION_FAILED $EXEC_C_FILE"
    else 
      echo Compilation succeeded!
      echo Linking $TEST_BASENAME-exec.o with other files ...
      if ! clang -o $TEST_BASENAME-output $TEST_BASENAME-exec.o cn.o hash_table.o alloc.o cn_utils.o
      then 
        echo Linking failed.
        NUM_LINKING_FAILED=$(( $NUM_LINKING_FAILED + 1 ))
        LINKING_FAILED="$LINKING_FAILED $EXEC_C_FILE"
      else 
        echo Linking succeeded!
        echo Running the $TEST_BASENAME-output binary ...
        if ! ./$TEST_BASENAME-output
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
  fi
  
done


# FAIL=$(find $DIRNAME -name '*.error.c')

# for TEST in $FAIL
# do
#   echo cn $TEST
#   if ! cn $TEST
#   then
#     NUM_FAILED=$(( $NUM_FAILED + 1 ))
#     FAILED="$FAILED $TEST"
#   fi
# done

# UNKNOWN=$(find $DIRNAME -name '*.unknown.c')

# echo $UNKNOWN | xargs -n 1 cn

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
  echo "$NUM_COMPILATION_FAILED tests failed to be compiled:"
  echo "  $COMPILATION_FAILED"
  echo " "
  echo "$NUM_LINKING_FAILED tests failed to be linked:"
  echo "  $LINKING_FAILED"
  echo " "
  echo "$NUM_RUNNING_BINARY_FAILED tests failed to be run as binaries:"
  echo "  $RUNNING_BINARY_FAILED"
  echo " "
  echo "$NUM_SUCC tests passed:"
  echo "  $SUCC_FILES"
  exit 1
fi


