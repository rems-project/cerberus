#!/bin/bash
set -e

OWNERSHIP_CLI_FLAG_OPT=""
OWNERSHIP_C_FILE_OPT=""
OWNERSHIP_OBJECT_FILE_OPT=""

while getopts "o:" flag; do
 case $flag in
   o) 
   echo "Ownership checking enabled"
   OWNERSHIP_CLI_FLAG="--with-ownership-checking"
   OWNERSHIP_C_FILE="ownership.c"
   OWNERSHIP_OBJECT_FILE="ownership.o"
   ;;
   \?)
   # Handle invalid options
   ;;
 esac
done

RUNTIME_PREFIX="$OPAM_SWITCH_PREFIX/lib/cn/runtime/"

if [ ! -d $RUNTIME_PREFIX ]; then
  echo "Could not find CN's runtime directory (looked at: '$RUNTIME_PREFIX')";
  exit 1
fi

if [ $# -ne 1 ]; then
  echo "USAGE $0 FILE.c";
  exit 1;
fi

# the XXXX is ignored by Darwin's mktemp but needed
# by the GNU version
# EXEC_DIR="buddy-exec-2"
# rm -rf $EXEC_DIR
# mkdir $EXEC_DIR
EXEC_DIR=$(mktemp -d -t 'cn-exec.XXXX')
echo -n "Creating $EXEC_DIR directory... "
if [ ! -d $EXEC_DIR ]; then
  echo "FAILED"
  exit 1
else
  echo "done"
fi

INPUT_FN=$1
INPUT_BASENAME=$(basename $INPUT_FN .c)
INPUT_DIR=$(dirname $INPUT_FN)

if grep -q "#define" "$INPUT_FN"; then
  INPUT_BASENAME=${INPUT_BASENAME}_pp
  cpp -P -CC $INPUT_FN >! $INPUT_DIR/${INPUT_BASENAME}.c  # macros present - need to preprocess
  INPUT_FN=$INPUT_DIR/${INPUT_BASENAME}.c
fi


echo -n "Generating C files from CN-annotated source... "
if ! cn verify $INPUT_FN --output-decorated=$INPUT_BASENAME-exec.c --output-decorated-dir=$EXEC_DIR/ --with-ownership-checking
then
  echo generation failed.
else 
  echo done!
  cd $EXEC_DIR
  echo -n "Compiling... "

  if ! cc -g -c -I$RUNTIME_PREFIX/include/ *.c $OWNERSHIP_C_FILE_OPT $RUNTIME_PREFIX/libcn.a
  then
    echo "compiling failed."
  else 
    echo "done!"
    echo "Linking..."
    if ! cc -I$RUNTIME_PREFIX/include/ -o $INPUT_BASENAME-exec-output.bin *.o $OWNERSHIP_OBJECT_FILE_OPT $RUNTIME_PREFIX/libcn.a
    then 
      echo "linking failed."
    else 
      echo "done!"
      echo "Running binary with CN runtime checking..."
      if "./${INPUT_BASENAME}-exec-output.bin"
      then 
        echo "Success!"
      else
        echo "Test failed."
        exit 1
      fi
    fi
  fi
fi
