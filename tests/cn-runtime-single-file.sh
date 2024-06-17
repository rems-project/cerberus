#!/bin/bash

RUNTIME_PREFIX="$OPAM_SWITCH_PREFIX/lib/cn/runtime/"

if [ ! -d $RUNTIME_PREFIX ]; then
  echo "Could not find CN's runtime directory (looked at: '$RUNTIME_PREFIX')";
  exit 1
fi

if [ $# -ne 1 ]; then
  echo "USAGE $0 FILE.c";
  exit 1;
fi

EXEC_DIR=$(mktemp -t 'cn-exec' -d)
echo "Creating $EXEC_DIR directory..."

INPUT_FN=$1
INPUT_BASENAME=$(basename $INPUT_FN .c)

trap - 0

echo -n "Generating C files from CN-annotated source... "
if ! cn $INPUT_FN --output_decorated=$INPUT_BASENAME-exec.c --output_decorated_dir=$EXEC_DIR/
then
  echo generation failed.
else 
  echo done!
  cd $EXEC_DIR
  echo -n "Compiling and linking... "
  if ! cc -I$RUNTIME_PREFIX/include/ $RUNTIME_PREFIX/libcn.a -o $INPUT_BASENAME-exec-output $INPUT_BASENAME-exec.c cn.c
  then
    echo "compiling/linking failed."
  else 
    echo "done!"
    echo "Running binary..."
    if ./$INPUT_BASENAME-exec-output
    then 
      echo "Success!"
    else
      echo "Test failed."
      exit 1
    fi
  fi
fi

