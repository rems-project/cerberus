#! /bin/bash

INPUT_FN=$1
INPUT_BASENAME=$(basename $INPUT_FN .c)
INPUT_DIRNAME=$(dirname $INPUT_FN)
INPUT_EXEC_DIR=$INPUT_DIRNAME/exec/$INPUT_BASENAME-exec
INPUT_EXEC_FILE=$INPUT_EXEC_DIR/$INPUT_BASENAME-exec.c

rm -rf $INPUT_EXEC_DIR
echo "Creating $INPUT_EXEC_DIR directory..."
mkdir $INPUT_EXEC_DIR
echo "Generating C files from CN-annotated source..."
~/.opam/4.14.0/bin/cn $INPUT_FN --output_decorated=$INPUT_BASENAME-exec.c --output_decorated_dir=$INPUT_EXEC_DIR/
echo "Done!"
cd $INPUT_EXEC_DIR
echo "Compiling and linking..."
clang -std=c11 -fno-lto -c -g $INPUT_BASENAME-exec.c cn.c ../../../../executable-spec/alloc.c ../../../../executable-spec/hash_table.c ../../../../executable-spec/cn_utils.c
clang -o $INPUT_BASENAME-exec-output -g $INPUT_BASENAME-exec.o cn.o alloc.o hash_table.o cn_utils.o
echo "Done!"
echo "Running binary..."

if ./${INPUT_BASENAME}-exec-output
then 
    echo "Success!"
else
    echo "Test failed."
fi