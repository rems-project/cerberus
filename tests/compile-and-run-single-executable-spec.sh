#! /bin/bash

# tests for the CN executable spec tool attached to cerberus

FILE_NAME=$1

EXECUTABLE_SPEC_DIR='../executable-spec'

TEST=$FILE_NAME
TEST_BASENAME=$(basename $TEST .c)
clang -fno-lto -c $EXECUTABLE_SPEC_DIR/hash_table.c $EXECUTABLE_SPEC_DIR/alloc.c $EXECUTABLE_SPEC_DIR/cn_utils.c


EXEC_C_DIRECTORY=$TEST_BASENAME
EXEC_C_FILE=$EXEC_C_DIRECTORY/$TEST_BASENAME-exec.c
mkdir -p $EXEC_C_DIRECTORY
echo Generating $EXEC_C_FILE ...
if ! ~/.opam/4.14.0/bin/cn $TEST --output_decorated=$TEST_BASENAME-exec.c --output_decorated_dir=$EXEC_C_DIRECTORY/
then
    echo Generation failed.
else 
    echo Generation succeeded!
    echo Compiling $EXEC_C_FILE ...
    if ! clang -fno-lto -c $EXEC_C_FILE $EXEC_C_DIRECTORY/cn.c   
    then
        echo Compilation failed.
    else 
        echo Compilation succeeded!
        echo Linking $TEST_BASENAME-exec.o with other files ...
        if ! clang -o $TEST_BASENAME-output $TEST_BASENAME-exec.o cn.o hash_table.o alloc.o cn_utils.o
        then 
            echo Linking failed.
        else 
            echo Linking succeeded!
            echo Running the $TEST_BASENAME-output binary ...
            if ! ./$TEST_BASENAME-output
            then 
                echo Running binary failed.
            else 
                echo Running binary succeeded!
            fi
        fi
    fi
fi

