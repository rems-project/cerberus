#!/bin/bash


TUTORIAL_PATH=$1

if [ -n "$TUTORIAL_PATH" ] 
then
    echo "using tutorial path $TUTORIAL_PATH"
else
    echo "missing argument for CN tutorial path"
    exit 1
fi



# copying from run-ci.sh
export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:`ocamlfind query z3`
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`ocamlfind query z3`
CN=$OPAM_SWITCH_PREFIX/bin/cn

HERE=$(pwd)

cd "$TUTORIAL_PATH"/src/example-archive/

cd SAW
sh ../check.sh $CN
cd ..

cd c-testsuite
sh ../check.sh $CN
cd ..

cd dafny-tutorial
sh ../check.sh $CN
cd ..

cd simple-examples
sh ../check.sh $CN
cd ..

cd $HERE



