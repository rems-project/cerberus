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

FAILURE=0

# Check the example archive 
./check-all.sh "$CN --solver-type=cvc5"
if [ $? != 0 ] 
then
   FAILURE=1
fi

./check-all.sh "$CN --solver-type=z3"
if [ $? != 0 ] 
then
   FAILURE=1
fi


# Check the tutorial examples 
cd ../..

./check.sh "$CN --solver-type=cvc5"
if [ $? != 0 ] 
then
   FAILURE=1
fi

./check.sh "$CN --solver-type=z3"
if [ $? != 0 ] 
then
   FAILURE=1
fi

cd $HERE

if [ $FAILURE == 0 ]
then
    echo "Ok"
    exit 0
else 
    echo "There were errors"
    exit 1
fi
