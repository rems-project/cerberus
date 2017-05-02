#!/bin/bash

source tests.sh

echo "Creating temp folder..."
mkdir -p tmp
mkdir -p tmp/src
mkdir -p tmp/ci

echo "Copying Cerberus source code..."
cp $CERB_PATH/ocaml_generated/*.{ml,mli} tmp/src/
cp $CERB_PATH/pprinters/*.{ml,mli} tmp/src/

cp $CERB_PATH/src/util.ml tmp/src/
cp $CERB_PATH/src/codegen/rt_ocaml.ml tmp/src/

cp $CERB_PATH/src/tags.{ml,mli} tmp/src/
cp $CERB_PATH/src/location_ocaml.ml tmp/src/
cp $CERB_PATH/src/debug_ocaml.{ml,mli} tmp/src/
cp $CERB_PATH/src/sat_solving.{ml,mli} tmp/src/
cp $CERB_PATH/src/boot_printf.{ml,mli} tmp/src/
cp $CERB_PATH/src/decode_ocaml.ml tmp/src/
cp $CERB_PATH/src/global_ocaml.{ml,mli} tmp/src/
cp $CERB_PATH/src/input.{ml,mli} tmp/src/

cp $CERB_PATH/parsers/coreparser/core_parser_util.ml tmp/src/

echo "Creating _tag .merlin files..."
echo $'true: -traverse\n\n\"src\":include\n\"ci\":include' > tmp/_tags
echo $'S src\nS ci\nS .\nB _build\nB _build/src\nB _build/ci' > tmp/.merlin

echo "Copying tests..."
cp ci/*.c tmp/ci

if [ -n "$BASIC_MEM" ]; then
  echo "Changing files to use basic memory model..."
  sed -i '' 's/Defacto\_memory\_types/Basic\_mem\_types/g' tmp/src/*.{ml,mli}
  sed -i '' 's/Defacto\_memory/Basic\_mem/g' tmp/src/*.{ml,mli}
fi

cd tmp

pass=0
fail=0

function test {
  cerberus --ocaml $2/$1 2> /dev/null
  ocamlbuild -pkgs pprint,zarith -libs nums,unix,str ${1%.c}.native > /dev/null
  CERBOUTPUT=1 ./${1%.c}.native > result
  cmp --silent result ../$2/expected/$1.expected
  if [[ "$?" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
  fi

  echo -e "Test $1: $res"
}

# Running ci tests

for file in "${citests[@]}"
do
  test $file ci
done

echo "PASSED: $pass"
echo "FAILED: $fail"

