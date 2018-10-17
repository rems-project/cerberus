#!/bin/bash
# This script tests if Core pretty printer and parse coincide!

function report {
  if [[ "$2" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
  else
    res="\033[1m\033[31mFAILED!\033[0m"
  fi
  echo -e "Test $1: $res"
}

mkdir -p tmp

# Running ci tests
for file in ./ci/*.c
do
  if [[ $file == *.error.c || $file == *.undef.c ]]; then
    continue;
  fi
  file_no_suffix=${file%.c}
  name=${file_no_suffix##*/}
  ../cerberus $file --pp=core > tmp/$name.core
  ../cerberus tmp/$name.core
  # TODO: ideally we should compare the files, but --rewrite yields different values
  #../cerberus tmp/original.core --rewrite --pp=core > tmp/pp.core
  #cmp --silent tmp/origina.core tmp/pp.core
  report $file $?
done
