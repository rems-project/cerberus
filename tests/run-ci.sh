#!/bin/bash

export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:`ocamlfind query z3`
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`ocamlfind query z3`

. ./tests.sh

mkdir -p tmp

pass=0
fail=0


function doSkip {
  for f in "${skip[@]}"; do [[ $f == $1 ]] && return 0; done
  return 1
}

# Arguments:
# 1: test case name
# 2: result (0 is success)
function report {
  #If the test should fail
  if [[ $1 == *.error.c ]]; then
    res="1 - $2";
  else
    res=$2;
  fi

  # #If the test is about undef
  # if [[ $1 == *.undef.c ]]; then
  #   cat tmp/result tmp/stderr | grep -q -E "Undefined|UNDEFINED"
  #   res=$?
  # fi

  # If the test is about something currently not supported
  # This can still test the parser
  if [[ $1 == *.unsup.c ]]; then
    cat tmp/result tmp/stderr | grep -q "feature not yet supported"
    res=$?
  fi

  if [[ "$((res))" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
    #cat tmp/result tmp/stderr
  fi

  echo -e "Test $1: $res"
}

<<<<<<< HEAD
if [[ $# == 1 ]]; then
  citests=($(basename $1))
fi
=======
# Use the provided path to cerberus, otherwise default to the driver backend build
# CERB="${WITH_CERB:=dune exec cerberus --no-build -- }"
CERB="${WITH_CERB:=../_build/default/backend/driver/main.exe}"
export CERB_RUNTIME=../runtime/
>>>>>>> fb3ebc1f (forcing `run-ci.sh` to use the local runtime)

# Running ci tests
for file in "${citests[@]}"
do
  if [ ! -f ./ci/$file ]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m";
    fail=$((fail+1));
    continue
  fi
  
  if doSkip $file; then
    echo -e "Test $file: \033[1m\033[33mSKIPPING\033[0m";
    continue
  fi

  if [[ $file == *.syntax-only.c ]]; then
    ../_build/default/backend/driver/main.exe --nolibc ci/$file > tmp/result 2> tmp/stderr
  else
    ../_build/default/backend/driver/main.exe --nolibc --exec --batch ci/$file 1> tmp/result 2> tmp/stderr
  fi
  ret=$?;
  if [ -f ./ci/expected/$file.expected ]; then
    if [[ $file == *.error.c || $file == *.syntax-only.c ]]; then
      # removing the last line from stderr (the time stats)
      if [ "$(uname)" == "Linux" ]; then
          sed -i '$ d' tmp/stderr
      else # otherwise we assume this macOS or BSD
          sed -i '' -e '$ d' tmp/stderr
      fi;
      if ! cmp --silent "tmp/stderr" "ci/expected/$file.expected"; then
        ret=0;
      fi
    else
      if ! cmp --silent "tmp/result" "ci/expected/$file.expected"; then
        ret=1;
      fi
    fi
  else
    echo -e "Test $file: \033[1m\033[33mMISSING .expected FILE\033[0m";
    continue
  fi
  report $file $ret
done
echo "CI PASSED: $pass"
echo "CI FAILED: $fail"
