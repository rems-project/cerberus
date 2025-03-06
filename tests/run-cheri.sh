#!/bin/bash

TESTSDIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cd ${TESTSDIR}

# This initialises citests and skip
source ./tests-cheri.sh

# Load function for setting up CERB and CERB_INSTALL_PREFIX
source ./common.sh

mkdir -p tmp

CIDIR=cheri-ci
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
  if [[ $1 == *.error.c || $1 == *.undef.c ]]; then
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
    cat tmp/result tmp/stderr
  fi

  echo -e "Test $1: $res"
}

if [[ $# == 1 ]]; then
  citests=($(basename $1))
fi


# Setup CERB and CERB_INSTALL_PREFIX (see common.sh)
set_cerberus_exec "cerberus-cheri"

# Running ci tests
for file in "${citests[@]}"
do
  if [ ! -f $CIDIR/$file ]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m";
    fail=$((fail+1));
    continue
  fi
  
  if doSkip $file; then
    echo -e "Test $file: \033[1m\033[33mSKIPPING\033[0m";
    continue
  fi

  if [[ $file == *.syntax-only.c ]]; then
    $CERB --switches=PNVI_ae_udi,strict_pointer_equality,strict_pointer_arith,strict_pointer_relationals,CHERI --nolibc --typecheck-core $CIDIR/$file > tmp/result 2> tmp/stderr
  else
    $CERB --switches=PNVI_ae_udi,strict_pointer_equality,strict_pointer_arith,strict_pointer_relationals,CHERI --nolibc --typecheck-core --exec --batch $CIDIR/$file 1> tmp/result 2> tmp/stderr
  fi
  ret=$?;
  if [ -f $CIDIR/expected/$file.expected ]; then
    if [[ $file == *.error.c || $file == *.syntax-only.c ]]; then
      # removing the last line from stderr (the time stats)
      if [ "$(uname)" == "Linux" ]; then
          sed -i '$ d' tmp/stderr
      else # otherwise we assume this is macOS or BSD
          sed -i '' -e '$ d' tmp/stderr
      fi;
      if ! cmp --silent "tmp/stderr" "$CIDIR/expected/$file.expected"; then
        ret=0;
      fi
    else
      if ! cmp --silent "tmp/result" "$CIDIR/expected/$file.expected"; then
        if [[ $file == *.undef.c ]]; then
          ret=0;
        else
          ret=1;
        fi
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

[ $fail -eq 0 ]
