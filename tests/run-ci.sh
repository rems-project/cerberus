#!/bin/bash

TESTSDIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cd ${TESTSDIR}

# This initialises citests and skip
source ./tests.sh

# Load function for setting up CERB and CERB_INSTALL_PREFIX
source ./common.sh

mkdir -p tmp

# Usage: run-ci.sh [--both-callconvs] [<test file name>]
#
# By default every test runs under the "normal" calling convention of the
# elaboration. Calling with --both-callconvs runs them with both the "normal"
# and "inner_arg_temps" calling conventions.
#
# For future reference, entries of callconvs below are
#   "<name>:<cerberus flags>"
callconvs=("normal:")
for arg in "$@"; do
  case $arg in
    --both-callconvs)
      callconvs=("normal:" "inner_arg_temps:--switches=inner_arg_temps") ;;
    *)
      citests=($(basename $arg)) ;;
  esac
done

pass=0
fail=0
# number of failing tests per calling convention (indexed like callconvs)
conv_fails=()
for i in "${!callconvs[@]}"; do conv_fails[$i]=0; done


function doSkip {
  for f in "${skip[@]}"; do [[ $f == $1 ]] && return 0; done
  return 1
}


function runTest {
  local file=$1; shift
  local ret
  if [[ $file == *.syntax-only.c ]]; then
    $CERB --nolibc --typecheck-core "$@" ci/$file > tmp/result 2> tmp/stderr
  else
    $CERB --nolibc --typecheck-core --exec --batch "$@" ci/$file 1> tmp/result 2> tmp/stderr
  fi
  ret=$?
  if [[ $file == *.error.c || $file == *.syntax-only.c ]]; then
    # removing the last line from stderr (the time stats)
    if [ "$(uname)" == "Linux" ]; then
        sed -i '$ d' tmp/stderr
    else # otherwise we assume this is macOS or BSD
        sed -i '' -e '$ d' tmp/stderr
    fi;
    if ! cmp --silent "tmp/stderr" "ci/expected/$file.expected"; then
      ret=0;
    fi
  else
    if ! cmp --silent "tmp/result" "ci/expected/$file.expected"; then
      if [[ $file == *.undef.c ]]; then
        ret=0;
      else
        ret=1;
      fi
    fi
  fi
  # If the test should fail
  if [[ $file == *.error.c || $file == *.undef.c ]]; then
    ret=$((1 - ret))
  fi
  # If the test is about something currently not supported
  if [[ $file == *.unsup.c ]]; then
    cat tmp/result tmp/stderr | grep -q "feature not yet supported"
    ret=$?
  fi
  return $ret
}


# Setup CERB and CERB_INSTALL_PREFIX (see common.sh)
set_cerberus_exec "cerberus"

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

  if [ ! -f ./ci/expected/$file.expected ]; then
    echo -e "Test $file: \033[1m\033[33mMISSING .expected FILE\033[0m";
    continue
  fi

  failed_convs=""
  for i in "${!callconvs[@]}"; do
    name=${callconvs[$i]%%:*}
    flags=${callconvs[$i]#*:}
    if ! runTest $file $flags; then
      failed_convs="$failed_convs $name"
      conv_fails[$i]=$((conv_fails[$i]+1))
      if (( ${#callconvs[@]} > 1 )); then
        echo "--- $file, $name calling convention:"
      fi
      cat tmp/result tmp/stderr
    fi
  done

  if [[ -z $failed_convs ]]; then
    echo -e "Test $file: \033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    if (( ${#callconvs[@]} > 1 )); then
      echo -e "Test $file: \033[1m\033[31mFAILED!\033[0m (calling convention(s):$failed_convs)"
    else
      echo -e "Test $file: \033[1m\033[31mFAILED!\033[0m"
    fi
    fail=$((fail+1))
  fi
done
echo "CI PASSED: $pass"
echo "CI FAILED: $fail"
if (( ${#callconvs[@]} > 1 )); then
  for i in "${!callconvs[@]}"; do
    echo "  failing under the ${callconvs[$i]%%:*} calling convention: ${conv_fails[$i]}"
  done
fi

[ $fail -eq 0 ]
