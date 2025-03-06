#!/bin/bash

trap ctrl_c INT
function ctrl_c() {
  echo "Aborting...";
  rm -f tmp/result tmp/stderr;
  # [ -d tmp ] && rmdir tmp;
  exit 0
}

TESTSDIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cd ${TESTSDIR}

# Load function for setting up CERB and CERB_INSTALL_PREFIX
source ./common.sh
source tests.sh

mkdir -p tmp

pass=0
fail=0
JOUTPUT=""

JOUTPUT_FILE="ci_results.xml"
echo "<testsuites>" > $JOUTPUT_FILE

# Arguments:
# 1: test case name
# 2: result (0 is success)
function report {
  #If the test should fail
  if [[ $1 == *.fail.c ]]; then
    res="1 - $2";
  else
    res=$2;
  fi

  #If the test is about undef
  if [[ $1 == *.undef.c ]]; then
    cat tmp/result tmp/stderr | grep -E "Undefined|UNDEFINED"
    res=$?
  fi

  # If the test is about something currently not supported
  # This can still test the parser
  if [[ $1 == *.unsup.c ]]; then
    cat tmp/result tmp/stderr | grep "feature not yet supported"
    res=$?
  fi

  if [[ "$((res))" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
    JOUTPUT+="\t<testcase name=\"$1\"/>\n"
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
    cat tmp/result tmp/stderr
    JOUTPUT+="\t<testcase name=\"$1\">\n"
    JOUTPUT+="\t\t<error message=\"fail\">$(cat tmp/result tmp/stderr | sed 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g; s/"/\&quot;/g; s/'"'"'/\&#39;/g')</error>\n"
    JOUTPUT+="\t</testcase>\n"
  fi

  echo -e "Test $1: $res"
}

function create_testsuite {
  echo "<testsuite name=\"$1\" tests=\"$((pass + fail))\" failures=\"${fail}\" timestamp=\"$(date)\">" >> $JOUTPUT_FILE
  echo -e ${JOUTPUT} >> $JOUTPUT_FILE
  echo "</testsuite>" >> $JOUTPUT_FILE
  pass=0
  fail=0
  JOUTPUT=""
}

# Setup CERB and CERB_INSTALL_PREFIX (see common.sh)
set_cerberus_exec "cerberus"

# Running TinyCC tests
for file in tcc/*.c
do
  if [ $file == "tcc/24_math_library.c" ]; then
    echo -e "Test $file: \x1b[33mSKIPPED (Cerberus' libc does not currently implement most floating functions)\x1b[0m"
    continue
  fi
  # if [ $file == "tcc/60_errors_and_warnings.c "]; then
  # else
  $CERB $file -D__LP64__ --exec > tmp/result 2> tmp/stderr
  cmp --silent tmp/result ${file%.c}.expect
  report $file $?
  # fi
done
echo "TCC PASSED: $pass"
echo "TCC FAILED: $fail"
create_testsuite "tcc"

echo "</testsuites>" >> $JOUTPUT_FILE
