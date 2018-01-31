#!/bin/bash

export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:$HOME/Applications/usr/lib

#cd $CERB_PATH/tests

source tests.sh

mkdir -p tmp

pass=0
fail=0

JOUTPUT=""
JOUTPUT_FILE="ci_results.xml"

# Arguments:
# 1: test case name
# 2: result (0 is success)
function report {
  if [[ $1 == *.fail.c ]]; then
    res="1 - $2";
  else
    res=$2;
  fi

  if [[ "$res" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
    JOUTPUT+="\t<testcase name=\"$1\"/>\n"
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
    cat tmp/result
    JOUTPUT+="\t<testcase name=\"$1\">\n"
    JOUTPUT+="\t\t<error message=\"fail\">`cat tmp/result`</error>\n"
    JOUTPUT+="\t</testcase>\n"
  fi

  echo -e "Test $1: $res"
}

# Arguments:
# 1: file name
# 2: relative path
function test_exec {
  ../cerberus --exec --batch $2/$1
  if [ -f $2/expected/$1.expected ]; then
    cmp --silent tmp/result $2/expected/$1.expected
  fi
  report $1 $?
}

# Arguments:
# 1: file name
# 2: relative path
function test {
  ../cerberus $2/$1
  report $1 $?
}

# Running parsing tests
for file in suite/parsing/*.c
do
  test $file .
done

# Running ci tests
for file in "${citests[@]}"
do
  test_exec $file ci
done

echo "PASSED: $pass"
echo "FAILED: $fail"

# JUnit XML output (for Jenkins report)
echo "<testsuites>" > $JOUTPUT_FILE
echo "<testsuite name=\"ci\" tests=\"$((pass + fail))\" failures=\"${fail}\" timestamp=\"$(date)\">" >> $JOUTPUT_FILE
echo -e ${JOUTPUT} >> $JOUTPUT_FILE
echo "</testsuite>" >> $JOUTPUT_FILE
echo "</testsuites>" >> $JOUTPUT_FILE

