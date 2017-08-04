#!/bin/bash

export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:$HOME/Applications/usr/lib

#Jenkins variables
export CERB_PATH=/local/jenkins/home/workspace/rems/bitbucket/cerberus
export LD_LIBRARY_PATH=/local/jenkins/home/workspace/rems/bitbucket/cerberus/dependencies/z3/lib

source tests.sh

mkdir -p tmp

pass=0
fail=0

JOUTPUT=""
JOUTPUT_FILE="ci_results.xml"

function test {
  ../cerberus --exec --batch $2/$1 > tmp/result 2> /dev/null
  cmp --silent tmp/result $2/expected/$1.expected

  if [[ "$?" -eq "0" ]]; then
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



# Running ci tests
for file in "${citests[@]}"
do
  test $file ci
done

echo "PASSED: $pass"
echo "FAILED: $fail"

# JUnit XML output (for Jenkins report)
echo "<testsuites>" > $JOUTPUT_FILE
echo "<testsuite name=\"ci\" tests=\"$((pass + failt))\" failures=\"${fail}\" timestamp=\"$(date)\">" >> $JOUTPUT_FILE
echo -e ${JOUTPUT} >> $JOUTPUT_FILE
echo "</testsuite>" >> $JOUTPUT_FILE
echo "</testsuites>" >> $JOUTPUT_FILE

