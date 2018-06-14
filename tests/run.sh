#!/bin/bash

export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:`ocamlfind query Z3`
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`ocamlfind query Z3`

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
    cat tmp/result | grep -E "Undefined|UNDEFINED"
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
    JOUTPUT+="\t\t<error message=\"fail\">`cat tmp/result tmp/stderr`</error>\n"
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

# Running parsing tests
for file in suite/parsing/*.c
do
  ../cerberus $file > tmp/result 2> tmp/stderr
  report $file $?
done
echo "PARSING PASSED: $pass"
echo "CI FAILED: $fail"
create_testsuite "parsing"

# Running ci tests
for file in "${citests[@]}"
do
  ../cerberus --exec --batch ci/$file > tmp/result 2> tmp/stderr
  if [ -f ci/expected/$1.expected ]; then
    cmp --silent tmp/result ci/expected/$file.expected
  fi
  report $file $?
done
echo "CI PASSED: $pass"
echo "CI FAILED: $fail"
create_testsuite "ci"

# Running TinyCC tests
for file in tcc/*.c
do
  ../cerberus $file --cpp="cc -E -C -nostdinc -undef -D__cerb__ -I../include/c/libc -I..include/c/posix" --exec > tmp/result 2> tmp/stderr
  cmp --silent tmp/result ${file%.c}.expect
  report $file $?
done
echo "TCC PASSED: $pass"
echo "TCC FAILED: $fail"
create_testsuite "tcc"

# Running gcc torture
for file in gcc-torture/breakdown/success/*.c
do
  # Disable -traditional-cpp
  ../cerberus $file --cpp="cc -E -C -nostdinc -undef -D__cerb__ -I../include/c/libc -I..include/c/posix" --exec --batch > tmp/result 2> tmp/stderr
  grep -E "Specified.0.|EXIT" tmp/result > /dev/null
  report $file $?
done
echo "GCC-TORTURE PASSED: $pass"
echo "GCC-TORTURE FAILED: $fail"
create_testsuite "gcc-torture"

echo "</testsuites>" >> $JOUTPUT_FILE
