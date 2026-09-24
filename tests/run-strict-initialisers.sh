#!/bin/bash
# Verifies that --switches=strict_initialisers turns the STD §6.7.9#2
# diagnostics (excess initialisers, out-of-range array designators) into
# constraint violations, and that the same programs are still accepted
# without the switch.

TESTSDIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
cd "$TESTSDIR"

source ./common.sh  # set_cerberus_exec

mkdir -p tmp

pass=0
fail=0

function report {
  if [[ "$2" -eq 0 ]]; then
    echo -e "$1: \033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    echo -e "$1: \033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
    cat tmp/result tmp/stderr
  fi
}

set_cerberus_exec "cerberus"

# a case for the out-of-range designator message on its own (the CI files
# below trip over an excess element first)
cat > tmp/strict-designator.c <<'EOF'
int a[5] = {[7] = 1};
int main(void) { return a[0]; }
EOF

# <file>|<message expected on stderr under the switch>
cases=(
  "ci/0350-init-excess-warning.c|excess elements in initializer"
  "ci/0349-init-overflow-nested-braces.c|excess elements in initializer"
  "tmp/strict-designator.c|array designator index (7) exceeds array bounds (5)"
)

for entry in "${cases[@]}"
do
  file=${entry%%|*}
  msg=${entry#*|}

  # without the switch: accepted (the excess initialisers are dropped)
  $CERB --nolibc --typecheck-core --exec --batch $file > tmp/result 2> tmp/stderr
  report "$file (default)" $?

  # with the switch: rejected, with the §6.7.9#2 constraint violation
  $CERB --nolibc --switches=strict_initialisers --typecheck-core --exec --batch \
    $file > tmp/result 2> tmp/stderr
  if [ $? -eq 0 ]; then
    ret=1
  else
    grep -q "constraint violation: $msg" tmp/stderr
    ret=$?
  fi
  report "$file (strict_initialisers)" $ret
done

echo "STRICT-INITIALISERS PASSED: $pass"
echo "STRICT-INITIALISERS FAILED: $fail"

[ $fail -eq 0 ]
