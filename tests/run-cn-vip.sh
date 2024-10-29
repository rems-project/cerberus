#!/usr/bin/env bash
set -euo pipefail -o noclobber

# copying from run-ci.sh
# Z3=$(ocamlfind query z3)
# export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-}:${Z3}"
# export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:${Z3}"

USAGE="USAGE: $0 [-h]"

function echo_and_err() {
    printf "%s\n" "$1"
    exit 1
}

LEMMATA=0

while getopts "h" flag; do
 case "$flag" in
   h)
   printf "%s\n" "${USAGE}"
   exit 0
   ;;
   \?)
   echo_and_err "${USAGE}"
   ;;
 esac
done

function exits_with_code() {
  local action=$1
  local file=$2
  local -a expected_exit_codes=$3

  printf "[$file]...\n"
  timeout 15 ${action} "$file"
  local result=$?

  for code in "${expected_exit_codes[@]}"; do
    if [ $result -eq $code ]; then
      printf "\033[32mPASS\033[0m\n"
      return 0
    fi
  done

  printf "\033[31mFAIL\033[0m (Unexpected return code: %d)\n" "$result"
  return 1
}

DIRNAME=$(dirname "$0")

SUCC=$(
    find $DIRNAME/cn_vip_testsuite -name '*.c' \
        \! -name '*.annot.c' \
        \! -name '*.error.c' \
        \! -name '*.unprovable.c' \
)
FAIL=$(find $DIRNAME/cn_vip_testsuite -name '*.error.c')
ANNOT=$(find $DIRNAME/cn_vip_testsuite -name '*.annot.c')
UNPROV=$(
    find $DIRNAME/cn_vip_testsuite -name '*.unprovable.c' \
        \! -name 'pointer_copy_user_ctrlflow_bytewise.unprovable.c'
)

FAILED=''

for TEST in ${SUCC} ${ANNOT}; do
  if ! exits_with_code "cn verify -DVIP -DANNOT -DNO_ROUND_TRIP --solver-type=cvc5" "${TEST}" 0; then
      FAILED+=" ${TEST}"
  fi
done

# TODO add below with both -DNON_DET_TRUE and -DNON_DET_FALSE
# provenance_equality_auto_yx.c
# provenance_equality_global_fn_yx.c
# provenance_equality_global_yx.c

# for TEST in $FAIL $ANNOT $UNPROV
# do
#   echo $CN verify $TEST
#   RET=$?
#   if [[ "$RET" = 1 || "$RET" = 2 ]]
#   then
#     echo "$TEST -- OK"
#   else
#     echo "$TEST -- Unexpected"
#     NUM_FAILED=$(( $NUM_FAILED + 1 ))
#     FAILED="$FAILED $TEST"
#   fi
#   echo
# done

if [ -z "${FAILED}" ]; then
  exit 0
else
  printf "\033[31mFAILED: %s\033[0m\n" "${FAILED}"
  exit 1
fi



