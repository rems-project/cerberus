#!/usr/bin/env bash
set -euo pipefail -o noclobber

# copying from run-ci.sh
Z3=$(ocamlfind query z3)
export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-}:${Z3}"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:${Z3}"

USAGE="USAGE: $0 [-hl]"

function echo_and_err() {
    printf "%s\n" "$1"
    exit 1
}

LEMMATA=0
VIP=""

while getopts "hlv" flag; do
 case "$flag" in
   h)
   printf "%s\n" "${USAGE}"
   exit 0
   ;;
   l)
   LEMMATA=1
   ;;
   v)
   VIP="--vip"
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
  timeout 30 ${action} "$file"
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

SUCC=$(find "${DIRNAME}"/cn -name '*.c' | grep -v '\.error\.c')
FAIL=$(find "${DIRNAME}"/cn -name '*.error.c')

FAILED=""

for TEST in ${SUCC}; do
  if ! exits_with_code "cn verify ${VIP}" "${TEST}" 0; then
    FAILED+=" ${TEST}"
  fi
done

for TEST in ${FAIL}; do
  if ! exits_with_code "cn verify ${VIP}" "${TEST}" "(1 2)"; then
    FAILED+=" ${TEST}"
  fi
done

COQ_LEMMAS=$(find "${DIRNAME}"/cn -type d -name 'coq_lemmas')

if [ "${LEMMATA}" -eq 1 ]; then
  for TEST in ${COQ_LEMMAS}; do
      if ! exits_with_code "make -C" "${TEST}" 0; then
        FAILED+=" ${TEST}"
      fi
  done
fi

if [ -z "${FAILED}" ]; then
  exit 0
else
  printf "\033[31mFAILED: %s\033[0m\n" "${FAILED}"
  exit 1
fi

