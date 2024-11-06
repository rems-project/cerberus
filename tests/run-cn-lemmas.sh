#!/usr/bin/env bash
set -euo pipefail -o noclobber

function exits_with_code() {
  local action=$1
  local file=$2
  local -a expected_exit_codes=$3

  printf "[$file]...\n"
  timeout 60 ${action} "$file"
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

FAILED=""

COQ_LEMMAS=$(find "${DIRNAME}"/cn -type d -name 'coq_lemmas')

for TEST in ${COQ_LEMMAS}; do
  if ! exits_with_code "make -C" "${TEST}" 0; then
    FAILED+=" ${TEST}"
  fi
done

if [ -z "${FAILED}" ]; then
  exit 0
else
  printf "\033[31mFAILED: %s\033[0m\n" "${FAILED}"
  exit 1
fi

