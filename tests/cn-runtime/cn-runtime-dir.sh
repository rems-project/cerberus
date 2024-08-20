#!/usr/bin/env bash
set -euo pipefail -o noclobber

function echo_and_err() {
    printf "$1\n"
    exit 1
}

[ $# -eq 0 ] || echo_and_err "USAGE: $0"

RUNTIME_PREFIX="$OPAM_SWITCH_PREFIX/lib/cn/runtime"
[ -d "${RUNTIME_PREFIX}" ] || echo_and_err "Could not find CN's runtime directory (looked at: '${RUNTIME_PREFIX}')"

CHECK_SCRIPT="${RUNTIME_PREFIX}/libexec/cn-runtime-single-file.sh"

[ -f "${CHECK_SCRIPT}" ] || echo_and_err "Could not find single file helper script: ${CHECK_SCRIPT}"

SCRIPT_OPT="-oq"

function exits_with_code() {
  local file=$1
  local expected_exit_code=$2

  printf "[$file]... "
  timeout 20 "${CHECK_SCRIPT}" "${SCRIPT_OPT}" "$file" &> /dev/null
  local result=$?

  if [ $result -eq $expected_exit_code ]; then
    printf "\033[32mPASS\033[0m\n"
    return 0
  else
    printf "\033[31mFAIL\033[0m (Unexpected return code: $result)\n"
    return 1
  fi
}

SUCCESS=$(find tests/cn -name '*.c' \
    ! -name "*.error.c" \
)

BUGGY=("")

SHOULD_FAIL=$(find tests/cn -name '*.error.c')
# SHOULD_FAIL=("src/examples/read.broken.c" "src/examples/slf14_basic_succ_using_incr_attempt.broken.c")

FAILED=""

for FILE in ${SUCCESS}; do
  if ! exits_with_code "${FILE}" 0; then
    FAILED+=" ${FILE}"
  fi
done

for FILE in ${SHOULD_FAIL}; do
  if ! exits_with_code "${FILE}" 1; then
    FAILED+=" ${FILE}"
  fi
done

for FILE in ${BUGGY}; do
  if ! exits_with_code "${FILE}" 1; then
    FAILED+=" ${FILE}"
  fi
done

if [ -z "${FAILED}" ]; then
  exit 0
else
  printf "\033[31mFAILED: ${FAILED}\033[0m\n"
  exit 1
fi

