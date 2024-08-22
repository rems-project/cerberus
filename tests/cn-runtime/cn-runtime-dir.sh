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
    ! -name "*.error.c"  \
    ! -path '*/multifile/*' \
    ! -path '*/mutual_rec/*' \
    ! -path '*/tree16/*' \
    ! -name "division_casting.c" \
    ! -name "b_or.c" \
    ! -name "mod_with_constants.c" \
    ! -name "inconsistent.c" \
    ! -name "forloop_with_decl.c" \
    ! -name "tree16/as_partial_map/tree16.c" \
    ! -name "tree16/as_mutual_dt/tree16.c" \
    ! -name "mod.c" \
    ! -name "mod_precedence.c" \
    ! -name "multifile/g.c" \
    ! -name "multifile/f.c" \
    ! -name "left_shift_const.c" \
    ! -name "bitwise_compl_precedence.c" \
    ! -name "fun_ptr_three_opts.c" \
    ! -name "inconsistent2.c" \
    ! -name "list_rev01.c" \
    ! -name "block_type.c" \
    ! -name "gnu_choose.c" \
    ! -name "division_with_constants.c" \
    ! -name "division.c" \
    ! -name "get_from_arr.c" \
    ! -name "implies.c" \
    ! -name "split_case.c" \
    ! -name "mod_casting.c" \
    ! -name "arrow_access.c" \
    ! -name "ghost_pointer_to_bitvec_cast.c" \
    ! -name "tag_defs.c" \
    ! -name "cn_inline.c" \
    ! -name "mutual_rec/mutual_rec.c" \
    ! -name "bitwise_and.c" \
    ! -name "test_pointer_eq.c" \
    ! -name "get_from_array.c" \
    ! -name "ownership_at_negative_index.c" \
    ! -name "fun_addrs_cn_stmt.c" \
    ! -name "enum_and_and.c" \
    ! -name "division_precedence.c" \
    ! -name "implies_associativity.c" \
    ! -name "pred_def04.c" \
    ! -name "gnu_types_compatible.c" \
    ! -name "implies_precedence.c" \
    ! -name "bitwise_compl.c" \
    ! -name "fun_ptr_extern.c" \
    ! -name "b_xor.c" \
)


BUGGY="tests/cn/division_casting.c \
       tests/cn/b_or.c \
       tests/cn/mod_with_constants.c \
       tests/cn/inconsistent.c \
       tests/cn/forloop_with_decl.c \
       tests/cn/tree16/as_partial_map/tree16.c \
       tests/cn/tree16/as_mutual_dt/tree16.c \
       tests/cn/mod.c \
       tests/cn/mod_precedence.c \
       tests/cn/multifile/g.c \
       tests/cn/multifile/f.c \
       tests/cn/left_shift_const.c \
       tests/cn/bitwise_compl_precedence.c \
       tests/cn/fun_ptr_three_opts.c \
       tests/cn/inconsistent2.c \
       tests/cn/list_rev01.c \
       tests/cn/block_type.c \
       tests/cn/gnu_choose.c \
       tests/cn/division_with_constants.c \
       tests/cn/division.c \
       tests/cn/get_from_arr.c \
       tests/cn/implies.c \
       tests/cn/split_case.c \
       tests/cn/mod_casting.c \
       tests/cn/arrow_access.c \
       tests/cn/ghost_pointer_to_bitvec_cast.c \
       tests/cn/tag_defs.c \
       tests/cn/cn_inline.c \
       tests/cn/mutual_rec/mutual_rec.c \
       tests/cn/bitwise_and.c \
       tests/cn/test_pointer_eq.c \
       tests/cn/get_from_array.c \
       tests/cn/ownership_at_negative_index.c \
       tests/cn/fun_addrs_cn_stmt.c \
       tests/cn/enum_and_and.c \
       tests/cn/division_precedence.c \
       tests/cn/implies_associativity.c \
       tests/cn/pred_def04.c \
       tests/cn/gnu_types_compatible.c \
       tests/cn/implies_precedence.c \
       tests/cn/bitwise_compl.c \
       tests/cn/fun_ptr_extern.c \
       tests/cn/b_xor.c \
       "


SHOULD_FAIL=$(find tests/cn -name '*.error.c')

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

