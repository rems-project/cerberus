#!/usr/bin/env bash
set -euo pipefail -o noclobber

# set -xv # uncomment for debugging

function echo_and_err() {
    printf "$1\n"
    exit 1
}

[ $# -eq 0 ] || echo_and_err "USAGE: $0"

RUNTIME_PREFIX="$OPAM_SWITCH_PREFIX/lib/cn/runtime"
[ -d "${RUNTIME_PREFIX}" ] || echo_and_err "Could not find CN's runtime directory (looked at: '${RUNTIME_PREFIX}')"

CHECK_SCRIPT="${RUNTIME_PREFIX}/libexec/cn-runtime-single-file.sh"

[ -f "${CHECK_SCRIPT}" ] || echo_and_err "Could not find single file helper script: ${CHECK_SCRIPT}"

SCRIPT_OPT="-ovq"

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


SUCCESS=$(find cn -name '*.c' \
    ! -name "*.error.c"  \
    ! -path '*/multifile/*' \
    ! -path '*/mutual_rec/*' \
    ! -path '*/tree16/*' \
    ! -name "division_casting.c" \
    ! -name "b_or.c" \
    ! -name "mod_with_constants.c" \
    ! -name "inconsistent.c" \
    ! -name "forloop_with_decl.c" \
    ! -path "tree16/as_partial_map/tree16.c" \
    ! -path "tree16/as_mutual_dt/tree16.c" \
    ! -name "mod.c" \
    ! -name "mod_precedence.c" \
    ! -path "multifile/g.c" \
    ! -path "multifile/f.c" \
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
    ! -name "tag_defs.c" \
    ! -name "cn_inline.c" \
    ! -path "mutual_rec/mutual_rec.c" \
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
    ! -name "mask_ptr.c" \
    ! -name "copy_alloc_id.c" \
    ! -name "has_alloc_id.c" \
    ! -name "ptr_diff2.c" \
    ! -name "has_alloc_id_ptr_neq.c" \
    ! -name "spec_null_shift.c" \
    ! -name "alloc_token.c" \
    ! -name "ptr_diff.c" \
    ! -name "has_alloc_id_shift.c" \
)

# Include files which cause error for proof but not testing
SUCCESS+=("merging_arrays.error.c" "pointer_to_char_cast.error.c" "pointer_to_unsigned_int_cast.error.c")


BUGGY="cn/division_casting.c \
       cn/b_or.c \
       cn/mod_with_constants.c \
       cn/inconsistent.c \
       cn/forloop_with_decl.c \
       cn/tree16/as_partial_map/tree16.c \
       cn/tree16/as_mutual_dt/tree16.c \
       cn/mod.c \
       cn/mod_precedence.c \
       cn/multifile/g.c \
       cn/multifile/f.c \
       cn/left_shift_const.c \
       cn/bitwise_compl_precedence.c \
       cn/fun_ptr_three_opts.c \
       cn/inconsistent2.c \
       cn/list_rev01.c \
       cn/block_type.c \
       cn/gnu_choose.c \
       cn/division_with_constants.c \
       cn/division.c \
       cn/get_from_arr.c \
       cn/implies.c \
       cn/split_case.c \
       cn/mod_casting.c \
       cn/arrow_access.c \
       cn/tag_defs.c \
       cn/cn_inline.c \
       cn/mutual_rec/mutual_rec.c \
       cn/bitwise_and.c \
       cn/test_pointer_eq.c \
       cn/get_from_array.c \
       cn/ownership_at_negative_index.c \
       cn/fun_addrs_cn_stmt.c \
       cn/enum_and_and.c \
       cn/division_precedence.c \
       cn/implies_associativity.c \
       cn/pred_def04.c \
       cn/gnu_types_compatible.c \
       cn/implies_precedence.c \
       cn/bitwise_compl.c \
       cn/fun_ptr_extern.c \
       cn/b_xor.c \
       cn/mask_ptr.c \
       cn/copy_alloc_id.c \
       cn/has_alloc_id.c \
       cn/ptr_diff2.c \
       cn/has_alloc_id_ptr_neq.c \
       cn/spec_null_shift.c \
       cn/alloc_token.c \
       cn/ptr_diff.c \
       cn/has_alloc_id_shift.c \
       "

# Exclude files which cause error for proof but not testing
SHOULD_FAIL=$(find cn -name '*.error.c' \
  ! -name "merging_arrays.error.c" \
  ! -name "pointer_to_char_cast.error.c" \
  ! -name "pointer_to_unsigned_int_cast.error.c" \
  ! -name "ptr_diff2.error.c" \
)

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

