#!/bin/bash

pass=0
fail=0

function test {
  cerberus --exec --batch $2/$1 > result 2> /dev/null
  cmp --silent result $2/expected/$1.expected
  if [[ "$?" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
  fi

  echo -e "Test $1: $res"
}

citests=(
  01-emptymain.c
  02-return_const.c
  03-return_arith.c
  04-return_var.c
  05-return_var_arith.c
  06-return_var_unspec.c
  07-inits.c
  08-cond_integer.c
  09-cond-pointer.c
  10-if_int.c
  101-sym_cfunction.c
  105-incr.c
  106-typedef_parsing_bug.c
  108-shifts.c
  109-promotion_lt.c
  11-if_pointer.c
  12-incr_integer.c
  13-incr_pointer.c
  14-labels_scopes_bug.c
  15-while_break.c
  16-do_break.c
  17-for_simple.c
  18-lt_promotion.c
  19-arith_promotion.c
  20-end_of_lifetime.c
  21-fact.c
  22-while_continue.c
#  23-jump1.c
  24-jump2.c
#  25-jump3.c
  26-jump4.c
  27-jump5.c
  28-division_by_zero.undef.c
  29-modulo_by_zero.undef.c
  30-call_arith.c
  31-global.c
  32-empty_struct_decl.c
#  33-duplicate.error.c
#  34-duplicate_proto.error.c
#  35-thread_local_function.error.c
#  36-auto_register_function.error.c
#  37-function_conflicting_types.error.c
#  38-function_redefinition.error.c
#  39-struct_imcomplete.error.c
#  40-struct_redefinition.error.c
#  41-struct_incompatible.error.c
  42-struct_namespace.c
  43-struct_shadowing.c
  44-init_scalar_enclosed.c
  45-global_postinit.c
  46-jump_inside_lifetime.c
  47-conditional_eq.c
  48-conditional_eq_else.c
  49-void_return_empty.c
  50-void_return_arith.c
  51-global_non_startup.c
#  52-global_not_constant.error.c
  53-recursive_factorial5.c
  54-while_factorial5.c
  55-while_acc.c
  56-unary_plus.c
  57-std_footnote_118.c
  58-pointer_zero_init.c
  59-glob_coretyping.c
  60-emptydecl.c
  61-cond_call_e.c
  62-cond_call_e2.c
  63-cond_e.c
  64-cond_e2.c
)

# Running ci tests

for file in "${citests[@]}"
do
  test $file ci
done

echo "PASSED: $pass"
echo "FAILED: $fail"
