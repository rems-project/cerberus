#!/usr/bash

citests=(
  0001-emptymain.c
  0002-return_const.c
  0003-return_arith.c
  0004-return_var.c
  0005-return_var_arith.c
  0006-return_var_unspec.c
#  0007-inits.c
  0008-cond_integer.c
  0009-cond-pointer.c
  0010-if_int.c
  0011-if_pointer.c
  0012-incr_integer.c
  0013-incr_pointer.c
#  0014-labels_scopes_bug.c
  0015-while_break.c
  0016-do_break.c
  0017-for_simple.c
  0018-lt_promotion.c
  0019-arith_promotion.c
  0020-end_of_lifetime.c
#  0021-fact.c
  0022-while_continue.c
#  0023-jump1.c
  0024-jump2.c
#  0025-jump3.c
  0026-jump4.c
  0027-jump5.c
  0028-division_by_zero.undef.c
  0029-modulo_by_zero.undef.c
  0030-call_arith.c
  0031-global.c
  0032-empty_struct_decl.c
#  0033-duplicate.error.c
#  0034-duplicate_proto.error.c
#  0035-thread_local_function.error.c
#  0036-auto_register_function.error.c
#  0037-function_conflicting_types.error.c
#  0038-function_redefinition.error.c
#  0039-struct_imcomplete.error.c
#  0040-struct_redefinition.error.c
#  0041-struct_incompatible.error.c
  0042-struct_namespace.c
  0043-struct_shadowing.c
  0044-init_scalar_enclosed.c
  0045-global_postinit.c
  0046-jump_inside_lifetime.c
  0047-conditional_eq.c
  0048-conditional_eq_else.c
  0049-void_return_empty.c
  0050-void_return_arith.c
  0051-global_non_startup.c
#  0052-global_not_constant.error.c
#  0053-recursive_factorial5.c
  0054-while_factorial5.c
  0055-while_acc.c
  0056-unary_plus.c
  0057-std_footnote_118.c
  0058-pointer_zero_init.c
  0059-glob_coretyping.c
  0060-emptydecl.c
  0061-cond_call_e.c
  0062-cond_call_e2.c
  0063-cond_e.c
  0064-cond_e2.c
# 0065-const1.error.c
# 0066-const2.error.c
# 0101-sym_cfunction.c
# 0105-incr.c
  0106-typedef_parsing_bug.c
# 0108-shifts.c
  0109-promotion_lt.c
  0110-loop_in_loop.c
  0111-skipped_label.c
  0112-call_in_label.c
# 0113-cast_assign_parsing.error.c
# 0114-const_return.error.c
  0115-hex_char_const.c
  0116-enum_constants.c
)

