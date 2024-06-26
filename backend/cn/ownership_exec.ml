module CF=Cerb_frontend
open Executable_spec_utils
module A=CF.AilSyntax
module C=CF.Ctype

let cn_ghost_state_sym = Sym.fresh_pretty "cn_ownership_global_ghost_state"
let cn_ghost_state_struct_type = mk_ctype ~annots:[CF.Annot.Atypedef (Sym.fresh_pretty "ownership_ghost_state")] C.Void
let cn_stack_depth_sym = Sym.fresh_pretty "cn_stack_depth"
let cn_stack_depth_ctype = C.mk_ctype_integer (Signed Long)


let create_ail_ownership_global_decls () = 
  [(cn_ghost_state_sym, C.mk_ctype_pointer empty_qualifiers cn_ghost_state_struct_type); (cn_stack_depth_sym, cn_stack_depth_ctype)]

let get_ownership_global_init_stats () = 
  let cn_ghost_state_init_fcall = mk_expr A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "initialise_ownership_ghost_state")), [])) in
  let cn_ghost_state_init_assign = A.(AilSexpr (mk_expr (AilEassign (mk_expr (AilEident cn_ghost_state_sym), cn_ghost_state_init_fcall)))) in
  let cn_stack_depth_init_assign = A.(AilSexpr (mk_expr (AilEassign (mk_expr (AilEident cn_stack_depth_sym), (mk_expr (A.AilEconst (ConstantInteger (IConstant (Z.of_int (-1), Decimal, None))))))))) in
  [cn_ghost_state_init_assign; cn_stack_depth_init_assign]
  
(* TODO: C ownership checking

1. Collect all C functions in program from Ail.
2. For each function, add ownership checking on every function entry and block entry, and equivalent for function exit and block exit.
3. Inject.
  a. For function injections, can add to existing injection and corresponds to where pre and postcondition are executed.
  b. For block injections, new injection machinery needed - unless we adapt the block itself to include these statements and then pretty-print this modified program? Function modification would be harder - precondition
  would be fine but postcondition would need existing cn_epilogue machinery to ensure the correct removal is happening at modified return statements.
  For blocks, could edit `program` member of `cn_injection` type in `Source_injection` module.

*)