module CF=Cerb_frontend
(* module CB=Cerb_backend
open CB.Pipeline
open Setup *)
(* open CF.Cn *)
open Executable_spec_utils
module A=CF.AilSyntax
module C=CF.Ctype

let cn_ghost_state_sym = Sym.fresh_pretty "cn_ownership_global_ghost_state"
let cn_ghost_state_struct_type = mk_ctype ~annots:[CF.Annot.Atypedef (Sym.fresh_pretty "ownership_ghost_state")] C.Void

let cn_stack_depth_sym = Sym.fresh_pretty "cn_stack_depth"


let create_ail_ownership_global_decls () = 
  let ghost_decl_object = create_decl_object (C.mk_ctype_pointer empty_qualifiers cn_ghost_state_struct_type) in 
  let ghost_decl = create_declaration cn_ghost_state_sym ghost_decl_object in
  let stack_depth_decl_object = create_decl_object (C.mk_ctype_integer (Signed Long)) in 
  let stack_depth_decl = create_declaration cn_stack_depth_sym stack_depth_decl_object in
  [ghost_decl; stack_depth_decl]
