module CF=Cerb_frontend
open Executable_spec_utils
module A=CF.AilSyntax
module C=CF.Ctype

let cn_ghost_state_sym = Sym.fresh_pretty "cn_ownership_global_ghost_state"
let cn_ghost_state_struct_type = mk_ctype ~annots:[CF.Annot.Atypedef (Sym.fresh_pretty "ownership_ghost_state")] C.Void
let cn_stack_depth_sym = Sym.fresh_pretty "cn_stack_depth"
let cn_stack_depth_ctype = C.mk_ctype_integer (Signed Long)

let c_map_local_ownership_fn_sym = Sym.fresh_pretty "c_map_local_to_stack_depth"
let c_remove_local_ownership_fn_sym = Sym.fresh_pretty "c_remove_local_footprint"


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


(*   
   c_map_local_to_stack_depth((uintptr_t) &xs, cn_ownership_global_ghost_state, sizeof(struct node * ), cn_stack_depth) 
*)

let generate_c_local_ownership_entry_fcall (local_sym, local_ctype) = 
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 = A.(AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident)))) in 
  let arg2 = A.(AilEident cn_ghost_state_sym) in
  let arg3 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in 
  let arg4 = A.(AilEident cn_stack_depth_sym) in 
  A.(AilSexpr (mk_expr (AilEcall (mk_expr (AilEident c_map_local_ownership_fn_sym), List.map mk_expr [arg1; arg2; arg3; arg4]))))


(*
  c_remove_local_footprint((uintptr_t) &xs, cn_ownership_global_ghost_state, sizeof(struct node * ));   
*)
let generate_c_local_ownership_exit_fcall (local_sym, local_ctype) = 
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 = A.(AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident)))) in 
  let arg2 = A.(AilEident cn_ghost_state_sym) in
  let arg3 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in 
  A.(AilSexpr (mk_expr A.(AilEcall (mk_expr (AilEident c_remove_local_ownership_fn_sym), List.map mk_expr [arg1; arg2; arg3]))))


let get_c_local_ownership_checking_fn_stats params = 
  let entry_ownership_stats = List.map generate_c_local_ownership_entry_fcall params in 
  let exit_ownership_stats = List.map generate_c_local_ownership_exit_fcall params in 
  (entry_ownership_stats, exit_ownership_stats)


let get_c_fn_local_ownership_checking_injs sym (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) = 
  (* let sym_stat_pairs = List.map (fun (sym, (_, _, decl)) ->
    (match decl with
      | A.Decl_object _ -> []
      | Decl_function (_, _, param_types, _, _, _) -> 
       let param_types = List.map (fun (_, ctype, _) -> ctype) param_types in
        (match List.assoc_opt Sym.equal_sym sym sigm.function_definitions with
        | Some (_, _, _, param_syms, _) -> 
            let params = List.combine param_syms param_types in
            let ownership_stats_entry_exit = get_c_local_ownership_checking_fn_stats params in 
            [(sym, ownership_stats_entry_exit)]
        | None -> [])
      )
    ) *)
  (* sigm.declarations in  *)
  match (List.assoc_opt Sym.equal sym sigm.function_definitions, List.assoc_opt Sym.equal sym sigm.declarations) with 
    | (Some (_, _, _, param_syms, _), Some (_, _, Decl_function (_, _, param_types, _, _, _))) -> 
      let param_types = List.map (fun (_, ctype, _) -> ctype) param_types in
      let params = List.combine param_syms param_types in
      let ownership_stats_pair = get_c_local_ownership_checking_fn_stats params in
      Some ownership_stats_pair
    | (_, _) -> None



