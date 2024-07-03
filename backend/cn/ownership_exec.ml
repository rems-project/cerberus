module CF=Cerb_frontend
open Executable_spec_utils
module A=CF.AilSyntax
module C=CF.Ctype

let cn_ghost_state_sym = Sym.fresh_pretty "cn_ownership_global_ghost_state"
let cn_ghost_state_struct_type = mk_ctype ~annots:[CF.Annot.Atypedef (Sym.fresh_pretty "ownership_ghost_state")] C.Void
let cn_stack_depth_sym = Sym.fresh_pretty "cn_stack_depth"
let cn_stack_depth_ctype = C.mk_ctype_integer (Signed Long)

let c_map_local_ownership_fn_sym = Sym.fresh_pretty "c_add_local_to_ghost_state"
let c_remove_local_ownership_fn_sym = Sym.fresh_pretty "c_remove_local_from_ghost_state"

(* TODO: Use these to reduce verbosity of output.
Mirrors C+CN input slightly less since we replace declarations with a call to one of these macros *)
let c_declare_and_map_local_sym = Sym.fresh_pretty "c_declare_and_map_local"
let c_declare_init_and_map_local_sym = Sym.fresh_pretty "c_declare_init_and_map_local"


let create_ail_ownership_global_decls () = 
  [(cn_ghost_state_sym, C.mk_ctype_pointer empty_qualifiers cn_ghost_state_struct_type); (cn_stack_depth_sym, cn_stack_depth_ctype)]

let get_ownership_global_init_stats () = 
  let cn_ghost_state_init_fcall = mk_expr A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "initialise_ownership_ghost_state")), [])) in
  let cn_ghost_state_init_assign = A.(AilSexpr (mk_expr (AilEassign (mk_expr (AilEident cn_ghost_state_sym), cn_ghost_state_init_fcall)))) in
  let cn_stack_depth_init_assign = A.(AilSexpr (mk_expr (AilEassign (mk_expr (AilEident cn_stack_depth_sym), (mk_expr (A.AilEconst (ConstantInteger (IConstant (Z.of_int (-1), Decimal, None))))))))) in
  [cn_ghost_state_init_assign; cn_stack_depth_init_assign]
  

(*   
   c_map_local_to_stack_depth((uintptr_t) &xs, cn_ownership_global_ghost_state, sizeof(struct node * ), cn_stack_depth) 
*)

let generate_c_local_ownership_entry (local_sym, local_ctype) = 
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 = A.(AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident)))) in 
  let arg2 = A.(AilEident cn_ghost_state_sym) in
  let arg3 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in 
  let arg4 = A.(AilEident cn_stack_depth_sym) in 
  A.(AilSexpr (mk_expr (AilEcall (mk_expr (AilEident c_map_local_ownership_fn_sym), List.map mk_expr [arg1; arg2; arg3; arg4]))))


(*
  c_remove_local_footprint((uintptr_t) &xs, cn_ownership_global_ghost_state, sizeof(struct node * ));   
*)
let generate_c_local_ownership_exit (local_sym, local_ctype) = 
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 = A.(AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident)))) in 
  let arg2 = A.(AilEident cn_ghost_state_sym) in
  let arg3 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in 
  A.(AilSexpr (mk_expr A.(AilEcall (mk_expr (AilEident c_remove_local_ownership_fn_sym), List.map mk_expr [arg1; arg2; arg3]))))


let get_c_local_ownership_checking params = 
  let entry_ownership_stats = List.map generate_c_local_ownership_entry params in 
  let exit_ownership_stats = List.map generate_c_local_ownership_exit params in 
  (entry_ownership_stats, exit_ownership_stats)



let get_end_loc ?(offset=0) = function 
  | Cerb_location.Loc_region (_, end_pos, cursor) ->
    let new_end_pos = {end_pos with pos_cnum=end_pos.pos_cnum + offset} in 
    Cerb_location.region (new_end_pos, new_end_pos) cursor 
  | Loc_regions (pos_list, cursor) -> (match List.last pos_list with 
      | Some (_, end_pos) -> 
        let new_end_pos = {end_pos with pos_cnum=end_pos.pos_cnum + offset} in 
        Cerb_location.region (new_end_pos, new_end_pos) cursor 
      | None -> failwith "modify_decl_loc: Loc_regions has empty list of positions (should be non-empty)")
  | Loc_unknown
  | Loc_other _ 
  | Loc_point _ -> failwith "modify_decl_loc: Location of AilSdeclaration should be Loc_region or Loc_regions"



(* Ghost state tracking for block declarations *)
let rec get_c_block_local_ownership_checking_injs_aux A.(AnnotatedStatement (block_loc, attrs, block)) = 
  match block with 
    | (A.AilSblock (bindings, statements)) ->
      let end_of_block_loc = get_end_loc ~offset:(-1) block_loc in
      (match statements with 
      | [] -> [] 
      | A.(AnnotatedStatement (stat_loc, attrs', s_)) :: ss -> 
        let stat_injs = (match s_ with 
          | A.(AilSdeclaration decls) -> 
            let end_of_line_loc = get_end_loc stat_loc in 
            let decl_ownership_fcalls = List.map (fun (sym, _) -> 
              let ctype = find_ctype_from_bindings bindings sym in 
              (generate_c_local_ownership_entry (sym, ctype), generate_c_local_ownership_exit (sym, ctype))) 
            decls in
            let (decl_ownership_entry_fcalls, decl_ownership_exit_fcalls) = List.split decl_ownership_fcalls in 
            let entry_injs = [(end_of_line_loc, decl_ownership_entry_fcalls)] in 
            let exit_injs = [(end_of_block_loc, decl_ownership_exit_fcalls)] in 
            entry_injs @ exit_injs
          | (AilSblock _ as block_stat) -> get_c_block_local_ownership_checking_injs_aux A.(AnnotatedStatement (stat_loc, attrs', block_stat))
          | (AilSif (_, s1, s2)) -> 
            let injs = get_c_block_local_ownership_checking_injs_aux s1 in 
            let injs' = get_c_block_local_ownership_checking_injs_aux s2 in 
            injs @ injs'
          | AilSwhile (_, s, _) 
          | AilSdo (s, _, _) 
          | AilSswitch (_, s) 
          | AilScase (_, s) 
          | AilScase_rangeGNU (_, _, s) 
          | AilSdefault s 
          | AilSlabel (_, s, _) -> get_c_block_local_ownership_checking_injs_aux s
          | _ -> []
        ) in 
        stat_injs @ (get_c_block_local_ownership_checking_injs_aux A.(AnnotatedStatement (block_loc, attrs, (A.AilSblock (bindings, ss))))))
    | _ -> []

let rec combine_injs_over_location loc = function 
  | [] -> []
  | (loc', inj_stmt) :: injs' -> 
    let stmt = if String.equal (Cerb_location.location_to_string loc) (Cerb_location.location_to_string loc') then 
    [inj_stmt] else [] in 
    stmt @ (combine_injs_over_location loc injs')

let rec remove_duplicates ds = function 
  | [] -> []
  | l :: ls -> 
    let loc_eq_fn = fun loc loc' -> String.equal (Cerb_location.location_to_string loc) (Cerb_location.location_to_string loc') in 
    if List.mem loc_eq_fn l ds then 
      remove_duplicates ds ls 
    else 
      l :: (remove_duplicates (l::ds) ls)

let get_c_block_local_ownership_checking_injs A.(AnnotatedStatement (_, _, fn_block) as statement) = match fn_block with 
  | A.(AilSblock _) -> 
    let injs = get_c_block_local_ownership_checking_injs_aux statement in 
    let locs = List.map fst injs in 
    let locs = remove_duplicates [] locs in 
    let combined_injs = List.map (fun l -> 
      let injs' = combine_injs_over_location l injs in 
      let injs' = List.concat injs' in 
      (l, injs'))
    locs in 
    combined_injs
  | _ -> Printf.printf "Ownership_exec: function body is not a block"; []


(* Ghost state *)
let get_c_fn_local_ownership_checking_injs sym (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) = 
  match (List.assoc_opt Sym.equal sym sigm.function_definitions, List.assoc_opt Sym.equal sym sigm.declarations) with 
    | (Some (_, _, _, param_syms, fn_body), Some (_, _, Decl_function (_, _, param_types, _, _, _))) -> 
      let param_types = List.map (fun (_, ctype, _) -> ctype) param_types in
      let params = List.combine param_syms param_types in
      let ownership_stats_pair = get_c_local_ownership_checking params in
      let block_ownership_injs = get_c_block_local_ownership_checking_injs fn_body in 
      (Some ownership_stats_pair, block_ownership_injs)
    | (_, _) -> (None, [])

