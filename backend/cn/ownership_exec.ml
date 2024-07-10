module CF=Cerb_frontend
open Executable_spec_utils
module A=CF.AilSyntax
module C=CF.Ctype

let cn_ghost_state_sym = Sym.fresh_pretty "cn_ownership_global_ghost_state"
let cn_ghost_state_struct_type = mk_ctype ~annots:[CF.Annot.Atypedef (Sym.fresh_pretty "ownership_ghost_state")] C.Void
let cn_stack_depth_sym = Sym.fresh_pretty "cn_stack_depth"
let cn_stack_depth_ctype = C.mk_ctype_integer (Signed Long)
let cn_stack_depth_incr_sym = Sym.fresh_pretty "ghost_stack_depth_incr"
let cn_stack_depth_decr_sym = Sym.fresh_pretty "ghost_stack_depth_decr"

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
  let cn_ghost_stack_depth_init_fcall = mk_expr A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "initialise_ghost_stack_depth")), [])) in
  List.map (fun e -> A.(AilSexpr e)) [cn_ghost_state_init_fcall; cn_ghost_stack_depth_init_fcall]
  

(*   
   c_map_local_to_stack_depth((uintptr_t) &xs, sizeof(struct node * )) 
*)

let generate_c_local_ownership_entry (local_sym, local_ctype) = 
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 = A.(AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident)))) in 
  let arg2 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in 
  A.(AilSexpr (mk_expr (AilEcall (mk_expr (AilEident c_map_local_ownership_fn_sym), List.map mk_expr [arg1; arg2]))))


(*
  c_remove_local_footprint((uintptr_t) &xs, cn_ownership_global_ghost_state, sizeof(struct node * ));   
*)
let generate_c_local_ownership_exit (local_sym, local_ctype) = 
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 = A.(AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident)))) in 
  let arg2 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in 
  A.(AilSexpr (mk_expr A.(AilEcall (mk_expr (AilEident c_remove_local_ownership_fn_sym), List.map mk_expr [arg1; arg2]))))


let get_c_local_ownership_checking params = 
  let entry_ownership_stats = List.map generate_c_local_ownership_entry params in 
  let exit_ownership_stats = List.map generate_c_local_ownership_exit params in 
  (entry_ownership_stats, exit_ownership_stats)


let get_start_loc ?(offset=0) = function 
  | Cerb_location.Loc_region (start_pos, _, _) ->
    let new_start_pos = {start_pos with pos_cnum=start_pos.pos_cnum + offset} in 
    Cerb_location.point new_start_pos 
  | Loc_regions (pos_list, _) -> (match List.last pos_list with 
      | Some (_, start_pos) -> 
        let new_start_pos = {start_pos with pos_cnum=start_pos.pos_cnum + offset} in 
        Cerb_location.point new_start_pos 
      | None -> failwith "modify_decl_loc: Loc_regions has empty list of positions (should be non-empty)")
  | Loc_unknown
  | Loc_other _ 
  | Loc_point _ -> failwith "modify_decl_loc: Location of AilSdeclaration should be Loc_region or Loc_regions"


let get_end_loc ?(offset=0) = function 
  | Cerb_location.Loc_region (_, end_pos, _) ->
    let new_end_pos = {end_pos with pos_cnum=end_pos.pos_cnum + offset} in 
    Cerb_location.point new_end_pos 
  | Loc_regions (pos_list, _) -> (match List.last pos_list with 
      | Some (_, end_pos) -> 
        let new_end_pos = {end_pos with pos_cnum=end_pos.pos_cnum + offset} in 
        Cerb_location.point new_end_pos 
      | None -> failwith "modify_decl_loc: Loc_regions has empty list of positions (should be non-empty)")
  | Loc_unknown
  | Loc_other _ 
  | Loc_point _ -> failwith "modify_decl_loc: Location of AilSdeclaration should be Loc_region or Loc_regions"



let rec get_c_block_unmaps_for_return vars A.(AnnotatedStatement (loc, _, s_)) = 
  match s_ with 
      (* let end_of_block_loc = get_end_loc ~offset:(-1) block_loc in *)
    | A.(AilSdeclaration _) -> []
    | (AilSblock (bs, ss)) ->
      let binding_syms_and_ctypes = List.map (fun (sym, (_, _, _, ctype)) -> (sym, ctype)) bs in
      let injs = List.map (fun s -> get_c_block_unmaps_for_return (binding_syms_and_ctypes @ vars) s) ss in 
      List.concat injs
    | (AilSif (_, s1, s2)) -> 
      let injs = get_c_block_unmaps_for_return vars s1 in 
      let injs' = get_c_block_unmaps_for_return vars s2  in 
      injs @ injs'
    | AilSwhile (_, s, _) 
    | AilSdo (s, _, _) 
    | AilSswitch (_, s) 
    | AilScase (_, s) 
    | AilScase_rangeGNU (_, _, s) 
    | AilSdefault s
    | AilSlabel (_, s, _) -> get_c_block_unmaps_for_return vars s
    | AilSgoto _ -> [] (* TODO *)
    | AilSreturn _ -> 
      let loc_before_return_stmt = get_start_loc loc in 
      let unmap_fcalls = List.map generate_c_local_ownership_exit vars in 
      [(loc_before_return_stmt, unmap_fcalls)]
    | AilScontinue
    | AilSbreak -> [] (* TODO - can be out of loop or switch statement *)
    | AilSskip 
    | AilSreturnVoid
    | AilSexpr _
    | AilSpar _
    | AilSreg_store _
    | AilSmarker _ -> []


let rec get_c_block_local_ownership_checking_injs_aux bindings A.(AnnotatedStatement (loc, _, s_)) = 
  match s_ with 
    | A.(AilSdeclaration decls) -> 
      let decl_ownership_fcalls = List.map (fun (sym, _) -> 
        let ctype = find_ctype_from_bindings bindings sym in 
        (generate_c_local_ownership_entry (sym, ctype))) 
      decls in
      (List.map fst decls, [(get_end_loc loc, decl_ownership_fcalls)])
    | (AilSblock (bs, ss)) ->
      let exit_injs = List.map (fun (b_sym, ((_, _, _), _, _, b_ctype)) -> (get_end_loc ~offset:(-1) loc, [generate_c_local_ownership_exit (b_sym, b_ctype)])) bs in 
      let stat_injs_with_decl_syms = List.map (fun s -> get_c_block_local_ownership_checking_injs_aux (bs @ bindings) s) ss in 
      let (decl_syms, stat_injs) = List.split stat_injs_with_decl_syms in 
      let bindings_without_decls = List.filter (fun (b_sym, _) -> not (List.mem Sym.equal b_sym (List.concat decl_syms))) bs in 
      (* TODO: fix location, might need comma operator *)
      let extra_binding_entry_injs = List.map (fun (b_sym, ((b_loc, _, _), _, _, b_ctype)) -> (get_end_loc ~offset:1 b_loc, [generate_c_local_ownership_entry (b_sym, b_ctype)])) bindings_without_decls in 
      ([], extra_binding_entry_injs @ (List.concat stat_injs) @ exit_injs)
    | (AilSif (_, s1, s2)) -> 
      let (decl_syms, injs) = get_c_block_local_ownership_checking_injs_aux bindings s1 in 
      let (decl_syms', injs') = get_c_block_local_ownership_checking_injs_aux bindings s2  in 
      (decl_syms @ decl_syms', injs @ injs')
    | AilSwhile (_, s, _) 
    | AilSdo (s, _, _) 
    | AilSswitch (_, s) 
    | AilScase (_, s) 
    | AilScase_rangeGNU (_, _, s) 
    | AilSdefault s
    | AilSlabel (_, s, _) -> get_c_block_local_ownership_checking_injs_aux bindings s
    | AilSgoto _
    | AilSreturn _ 
    | AilScontinue
    | AilSbreak
    | AilSskip 
    | AilSreturnVoid
    | AilSexpr _
    | AilSpar _
    | AilSreg_store _
    | AilSmarker _ -> ([], [])


(* Ghost state tracking for block declarations *)
(* let rec get_c_block_local_ownership_checking_injs_aux A.(AnnotatedStatement (block_loc, attrs, block)) label_visibles_map = 
  match block with 
    | (A.AilSblock (bindings, statements)) ->
      let end_of_block_loc = get_end_loc ~offset:(-1) block_loc in
      (match statements with 
      | [] -> [] 
      (* TODO: Use bindings and locations, not AilSDeclaration. Unitialised vars are not being mapped/unmapped under the current scheme *)
      | A.(AnnotatedStatement (stat_loc, _, s_) as stat) :: ss -> 
        let stat_injs = (match s_ with 
          | A.(AilSdeclaration decls) -> 
            let end_of_line_loc = get_end_loc stat_loc in 
            let decl_ownership_fcalls = List.map (fun (sym, _) -> 
              Printf.printf "sym: %s\n" (Sym.pp_string sym);
              let ctype = find_ctype_from_bindings bindings sym in 
              (generate_c_local_ownership_entry (sym, ctype), generate_c_local_ownership_exit (sym, ctype))) 
            decls in
            let (decl_ownership_entry_fcalls, decl_ownership_exit_fcalls) = List.split decl_ownership_fcalls in 
            let entry_injs = [(end_of_line_loc, decl_ownership_entry_fcalls)] in 
            let exit_injs = [(end_of_block_loc, decl_ownership_exit_fcalls)] in 
            entry_injs @ exit_injs
          | (AilSblock _) -> get_c_block_local_ownership_checking_injs_aux stat label_visibles_map
          | (AilSif (_, s1, s2)) -> 
            let injs = get_c_block_local_ownership_checking_injs_aux s1 label_visibles_map in 
            let injs' = get_c_block_local_ownership_checking_injs_aux s2 label_visibles_map in 
            injs @ injs'
          | AilSwhile (_, s, _) 
          | AilSdo (s, _, _) 
          | AilSswitch (_, s) 
          | AilScase (_, s) 
          | AilScase_rangeGNU (_, _, s) 
          | AilSdefault s
          | AilSlabel (_, s, _) -> get_c_block_local_ownership_checking_injs_aux s label_visibles_map
          (* | AilSlabel (label_sym, (AnnotatedStatement (s_loc, _, _) as s), _) ->  *)
            (* let visible_syms_and_ctypes = Pmap.find label_sym label_visibles_map in 
            let visible_var_entry_fcalls = List.map generate_c_local_ownership_entry visible_syms_and_ctypes in 
            let start_of_block_loc = get_start_loc ~offset:1 s_loc in  *)
            (* TODO (!!): Turn label body into block if it isn't already *)
            (* (start_of_block_loc, visible_var_entry_fcalls) :: get_c_block_local_ownership_checking_injs_aux s label_visibles_map *)
          | AilSgoto _ -> [] (* TODO *)
          | AilSreturn _ -> [] (* TODO *)
          | AilSbreak -> [] (* TODO - can be out of loop or switch statement *)
          | _ -> []
        ) in 
        stat_injs @ (get_c_block_local_ownership_checking_injs_aux A.(AnnotatedStatement (block_loc, attrs, (A.AilSblock (bindings, ss)))) label_visibles_map))
    | _ -> [] *)

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
    let (_, injs) = get_c_block_local_ownership_checking_injs_aux [] statement in 
    let injs' = get_c_block_unmaps_for_return [] statement in
    let injs = injs @ injs' in 
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

