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

let get_start_loc ?(offset=0) = function 
  | Cerb_location.Loc_region (start_pos, _, _) ->
    let new_start_pos = {start_pos with pos_cnum=start_pos.pos_cnum + offset} in 
    Cerb_location.point new_start_pos 
  | Loc_regions (pos_list, _) -> (match List.Old.last pos_list with 
      | Some (_, start_pos) -> 
        let new_start_pos = {start_pos with pos_cnum=start_pos.pos_cnum + offset} in 
        Cerb_location.point new_start_pos 
      | None -> failwith "modify_decl_loc: Loc_regions has empty list of positions (should be non-empty)")
  | Loc_point pos -> Cerb_location.point {pos with pos_cnum=pos.pos_cnum + offset}
  | Loc_unknown
  | Loc_other _ -> failwith "modify_decl_loc: Location of AilSdeclaration should be Loc_region or Loc_regions"


let get_end_loc ?(offset=0) = function 
  | Cerb_location.Loc_region (_, end_pos, _) ->
    let new_end_pos = {end_pos with pos_cnum=end_pos.pos_cnum + offset} in 
    Cerb_location.point new_end_pos 
  | Loc_regions (pos_list, _) -> (match List.Old.last pos_list with 
      | Some (_, end_pos) -> 
        let new_end_pos = {end_pos with pos_cnum=end_pos.pos_cnum + offset} in 
        Cerb_location.point new_end_pos 
      | None -> failwith "modify_decl_loc: Loc_regions has empty list of positions (should be non-empty)")
  | Loc_point pos -> Cerb_location.point {pos with pos_cnum=pos.pos_cnum + offset}
  | Loc_unknown
  | Loc_other _ -> failwith "modify_decl_loc: Location of AilSdeclaration should be Loc_region or Loc_regions"



let create_ail_ownership_global_decls () = 
  [(cn_ghost_state_sym, C.mk_ctype_pointer empty_qualifiers cn_ghost_state_struct_type); (cn_stack_depth_sym, cn_stack_depth_ctype)]

let get_ownership_global_init_stats () = 
  let cn_ghost_state_init_fcall = mk_expr A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "initialise_ownership_ghost_state")), [])) in
  let cn_ghost_stack_depth_init_fcall = mk_expr A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "initialise_ghost_stack_depth")), [])) in
  List.map ~f:(fun e -> A.(AilSexpr e)) [cn_ghost_state_init_fcall; cn_ghost_stack_depth_init_fcall]
  

(*   
   c_map_local_to_stack_depth((uintptr_t) &xs, sizeof(struct node * )) 
*)

let generate_c_local_ownership_entry_fcall (local_sym, local_ctype) = 
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 = A.(AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident)))) in 
  let arg2 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in 
  mk_expr (AilEcall (mk_expr (AilEident c_map_local_ownership_fn_sym), List.map ~f:mk_expr [arg1; arg2]))


(* 

  int x = 0, y = 5;

  ->

  int x = 0, _dummy = (c_map_local(&x), 0), y = 5, _dummy2 = (c_map_local(&y), 0);

*)

let rec gen_loop_ownership_entry_decls bindings = function
  | [] -> ([], [])
  | (sym, expr_opt) :: xs -> 
      let dummy_sym = Sym.fresh () in 
      let ctype = find_ctype_from_bindings bindings sym in 
      let entry_fcall = generate_c_local_ownership_entry_fcall (sym, ctype) in 
      let zero_const = A.(AilEconst (ConstantInteger (IConstant (Z.of_int 0, Decimal, None)))) in
      let dummy_rhs = mk_expr A.(AilEbinary (entry_fcall, Comma, mk_expr zero_const)) in 
      let new_bindings = List.map ~f:(fun sym -> create_binding sym ctype) [sym; dummy_sym] in 
      let (bindings', decls') = gen_loop_ownership_entry_decls bindings xs in 
      (new_bindings @ bindings', (sym, expr_opt) :: (dummy_sym, Some dummy_rhs) :: decls')

let generate_c_local_ownership_entry_inj dest_is_loop loc decls bindings =
  if dest_is_loop then 
    (let (new_bindings, new_decls) = gen_loop_ownership_entry_decls bindings decls in
    [loc, new_bindings, [A.AilSdeclaration new_decls]])
  else 
    (let stats_ = List.map ~f:(fun (sym, _) -> 
      let ctype = find_ctype_from_bindings bindings sym in 
      let entry_fcall = generate_c_local_ownership_entry_fcall (sym, ctype) in 
      A.(AilSexpr entry_fcall))
    decls
    in
    [(get_end_loc loc, [], stats_)])
  
(*
  c_remove_local_footprint((uintptr_t) &xs, cn_ownership_global_ghost_state, sizeof(struct node * ));   
*)
let generate_c_local_ownership_exit (local_sym, local_ctype) = 
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 = A.(AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident)))) in 
  let arg2 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in 
  A.(AilSexpr (mk_expr A.(AilEcall (mk_expr (AilEident c_remove_local_ownership_fn_sym), List.map ~f:mk_expr [arg1; arg2]))))


let get_c_local_ownership_checking params = 
  let entry_ownership_stats = List.map ~f:(fun param -> A.(AilSexpr (generate_c_local_ownership_entry_fcall param))) params in 
  let exit_ownership_stats = List.map ~f:generate_c_local_ownership_exit params in 
  (entry_ownership_stats, exit_ownership_stats)


let rec collect_visibles bindings = function 
  | [] -> []
  | A.(AnnotatedStatement (_, _, AilSdeclaration decls)) :: ss -> 
    (* Printf.printf "Bindings: \n" ;
    List.Old.iter (fun (b_sym, _) -> Printf.printf "%s\n" (Sym.pp_string b_sym)) bindings;
    Printf.printf "Decl syms: \n" ;
    List.Old.iter (fun (decl_sym, _) -> Printf.printf "%s\n" (Sym.pp_string decl_sym)) decls; *)
    let decl_syms_and_ctypes = List.map ~f:(fun (sym, _) -> (sym, find_ctype_from_bindings bindings sym)) decls in 
    decl_syms_and_ctypes @ collect_visibles bindings ss
  | _ :: ss -> collect_visibles bindings ss

(* TODO replace with Base.List: https://github.com/rems-project/cerberus/pull/347 *)
let rec take n = function 
  | [] -> []
  | x :: xs -> 
    if n = 0 then [] else
    x :: (take (n - 1) xs)

let rec get_c_control_flow_block_unmaps_aux break_vars continue_vars return_vars bindings A.(AnnotatedStatement (loc, _, s_)) = 
  match s_ with 
    | A.(AilSdeclaration _) -> []
    | (AilSblock (bs, ss)) ->
      let injs = List.Old.mapi (fun i s ->
        let ss_ = take (i + 1) ss in 
        let visibles = collect_visibles (bs @ bindings) ss_ in 
        get_c_control_flow_block_unmaps_aux (visibles @ break_vars) (visibles @ continue_vars) (visibles @ return_vars) (bs @ bindings) s 
      ) ss in 
      List.concat injs
    | (AilSif (_, s1, s2)) -> 
      let injs = get_c_control_flow_block_unmaps_aux break_vars continue_vars return_vars bindings s1 in 
      let injs' = get_c_control_flow_block_unmaps_aux break_vars continue_vars return_vars bindings s2  in 
      injs @ injs'
    | AilSwhile (_, s, _)
    | AilSdo (s, _, _)  -> get_c_control_flow_block_unmaps_aux [] [] return_vars bindings s (* For while and do-while loops *)
    | AilSswitch (_, s) -> get_c_control_flow_block_unmaps_aux [] continue_vars return_vars bindings s
    | AilScase (_, s) 
    | AilScase_rangeGNU (_, _, s) 
    | AilSdefault s
    | AilSlabel (_, s, _) -> get_c_control_flow_block_unmaps_aux break_vars continue_vars return_vars bindings s
    | AilSgoto _ -> [] (* TODO *)
    | AilSreturnVoid ->
      [(loc, Some (None), [], List.map ~f:generate_c_local_ownership_exit return_vars)]
    | AilSreturn e -> 
      [(loc, Some (Some e), [], List.map ~f:generate_c_local_ownership_exit return_vars)]
    | AilScontinue ->
      let loc_before_continue = get_start_loc loc in 
      [(loc_before_continue, None, [], List.map ~f:generate_c_local_ownership_exit continue_vars)]
    | AilSbreak -> 
      let loc_before_break = get_start_loc loc in 
      [(loc_before_break, None, [], List.map ~f:generate_c_local_ownership_exit break_vars)]
    | AilSskip 
    | AilSexpr _
    | AilSpar _
    | AilSreg_store _
    | AilSmarker _ -> []
    
let get_c_control_flow_block_unmaps stat = get_c_control_flow_block_unmaps_aux [] [] [] [] stat
    
(* Ghost state tracking for block declarations *)
let rec get_c_block_entry_exit_injs_aux bindings A.(AnnotatedStatement (loc, _, s_)) = 
  match s_ with 
    | A.(AilSdeclaration decls) -> 
      (* 
      int x = 0;
      ->
      int x = 0, _dummy = (c_map_local(&x), 0);
      *)
      generate_c_local_ownership_entry_inj false loc decls bindings
    | (AilSblock (bs, [A.AnnotatedStatement (decl_loc, _, A.AilSdeclaration decls); A.AnnotatedStatement (_, _, A.AilSwhile (_, s, _))])) ->
      let inj = generate_c_local_ownership_entry_inj true decl_loc decls bs in  
      let injs' = get_c_block_entry_exit_injs_aux [] s in 
      inj @ injs'
    | (AilSblock (bs, ss)) ->
      let exit_injs = List.map ~f:(fun (b_sym, ((_, _, _), _, _, b_ctype)) -> (get_end_loc ~offset:(-1) loc, [generate_c_local_ownership_exit (b_sym, b_ctype)])) bs in 
      let exit_injs' = List.map ~f:(fun (loc, stats) -> (loc, [], stats)) exit_injs in 
      let stat_injs = List.map ~f:(fun s -> get_c_block_entry_exit_injs_aux  bs s) ss in 
      (List.concat stat_injs) @ exit_injs'
    | (AilSif (_, s1, s2)) -> 
      let injs = get_c_block_entry_exit_injs_aux bindings s1 in 
      let injs' = get_c_block_entry_exit_injs_aux bindings s2  in 
      injs @ injs'
    | AilSwhile (_, s, _) -> get_c_block_entry_exit_injs_aux bindings s
    | AilSdo (s, _, _) -> get_c_block_entry_exit_injs_aux bindings s
    | AilSswitch (_, s) 
    | AilScase (_, s) 
    | AilScase_rangeGNU (_, _, s) 
    | AilSdefault s
    | AilSlabel (_, s, _) -> get_c_block_entry_exit_injs_aux bindings s
    | AilSgoto _
    | AilSreturn _ 
    | AilScontinue
    | AilSbreak
    | AilSskip 
    | AilSreturnVoid
    | AilSexpr _
    | AilSpar _
    | AilSreg_store _
    | AilSmarker _ -> []

let get_c_block_entry_exit_injs stat = 
  let injs = get_c_block_entry_exit_injs_aux [] stat in 
  List.map ~f:(fun (loc, bs, ss) -> (loc, None, bs, ss)) injs

let rec combine_injs_over_location loc = function 
  | [] -> []
  | (loc', expr_opt, bs, inj_stmt) :: injs' -> 
    let stmt = if String.equal (Cerb_location.location_to_string loc) (Cerb_location.location_to_string loc') then 
    [(expr_opt, bs, inj_stmt)] else [] in 
    stmt @ (combine_injs_over_location loc injs')

let rec get_return_expr_opt = function 
  | [] -> None
  | Some e :: _ -> Some e
  | None :: xs -> get_return_expr_opt xs


(* TODO replace with Base.List: https://github.com/rems-project/cerberus/pull/347 *)
let rec remove_duplicates ds = function 
  | [] -> []
  | l :: ls -> 
    let loc_eq_fn = fun loc loc' -> String.equal (Cerb_location.location_to_string loc) (Cerb_location.location_to_string loc') in 
    if List.Old.mem loc_eq_fn l ds then 
      remove_duplicates ds ls 
    else 
      l :: (remove_duplicates (l::ds) ls)

let get_c_block_local_ownership_checking_injs A.(AnnotatedStatement (_, _, fn_block) as statement) = match fn_block with 
  | A.(AilSblock _) -> 
    let injs = get_c_block_entry_exit_injs statement in 
    let injs' = get_c_control_flow_block_unmaps statement in
    let injs = injs @ injs' in 
    let locs = List.map ~f:(fun (l, _, _, _) -> l) injs in 
    let locs = remove_duplicates [] locs in 
    let combined_injs = List.map ~f:(fun l -> 
      let injs' = combine_injs_over_location l injs in 
      let (expr_opt_list, bs_list, stats_list) = Executable_spec_utils.list_split_three injs' in 
      let return_expr_opt = get_return_expr_opt expr_opt_list in 
      (l, return_expr_opt, List.concat bs_list, List.concat stats_list))
    locs in 
    combined_injs
  | _ -> Printf.printf "Ownership_exec: function body is not a block"; []


(* Ghost state *)
let get_c_fn_local_ownership_checking_injs sym (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) = 
  match (List.Old.assoc_opt Sym.equal sym sigm.function_definitions, List.Old.assoc_opt Sym.equal sym sigm.declarations) with 
    | (Some (_, _, _, param_syms, fn_body), Some (_, _, Decl_function (_, _, param_types, _, _, _))) -> 
      let param_types = List.map ~f:(fun (_, ctype, _) -> ctype) param_types in
      let params = List.zip_exn param_syms param_types in
      let ownership_stats_pair = get_c_local_ownership_checking params in
      let block_ownership_injs = get_c_block_local_ownership_checking_injs fn_body in 
      (Some ownership_stats_pair, block_ownership_injs)
    | (_, _) -> (None, [])

