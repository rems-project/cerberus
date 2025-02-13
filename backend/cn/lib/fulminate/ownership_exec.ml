module CF = Cerb_frontend
open Executable_spec_utils
module A = CF.AilSyntax
module C = CF.Ctype

type ail_bindings_and_statements =
  A.bindings * CF.GenTypes.genTypeCategory A.statement_ list

(* Differentiate between whether return statement carries an expression or not *)
type return_kind =
  | ReturnVoid
  | ReturnExpr of CF.GenTypes.genTypeCategory A.expression

(* Injections are treated differently depending on whether they involve returns or not *)
type injection_kind =
  | ReturnInj of return_kind
  | NonReturnInj

type ownership_injection =
  { loc : Cerb_location.t;
    bs_and_ss : ail_bindings_and_statements;
    injection_kind : injection_kind
  }

let cn_ghost_state_sym = Sym.fresh_pretty "cn_ownership_global_ghost_state"

let cn_ghost_state_struct_type =
  mk_ctype ~annots:[ CF.Annot.Atypedef (Sym.fresh_pretty "ownership_ghost_state") ] C.Void


let get_cn_stack_depth_sym = Sym.fresh_pretty "get_cn_stack_depth"

let cn_stack_depth_ctype = C.mk_ctype_integer (Signed Long)

let cn_stack_depth_incr_sym = Sym.fresh_pretty "ghost_stack_depth_incr"

let cn_stack_depth_decr_sym = Sym.fresh_pretty "ghost_stack_depth_decr"

let c_add_ownership_fn_sym = Sym.fresh_pretty "c_add_to_ghost_state"

let c_remove_ownership_fn_sym = Sym.fresh_pretty "c_remove_from_ghost_state"

(* TODO: Use these to reduce verbosity of output. Mirrors C+CN input slightly less since
   we replace declarations with a call to one of these macros *)
let c_declare_and_map_local_sym = Sym.fresh_pretty "c_declare_and_map_local"

let c_declare_init_and_map_local_sym = Sym.fresh_pretty "c_declare_init_and_map_local"

let get_start_loc ?(offset = 0) = function
  | Cerb_location.Loc_region (start_pos, _, _) ->
    let new_start_pos = { start_pos with pos_cnum = start_pos.pos_cnum + offset } in
    Cerb_location.point new_start_pos
  | Loc_regions (pos_list, _) ->
    (match List.last pos_list with
     | Some (_, start_pos) ->
       let new_start_pos = { start_pos with pos_cnum = start_pos.pos_cnum + offset } in
       Cerb_location.point new_start_pos
     | None ->
       failwith
         "get_start_loc: Loc_regions has empty list of positions (should be non-empty)")
  | Loc_point pos -> Cerb_location.point { pos with pos_cnum = pos.pos_cnum + offset }
  | Loc_unknown | Loc_other _ ->
    failwith
      "get_start_loc: Location of AilSdeclaration should be Loc_region or Loc_regions"


let get_end_loc ?(offset = 0) = function
  | Cerb_location.Loc_region (_, end_pos, _) ->
    let new_end_pos = { end_pos with pos_cnum = end_pos.pos_cnum + offset } in
    Cerb_location.point new_end_pos
  | Loc_regions (pos_list, _) ->
    (match List.last pos_list with
     | Some (_, end_pos) ->
       let new_end_pos = { end_pos with pos_cnum = end_pos.pos_cnum + offset } in
       Cerb_location.point new_end_pos
     | None ->
       failwith
         "get_end_loc: Loc_regions has empty list of positions (should be non-empty)")
  | Loc_point pos -> Cerb_location.point { pos with pos_cnum = pos.pos_cnum + offset }
  | Loc_unknown | Loc_other _ ->
    failwith
      "get_end_loc: Location of AilSdeclaration should be Loc_region or Loc_regions"


let get_ownership_global_init_stats () =
  let cn_ghost_state_init_fcall =
    mk_expr
      A.(
        AilEcall
          (mk_expr (AilEident (Sym.fresh_pretty "initialise_ownership_ghost_state")), []))
  in
  let cn_ghost_stack_depth_init_fcall =
    mk_expr
      A.(
        AilEcall
          (mk_expr (AilEident (Sym.fresh_pretty "initialise_ghost_stack_depth")), []))
  in
  List.map
    (fun e -> A.(AilSexpr e))
    [ cn_ghost_state_init_fcall; cn_ghost_stack_depth_init_fcall ]


(* c_map_local_to_stack_depth((uintptr_t) &xs, sizeof(struct node * )) *)

let generate_c_local_ownership_entry_fcall (local_sym, local_ctype) =
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 =
    A.(
      AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident))))
  in
  let arg2 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in
  let arg3 = A.(AilEcall (mk_expr (AilEident get_cn_stack_depth_sym), [])) in
  mk_expr
    (AilEcall
       (mk_expr (AilEident c_add_ownership_fn_sym), List.map mk_expr [ arg1; arg2; arg3 ]))


(* int x = 0, y = 5;

   ->

   int x = 0, _dummy = (c_map_local(&x), 0), y = 5, _dummy2 = (c_map_local(&y), 0); *)

let rec gen_loop_ownership_entry_decls bindings = function
  | [] -> ([], [])
  | (sym, expr_opt) :: xs ->
    let dummy_sym = Sym.fresh () in
    let ctype = find_ctype_from_bindings bindings sym in
    let entry_fcall = generate_c_local_ownership_entry_fcall (sym, ctype) in
    let zero_const =
      A.(AilEconst (ConstantInteger (IConstant (Z.of_int 0, Decimal, None))))
    in
    let dummy_rhs = mk_expr A.(AilEbinary (entry_fcall, Comma, mk_expr zero_const)) in
    let new_bindings =
      List.map (fun sym -> create_binding sym ctype) [ sym; dummy_sym ]
    in
    let bindings', decls' = gen_loop_ownership_entry_decls bindings xs in
    (new_bindings @ bindings', (sym, expr_opt) :: (dummy_sym, Some dummy_rhs) :: decls')


let generate_c_local_ownership_entry_inj dest_is_loop loc decls bindings =
  if dest_is_loop then (
    let new_bindings, new_decls = gen_loop_ownership_entry_decls bindings decls in
    [ (loc, new_bindings, [ A.AilSdeclaration new_decls ]) ])
  else (
    let stats_ =
      List.map
        (fun (sym, _) ->
          let ctype = find_ctype_from_bindings bindings sym in
          let entry_fcall = generate_c_local_ownership_entry_fcall (sym, ctype) in
          A.(AilSexpr entry_fcall))
        decls
    in
    [ (get_end_loc loc, [], stats_) ])


(* c_remove_local_footprint((uintptr_t) &xs, cn_ownership_global_ghost_state,
   sizeof(struct node * )); *)
let generate_c_local_ownership_exit (local_sym, local_ctype) =
  let local_ident = mk_expr A.(AilEident local_sym) in
  let arg1 =
    A.(
      AilEcast (empty_qualifiers, C.uintptr_t, mk_expr (AilEunary (Address, local_ident))))
  in
  let arg2 = A.(AilEsizeof (empty_qualifiers, local_ctype)) in
  A.(
    AilSexpr
      (mk_expr
         A.(
           AilEcall
             ( mk_expr (AilEident c_remove_ownership_fn_sym),
               List.map mk_expr [ arg1; arg2 ] ))))


let get_c_local_ownership_checking params =
  let entry_ownership_stats =
    List.map
      (fun param -> A.(AilSexpr (generate_c_local_ownership_entry_fcall param)))
      params
  in
  let exit_ownership_stats = List.map generate_c_local_ownership_exit params in
  (entry_ownership_stats, exit_ownership_stats)


let rec collect_visibles bindings = function
  | [] -> []
  | A.(AnnotatedStatement (_, _, AilSdeclaration decls)) :: ss ->
    let decl_syms_and_ctypes =
      List.map (fun (sym, _) -> (sym, find_ctype_from_bindings bindings sym)) decls
    in
    decl_syms_and_ctypes @ collect_visibles bindings ss
  | _ :: ss -> collect_visibles bindings ss


(* TODO replace with Base.List: https://github.com/rems-project/cerberus/pull/347 *)
let rec take n = function
  | [] -> []
  | x :: xs ->
    if n = 0 then
      []
    else
      x :: take (n - 1) xs


let rec get_c_control_flow_block_unmaps_aux
  break_vars
  continue_vars
  return_vars
  bindings
  A.(AnnotatedStatement (loc, _, s_))
  : ownership_injection list
  =
  match s_ with
  | A.(AilSdeclaration _) -> []
  | AilSblock (bs, ss) ->
    let injs =
      List.mapi
        (fun i s ->
          let ss_ = take (i + 1) ss in
          let visibles = collect_visibles (bs @ bindings) ss_ in
          get_c_control_flow_block_unmaps_aux
            (visibles @ break_vars)
            (visibles @ continue_vars)
            (visibles @ return_vars)
            (bs @ bindings)
            s)
        ss
    in
    List.concat injs
  | AilSif (_, s1, s2) ->
    let injs =
      get_c_control_flow_block_unmaps_aux break_vars continue_vars return_vars bindings s1
    in
    let injs' =
      get_c_control_flow_block_unmaps_aux break_vars continue_vars return_vars bindings s2
    in
    injs @ injs'
  | AilSwhile (_, s, _) | AilSdo (s, _, _) ->
    get_c_control_flow_block_unmaps_aux
      []
      []
      return_vars
      bindings
      s (* For while and do-while loops *)
  | AilSswitch (_, s) ->
    get_c_control_flow_block_unmaps_aux [] continue_vars return_vars bindings s
  | AilScase (_, s) | AilScase_rangeGNU (_, _, s) | AilSdefault s | AilSlabel (_, s, _) ->
    get_c_control_flow_block_unmaps_aux break_vars continue_vars return_vars bindings s
  | AilSgoto _ -> [] (* TODO *)
  | AilSreturnVoid ->
    [ { loc;
        bs_and_ss = ([], List.map generate_c_local_ownership_exit return_vars);
        injection_kind = ReturnInj ReturnVoid
      }
    ]
  | AilSreturn e ->
    [ { loc;
        bs_and_ss = ([], List.map generate_c_local_ownership_exit return_vars);
        injection_kind = ReturnInj (ReturnExpr e)
      }
    ]
  | AilScontinue ->
    let loc_before_continue = get_start_loc loc in
    [ { loc = loc_before_continue;
        bs_and_ss = ([], List.map generate_c_local_ownership_exit continue_vars);
        injection_kind = NonReturnInj
      }
    ]
  | AilSbreak ->
    let loc_before_break = get_start_loc loc in
    [ { loc = loc_before_break;
        bs_and_ss = ([], List.map generate_c_local_ownership_exit break_vars);
        injection_kind = NonReturnInj
      }
    ]
  | AilSskip | AilSexpr _ | AilSpar _ | AilSreg_store _ | AilSmarker _ -> []


let get_c_control_flow_block_unmaps stat =
  get_c_control_flow_block_unmaps_aux [] [] [] [] stat


(* Ghost state tracking for block declarations *)
let rec get_c_block_entry_exit_injs_aux bindings A.(AnnotatedStatement (loc, _, s_)) =
  match s_ with
  | A.(AilSdeclaration decls) ->
    (* int x = 0; -> int x = 0, _dummy = (c_map_local(&x), 0); *)
    generate_c_local_ownership_entry_inj false loc decls bindings
  | AilSblock
      ( bs,
        [ A.AnnotatedStatement (decl_loc, _, A.AilSdeclaration decls);
          A.AnnotatedStatement (_, _, A.AilSwhile (_, s, _))
        ] ) ->
    let inj = generate_c_local_ownership_entry_inj true decl_loc decls bs in
    let injs' = get_c_block_entry_exit_injs_aux [] s in
    inj @ injs'
  | AilSblock (bs, ss) ->
    let exit_injs =
      List.map
        (fun (b_sym, ((_, _, _), _, _, b_ctype)) ->
          ( get_end_loc ~offset:(-1) loc,
            [ generate_c_local_ownership_exit (b_sym, b_ctype) ] ))
        bs
    in
    let exit_injs' = List.map (fun (loc, stats) -> (loc, [], stats)) exit_injs in
    let stat_injs = List.map (fun s -> get_c_block_entry_exit_injs_aux bs s) ss in
    List.concat stat_injs @ exit_injs'
  | AilSif (_, s1, s2) ->
    let injs = get_c_block_entry_exit_injs_aux bindings s1 in
    let injs' = get_c_block_entry_exit_injs_aux bindings s2 in
    injs @ injs'
  | AilSwhile (_, s, _) -> get_c_block_entry_exit_injs_aux bindings s
  | AilSdo (s, _, _) -> get_c_block_entry_exit_injs_aux bindings s
  | AilSswitch (_, s)
  | AilScase (_, s)
  | AilScase_rangeGNU (_, _, s)
  | AilSdefault s
  | AilSlabel (_, s, _) ->
    get_c_block_entry_exit_injs_aux bindings s
  | AilSgoto _ | AilSreturn _ | AilScontinue | AilSbreak | AilSskip | AilSreturnVoid
  | AilSexpr _ | AilSpar _ | AilSreg_store _ | AilSmarker _ ->
    []


let get_c_block_entry_exit_injs stat : ownership_injection list =
  let injs = get_c_block_entry_exit_injs_aux [] stat in
  List.map
    (fun (loc, bs, ss) -> { loc; bs_and_ss = (bs, ss); injection_kind = NonReturnInj })
    injs


let rec remove_duplicates ds = function
  | [] -> []
  | l :: ls ->
    let loc_eq_fn loc loc' =
      String.equal
        (Cerb_location.location_to_string loc)
        (Cerb_location.location_to_string loc')
    in
    if List.mem loc_eq_fn l ds then
      remove_duplicates ds ls
    else
      l :: remove_duplicates (l :: ds) ls


let get_c_block_local_ownership_checking_injs
  A.(AnnotatedStatement (_, _, fn_block) as statement)
  =
  match fn_block with
  | A.(AilSblock _) ->
    let injs = get_c_block_entry_exit_injs statement in
    let injs' = get_c_control_flow_block_unmaps statement in
    let injs = injs @ injs' in
    let locs = List.map (fun o_inj -> o_inj.loc) injs in
    let locs = remove_duplicates [] locs in
    let rec combine_injs_over_location loc = function
      | [] -> []
      | inj :: injs' ->
        if
          String.equal
            (Cerb_location.location_to_string loc)
            (Cerb_location.location_to_string inj.loc)
        then (
          let bs, ss = inj.bs_and_ss in
          (bs, ss, inj.injection_kind) :: combine_injs_over_location loc injs')
        else
          combine_injs_over_location loc injs'
    in
    (* If any of the individual injections to be combined is a return injection, the entire combined injection becomes a return injection *)
    let rec get_return_inj_kind = function
      | [] -> NonReturnInj
      | ReturnInj r :: _ -> ReturnInj r
      | NonReturnInj :: xs -> get_return_inj_kind xs
    in
    (* Injections at the same location need to be grouped together *)
    let combined_injs =
      List.map
        (fun l ->
          let injs' = combine_injs_over_location l injs in
          let bs_list, ss_list, inj_kind_list =
            Executable_spec_utils.list_split_three injs'
          in
          let inj_kind = get_return_inj_kind inj_kind_list in
          { loc = l;
            bs_and_ss = (List.concat bs_list, List.concat ss_list);
            injection_kind = inj_kind
          })
        locs
    in
    combined_injs
  | _ ->
    Printf.printf "Ownership_exec: function body is not a block";
    []


(* Ghost state *)
let get_c_fn_local_ownership_checking_injs
  sym
  (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
  =
  match
    ( List.assoc_opt Sym.equal sym sigm.function_definitions,
      List.assoc_opt Sym.equal sym sigm.declarations )
  with
  | ( Some (_, _, _, param_syms, fn_body),
      Some (_, _, Decl_function (_, _, param_types, _, _, _)) ) ->
    let param_types = List.map (fun (_, ctype, _) -> ctype) param_types in
    let params = List.combine param_syms param_types in
    let ownership_stats_pair = get_c_local_ownership_checking params in
    let block_ownership_injs = get_c_block_local_ownership_checking_injs fn_body in
    (Some ownership_stats_pair, block_ownership_injs)
  | _, _ -> (None, [])
