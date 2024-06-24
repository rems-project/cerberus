module CF=Cerb_frontend
module CB=Cerb_backend
open PPrint
open Executable_spec_utils
module BT=BaseTypes



module A=CF.AilSyntax
(* Executable spec helper functions *)

type executable_spec = {
    pre_post: (CF.Symbol.sym * (string list * string list)) list;
    in_stmt: (Cerb_location.t * string list) list;
    returns: (Cerb_location.t * (CF.GenTypes.genTypeCategory A.expression) option * string list) list;
}

let generate_ail_stat_strs ?(with_newline=false) (bs, (ail_stats_ : CF.GenTypes.genTypeCategory A.statement_ list)) =
  let is_assert_true = function
    | A.(AilSexpr (AnnotatedExpression (_, _, _, AilEassert expr))) ->
      (match (rm_expr expr) with
        | A.(AilEconst (ConstantPredefined PConstantTrue)) -> true
        | _ -> false
        )
    | _ -> false
  in

  let ail_stats_ = List.Old.filter (fun s -> not (is_assert_true s)) ail_stats_ in
  let doc = List.map ~f:(fun s -> CF.Pp_ail.pp_statement ~executable_spec:true ~bs (mk_stmt s)) ail_stats_ in
  let doc = List.map ~f:(fun d ->
    let newline = if with_newline then PPrint.hardline else PPrint.empty in
    newline ^^ d ^^ PPrint.hardline) doc in
  List.map ~f:CF.Pp_utils.to_plain_pretty_string doc


let populate_record_map_aux (sym, bt_ret_type) =
  match Cn_internal_to_ail.bt_to_cn_base_type bt_ret_type with
    | Cn.CN_record members ->
      let sym' = Cn_internal_to_ail.generate_sym_with_suffix ~suffix:"_record" sym in
      Cn_internal_to_ail.records := Cn_internal_to_ail.RecordMap.add members sym' !(Cn_internal_to_ail.records);
    | _ -> ()


(* Populate record table with function and predicate record return types *)
let populate_record_map (prog5: unit Mucore.mu_file) =
  let fun_syms_and_ret_types = List.map ~f:(fun (sym, (def : LogicalFunctions.definition)) -> (sym, def.return_bt)) prog5.mu_logical_predicates in
  let pred_syms_and_ret_types = List.map ~f:(fun (sym, (def : ResourcePredicates.definition)) -> (sym, def.oarg_bt)) prog5.mu_resource_predicates in
  let _ = List.map ~f:populate_record_map_aux (fun_syms_and_ret_types @ pred_syms_and_ret_types) in
  ()


let rec extract_global_variables = function
  | [] -> []
  | (sym, mu_globs) :: ds ->
      (match mu_globs with
        | Mucore.M_GlobalDef (ctype, _) -> (sym, Sctypes.to_ctype ctype) :: extract_global_variables ds
        | M_GlobalDecl (ctype) -> (sym, Sctypes.to_ctype ctype) :: extract_global_variables ds)


let generate_c_pres_and_posts_internal with_ownership_checking (instrumentation : Core_to_mucore.instrumentation) _ (sigm: _ CF.AilSyntax.sigma) (prog5: unit Mucore.mu_file) =
  let dts = sigm.cn_datatypes in
  let preds = prog5.mu_resource_predicates in
  let c_return_type = match List.Old.assoc CF.Symbol.equal_sym instrumentation.fn sigm.A.declarations with
    | (_, _, A.Decl_function (_, (_, ret_ty), _, _, _, _)) -> ret_ty
    | _ -> failwith "TODO"
  in
  let globals = extract_global_variables prog5.mu_globs in 
  let ail_executable_spec = Cn_internal_to_ail.cn_to_ail_pre_post_internal with_ownership_checking dts preds globals c_return_type instrumentation.internal in
  let pre_str = generate_ail_stat_strs ail_executable_spec.pre in
  let post_str = generate_ail_stat_strs ail_executable_spec.post in

  (* C ownership checking *)
  let ((pre_str, post_str), block_ownership_injs) = 
  if with_ownership_checking then 
    (let (fn_ownership_stats_opt, block_ownership_injs) = Ownership_exec.get_c_fn_local_ownership_checking_injs instrumentation.fn sigm in
    match fn_ownership_stats_opt with 
      | Some (entry_ownership_stats, exit_ownership_stats) -> 
         let entry_ownership_str = generate_ail_stat_strs ([], entry_ownership_stats) in 
         let exit_ownership_str = generate_ail_stat_strs ([], exit_ownership_stats) in 
         let pre_post_pair = (pre_str @ ("\n\t/* C OWNERSHIP */\n\n" :: entry_ownership_str), post_str @ ("\n\t/* C OWNERSHIP */\n\n" :: exit_ownership_str)) in 
         (pre_post_pair, block_ownership_injs)
      | None -> ((pre_str, post_str), []))
  else 
    ((pre_str, post_str), [])
  in 

  (* Needed for extracting correct location for CN statement injection *)
  let modify_magic_comment_loc loc = match loc with
    | Cerb_location.Loc_region (start_pos, end_pos, cursor) ->
        Cerb_location.(region ({start_pos with pos_cnum=start_pos.pos_cnum - 3}, {end_pos with pos_cnum=end_pos.pos_cnum + 2}) cursor)
    | _ -> assert false (* loc should always be a region *)
  in


  let in_stmt = List.map ~f:(fun (loc, bs_and_ss) -> (modify_magic_comment_loc loc, generate_ail_stat_strs bs_and_ss)) ail_executable_spec.in_stmt in
  let return_injs = List.Old.filter_map (fun (loc, e_opt, bs, ss) -> match e_opt with | Some e_opt' -> Some (loc, e_opt', bs, ss) | None -> None ) block_ownership_injs in 
  let non_return_injs = List.Old.filter (fun (_, e_opt, _, _) -> Option.is_none e_opt) block_ownership_injs in 
  let block_ownership_stmts = List.map ~f:(fun (loc, _, bs, ss) -> (loc, generate_ail_stat_strs ~with_newline:true (bs, ss))) non_return_injs in 
  let block_ownership_stmts = List.map ~f:(fun (loc, strs) -> (loc, [String.concat "\n" strs])) block_ownership_stmts in 
  let return_ownership_stmts = List.map ~f:(fun (loc, e_opt, bs, ss) -> (loc, e_opt, generate_ail_stat_strs ~with_newline:true (bs, ss))) return_injs in 
  let return_ownership_stmts = List.map ~f:(fun (loc, e_opt, strs) -> (loc, e_opt, [String.concat "\n" strs])) return_ownership_stmts in 
  ([(instrumentation.fn, (pre_str, post_str))], in_stmt @ block_ownership_stmts, return_ownership_stmts)




(* Core_to_mucore.instrumentation list -> executable_spec *)
let generate_c_specs_internal with_ownership_checking instrumentation_list type_map (_ : Cerb_location.t CStatements.LocMap.t)
(sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
(prog5: unit Mucore.mu_file)
=
let generate_c_spec (instrumentation : Core_to_mucore.instrumentation) =
  generate_c_pres_and_posts_internal with_ownership_checking instrumentation type_map sigm prog5
in
let specs = List.map ~f:generate_c_spec instrumentation_list in
let (pre_post, in_stmt, returns) = Executable_spec_utils.list_split_three specs in
let executable_spec = {pre_post = List.concat pre_post; in_stmt = List.concat in_stmt; returns = List.concat returns} in
executable_spec

let concat_map_newline docs =
  PPrint.concat_map (fun doc -> doc ^^ PPrint.hardline) docs

let generate_doc_from_ail_struct ail_struct =
  CF.Pp_ail.pp_tag_definition ~executable_spec:true ail_struct ^^ PPrint.hardline

let generate_struct_decl_str (tag, (_, _, def)) = match def with 
  | C.StructDef _ -> Printf.sprintf "struct %s;\n" (Sym.pp_string tag)
  | UnionDef _ -> ""
    
    
    
let generate_c_records ail_structs =
  let struct_docs = List.map ~f:generate_doc_from_ail_struct ail_structs in
  (CF.Pp_utils.to_plain_pretty_string (PPrint.concat struct_docs), (String.concat "" (List.map ~f:generate_struct_decl_str ail_structs)))

let generate_record_strs (_sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) ail_records =
  let (record_def_strs, record_decl_strs) = generate_c_records ail_records in
  (record_def_strs, record_decl_strs)

  (* let ail_record_equality_functions = List.map ~f:(fun r -> Cn_internal_to_ail.generate_struct_equality_function ~is_record:true sigm.cn_datatypes r) ail_records in
  let ail_record_equality_functions = List.concat ail_record_equality_functions in
  let ail_record_default_functions = List.map ~f:(fun r -> Cn_internal_to_ail.generate_struct_default_function ~is_record:true sigm.cn_datatypes r) ail_records in
  let ail_record_default_functions = List.concat ail_record_default_functions in 
  let ail_record_mapget_functions = List.map ~f:(fun r -> Cn_internal_to_ail.generate_struct_map_get ~is_record:true sigm.cn_datatypes r) ail_records in
  let ail_record_mapget_functions = List.concat ail_record_mapget_functions in  *)
  (* let (eq_decls, eq_defs) = List.Old.split ail_record_equality_functions in
  let (default_decls, default_defs) = List.Old.split ail_record_default_functions in 
  let (mapget_decls, mapget_defs) = List.Old.split ail_record_mapget_functions in  *)
  (* let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = eq_decls @ default_decls @ mapget_decls; function_definitions = eq_defs @ default_defs @ mapget_defs} in
  let equality_fun_strs = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1) in
  let decl_docs = List.map ~f:(fun (sym, (_, _, decl)) -> CF.Pp_ail.pp_function_prototype ~executable_spec:true sym decl) eq_decls in
  let equality_fun_prot_strs = List.map ~f:(fun doc -> [CF.Pp_utils.to_plain_pretty_string doc]) decl_docs in
  let equality_fun_prot_strs = String.concat "\n" (List.concat equality_fun_prot_strs) in *)
  (* (record_def_strs, record_decl_strs, CF.Pp_utils.to_plain_pretty_string equality_fun_strs, equality_fun_prot_strs) *)

let generate_all_record_strs sigm =
  generate_record_strs sigm (Cn_internal_to_ail.cn_to_ail_pred_records (Cn_internal_to_ail.RecordMap.bindings !(Cn_internal_to_ail.records)))

let generate_str_from_ail_struct ail_struct =
  CF.Pp_utils.to_plain_pretty_string (generate_doc_from_ail_struct ail_struct)

let generate_str_from_ail_structs ail_structs =
  let docs = List.map ~f:generate_doc_from_ail_struct ail_structs in
  CF.Pp_utils.to_plain_pretty_string (concat_map_newline docs)

(* TODO: Use Mucore datatypes instead of CN datatypes from Ail program *)
let generate_c_datatypes (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) =
  let ail_datatypes = match sigm.cn_datatypes with
    | [] -> []
    | (d :: ds) ->
        let ail_dt1 = Cn_internal_to_ail.cn_to_ail_datatype ~first:true d in
        let ail_dts = List.map ~f:Cn_internal_to_ail.cn_to_ail_datatype ds in
        ail_dt1 :: ail_dts
      in

  let ail_datatype_decls = List.map ~f:generate_struct_decl_str (List.concat (List.map ~f:snd ail_datatypes)) in 
  let locs_and_structs = List.map ~f:(fun (loc, structs) -> (loc, List.map ~f:generate_doc_from_ail_struct structs)) ail_datatypes in
  let locs_and_struct_strs = List.map ~f:(fun (loc, ail_structs) -> (loc, CF.Pp_utils.to_plain_pretty_string (concat_map_newline ail_structs))) locs_and_structs in
  (* let structs = List.map ~f:generate_doc_from_ail_struct ail_datatypes in *)
  (* CF.Pp_utils.to_plain_pretty_string (concat_map_newline structs) *)
  (* let _ = List.map ~f:(fun (loc, _) -> Printf.printf "Datatype location: %s\n" (Cerb_location.simple_location loc)) locs_and_struct_strs in *)

  (* Need to generate function prototype for corresponding equality function *)
  let datatype_equality_funs = List.map ~f:Cn_internal_to_ail.generate_datatype_equality_function sigm.cn_datatypes in
  let datatype_equality_funs = List.concat datatype_equality_funs in
  let (dt_eq_decls, _) = List.Old.split datatype_equality_funs in
  let decl_docs = List.map ~f:(fun (sym, (_, _, decl)) -> CF.Pp_ail.pp_function_prototype ~executable_spec:true sym decl) dt_eq_decls in
  let decl_strs = List.map ~f:(fun doc -> CF.Pp_utils.to_plain_pretty_string doc) decl_docs in
  (locs_and_struct_strs, String.concat "\n" ail_datatype_decls, decl_strs)


let print_c_structs c_structs =
  let struct_defs_str = generate_str_from_ail_structs c_structs in 
  let struct_decls_str = List.map ~f:generate_struct_decl_str c_structs in 
  ("\n/* ORIGINAL C STRUCTS */\n\n" ^ struct_defs_str, String.concat "" struct_decls_str)

let generate_cn_versions_of_structs c_structs =
  let ail_structs = List.concat (List.map ~f:Cn_internal_to_ail.cn_to_ail_struct c_structs) in
  let struct_decls = List.map ~f:generate_struct_decl_str ail_structs in
  ("\n/* CN VERSIONS OF C STRUCTS */\n\n" ^ generate_str_from_ail_structs ail_structs, String.concat "" struct_decls)

let generate_struct_injs (sigm: CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)  =
  let generate_struct_inj (((_, (loc, _, tag_def)) as def) : (A.ail_identifier * (Cerb_location.t * CF.Annot.attributes * C.tag_definition))) =
    match tag_def with
    | C.StructDef _ ->
      let c_struct_str = generate_str_from_ail_struct def in
      let cn_struct_str = generate_str_from_ail_structs (Cn_internal_to_ail.cn_to_ail_struct def) in
      let xs = Cn_internal_to_ail.generate_struct_conversion_function def in
      let ys = Cn_internal_to_ail.generate_struct_equality_function sigm.cn_datatypes def in
      let prototypes_str = match (xs, ys) with
        | (((sym1, (loc1, attrs1, conversion_decl)), _) :: _, ((sym2, (loc2, attrs2, equality_decl)), _) :: _) ->
          let conversion_def = (sym1, (loc1, attrs1, conversion_decl)) in
          let equality_def = (sym2, (loc2, attrs2, equality_decl)) in
          let decl_docs = List.map ~f:(fun (sym, (_, _, decl)) -> CF.Pp_ail.pp_function_prototype ~executable_spec:true sym decl) [conversion_def; equality_def] in
          let decl_strs = List.map ~f:(fun doc -> CF.Pp_utils.to_plain_pretty_string doc) decl_docs in
          String.concat "\n" decl_strs
        | (_, _) -> ""
      in
      let str_list = [c_struct_str; cn_struct_str; prototypes_str] in
      (* let filename = Cerb_location.get_filename loc in  *)
      [(loc, str_list)]
    | C.UnionDef _ -> []
  in
  let struct_injs = List.map ~f:generate_struct_inj sigm.tag_definitions in
  List.concat struct_injs


let bt_is_record_or_tuple = function
  | BT.Record _
  | BT.Tuple _ -> true
  | _ -> false

let fns_and_preds_with_record_rt (funs, preds) =
  let funs' = List.Old.filter (fun (_, (def : LogicalFunctions.definition)) -> bt_is_record_or_tuple def.return_bt) funs in
  let fun_syms = List.map ~f:(fun (fn_sym, _) -> fn_sym) funs' in
  let preds' = List.Old.filter (fun (_, (def : ResourcePredicates.definition)) -> bt_is_record_or_tuple def.oarg_bt) preds in
  let pred_syms = List.map ~f:(fun (pred_sym, _) -> pred_sym) preds' in
  (fun_syms, pred_syms)

let generate_c_record_funs (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) (logical_predicates : Mucore.T.logical_predicates) (resource_predicates : Mucore.T.resource_predicates) =
  let cn_record_info = List.map ~f:(fun (sym, (def : LogicalFunctions.definition)) ->
    match def.return_bt with | BT.Record ms -> [(Cn_internal_to_ail.generate_sym_with_suffix ~suffix:"_record" sym, ms)] | _ -> []) logical_predicates in 
  let cn_record_info' = List.map ~f:(fun (sym, (def : ResourcePredicates.definition)) ->
    match def.oarg_bt with | BT.Record ms -> [(Cn_internal_to_ail.generate_sym_with_suffix ~suffix:"_record" sym, ms)] | _ -> []) resource_predicates in 
  let cn_record_info = List.concat (cn_record_info @ cn_record_info') in 
  let record_equality_functions = List.concat (List.map ~f:(Cn_internal_to_ail.generate_record_equality_function sigm.cn_datatypes) cn_record_info) in 
  let record_default_functions = List.concat (List.map ~f:(Cn_internal_to_ail.generate_record_default_function sigm.cn_datatypes) cn_record_info) in 
  let record_map_get_functions = List.concat (List.map ~f:(Cn_internal_to_ail.generate_record_map_get sigm.cn_datatypes) cn_record_info) in 
  let (eq_decls, eq_defs) = List.Old.split record_equality_functions in
  let (default_decls, default_defs) = List.Old.split record_default_functions in 
  let (mapget_decls, mapget_defs) = List.Old.split record_map_get_functions in 
  let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = eq_decls @ default_decls @ mapget_decls; function_definitions = eq_defs @ default_defs @ mapget_defs} in
  let fun_doc = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1) in
  let fun_strs = CF.Pp_utils.to_plain_pretty_string fun_doc in
  let decl_docs = List.map ~f:(fun (sym, (_, _, decl)) -> CF.Pp_ail.pp_function_prototype ~executable_spec:true sym decl) (eq_decls @ default_decls @ mapget_decls) in
  let fun_prot_strs = List.map ~f:(fun doc -> [CF.Pp_utils.to_plain_pretty_string doc]) decl_docs in
  let fun_prot_strs = String.concat "\n" (List.concat fun_prot_strs) in
  (fun_strs, fun_prot_strs)


let generate_c_functions_internal (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) (logical_predicates : Mucore.T.logical_predicates)  =
  let ail_funs_and_records = List.map ~f:(fun cn_f -> Cn_internal_to_ail.cn_to_ail_function_internal cn_f sigm.cn_datatypes sigm.cn_functions) logical_predicates in

  let (ail_funs, ail_records_opt) = List.Old.split ail_funs_and_records in
  let (locs_and_decls, defs) = List.Old.split ail_funs in
  let (locs, decls) = List.Old.split locs_and_decls in
  let decl_docs = List.map ~f:(fun (sym, (_, _, decl)) -> CF.Pp_ail.pp_function_prototype ~executable_spec:true sym decl) decls in
  let decl_strs = List.map ~f:(fun doc -> CF.Pp_utils.to_plain_pretty_string doc) decl_docs in
  let decl_str = String.concat "\n" decl_strs in

  let defs = List.Old.filter_map (fun x -> x) defs in
  let modified_prog_1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = decls; function_definitions = defs} in
  let doc_1 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog_1) in
  let inline_decl_docs = List.map ~f:(fun (sym, (_, _, decl)) -> CF.Pp_ail.pp_function_prototype ~executable_spec:true sym decl) decls in
  let inline_decl_strs = List.map ~f:(fun doc -> [CF.Pp_utils.to_plain_pretty_string doc]) inline_decl_docs in
  let locs_and_decls' = List.Old.combine locs inline_decl_strs in
  (* let modified_prog_2 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = decls; function_definitions = []} in *)
  (* let doc_2 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog_2) in *)
  let ail_records = List.map ~f:(fun r -> match r with | Some record -> [record] | None -> []) ail_records_opt in
  let record_triple_str = generate_record_strs sigm (List.concat ail_records) in
  let funs_defs_str = CF.Pp_utils.to_plain_pretty_string doc_1 in
  (* let funs_decls_str = CF.Pp_utils.to_plain_pretty_string doc_2 in  *)
  (funs_defs_str, "\n/* CN FUNCTIONS */\n\n" ^ decl_str, locs_and_decls', record_triple_str)

let rec remove_duplicates eq_fun = function
  | [] -> []
  | t :: ts ->
    if List.Old.mem eq_fun t ts then
      remove_duplicates eq_fun ts
    else
      t :: (remove_duplicates eq_fun ts)

let generate_c_predicates_internal (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) (resource_predicates : Mucore.T.resource_predicates) =
  (* let ail_info = List.map ~f:(fun cn_f -> Cn_internal_to_ail.cn_to_ail_predicate_internal cn_f sigm.cn_datatypes [] ownership_ctypes resource_predicates) resource_predicates in *)
  (* TODO: Remove passing of resource_predicates argument twice - could use counter? *)
  let (ail_funs, ail_records_opt) = Cn_internal_to_ail.cn_to_ail_predicates_internal resource_predicates sigm.cn_datatypes [] resource_predicates sigm.cn_predicates in
  let (locs_and_decls, defs) = List.Old.split ail_funs in
  let (locs, decls) = List.Old.split locs_and_decls in
  let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = decls; function_definitions = defs} in
  let doc1 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1) in
  let pred_defs_str =
  CF.Pp_utils.to_plain_pretty_string doc1 in
  let pred_locs_and_decls = List.map ~f:(fun (loc, (sym, (_, _, decl))) ->
     (loc, [CF.Pp_utils.to_plain_pretty_string (CF.Pp_ail.pp_function_prototype ~executable_spec:true sym decl)])) (List.Old.combine locs decls) in
  let ail_records = List.map ~f:(fun r -> match r with | Some record -> [record] | None -> []) ail_records_opt in
  let record_triple_str = generate_record_strs sigm (List.concat ail_records) in
  ("\n/* CN PREDICATES */\n\n" ^ pred_defs_str, pred_locs_and_decls, record_triple_str)

let generate_ownership_functions with_ownership_checking ownership_ctypes (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)  =
  (* let ctypes = List.map ~f:get_ctype_without_ptr ctypes in  *)
  let rec remove_duplicates ret_list = function 
    | [] -> []
    | x :: xs ->
        if (List.Old.mem execCtypeEqual x ret_list) then 
          remove_duplicates (x :: ret_list) xs
        else 
          x :: remove_duplicates (x :: ret_list) xs  
  in 
  let ctypes = !ownership_ctypes in 
  let ctypes = remove_duplicates [] ctypes in 
  let ail_funs = List.map ~f:(fun ctype -> Cn_internal_to_ail.generate_ownership_function with_ownership_checking ctype) ctypes in
  let (decls, defs) = List.Old.split ail_funs in
  let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = decls; function_definitions = defs} in
  let doc1 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1) in
  let modified_prog2 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = decls; function_definitions = []} in
  let doc2 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog2) in
  let comment = "\n/* OWNERSHIP FUNCTIONS */\n\n" in
  (comment ^ CF.Pp_utils.to_plain_pretty_string doc1, CF.Pp_utils.to_plain_pretty_string doc2)

let generate_conversion_and_equality_functions (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) =
  let ail_funs = List.map ~f:Cn_internal_to_ail.generate_struct_conversion_function sigm.tag_definitions in
  let ail_funs' = List.map ~f:(Cn_internal_to_ail.generate_struct_equality_function sigm.cn_datatypes) sigm.tag_definitions in
  let ail_funs'' = List.map ~f:Cn_internal_to_ail.generate_datatype_equality_function sigm.cn_datatypes in
  let ail_funs''' = List.map ~f:(Cn_internal_to_ail.generate_struct_map_get sigm.cn_datatypes) sigm.tag_definitions in
  let ail_funs'''' = List.map ~f:(Cn_internal_to_ail.generate_struct_default_function sigm.cn_datatypes) sigm.tag_definitions in
  let ail_funs = List.concat ail_funs in
  let ail_funs = ail_funs @ List.concat ail_funs' @ List.concat ail_funs'' @ List.concat ail_funs''' @ List.concat ail_funs'''' in
  let (decls, defs) = List.Old.split ail_funs in
  let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = decls; function_definitions = defs} in
  let doc1 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1) in
  let modified_prog2 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {sigm with declarations = decls; function_definitions = []} in
  let doc2 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog2) in
  let comment = "\n/* GENERATED STRUCT FUNCTIONS */\n\n" in
  (comment ^ CF.Pp_utils.to_plain_pretty_string doc1, comment ^ CF.Pp_utils.to_plain_pretty_string doc2)


let generate_ownership_global_assignments (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) (prog5: unit Mucore.mu_file) = 
  let main_fn_sym_list = List.Old.filter (fun (fn_sym, _) -> String.equal "main" (Sym.pp_string fn_sym)) sigm.function_definitions in 
  match main_fn_sym_list with 
    | [] -> failwith "CN-exec: No main function so ownership globals cannot be initialised"
    | (main_sym, _) :: _ ->
      let globals = extract_global_variables prog5.mu_globs in 
      let global_map_fcalls = List.map ~f:Ownership_exec.generate_c_local_ownership_entry_fcall globals in 
      let global_map_stmts_ = List.map ~f:(fun e -> A.AilSexpr e) global_map_fcalls in 
      let assignments = Ownership_exec.get_ownership_global_init_stats () in
      let init_and_global_mapping_str = generate_ail_stat_strs ([], assignments @ global_map_stmts_) in
      let global_unmapping_stmts_ = List.map ~f:Ownership_exec.generate_c_local_ownership_exit globals in 
      let global_unmapping_str = generate_ail_stat_strs ([], global_unmapping_stmts_) in
      [(main_sym, (init_and_global_mapping_str, global_unmapping_str))]
