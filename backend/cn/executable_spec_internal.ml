[@@@warning "-27"]
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
    ownership_ctypes: CF.Ctype.ctype list;
}

let generate_ail_stat_strs (bs, (ail_stats_ : CF.GenTypes.genTypeCategory A.statement_ list)) = 
  let is_assert_true = function 
    | A.(AilSexpr (AnnotatedExpression (_, _, _, AilEassert expr))) ->
      (match (rm_expr expr) with
        | A.(AilEconst (ConstantInteger (IConstant (z, Decimal, Some B)))) -> Z.equal z (Z.of_int 1)
        | _ -> false
        )
    | _ -> false
  in

  let ail_stats_ = List.filter (fun s -> not (is_assert_true s)) ail_stats_ in
  let doc = List.map (fun s -> CF.Pp_ail.pp_statement ~executable_spec:true ~bs (mk_stmt s)) ail_stats_ in
  let doc = List.map (fun d -> d ^^ PPrint.hardline) doc in
  List.map CF.Pp_utils.to_plain_pretty_string doc



let rec extract_global_variables = function
  | [] -> []
  | (sym, (_, _, decl)) :: ds -> 
      (match decl with 
        | A.Decl_object (_, _, _, ctype) -> (sym, ctype) :: extract_global_variables ds
        | A.Decl_function _ -> extract_global_variables ds)


let generate_c_pres_and_posts_internal (instrumentation : Core_to_mucore.instrumentation) type_map (ail_prog: _ CF.AilSyntax.sigma) (prog5: unit Mucore.mu_file) =
  let dts = ail_prog.cn_datatypes in
  let preds = prog5.mu_resource_predicates in
  let c_return_type = match List.assoc CF.Symbol.equal_sym instrumentation.fn ail_prog.A.declarations with 
    | (_, _, A.Decl_function (_, (_, ret_ty), _, _, _, _)) -> ret_ty
    | _ -> failwith "TODO" 
  in
  let globals = extract_global_variables ail_prog.declarations in
  let ail_executable_spec = Cn_internal_to_ail.cn_to_ail_pre_post_internal dts preds globals c_return_type instrumentation.internal in 
  let pre_str = generate_ail_stat_strs ail_executable_spec.pre in
  let post_str = generate_ail_stat_strs ail_executable_spec.post in
  let in_stmt = List.map (fun (loc, bs_and_ss) -> (loc, generate_ail_stat_strs bs_and_ss)) ail_executable_spec.in_stmt in
  ([(instrumentation.fn, (pre_str, post_str))], in_stmt, ail_executable_spec.ownership_ctypes)




(* Core_to_mucore.instrumentation list -> executable_spec *)
let generate_c_specs_internal instrumentation_list type_map (statement_locs : Cerb_location.t CStatements.LocMap.t)
(ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
(prog5: unit Mucore.mu_file)
=
  let generate_c_spec (instrumentation : Core_to_mucore.instrumentation) =
    let (c_pres_and_posts, c_in_stmt, ownership_ctypes) = generate_c_pres_and_posts_internal instrumentation type_map ail_prog prog5 in 
    (c_pres_and_posts, c_in_stmt, ownership_ctypes)
  in
  let specs = List.map generate_c_spec instrumentation_list in 
  let (pre_post, in_stmt, ownership_ctypes) = list_split_three specs in
  let executable_spec = {pre_post = List.concat pre_post; in_stmt = List.concat in_stmt; ownership_ctypes = List.concat ownership_ctypes} in
  executable_spec

let concat_map_newline docs = 
  PPrint.concat_map (fun doc -> doc ^^ PPrint.hardline) docs

let generate_doc_from_ail_struct ail_struct = 
  CF.Pp_ail.pp_tag_definition ~executable_spec:true ail_struct ^^ PPrint.hardline


let generate_c_records ail_structs = 
  let struct_docs = List.map generate_doc_from_ail_struct ail_structs in
  CF.Pp_utils.to_plain_pretty_string (PPrint.concat struct_docs)

(* TODO: Use Mucore datatypes instead of CN datatypes from Ail program *)
let generate_c_datatypes (ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) = 
  let ail_datatypes = match ail_prog.cn_datatypes with
    | [] -> []
    | (d :: ds) ->
        let ail_dt1 = Cn_internal_to_ail.cn_to_ail_datatype ~first:true d in
        let ail_dts = List.map Cn_internal_to_ail.cn_to_ail_datatype ds in
        ail_dt1 :: ail_dts
  in

  let ail_datatypes = List.concat ail_datatypes in
  
  let structs = List.map generate_doc_from_ail_struct ail_datatypes in
  CF.Pp_utils.to_plain_pretty_string (concat_map_newline structs)

let generate_c_structs c_structs = 
  let ail_structs = List.map Cn_internal_to_ail.cn_to_ail_struct c_structs in 
  let docs = List.map generate_doc_from_ail_struct (List.concat ail_structs) in
  let comment = "\n/* CN VERSIONS OF C STRUCTS */\n\n" in
  comment ^ CF.Pp_utils.to_plain_pretty_string (concat_map_newline docs)


let bt_is_record_or_tuple = function 
  | BT.Record _ 
  | BT.Tuple _ -> true
  | _ -> false

let fns_and_preds_with_record_rt (funs, preds) = 
  let funs' = List.filter (fun (_, (def : LogicalFunctions.definition)) -> bt_is_record_or_tuple def.return_bt) funs in 
  let fun_syms = List.map (fun (fn_sym, _) -> fn_sym) funs' in
  let preds' = List.filter (fun (_, (def : ResourcePredicates.definition)) -> bt_is_record_or_tuple def.oarg_bt) preds in 
  let pred_syms = List.map (fun (pred_sym, _) -> pred_sym) preds' in 
  (fun_syms, pred_syms)



let generate_c_functions_internal (ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) (logical_predicates : Mucore.T.logical_predicates)  =
  let ail_funs_and_records = List.map (fun cn_f -> Cn_internal_to_ail.cn_to_ail_function_internal cn_f ail_prog.cn_datatypes) logical_predicates in
  let (ail_funs, ail_records_opt) = List.split ail_funs_and_records in
  let (decls, defs) = List.split ail_funs in
  let defs = List.filter_map (fun x -> x) defs in
  let modified_prog_1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = defs} in
  let doc_1 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog_1) in
  let modified_prog_2 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = []} in
  let doc_2 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog_2) in
  let ail_records = List.map (fun r -> match r with | Some record -> [record] | None -> []) ail_records_opt in
  let records_str = generate_c_records (List.concat ail_records) in
  let funs_defs_str = CF.Pp_utils.to_plain_pretty_string doc_1 in 
  let funs_decls_str = CF.Pp_utils.to_plain_pretty_string doc_2 in 
  let comment = "\n/* CN FUNCTIONS */\n\n" in
  (comment ^ funs_defs_str, comment ^ funs_decls_str, records_str)

let rec remove_duplicates eq_fun = function 
  | [] -> []
  | t :: ts ->
    if List.mem eq_fun t ts then
      remove_duplicates eq_fun ts 
    else
      t :: (remove_duplicates eq_fun ts)

let generate_c_predicates_internal (ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) (resource_predicates : Mucore.T.resource_predicates) ownership_ctypes =
  (* let ail_info = List.map (fun cn_f -> Cn_internal_to_ail.cn_to_ail_predicate_internal cn_f ail_prog.cn_datatypes [] ownership_ctypes resource_predicates) resource_predicates in *)
  let (ail_funs, ail_records_opt, ownership_ctypes') = Cn_internal_to_ail.cn_to_ail_predicates_internal resource_predicates ail_prog.cn_datatypes [] ownership_ctypes resource_predicates in 
  let (decls, defs) = List.split ail_funs in
  let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = defs} in
  let doc1 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1) in
  let pred_defs_str = 
  CF.Pp_utils.to_plain_pretty_string doc1 in
  let modified_prog2 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = []} in
  let doc2 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog2) in
  let pred_decls_str = 
  CF.Pp_utils.to_plain_pretty_string doc2 in
  let ail_records = List.map (fun r -> match r with | Some record -> [record] | None -> []) ail_records_opt in
  let records_str = generate_c_records (List.concat ail_records) in
  let comment = "\n/* CN PREDICATES */\n\n" in
  (comment ^ pred_defs_str, comment ^ pred_decls_str, records_str, remove_duplicates CF.Ctype.ctypeEqual ownership_ctypes')

let generate_ownership_functions ctypes (ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)  = 
  let ail_funs = List.map Cn_internal_to_ail.generate_ownership_function ctypes in 
  let (decls, defs) = List.split ail_funs in
  let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = defs} in
  let doc1 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1) in
  let modified_prog2 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = []} in
  let doc2 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog2) in
  let comment = "\n/* OWNERSHIP FUNCTIONS */\n\n" in
  (comment ^ CF.Pp_utils.to_plain_pretty_string doc1, comment ^ CF.Pp_utils.to_plain_pretty_string doc2)

let generate_conversion_and_equality_functions (ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) = 
  let ail_funs = List.map Cn_internal_to_ail.generate_struct_conversion_function ail_prog.tag_definitions in 
  let ail_funs' = List.map Cn_internal_to_ail.generate_struct_equality_function ail_prog.tag_definitions in 
  let ail_funs'' = List.map Cn_internal_to_ail.generate_datatype_equality_function ail_prog.cn_datatypes in
  let ail_funs = List.concat ail_funs in 
  let ail_funs = ail_funs @ List.concat ail_funs' @ List.concat ail_funs'' in
  let (decls, defs) = List.split ail_funs in
  let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = defs} in
  let doc1 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1) in
  let modified_prog2 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = []} in
  let doc2 = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog2) in
  let comment = "\n/* CONVERSION AND EQUALITY FUNCTIONS */\n\n" in
  (comment ^ CF.Pp_utils.to_plain_pretty_string doc1, comment ^ CF.Pp_utils.to_plain_pretty_string doc2)
