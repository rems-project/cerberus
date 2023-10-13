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


let generate_c_statements_internal (loc, statements) dts =
  Printf.printf "Location at which translation happening: %s\n" (Cerb_location.simple_location loc);
  let (bindings, stats_) = List.split (List.map (Cn_internal_to_ail.cn_to_ail_cnprog_internal dts []) statements) in
  let stat_strs = List.map generate_ail_stat_strs (List.combine bindings stats_) in
  let stat_strs = List.map (List.fold_left (^) "") stat_strs in
  (* let stat_str = List.fold_left (^) "" stat_strs in *)
  (loc, stat_strs)


let generate_c_pres_and_posts_internal (instrumentation : Core_to_mucore.instrumentation) type_map (ail_prog: _ CF.AilSyntax.sigma) (prog5: unit Mucore.mu_file) =
  let dts = ail_prog.cn_datatypes in
  let preds = prog5.mu_resource_predicates in
  let (pre_bs, pre_ss, cn_vars, ownership_ctypes) = Cn_internal_to_ail.cn_to_ail_arguments_internal dts preds instrumentation.internal.pre in
  let (post_bs, post_ss, ownership_ctypes') = Cn_internal_to_ail.cn_to_ail_post_internal dts cn_vars ownership_ctypes preds instrumentation.internal.post in
  let pre_str = generate_ail_stat_strs (pre_bs, pre_ss) in
  let post_str = generate_ail_stat_strs (post_bs, post_ss) in
  ([(instrumentation.fn, (pre_str, post_str))], ownership_ctypes')




(* Core_to_mucore.instrumentation list -> executable_spec *)
let generate_c_specs_internal instrumentation_list type_map (statement_locs : Cerb_location.t CStatements.LocMap.t)
(ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
(prog5: unit Mucore.mu_file)
=
  let generate_c_spec (instrumentation : Core_to_mucore.instrumentation) =
    let rec remove_duplicates locs stats = 
      (match stats with 
        | [] -> []
        | (loc, s) :: ss ->
          let loc_equality x y = 
            String.equal (Cerb_location.location_to_string x) (Cerb_location.location_to_string y) in 
          if (List.mem loc_equality loc locs) then 
            remove_duplicates locs ss
          else 
            (loc, s) :: (remove_duplicates (loc :: locs) ss))
    in
    (* let internal_statements = List.filter (fun (_, ss) ->  List.length ss != 0) instrumentation.internal.statements in *)
    let internal_statements = remove_duplicates [] instrumentation.internal.statements in
    let c_statements = List.map (fun s -> generate_c_statements_internal s ail_prog.cn_datatypes) internal_statements in
    let (c_pres_and_posts, ownership_ctypes) = generate_c_pres_and_posts_internal instrumentation type_map ail_prog prog5 in 
    (c_pres_and_posts, c_statements, ownership_ctypes)
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
let generate_c_datatypes cn_datatypes = 
  let ail_datatypes = match cn_datatypes with
    | [] -> []
    | (d :: ds) ->
        let ail_dt1 = Cn_internal_to_ail.cn_to_ail_datatype ~first:true d in
        let ail_dts = List.map Cn_internal_to_ail.cn_to_ail_datatype ds in
        ail_dt1 :: ail_dts
  in

  let ail_datatypes = List.concat ail_datatypes in
  
  let structs = List.map generate_doc_from_ail_struct ail_datatypes in
  CF.Pp_utils.to_plain_pretty_string (concat_map_newline structs)

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
  let modified_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = defs} in
  let doc = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog) in
  let ail_records = List.map (fun r -> match r with | Some record -> [record] | None -> []) ail_records_opt in
  let records_str = generate_c_records (List.concat ail_records) in
  let funs_str = CF.Pp_utils.to_plain_pretty_string doc in 
  (funs_str, records_str)

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
  let modified_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = defs} in
  let doc = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog) in
  let preds_str = 
  CF.Pp_utils.to_plain_pretty_string doc in
  let ail_records = List.map (fun r -> match r with | Some record -> [record] | None -> []) ail_records_opt in
  let records_str = generate_c_records (List.concat ail_records) in
  (preds_str, records_str, remove_duplicates CF.Ctype.ctypeEqual ownership_ctypes')

let generate_ownership_functions ctypes (ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)  = 
  let ail_funs = List.map Cn_internal_to_ail.generate_ownership_function ctypes in 
  let (decls, defs) = List.split ail_funs in
  let modified_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = defs} in
  let doc = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog) in
  CF.Pp_utils.to_plain_pretty_string doc

