module CF=Cerb_frontend
module CB=Cerb_backend
open PPrint
open CF.Cn

module A=CF.AilSyntax 
(* Executable spec helper functions *)

type executable_spec = {
    pre_post: (CF.Symbol.sym * (string list * string list)) list;
    in_stmt: (Cerb_location.t * string) list;
}


let generate_c_statements cn_statements cn_datatypes =
  let generate_c_statement (CN_statement (loc, stmt_)) = 
    (* TODO: Remove pattern matching here - should only be in cn_to_ail.ml *)
    let pp_statement =
      match stmt_ with
      | CN_assert_stmt e -> 
        let ail_stats = Cn_to_ail.cn_to_ail_assertion e cn_datatypes in
        let doc = List.map (fun s -> CF.Pp_ail.pp_statement ~executable_spec:true s) ail_stats in
        CF.Pp_utils.to_plain_pretty_string (List.fold_left (^^) empty doc)
      | _ -> ""
    in 
  (loc, pp_statement)
  in
  List.map generate_c_statement cn_statements

let generate_c_pres_and_posts (instrumentation : Core_to_mucore.instrumentation) type_map ail_prog =
  let sym_equality = fun (loc, _) -> CF.Symbol.equal_sym loc instrumentation.fn in
  let fn_decl = List.filter sym_equality ail_prog.A.declarations in
  let fn_def = List.filter sym_equality ail_prog.A.function_definitions in
  let (arg_types, arg_syms) = 
  match (fn_decl, fn_def) with 
    | ((_, (_, _, A.(Decl_function (_, _, arg_types, _, _, _)))) :: _), ((_, (_, _, _, arg_syms, _)) :: _) -> 
      let arg_types = List.map (fun (_, ctype, _) -> ctype) arg_types in
      (arg_types, arg_syms)
    | _ -> ([], [])
  in
  let gen_old_var_fn = (fun sym -> (CF.Pp_symbol.to_string_pretty sym) ^ "_old") in
  let empty_qualifiers : CF.Ctype.qualifiers = {const = false; restrict = false; volatile = false} in
  let pp_ctype ctype = CF.Pp_utils.to_plain_pretty_string (CF.Pp_ail.pp_ctype empty_qualifiers ctype) in
  let arg_str_fn (ctype, sym) =
    pp_ctype ctype ^
    " " ^
    gen_old_var_fn sym ^
    " = " ^
    CF.Pp_symbol.to_string_pretty sym ^
    ";\n"
  in
  let arg_names = List.map CF.Pp_symbol.to_string_pretty arg_syms in
  let arg_strs = List.map arg_str_fn (List.combine arg_types arg_syms) in
  let generate_condition_str cn_condition arg_names_opt =
    (let (ail_stats, type_info) = Cn_to_ail.cn_to_ail_condition cn_condition type_map ail_prog.cn_datatypes in
    let strs = List.map (fun s -> Ail_to_c.pp_ail_stmt (s, type_info) arg_names_opt) ail_stats in
    (List.fold_left (^) "" strs) ^ ";\n")
  in
  let pres = List.map (fun i -> generate_condition_str i None) instrumentation.surface.requires in
  let posts = List.map (fun i -> generate_condition_str i (Some arg_names)) instrumentation.surface.ensures in
  (* let arg_strs = List.fold_left (^) "" arg_strs in *)
  [(instrumentation.fn, (arg_strs @ pres, posts))]
  (* let function_identifiers = List.map fst function_definitions in *)
  (* let _pres = List.map generate_c_pre instrumentation.requires in *)
  (* [(instrumentation.fn, ("some precondition;\n", ""))] *)
  
  (* let posts = List.map generate_c_post instrumentation.ensures in *)
  (* let pres_and_posts = List.combine pres posts in *)
  (* print_string ((string_of_int (List.length pres_and_posts)) ^ "\n"); *)
  (* print_string ((string_of_int (List.length function_identifiers)) ^ "\n"); *)
  (* let pres_and_posts = List.combine function_identifiers pres_and_posts in *)
  (* pres_and_posts *)
  (* pres *)
  (* [(instrumentation.fn, ("pre", "post"))] *)


(* Core_to_mucore.instrumentation list -> executable_spec *)
let generate_c_specs instrumentation_list type_map (ail_prog : _ CF.AilSyntax.sigma) =
  (* let open Core_to_mucore in *)
  let generate_c_spec (instrumentation : Core_to_mucore.instrumentation) =
    let c_pres_and_posts = generate_c_pres_and_posts instrumentation type_map ail_prog in 
    let c_statements = generate_c_statements instrumentation.surface.statements ail_prog.cn_datatypes in
    (* ([(Sym.fresh_pretty "main", ("int i_old = i;", ""))], generate_c_statements instrumentation.statements) *)
    (c_pres_and_posts, c_statements)
  in
  let specs = List.map generate_c_spec instrumentation_list in 
  let (pre_post, in_stmt) = List.split specs in
  let pre_post = List.fold_left List.append [] pre_post in
  let in_stmt = List.fold_left List.append [] in_stmt in
  let executable_spec = {pre_post = pre_post; in_stmt = in_stmt} in
  executable_spec

let concat_map_newline docs = 
  PPrint.concat_map (fun doc -> doc ^^ PPrint.hardline) docs

let generate_c_datatypes cn_datatypes = 
  let ail_datatypes = match cn_datatypes with
    | [] -> []
    | (d :: ds) ->
        let ail_dt1 = Cn_to_ail.cn_to_ail_datatype ~first:true d in
        let ail_dts = List.map Cn_to_ail.cn_to_ail_datatype ds in
        ail_dt1 :: ail_dts
  in
  (* TODO: Fix number of newlines generated using fold *)
  let generate_str_from_ail_dt (ail_dt: CF.GenTypes.genTypeCategory Cn_to_ail.ail_datatype) = 
    let stats = List.map (fun c -> CF.Pp_ail.pp_statement ~executable_spec:true c ^^ PPrint.hardline) ail_dt.stats in
    let stats = List.fold_left (^^) empty stats in
    let decls_doc = List.map Ail_to_c.pp_ail_declaration ail_dt.decls in
    let decls_doc = List.fold_left (^^) empty decls_doc in
    let structs_doc = PPrint.concat_map (fun s -> CF.Pp_ail.pp_tag_definition ~executable_spec:true s ^^ PPrint.hardline) ail_dt.structs in 
    (decls_doc ^^ PPrint.hardline ^^ stats, structs_doc)
  in
  let docs = List.map generate_str_from_ail_dt ail_datatypes in
  let (consts, structs) = List.split docs in
  CF.Pp_utils.to_plain_pretty_string (concat_map_newline consts ^^ concat_map_newline structs)

let generate_c_functions (ail_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) =
  let cn_functions = ail_prog.cn_functions in 
  let ail_funs = List.map (fun cn_f -> Cn_to_ail.cn_to_ail_function cn_f ail_prog.cn_datatypes) cn_functions in
  let (decls, defs) = List.split ail_funs in
  let modified_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma = {ail_prog with declarations = decls; function_definitions = defs} in
  let doc = CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog) in
  (* let docs = List.map (fun s -> CF.Pp_ail.pp_statement ~executable_spec:true s) ail_stats in  *)
  CF.Pp_utils.to_plain_pretty_string doc
  (* (concat_map_newline docs) *)
