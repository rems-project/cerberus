module CF = Cerb_frontend
module CB = Cerb_backend
open PPrint
open Executable_spec_utils
module BT = BaseTypes
module A = CF.AilSyntax
module IT = IndexTerms
module LRT = LogicalReturnTypes
module LAT = LogicalArgumentTypes
module AT = ArgumentTypes

type executable_spec =
  { pre_post : (CF.Symbol.sym * (string list * string list)) list;
    in_stmt : (Cerb_location.t * string list) list;
    returns :
      (Cerb_location.t * (CF.GenTypes.genTypeCategory A.expression option * string list))
        list
  }

let doc_to_pretty_string = CF.Pp_utils.to_plain_pretty_string

let generate_ail_stat_strs
  ?(with_newline = false)
  (bs, (ail_stats_ : CF.GenTypes.genTypeCategory A.statement_ list))
  =
  let is_assert_true = function
    | A.(AilSexpr (AnnotatedExpression (_, _, _, AilEassert expr))) ->
      (match rm_expr expr with
       | A.(AilEconst (ConstantPredefined PConstantTrue)) -> true
       | _ -> false)
    | _ -> false
  in
  (* Filter out unneeded assert(true) statements *)
  let ail_stats_ = List.filter (fun s -> not (is_assert_true s)) ail_stats_ in
  let doc =
    List.map
      (fun s -> CF.Pp_ail.(with_executable_spec (pp_statement ~bs) (mk_stmt s)))
      ail_stats_
  in
  let doc =
    List.map
      (fun d ->
        let newline = if with_newline then PPrint.hardline else PPrint.empty in
        newline ^^ d ^^ PPrint.hardline)
      doc
  in
  List.map doc_to_pretty_string doc


let rec extract_global_variables = function
  | [] -> []
  | (sym, globs) :: ds ->
    (match globs with
     | Mucore.GlobalDef (ctype, _) ->
       (sym, Sctypes.to_ctype ctype) :: extract_global_variables ds
     | GlobalDecl ctype -> (sym, Sctypes.to_ctype ctype) :: extract_global_variables ds)


let generate_c_pres_and_posts_internal
  without_ownership_checking
  (instrumentation : Executable_spec_extract.instrumentation)
  (sigm : _ CF.AilSyntax.sigma)
  (prog5 : unit Mucore.file)
  =
  let dts = sigm.cn_datatypes in
  let preds = prog5.resource_predicates in
  let c_return_type =
    match List.assoc CF.Symbol.equal_sym instrumentation.fn sigm.A.declarations with
    | _, _, A.Decl_function (_, (_, ret_ty), _, _, _, _) -> ret_ty
    | _ -> failwith (__LOC__ ^ ": C function to be instrumented not found in Ail AST")
  in
  let globals = extract_global_variables prog5.globs in
  let ail_executable_spec =
    Cn_to_ail.cn_to_ail_pre_post
      ~without_ownership_checking
      dts
      preds
      globals
      c_return_type
      instrumentation.internal
  in
  let pre_str = generate_ail_stat_strs ail_executable_spec.pre in
  let post_str = generate_ail_stat_strs ail_executable_spec.post in
  (* C ownership checking *)
  let (pre_str, post_str), block_ownership_injs =
    if without_ownership_checking then
      ((pre_str, post_str), [])
    else (
      let fn_ownership_stats_opt, block_ownership_injs =
        Ownership_exec.get_c_fn_local_ownership_checking_injs instrumentation.fn sigm
      in
      match fn_ownership_stats_opt with
      | Some (entry_ownership_stats, exit_ownership_stats) ->
        let entry_ownership_str = generate_ail_stat_strs ([], entry_ownership_stats) in
        let exit_ownership_str = generate_ail_stat_strs ([], exit_ownership_stats) in
        let pre_post_pair =
          ( pre_str @ ("\n\t/* C OWNERSHIP */\n\n" :: entry_ownership_str),
            (* NOTE - the nesting pre - entry - exit - post *)
            ("\n\t/* C OWNERSHIP */\n\n" :: exit_ownership_str) @ post_str )
        in
        (pre_post_pair, block_ownership_injs)
      | None -> ((pre_str, post_str), []))
  in
  (* Needed for extracting correct location for CN statement injection *)
  let modify_magic_comment_loc loc =
    match loc with
    | Cerb_location.Loc_region (start_pos, end_pos, cursor) ->
      Cerb_location.(
        region
          ( { start_pos with pos_cnum = start_pos.pos_cnum - 3 },
            { end_pos with pos_cnum = end_pos.pos_cnum + 2 } )
          cursor)
    | _ -> assert false (* loc should always be a region *)
  in
  let in_stmt =
    List.map
      (fun (loc, bs_and_ss) ->
        (modify_magic_comment_loc loc, generate_ail_stat_strs bs_and_ss))
      ail_executable_spec.in_stmt
  in
  let return_injs =
    List.filter_map
      (fun (loc, e_opt, bs, ss) ->
        match e_opt with Some e_opt' -> Some (loc, e_opt', bs, ss) | None -> None)
      block_ownership_injs
  in
  let non_return_injs =
    List.filter (fun (_, e_opt, _, _) -> Option.is_none e_opt) block_ownership_injs
  in
  let block_ownership_stmts =
    List.map
      (fun (loc, _, bs, ss) -> (loc, generate_ail_stat_strs ~with_newline:true (bs, ss)))
      non_return_injs
  in
  let block_ownership_stmts =
    List.map (fun (loc, strs) -> (loc, [ String.concat "\n" strs ])) block_ownership_stmts
  in
  let return_ownership_stmts =
    List.map
      (fun (loc, e_opt, bs, ss) ->
        (loc, e_opt, generate_ail_stat_strs ~with_newline:true (bs, ss)))
      return_injs
  in
  let return_ownership_stmts =
    List.map
      (fun (loc, e_opt, strs) -> (loc, e_opt, [ String.concat "\n" strs ]))
      return_ownership_stmts
  in
  ( [ (instrumentation.fn, (pre_str, post_str)) ],
    in_stmt @ block_ownership_stmts,
    return_ownership_stmts )


let generate_c_assume_pres_internal
  (instrumentation_list : Executable_spec_extract.instrumentation list)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  =
  let aux (inst : Executable_spec_extract.instrumentation) =
    let dts = sigma.cn_datatypes in
    let preds = prog5.resource_predicates in
    let args =
      match List.assoc Sym.equal inst.fn sigma.declarations with
      | _, _, Decl_function (_, _, args, _, _, _) ->
        let arg_names = AT.get_computational (Option.get inst.internal) in
        let arg_cts = List.map (fun (_, ct, _) -> ct) args in
        List.map (fun ((x, bt), ct) -> (x, (bt, ct))) (List.combine arg_names arg_cts)
      | _ -> failwith ("unreachable @ " ^ __LOC__)
    in
    let globals = extract_global_variables prog5.globs in
    Cn_to_ail.cn_to_ail_assume_pre
      dts
      inst.fn
      args
      globals
      preds
      (AT.get_lat (Option.get inst.internal))
  in
  instrumentation_list
  |> List.filter (fun (inst : Executable_spec_extract.instrumentation) ->
    Option.is_some inst.internal)
  |> List.map aux


let generate_c_specs_internal
  without_ownership_checking
  instrumentation_list
  (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
  (prog5 : unit Mucore.file)
  : executable_spec
  =
  let generate_c_spec (instrumentation : Executable_spec_extract.instrumentation) =
    generate_c_pres_and_posts_internal
      without_ownership_checking
      instrumentation
      sigm
      prog5
  in
  let specs = List.map generate_c_spec instrumentation_list in
  let pre_post, in_stmt, returns = Executable_spec_utils.list_split_three specs in
  let returns =
    List.map (fun (l, e_opt, strs) -> (l, (e_opt, strs))) (List.concat returns)
  in
  { pre_post = List.concat pre_post; in_stmt = List.concat in_stmt; returns }


let generate_doc_from_ail_struct ail_struct =
  CF.Pp_ail.(
    with_executable_spec (fun () -> pp_tag_definition ail_struct ^^ PPrint.hardline) ())


let generate_struct_decl_str (tag, (_, _, def)) =
  match def with
  | C.StructDef _ -> Printf.sprintf "struct %s;\n" (Sym.pp_string tag)
  | UnionDef _ -> ""


let generate_c_records ail_structs =
  let struct_docs = List.map generate_doc_from_ail_struct ail_structs in
  doc_to_pretty_string (PPrint.concat struct_docs)


let generate_str_from_ail_struct ail_struct =
  doc_to_pretty_string (generate_doc_from_ail_struct ail_struct)


let generate_str_from_ail_structs ail_structs =
  let docs = List.map generate_doc_from_ail_struct ail_structs in
  doc_to_pretty_string (Executable_spec_utils.concat_map_newline docs)


let generate_c_datatypes (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) =
  let ail_datatypes =
    match sigm.cn_datatypes with
    | [] -> []
    | d :: ds ->
      let ail_dt1 = Cn_to_ail.cn_to_ail_datatype ~first:true d in
      let ail_dts = List.map Cn_to_ail.cn_to_ail_datatype ds in
      ail_dt1 :: ail_dts
  in
  let locs_and_struct_strs =
    List.map
      (fun (loc, structs) ->
        let doc =
          Executable_spec_utils.concat_map_newline
            (List.map generate_doc_from_ail_struct structs)
        in
        (loc, doc_to_pretty_string doc))
      ail_datatypes
  in
  locs_and_struct_strs


let generate_c_struct_strs c_structs =
  "\n/* ORIGINAL C STRUCTS */\n\n" ^ generate_str_from_ail_structs c_structs


let generate_cn_versions_of_structs c_structs =
  let ail_structs = List.concat (List.map Cn_to_ail.cn_to_ail_struct c_structs) in
  "\n/* CN VERSIONS OF C STRUCTS */\n\n" ^ generate_str_from_ail_structs ail_structs


let generate_fun_def_and_decl_docs funs =
  let decls, defs = List.split funs in
  let defs_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma =
    { A.empty_sigma with declarations = decls; function_definitions = defs }
  in
  let decls_prog : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma =
    { A.empty_sigma with declarations = decls; function_definitions = [] }
  in
  let pp_program_with_exec_spec prog =
    CF.Pp_ail.(
      with_executable_spec (fun () -> pp_program ~show_include:true (None, prog)) ())
  in
  let defs_doc = pp_program_with_exec_spec defs_prog in
  let decls_doc = pp_program_with_exec_spec decls_prog in
  (defs_doc, decls_doc)


let generate_c_functions
  (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
  (logical_predicates : (Sym.t * Definition.Function.t) list)
  =
  let ail_funs_and_records =
    List.map
      (fun cn_f -> Cn_to_ail.cn_to_ail_function cn_f sigm.cn_datatypes sigm.cn_functions)
      logical_predicates
  in
  let ail_funs, _ = List.split ail_funs_and_records in
  let locs_and_decls, defs = List.split ail_funs in
  let locs, decls = List.split locs_and_decls in
  let defs = List.filter_map Fun.id defs in
  let decl_str_comment = "\n/* CN FUNCTIONS */\n\n" in
  let defs_doc, decls_doc = generate_fun_def_and_decl_docs (List.combine decls defs) in
  (doc_to_pretty_string defs_doc, decl_str_comment ^ doc_to_pretty_string decls_doc, locs)


let rec remove_duplicates eq_fun = function
  | [] -> []
  | t :: ts ->
    if List.mem eq_fun t ts then
      remove_duplicates eq_fun ts
    else
      t :: remove_duplicates eq_fun ts


let generate_c_predicates
  (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
  (resource_predicates : (Sym.t * Definition.Predicate.t) list)
  =
  let ail_funs, _ =
    Cn_to_ail.cn_to_ail_predicates
      resource_predicates
      sigm.cn_datatypes
      []
      sigm.cn_predicates
  in
  let locs_and_decls, defs = List.split ail_funs in
  let locs, decls = List.split locs_and_decls in
  let defs_doc, decls_doc = generate_fun_def_and_decl_docs (List.combine decls defs) in
  ( "\n/* CN PREDICATES */\n\n" ^ doc_to_pretty_string defs_doc,
    doc_to_pretty_string decls_doc,
    locs )


let generate_ownership_functions without_ownership_checking ownership_ctypes =
  let rec remove_duplicates ret_list = function
    | [] -> []
    | x :: xs ->
      if List.mem execCtypeEqual x ret_list then
        remove_duplicates (x :: ret_list) xs
      else
        x :: remove_duplicates (x :: ret_list) xs
  in
  let ctypes = remove_duplicates [] ownership_ctypes in
  let ail_funs =
    List.map
      (fun ctype ->
        Cn_to_ail.generate_get_or_put_ownership_function ~without_ownership_checking ctype)
      ctypes
  in
  let defs_doc, decls_doc = generate_fun_def_and_decl_docs ail_funs in
  let comment = "\n/* OWNERSHIP FUNCTIONS */\n\n" in
  (comment ^ doc_to_pretty_string defs_doc, doc_to_pretty_string decls_doc)


let generate_conversion_and_equality_functions
  (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
  =
  let struct_conversion_funs =
    List.map Cn_to_ail.generate_struct_conversion_to_function sigm.tag_definitions
    @ List.map Cn_to_ail.generate_struct_conversion_from_function sigm.tag_definitions
  in
  let struct_equality_funs =
    List.map Cn_to_ail.generate_struct_equality_function sigm.tag_definitions
  in
  let datatype_equality_funs =
    List.map Cn_to_ail.generate_datatype_equality_function sigm.cn_datatypes
  in
  let struct_map_get_funs =
    List.map Cn_to_ail.generate_struct_map_get sigm.tag_definitions
  in
  let struct_default_funs =
    List.map Cn_to_ail.generate_struct_default_function sigm.tag_definitions
  in
  let datatype_map_get_funs =
    List.map Cn_to_ail.generate_datatype_map_get sigm.cn_datatypes
  in
  let datatype_default_funs =
    List.map Cn_to_ail.generate_datatype_default_function sigm.cn_datatypes
  in
  let ail_funs =
    List.fold_left
      ( @ )
      []
      (List.map
         List.concat
         [ struct_conversion_funs;
           struct_equality_funs;
           datatype_equality_funs;
           struct_map_get_funs;
           struct_default_funs;
           datatype_map_get_funs;
           datatype_default_funs
         ])
  in
  let defs_doc, decls_doc = generate_fun_def_and_decl_docs ail_funs in
  let comment = "\n/* GENERATED STRUCT FUNCTIONS */\n\n" in
  (comment ^ doc_to_pretty_string defs_doc, comment ^ doc_to_pretty_string decls_doc)


let get_main (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) =
  List.filter
    (fun (fn_sym, _) -> String.equal "main" (Sym.pp_string fn_sym))
    sigm.function_definitions


let has_main (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) =
  List.non_empty (get_main sigm)


let generate_ownership_global_assignments
  (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
  (prog5 : unit Mucore.file)
  =
  match get_main sigm with
  | [] -> failwith "CN-exec: No main function so ownership globals cannot be initialised"
  | (main_sym, _) :: _ ->
    let globals = extract_global_variables prog5.globs in
    let global_map_fcalls =
      List.map Ownership_exec.generate_c_local_ownership_entry_fcall globals
    in
    let global_map_stmts_ = List.map (fun e -> A.AilSexpr e) global_map_fcalls in
    let assignments = Ownership_exec.get_ownership_global_init_stats () in
    let init_and_global_mapping_str =
      generate_ail_stat_strs ([], assignments @ global_map_stmts_)
    in
    let global_unmapping_stmts_ =
      List.map Ownership_exec.generate_c_local_ownership_exit globals
    in
    let global_unmapping_str = generate_ail_stat_strs ([], global_unmapping_stmts_) in
    [ (main_sym, (init_and_global_mapping_str, global_unmapping_str)) ]
