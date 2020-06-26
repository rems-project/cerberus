open Cmdliner
open Extra

type config =
  { output_dir    : string option
  ; gen_code      : bool
  ; gen_spec      : bool
  ; no_proof      : string list
  ; full_paths    : bool
  ; imports       : (string * string) list
  ; spec_ctxt     : string list
  ; cpp_I         : string list
  ; cpp_nostd     : bool
  ; cpp_output    : bool
  ; no_expr_loc   : bool
  ; no_stmt_loc   : bool
  ; warn_lifetime : bool }

(* Main entry point. *)
let run : config -> string -> unit = fun cfg c_file ->
  (* Set the printing flags. *)
  if cfg.no_expr_loc then Coq_pp.print_expr_locs := false;
  if cfg.no_stmt_loc then Coq_pp.print_stmt_locs := false;
  (* Get an absolute path to the file, for better error reporting. *)
  let full_c_file =
    try Filename.realpath c_file with Invalid_argument(_) ->
      Panic.panic_no_pos "File [%s] disappeared..." c_file
  in
  let c_file = if cfg.full_paths then full_c_file else c_file in
  (* Compute the path to the output files. *)
  let output_dir =
    match cfg.output_dir with
    | Some(dir) -> dir
    | None      -> Filename.dirname full_c_file
  in
  let base_name =
    let name = Filename.basename c_file in
    try Filename.chop_extension name with Invalid_argument(_) -> name
  in
  let outfile suffix = Filename.concat output_dir (base_name ^ suffix) in
  let cppc_file = outfile ".cpp.c" in
  let code_file = outfile "_code.v" in
  let spec_file = outfile "_spec.v" in
  let fprf_file name = outfile ("_proof_" ^ name ^ ".v") in
  (* Compute the import path (for the generated Coq files). *)
  let path =
    let path = List.tl (String.split_on_char '/' output_dir) in
    let rec build_path path =
      match path with
      | "theories" :: path -> "refinedc" :: path
      | _          :: path -> build_path path
      | []                 ->
      Panic.wrn None "A precise Coq import path cannot be derived form the \
        given C source file.\nDefaulting to [refinedc]."; ["refinedc"]
    in
    String.concat "." (build_path path)
  in
  (* Print the output of the preprocessor if necessary. *)
  let src_lines = Cerb_wrapper.cpp_lines cfg.cpp_I cfg.cpp_nostd c_file in
  if cfg.cpp_output then
    begin
      let oc = open_out cppc_file in
      output_lines oc src_lines; close_out oc
    end;
  (* Do the translation from C to Ail, and then to our AST (if necessary). *)
  if cfg.warn_lifetime || cfg.gen_code || cfg.gen_spec then
  let ail_ast = Cerb_wrapper.c_file_to_ail cfg.cpp_I cfg.cpp_nostd c_file in
  if cfg.warn_lifetime then Warn.warn_file ail_ast;
  let coq_ast = Ail_to_coq.translate c_file ail_ast in
  (* Generate the code, if necessary. *)
  if cfg.gen_code then
    Coq_pp.(write (Code(cfg.imports)) code_file coq_ast);
  (* Generate the spec, if necessary. *)
  if cfg.gen_spec then
    Coq_pp.(write (Spec(path, cfg.imports, cfg.spec_ctxt)) spec_file coq_ast);
  (* Generate the proof for each function, if necessary. *)
  let write_proof (id, def_or_decl) =
    let open Coq_ast in
    let open Coq_pp in
    match def_or_decl with
    | FDec(_)   -> ()
    | FDef(def) ->
    let proof_kind =
      if List.mem id cfg.no_proof then Rc_annot.Proof_trusted
      else Coq_ast.proof_kind def
    in
    let mode = Fprf(path, def, cfg.imports, cfg.spec_ctxt, proof_kind) in
    write mode (fprf_file id) coq_ast
  in
  if cfg.gen_spec then List.iter write_proof coq_ast.functions

let output_dir =
  let doc =
    "Directory in which generated files are placed. By default, output files \
     are placed in the same directory as the input file $(i,FILE)."
  in
  Arg.(value & opt (some dir) None & info ["output-dir"] ~docv:"DIR" ~doc)

let no_code =
  let doc =
    "Do not generate the Coq file that corresponds to the $(i,code) of the \
     functions defined in $(i,FILE)."
  in
  Arg.(value & flag & info ["no-code"] ~doc)

let no_spec =
  let doc =
    "Do not generate the Coq file that corresponds to the $(i,spec) of the \
     functions defined in $(i,FILE)."
  in
  Arg.(value & flag & info ["no-spec"] ~doc)

let no_proof =
  let doc =
    "Do not generate the Coq file that corresponds to the typing proof for \
     function $(docv) defined in $(i,FILE). If there is no function with the 
     given name then nothing happens."
  in
  Arg.(value & opt_all string [] & info ["no-proof"] ~docv:"NAME" ~doc)

let full_paths =
  let doc =
    "Use full, absolute file paths in generated files."
  in
  Arg.(value & flag & info ["full-paths"] ~doc)

let imports =
  let doc =
    "Specifies a module to import at the beginning of every generated Coq \
     source file. The argument $(docv) will lead to the following commant \
     being generated: \
     \"$(b,From) $(i,FROM) $(b,Require Import) $(i,MOD)$(b,.)\""
  in
  let i = Arg.(info ["import"] ~docv:"FROM:MOD" ~doc) in
  Arg.(value & opt_all (pair ~sep:':' string string) [] & i)

let spec_ctxt =
  let doc =
    "Specifies a Coq vernacular command to insert at the beginning of the \
     section generated for specification file. The can typically used with \
     an argument of the form $(b,\"Context \\\\`{!lockG Sigma}\")."
  in
  let i = Arg.(info ["spec-context"] ~docv:"CMD" ~doc) in
  Arg.(value & opt_all string [] & i)

let cpp_I =
  let doc =
    "Add the directory $(docv) to the list of directories to be searched for \
     header files during preprocessing."
  in
  let i = Arg.(info ["I"] ~docv:"DIR" ~doc) in
  Arg.(value & opt_all dir [] & i)

let cpp_nostd =
  let doc =
    "Do not search the standard system directories for header files. Only \
     the directories explicitly specified with $(b,-I) options are searched."
  in
  Arg.(value & flag & info ["nostdinc"] ~doc)

let cpp_output =
  let doc =
    "Write the output of the preprocessor to a file with '.cpp.c' extension."
  in
  Arg.(value & flag & info ["cpp-output"] ~doc)

let no_expr_loc =
  let doc =
    "Do not output location information for expressions in the generated \
     Coq files."
  in
  Arg.(value & flag & info ["no-expr-loc"] ~doc)

let no_stmt_loc =
  let doc =
    "Do not output location information for statements in the generated \
     Coq files."
  in
  Arg.(value & flag & info ["no-stmt-loc"] ~doc)

let warn_lifetime =
  let doc =
    "Give a warning if a value escapes its lifetime."
  in
  Arg.(value & flag & info ["warn-lifetime"] ~doc)

let no_loc =
  let doc =
    "Do not output any location information in the generated Coq files. This \
     flag subsumes both $(b,--no-expr-loc) and $(b,--no-stmt-loc)."
  in
  Arg.(value & flag & info ["no-loc"] ~doc)

let opts : config Term.t =
  let build output_dir no_code no_spec no_proof full_paths imports spec_ctxt
      cpp_I cpp_nostd cpp_output no_expr_loc no_stmt_loc no_loc
      warn_lifetime =
    let no_expr_loc = no_expr_loc || no_loc in
    let no_stmt_loc = no_stmt_loc || no_loc in
    { output_dir ; gen_code = not no_code ; gen_spec = not no_spec
    ; no_proof ; full_paths ; imports ; spec_ctxt ; cpp_I ; cpp_nostd
    ; cpp_output ; no_stmt_loc ; no_expr_loc ; warn_lifetime }
  in
  Term.(pure build $ output_dir $ no_code $ no_spec $ no_proof $ full_paths $
          imports $ spec_ctxt $ cpp_I $ cpp_nostd $ cpp_output $
          no_expr_loc $ no_stmt_loc $ no_loc $ warn_lifetime)

let c_file =
  let doc = "C language source file." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let _ =
  let open Term in
  let term = pure run $ opts $ c_file in
  let doc = "Generator form C to the RefinedC type system (in Coq)." in
  let version = Cerb_frontend.Version.version in (* FIXME use our own? *)
  exit @@ eval (term, info ~version ~doc "ail_to_coq")
