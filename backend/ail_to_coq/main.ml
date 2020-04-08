open Cmdliner
open Extra

type config =
  { output_dir : string option
  ; gen_code   : bool
  ; gen_spec   : bool
  ; full_paths : bool
  ; imports    : (string * string) list
  ; spec_ctxt  : string list }

(* Main entry point. *)
let run : config -> string -> unit = fun cfg c_file ->
  (* Get an absolute path to the file, for better error reporting. *)
  let c_file =
    if cfg.full_paths then
      try Filename.realpath c_file with Invalid_argument(_) ->
        Panic.panic_no_pos "File [%s] disappeared..." c_file
    else c_file
  in
  (* Do the translation from C to Ail, and then to our AST. *)
  let ail_ast = Cerb_wrapper.c_file_to_ail c_file in
  let coq_ast = Ail_to_coq.translate c_file ail_ast in
  (* Compute the path to the output files. *)
  let output_dir =
    match cfg.output_dir with
    | Some(dir) -> dir
    | None      -> Filename.dirname c_file
  in
  let base_name =
    let name = Filename.basename c_file in
    try Filename.chop_extension name with Invalid_argument(_) -> name
  in
  let code_file = Filename.concat output_dir (base_name ^ "_code.v") in
  let spec_file = Filename.concat output_dir (base_name ^ "_spec.v") in
  (* Print the code, if necessary. *)
  if cfg.gen_code then
    Coq_pp.(write (Code(cfg.imports)) code_file coq_ast);
  (* Print the spec, if necessary. *)
  if cfg.gen_spec then
    Coq_pp.(write (Spec(cfg.imports, cfg.spec_ctxt)) spec_file coq_ast)

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

let opts : config Term.t =
  let build output_dir no_code no_spec full_paths imports spec_ctxt =
    { output_dir ; gen_code = not no_code ; gen_spec = not no_spec
    ; full_paths ; imports ; spec_ctxt }
  in
  Term.(pure build $ output_dir $ no_code $ no_spec $ full_paths $
          imports $ spec_ctxt)

let c_file =
  let doc = "C language source file." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let _ =
  let open Term in
  let term = pure run $ opts $ c_file in
  let doc = "Generator form C to the RefinedC type system (in Coq)." in
  let version = Cerb_frontend.Version.version in (* FIXME use our own? *)
  exit @@ eval (term, info ~version ~doc "ail_to_coq")
