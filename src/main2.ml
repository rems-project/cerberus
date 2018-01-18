open Prelude
open Pipeline

open Smt2




(* == Symbol counter for the Core parser ======================================================== *)
let core_sym_counter = ref 0


let cerb_path =
    try
      Sys.getenv "CERB_PATH"
    with Not_found ->
      error "expecting the environment variable CERB_PATH set to point to the location cerberus."

let corelib_path =
  Filename.concat cerb_path "include/core"


type std_setting =
  | StdISO
  | StdDefacto

type cerb_opts = {
  pipeline_conf: Pipeline.configuration;
  
}

(*
type cerb_opts = {
  args: string list;
  cpp_cmd: string;
  macros: (string * string option) list;
  dirs: string list;
  std: std_setting;
  mem: Ocaml_mem.mem_setting;
  debug: int;
  batch: bool;
  exec: bool;
  pps: language list;
  asts: language list;
  ppflags: pp_flag list;
  rewrite: bool;
  sequentialise: bool;
  ocaml: bool;
  ocaml_corestd: bool;
  concurrency: bool;
}
*)

let cerb_opts args cpp_cmd macros dirs std mem debug batch exec pps asts
              ppflags rewrite sequentialise ocaml ocaml_corestd
              concurrency =
  Ocaml_mem.switch := mem;
  (* TODO: std *)
  (* TODO: set debug level *)
  { { debug_level= debug
    ; pprints= pps
    ; astprints= asts
    ; ppflags= ppflags
    ; typecheck_core= failwith "TODO: remove"
    ; rewrite_core= rewrite
    ; sequentialise_core= sequentialise
    ; cpp_cmd= cpp_cmd ^ "SOMETHING macros, dirs"
    ; core_stdlib= failwith ""
    ; core_impl= failwith "" }
  , args
  , batch
  , exec
  , ocaml
  , ocaml_corestd
  , concurrency }

(*
  { args; cpp_cmd; macros; dirs; std; mem; debug; batch; exec; pps; asts;
    ppflags; rewrite; sequentialise; ocaml; ocaml_corestd; concurrency; }
*)




(* BEGIN TMP MLM DEBUG *)
let mlm_dbg_oc =
  open_out (Unix.getenv "HOME" ^ "/.cerb")
(* END TMP MLM DEBUG *)

let io = let open Pipeline in {
  pass_message = begin
    let ref = ref 0 in
    fun str -> Debug_ocaml.print_success (string_of_int !ref ^ ". " ^ str);
               incr ref;
               Exception.except_return ()
  end;
  set_progress = begin
    fun str -> output_string mlm_dbg_oc (str ^ "  ");
               Exception.except_return ()
  end;
  run_pp = begin
    fun opts doc -> Pipeline.run_pp opts doc;
                    Exception.except_return ()
  end;
  print_endline = begin
    fun str -> print_endline str;
               Exception.except_return ();
  end;
  print_debug = begin
    fun n mk_str -> Debug_ocaml.print_debug n [] mk_str;
                    Exception.except_return ()
  end;
  warn = begin
    fun mk_str -> Debug_ocaml.warn [] mk_str;
                  Exception.except_return ()
  end;
}





let cerberus cerb_opts =
  Debug_ocaml.debug_level := cerb_opts.debug; (* TODO: do something cleaner *)
  Random.self_init ();
  
  (* Looking for and parsing the core standard library *)
  let core_stdlib = Pipeline.load_core_stdlib () in
  Debug_ocaml.print_success "0.1. - Core standard library loaded.";
































open Cmdliner

let macro_pair =
  let parser str =
    match String.index_opt str '=' with
      | None ->
          Result.Ok (str, None)
      | Some i ->
          let macro = String.sub str 0 i in
          let value = String.sub str (i+1) (String.length str - i - 1) in
          let is_digit n = 48 <= n && n <= 57 in
          if i = 0 || is_digit (Char.code (String.get macro 0)) then
            Result.Error (`Msg "macro name must be a C identifier")
          else
            Result.Ok (macro, Some value) in
  let printer ppf = function
    | (m, None)   -> Format.pp_print_string ppf m
    | (m, Some v) -> Format.fprintf ppf "%s=%s" m v in
  Arg.(conv (parser, printer))




let args =
  let doc = "List of arguments for the C program" in
  Arg.(value & opt (list string) [] & info ["args"] ~docv:"ARG1,..." ~doc)

let batch =
  let doc = "makes the execution driver produce batch friendly output" in
  Arg.(value & flag & info["batch"] ~doc)

let concurrency =
  let doc = "Activate the C11 concurrency" in
  Arg.(value & flag & info["concurrency"] ~doc)

let cpp_cmd =
  let doc = "Command to call for the C preprocessing." in
  Arg.(value & opt string (
       "cc -E -C -traditional-cpp -nostdinc -undef -D__cerb__ -I " ^
       cerb_path ^ "/include/c/libc -I "  ^ cerb_path ^ "/include/c/posix")
             & info ["cpp"] ~docv:"CMD" ~doc)

let debug =
  let doc = "Set the debug message level to $(docv) (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let exec =
  let doc = "Execute the Core program after the elaboration." in
  Arg.(value & flag & info ["exec"] ~doc)

let ocaml =
  let doc = "Ocaml backend." in
  Arg.(value & flag & info ["ocaml"] ~doc)

let ocaml_corestd =
  let doc = "Generate coreStd.ml" in
  Arg.(value & flag & info ["ocaml-corestd"] ~doc)

let pprints =
  let doc = "Pretty print the intermediate programs for the listed languages (ranging over {cabs, ail, core})." in
  Arg.(value & opt (list (enum ["cabs", Cabs; "ail", Ail; "core", Core])) [] & info ["pp"] ~docv:"LANG1,..." ~doc)

let asts =
  let doc = "Print the AST of the intermediate programs for the listed languages (ranging over {cabs, ail, core})." in
  Arg.(value & opt (list (enum ["cabs", Cabs; "ail", Ail; "core", Core])) [] & info ["ast"] ~docv:"LANG1,..." ~doc)

let ppflags =
  let doc = "Pretty print flags [annot: include location and ISO annotations, fout: output in a file]." in
  Arg.(value & opt (list (enum ["annot", Annot; "fout", FOut])) [] & info ["pp_flags"] ~doc)

let rewrite =
  let doc = "Activate the Core to Core transformations" in
  Arg.(value & flag & info["rewrite"] ~doc)

let sequentialise =
  let doc = "Replace all unseq() with left to right wseq(s)" in
  Arg.(value & flag & info["sequentialise"] ~doc)

let define_macros =
  let doc = "Tells the C preprocessor to predefine a macro, with \
             definition 1 if no VALUE is given" in
  Arg.(value & opt_all macro_pair [] & info ["D"; "define-macro"]
         ~docv:"NAME[=VALUE]" ~doc)

let include_dirs =
  let doc = "Add a directory to the include search path" in
  Arg.(value & opt_all dir [] & info ["I"; "include-directory"]
         ~docv:"DIR" ~doc)

let std =
  let doc = "Sets the language standard to follow (`iso' or `defacto')" in
  Arg.(value & opt (enum [("iso", StdISO); ("defacto", StdDefacto)]) StdDefacto
             & info ["std"] ~doc)

let mem =
  let doc = "Sets the memory model (`concrete' or `defacto')" in
  Arg.(value & opt (enum [("concrete", `MemConcrete); ("defacto", `MemDefacto)]) `MemDefacto
             & info ["mem"] ~doc)


(* module Core_run = Core_run.Make(Concrete) *)

let cerb_opts_t =
  Term.(const cerb_opts $ args $ cpp_cmd $ define_macros $ include_dirs $ std
                        $ mem $ debug $ batch $ exec $ pprints $ asts $ ppflags
                        $ rewrite $ sequentialise $ ocaml $ ocaml_corestd
                        $ concurrency)

let cerberus_t =
  Term.(const cerberus $ cerb_opts_t)

(* entry point *)
let () =
  Term.exit @@ Term.eval (cerberus_t, Term.info "cerberus")
