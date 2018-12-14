open Global_ocaml
open Pipeline

(* BEGIN TMP MLM DEBUG *)
let mlm_dbg_oc =
  open_out (Unix.getenv "HOME" ^ "/.cerb")
(* END TMP MLM DEBUG *)

let (>>=) = Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = Exception.except_return

let io, get_progress =
  let open Pipeline in
  let progress = ref 0 in
  { pass_message = begin
        let ref = ref 0 in
        fun str -> Debug_ocaml.print_success (string_of_int !ref ^ ". " ^ str);
                   incr ref;
                   return ()
      end;
    set_progress = begin
      fun str -> output_string mlm_dbg_oc (str ^ "  ");
                 incr progress;
                 return ()
      end;
    run_pp = begin
      fun opts doc -> run_pp opts doc;
                      return ()
      end;
    print_endline = begin
      fun str -> print_endline str;
                 return ();
      end;
    print_debug = begin
      fun n mk_str -> Debug_ocaml.print_debug n [] mk_str;
                      return ()
      end;
    warn = begin
      fun mk_str -> Debug_ocaml.warn [] mk_str;
                    return ()
      end;
  }, fun () -> !progress

let frontend conf filename core_std =
  if not (Sys.file_exists filename) then
    error ("The file `" ^ filename ^ "' doesn't exist.");
  if Filename.check_suffix filename ".co" then
    return @@ read_core_object filename
  else
    begin
      if Filename.check_suffix filename ".c" then
        c_frontend conf core_std filename >>= fun (_, _, core_file) ->
        return core_file
      else if Filename.check_suffix filename ".core" then
        core_frontend conf core_std ~filename
      else
        Exception.fail (Location_ocaml.unknown, Errors.UNSUPPORTED
                          "The file extention is not supported")
    end >>= core_passes conf ~filename >>= fun (core_file, _) ->
    return core_file

let cerberus debug_level progress core_obj
             cpp_cmd macros incl impl_name
             exec exec_mode switches batch experimental_unseq concurrency
             astprints pprints ppflags
             sequentialise_core rewrite_core typecheck_core defacto
             fs_dump fs
             ocaml ocaml_corestd
             files args =
  Debug_ocaml.debug_level := debug_level;
  let cpp_cmd =
    String.concat " " begin
      cpp_cmd ::
      List.map (function
          | (str1, None)      -> "-D" ^ str1
          | (str1, Some str2) -> "-D" ^ str1 ^ "=" ^ str2
        ) macros @
      List.map (fun str -> "-I " ^ str) incl
    end
  in
  (* set global configuration *)
  set_cerb_conf exec exec_mode concurrency QuoteStd defacto;
  let conf = { astprints; pprints; ppflags; debug_level; typecheck_core;
               rewrite_core; sequentialise_core; cpp_cmd; } in
  let prelude =
    (* Looking for and parsing the core standard library *)
    Switches.set switches;
    load_core_stdlib () >>= fun core_stdlib ->
    io.pass_message "Core standard library loaded." >>
    (* Looking for and parsing the implementation file *)
    load_core_impl core_stdlib impl_name >>= fun core_impl ->
    io.pass_message "Implementation file loaded." >>
    return (core_stdlib, core_impl)
  in
  let epilogue n =
    if batch = `Batch then
      Printf.fprintf stderr "Time spent: %f seconds\n" (Sys.time ());
    output_string mlm_dbg_oc "\n";
    close_out mlm_dbg_oc;
    if progress then get_progress ()
    else n
  in
  let runM = function
    | Exception.Exception err ->
        prerr_endline (Pp_errors.to_string err);
        epilogue 1
    | Exception.Result (Either.Left execs) ->
        List.iter print_string execs;
        epilogue 0
    | Exception.Result (Either.Right n) ->
        epilogue n
  in
  runM @@ match files with
    | [] ->
      if ocaml_corestd then
        error "TODO: ocaml_corestd"
      else
        Pp_errors.fatal "no input file"
    | files ->
      prelude >>= fun core_std ->
      Exception.foldlM (fun core_files file ->
          frontend (conf, io) file core_std >>= fun core_file ->
          return (core_file::core_files)) [] files
      >>= fun core_files ->
      let core_file = Core_aux.link core_files in
      Tags.set_tagDefs core_file.tagDefs;
      if ocaml then
        error "TODO: ocaml_backend"
      else if exec then
        let open Exhaustive_driver in
        let driver_conf = {concurrency; experimental_unseq; exec_mode; fs_dump;} in
        interp_backend io core_file ~args ~batch ~fs ~driver_conf
      else if core_obj then
        let core_obj_name =
          String.concat "_" (List.map Filename.remove_extension files) ^ ".co"
        in
        let () = write_core_object core_file core_obj_name in
        return @@ Either.Right 0
      else
        return @@ Either.Right 0

(* CLI stuff *)
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

let debug_level =
  let doc = "Set the debug message level to $(docv) (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let ocaml =
  let doc = "Ocaml backend." in
  Arg.(value & flag & info ["ocaml"] ~doc)

let ocaml_corestd =
  let doc = "Generate coreStd.ml" in
  Arg.(value & flag & info ["ocaml-corestd"] ~doc)

let impl =
  let doc = "Set the C implementation file (to be found in CERB_COREPATH/impls\
             and excluding the .impl suffix)." in
  Arg.(value & opt string "gcc_4.9.0_x86_64-apple-darwin10.8.0" & info ["impl"]
         ~docv:"NAME" ~doc)

let core_obj =
  let doc = "Run frontend generating a target '.co' core object file." in
  Arg.(value & flag & info ["c"] ~doc)

let cpp_cmd =
  let doc = "Command to call for the C preprocessing." in
  Arg.(value & opt string ("cc -E -C -nostdinc -undef -D__cerb__ -I " ^ cerb_path
                           ^ "/include/c/libc -I " ^ cerb_path ^ "/include/c/posix")
             & info ["cpp"] ~docv:"CMD" ~doc)

let incl =
  let doc = "Add the specified directory to the search path for the\
             C preprocessor." in
  Arg.(value & opt_all dir [] & info ["I"; "include-directory"]
         ~docv:"DIR" ~doc)

let macros =
  let doc = "Adds  an  implicit  #define  into the predefines buffer which is \
             read before the source file is preprocessed." in
  Arg.(value & opt_all macro_pair [] & info ["D"; "define-macro"]
         ~docv:"NAME[=VALUE]" ~doc)

let exec =
  let doc = "Execute the Core program after the elaboration." in
  Arg.(value & flag & info ["exec"] ~doc)

let exec_mode =
  let doc = "Set the Core evaluation mode (interactive | exhaustive | random)." in
  Arg.(value & opt (enum ["exhaustive", Smt2.Exhaustive; "random", Smt2.Random])
         Smt2.Random & info ["mode"] ~docv:"MODE" ~doc)

let pprints =
  let open Pipeline in
  let doc = "Pretty print the intermediate programs for the listed languages\
             (ranging over {cabs, ail, core})." in
  Arg.(value & opt (list (enum ["ail", Ail; "core", Core])) [] &
       info ["pp"] ~docv:"LANG1,..." ~doc)

let astprints =
  let open Pipeline in
  let doc = "Pretty print the intermediate syntax tree for the listed languages\
             (ranging over {cabs, ail, core})." in
  Arg.(value & opt (list (enum ["cabs", Cabs; "ail", Ail])) [] &
       info ["ast"] ~docv:"LANG1,..." ~doc)


let fs =
  let doc = "Initialise the internal file system with the contents of the\
             directory DIR" in
  Arg.(value & opt string "" & info ["fs"] ~docv:"DIR" ~doc)

let ppflags =
  let open Pipeline in
  let doc = "Pretty print flags [annot: include location and ISO annotations,\
             fout: output in a file]." in
  Arg.(value & opt (list (enum ["annot", Annot; "fout", FOut])) [] &
       info ["pp_flags"] ~doc)

let files =
  let doc = "source C or Core file" in
  Arg.(value & pos_all string [] & info [] ~docv:"FILE" ~doc)

let progress =
  let doc = "Progress mode: the return code indicate how far the source program\
             went through the pipeline \
             [1 = total failure, 10 = parsed, 11 = desugared, 12 = typed,\
             13 = elaborated, 14 = executed]" in
  Arg.(value & flag & info ["progress"] ~doc)

let rewrite =
  let doc = "Activate the Core to Core transformations" in
  Arg.(value & flag & info["rewrite"] ~doc)

let sequentialise =
  let doc = "Replace all unseq() with left to right wseq(s)" in
  Arg.(value & flag & info["sequentialise"] ~doc)

(* TODO: is this flag being used? *)
let concurrency =
  let doc = "Activate the C11 concurrency" in
  Arg.(value & flag & info["concurrency"] ~doc)

(* TODO: this is not being used
let preEx =
  let doc = "only generate and output the concurrency pre-execution (activates the C11 concurrency)" in
  Arg.(value & flag & info["preEx"] ~doc)
*)

let batch =
  let doc = "makes the execution driver produce batch friendly output" in
  Arg.(value & vflag `NotBatch & [(`Batch, info["batch"] ~doc);
                                  (`CharonBatch, info["charon-batch"]
                                     ~doc:(doc^" (for Charon)"))])

let experimental_unseq =
  let doc = "use a new (experimental) semantics for unseq() in Core_run" in
  Arg.(value & flag & info["experimental-unseq"] ~doc)

let typecheck_core =
  let doc = "typecheck the elaborated Core program" in
  Arg.(value & flag & info["typecheck-core"] ~doc)

let defacto =
  let doc = "relax some of the ISO constraints (outside of the memory)" in
  Arg.(value & flag & info["defacto"] ~doc)

let fs_dump =
  let doc = "dump the file system at the end of the execution" in
  Arg.(value & flag & info["fs-dump"] ~doc)

(* TODO: this is not being used
let default_impl =
  let doc = "run cerberus with a default implementation choice" in
  Arg.(value & flag & info["defacto_impl"] ~doc)
*)

(* TODO: this is not being used
let action_graph =
  let doc = "create a (dot) graph with all the possible executions" in
  Arg.(value & flag & info["graph"] ~doc)
*)

let switches =
  let doc = "list of semantics switches to turn on (see documentation for the list)" in
  Arg.(value & opt (list string) [] & info ["switches"] ~docv:"SWITCH1,..." ~doc)

(* TODO: this is not being used
let concurrency_tests =
  let doc = "Runs the concurrency regression tests" in
  Arg.(value & flag & info["regression-test"] ~doc)
*)

let args =
  let doc = "List of arguments for the C program" in
  Arg.(value & opt (list string) [] & info ["args"] ~docv:"ARG1,..." ~doc)

(* entry point *)
let () =
  let cerberus_t = Term.(pure cerberus $ debug_level $ progress $ core_obj $
                         cpp_cmd $ macros $ incl $ impl $
                         exec $ exec_mode $ switches $ batch $
                         experimental_unseq $ concurrency $
                         astprints $ pprints $ ppflags $
                         sequentialise $ rewrite $ typecheck_core $ defacto $
                         fs_dump $ fs $
                         ocaml $ ocaml_corestd $
                         files $ args) in
  (* the version is "sed-out" by the Makefile *)
  let info = Term.info "cerberus" ~version:"<<GIT-HEAD>>" ~doc:"Cerberus C semantics"  in
  Term.exit @@ Term.eval (cerberus_t, info)
