open Cn
open Builtins
module CF = Cerb_frontend
module CB = Cerb_backend
open CB.Pipeline
open Setup
module A = CF.AilSyntax

let return = CF.Exception.except_return

let ( let@ ) = CF.Exception.except_bind

type core_file = (unit, unit) CF.Core.generic_file

type file =
  | CORE of core_file
  | MUCORE of unit Mucore.file

let print_file filename file =
  match file with
  | CORE file -> Pp.print_file (filename ^ ".core") (CF.Pp_core.All.pp_file file)
  | MUCORE file -> Pp.print_file (filename ^ ".mucore") (Pp_mucore.pp_file file)


module Log : sig
  val print_log_file : string * file -> unit
end = struct
  let print_count = ref 0

  let print_log_file (filename, file) =
    if !Cerb_debug.debug_level > 0 then (
      Cerb_colour.do_colour := false;
      let count = !print_count in
      let file_path =
        Filename.concat
          (Filename.get_temp_dir_name ())
          (string_of_int count ^ "__" ^ filename)
      in
      print_file file_path file;
      print_count := 1 + !print_count;
      Cerb_colour.do_colour := true)
end

open Log

let frontend ~macros ~incl_dirs ~incl_files astprints ~filename ~magic_comment_char_dollar
  =
  let open CF in
  Cerb_global.set_cerb_conf
    ~backend_name:"Cn"
    ~exec:false
    (* execution mode *) Random
    ~concurrency:false
    (* error verbosity *) Basic
    ~defacto:false
    ~permissive:false
    ~agnostic:false
    ~ignore_bitfields:false;
  Ocaml_implementation.set Ocaml_implementation.HafniumImpl.impl;
  Switches.set
    ([ "inner_arg_temps"; "at_magic_comments" ]
     (* TODO (DCM, VIP) figure out how to support liveness checks for read-only
        resources and then switch on "strict_pointer_arith" to elaborate array
        shift to the effectful version. "strict_pointer_relationals" is also
        assumed, but this does not affect elaboration. *)
     @ if magic_comment_char_dollar then [ "magic_comment_char_dollar" ] else []);
  let@ stdlib = load_core_stdlib () in
  let@ impl = load_core_impl stdlib impl_name in
  let conf = Setup.conf macros incl_dirs incl_files astprints in
  let cn_init_scope : Cn_desugaring.init_scope =
    { predicates = [ Alloc.Predicate.(str, sym, Some loc) ];
      functions = List.map (fun (str, sym) -> (str, sym, None)) cn_builtin_fun_names;
      idents = [ Alloc.History.(str, sym, None) ]
    }
  in
  let@ cabs_tunit_opt, ail_prog_opt, prog0 =
    c_frontend_and_elaboration ~cn_init_scope (conf, io) (stdlib, impl) ~filename
  in
  let@ () =
    if conf.typecheck_core then
      let@ _ = Core_typing.typecheck_program prog0 in
      return ()
    else
      return ()
  in
  let cabs_tunit = Option.get cabs_tunit_opt in
  let markers_env, ail_prog = Option.get ail_prog_opt in
  Tags.set_tagDefs prog0.Core.tagDefs;
  let prog1 = Remove_unspecs.rewrite_file prog0 in
  let prog2 = Milicore.core_to_micore__file Locations.update prog1 in
  let prog3 = Milicore_label_inline.rewrite_file prog2 in
  let statement_locs = CStatements.search (snd ail_prog) in
  print_log_file ("original", CORE prog0);
  print_log_file ("without_unspec", CORE prog1);
  return (cabs_tunit, prog3, (markers_env, ail_prog), statement_locs)


let handle_frontend_error = function
  | CF.Exception.Exception ((_, CF.Errors.CORE_TYPING _) as err) ->
    prerr_string (CF.Pp_errors.to_string err);
    prerr_endline
    @@ Cerb_colour.(ansi_format ~err:true [ Bold; Red ] "error: ")
    ^ "this is likely a bug in the Core elaboration.";
    exit 2
  | CF.Exception.Exception err ->
    prerr_endline (CF.Pp_errors.to_string err);
    exit 2
  | CF.Exception.Result result -> result


let opt_comma_split = function None -> [] | Some str -> String.split_on_char ',' str

let check_input_file filename =
  if not (Sys.file_exists filename) then
    CF.Pp_errors.fatal ("file \"" ^ filename ^ "\" does not exist")
  else (
    let ext = String.equal (Filename.extension filename) in
    if not (ext ".c" || ext ".h") then
      CF.Pp_errors.fatal ("file \"" ^ filename ^ "\" has wrong file extension"))


let with_well_formedness_check
  ~(* CLI arguments *)
   filename
  ~macros
  ~incl_dirs
  ~incl_files
  ~coq_export_file
  ~csv_times
  ~log_times
  ~astprints
  ~no_inherit_loc
  ~magic_comment_char_dollar
  ~(* Callbacks *)
   handle_error
  ~(f :
     cabs_tunit:CF.Cabs.translation_unit ->
     prog5:unit Mucore.file ->
     ail_prog:CF.GenTypes.genTypeCategory A.ail_program ->
     statement_locs:Cerb_location.t CStatements.LocMap.t ->
     paused:_ Typing.pause ->
     unit Or_TypeError.t)
  =
  check_input_file filename;
  let cabs_tunit, prog, (markers_env, ail_prog), statement_locs =
    handle_frontend_error
      (frontend
         ~macros
         ~incl_dirs
         ~incl_files
         astprints
         ~filename
         ~magic_comment_char_dollar)
  in
  Cerb_debug.maybe_open_csv_timing_file ();
  Pp.maybe_open_times_channel
    (match (csv_times, log_times) with
     | Some times, _ -> Some (times, "csv")
     | _, Some times -> Some (times, "log")
     | _ -> None);
  try
    let result =
      let open Or_TypeError in
      let@ prog5 =
        Core_to_mucore.normalise_file
          ~inherit_loc:(not no_inherit_loc)
          (markers_env, snd ail_prog)
          prog
      in
      print_log_file ("mucore", MUCORE prog5);
      Option.iter
        (fun path -> Pp.print_file path (Pp_mucore_coq.pp_unit_file prog5))
        coq_export_file;
      let paused =
        Typing.run_to_pause Context.empty (Check.check_decls_lemmata_fun_specs prog5)
      in
      Result.iter_error handle_error (Typing.pause_to_result paused);
      f ~cabs_tunit ~prog5 ~ail_prog ~statement_locs ~paused
    in
    Pp.maybe_close_times_channel ();
    Result.fold ~ok:(fun () -> exit 0) ~error:handle_error result
  with
  | exc ->
    Pp.maybe_close_times_channel ();
    Cerb_debug.maybe_close_csv_timing_file_no_err ();
    Printexc.raise_with_backtrace exc (Printexc.get_raw_backtrace ())


(** Report an error on [stderr] in an appropriate format: JSON if [json] is
    true, or human-readable if not. *)
let report_type_error
  ~(json : bool)
  ?(output_dir : string option)
  ?(fn_name : string option)
  ?(serialize_json : bool = false)
  (error : TypeErrors.t)
  : unit
  =
  if json then
    TypeErrors.report_json ?output_dir ?fn_name ~serialize_json error
  else
    TypeErrors.report_pretty ?output_dir ?fn_name ~serialize_json error


(** Generate an appropriate exit code for the provided error. *)
let exit_code_of_error (error : TypeErrors.t) : int =
  match error.msg with TypeErrors.Unsupported _ -> 2 | _ -> 1


(** In the presence of nonempty errors, generate an appropriate exit code for
    them. *)
let exit_code_of_errors (errors : TypeErrors.t list) : int option =
  (* We arbitrarily choose to make any `Unsupported` message dominate all other
     messages. *)
  let is_unsupported (err : TypeErrors.t) =
    match err.msg with TypeErrors.Unsupported _ -> true | _ -> false
  in
  match errors with
  | [] -> None
  | _ -> Some (if List.exists is_unsupported errors then 2 else 1)


(** Report the provided error, then exit. *)
let handle_type_error
  ~(json : bool)
  ?(output_dir : string option)
  ?(serialize_json : bool = false)
  (error : TypeErrors.t)
  =
  report_type_error ~json ?output_dir ~serialize_json error;
  exit (exit_code_of_error error)


let well_formed
  filename
  macros
  incl_dirs
  incl_files
  json
  json_trace
  output_dir
  csv_times
  log_times
  astprints
  no_inherit_loc
  magic_comment_char_dollar
  =
  with_well_formedness_check
    ~filename
    ~macros
    ~incl_dirs
    ~incl_files
    ~coq_export_file:None
    ~csv_times
    ~log_times
    ~astprints
    ~no_inherit_loc
    ~magic_comment_char_dollar
    ~handle_error:(handle_type_error ~json ?output_dir ~serialize_json:json_trace)
    ~f:(fun ~cabs_tunit:_ ~prog5:_ ~ail_prog:_ ~statement_locs:_ ~paused:_ ->
      Or_TypeError.return ())


let verify
  filename
  macros
  incl_dirs
  incl_files
  loc_pp
  debug_level
  print_level
  print_sym_nums
  no_timestamps
  json
  json_trace
  output_dir
  diag
  lemmata
  coq_export_file
  only
  skip
  csv_times
  log_times
  solver_logging
  solver_flags
  solver_path
  solver_type
  astprints
  dont_use_vip
  no_use_ity
  fail_fast
  quiet
  no_inherit_loc
  magic_comment_char_dollar
  disable_resource_derived_constraints
  =
  if json then (
    if debug_level > 0 then
      CF.Pp_errors.fatal "debug level must be 0 for json output";
    if print_level > 0 then
      CF.Pp_errors.fatal "print level must be 0 for json output");
  (*flags *)
  Cerb_debug.debug_level := debug_level;
  Pp.loc_pp := loc_pp;
  Pp.print_level := print_level;
  CF.Pp_symbol.pp_cn_sym_nums := print_sym_nums;
  Pp.print_timestamps := not no_timestamps;
  (match solver_logging with
   | Some d ->
     Solver.Logger.to_file := true;
     Solver.Logger.dir := if String.equal d "" then None else Some d
   | _ -> ());
  Solver.solver_path := solver_path;
  Solver.solver_type := solver_type;
  Solver.solver_flags := solver_flags;
  Check.skip_and_only := (opt_comma_split skip, opt_comma_split only);
  IndexTerms.use_vip := not dont_use_vip;
  Check.fail_fast := fail_fast;
  Diagnostics.diag_string := diag;
  WellTyped.use_ity := not no_use_ity;
  Resource.disable_resource_derived_constraints := disable_resource_derived_constraints;
  with_well_formedness_check (* CLI arguments *)
    ~filename
    ~macros
    ~incl_dirs
    ~incl_files
    ~coq_export_file
    ~csv_times
    ~log_times
    ~astprints
    ~no_inherit_loc
    ~magic_comment_char_dollar (* Callbacks *)
    ~handle_error:(handle_type_error ~json ?output_dir ~serialize_json:json_trace)
    ~f:(fun ~cabs_tunit:_ ~prog5:_ ~ail_prog:_ ~statement_locs:_ ~paused ->
      let check (functions, global_var_constraints, lemmas) =
        let open Typing in
        let@ errors = Check.time_check_c_functions (global_var_constraints, functions) in
        if not quiet then
          List.iter
            (fun (fn, err) ->
              report_type_error
                ~json
                ?output_dir
                ~fn_name:fn
                ~serialize_json:json_trace
                err)
            errors;
        Option.fold ~none:() ~some:exit (exit_code_of_errors (List.map snd errors));
        Check.generate_lemmas lemmas lemmata
      in
      Typing.run_from_pause check paused)


let handle_error_with_user_guidance ~(label : string) (e : exn) : unit =
  let msg = Printexc.to_string e in
  let stack = Printexc.get_backtrace () in
  Printf.eprintf "cn: internal error, uncaught exception:\n    %s\n" msg;
  let lines = String.split_on_char '\n' stack in
  List.iter (fun line -> Printf.eprintf "    %s\n" line) lines;
  Printf.eprintf
    "Issues can be made at https://github.com/rems-project/cerberus/issues.\n";
  Printf.eprintf "Prefix your issue with \"[%s]\". " label;
  Printf.eprintf "Check that there isn't already one for this error.\n";
  exit 1


let generate_executable_specs
  filename
  macros
  incl_dirs
  incl_files
  loc_pp
  debug_level
  print_level
  print_sym_nums
  no_timestamps
  json
  json_trace
  output_dir
  diag
  only
  skip
  csv_times
  log_times
  astprints
  dont_use_vip
  no_use_ity
  fail_fast
  no_inherit_loc
  magic_comment_char_dollar
  (* Executable spec *)
    output_decorated
  output_decorated_dir
  without_ownership_checking
  with_test_gen
  copy_source_dir
  =
  if json then (
    if debug_level > 0 then
      CF.Pp_errors.fatal "debug level must be 0 for json output";
    if print_level > 0 then
      CF.Pp_errors.fatal "print level must be 0 for json output");
  (*flags *)
  Cerb_debug.debug_level := debug_level;
  Pp.loc_pp := loc_pp;
  Pp.print_level := print_level;
  CF.Pp_symbol.pp_cn_sym_nums := print_sym_nums;
  Pp.print_timestamps := not no_timestamps;
  Check.skip_and_only := (opt_comma_split skip, opt_comma_split only);
  IndexTerms.use_vip := not dont_use_vip;
  Check.fail_fast := fail_fast;
  Diagnostics.diag_string := diag;
  WellTyped.use_ity := not no_use_ity;
  Sym.executable_spec_enabled := true;
  with_well_formedness_check (* CLI arguments *)
    ~filename
    ~macros
    ~incl_dirs
    ~incl_files
    ~coq_export_file:None
    ~csv_times
    ~log_times
    ~astprints
    ~no_inherit_loc
    ~magic_comment_char_dollar (* Callbacks *)
    ~handle_error:(handle_type_error ~json ?output_dir ~serialize_json:json_trace)
    ~f:(fun ~cabs_tunit:_ ~prog5 ~ail_prog ~statement_locs ~paused:_ ->
      Cerb_colour.without_colour
        (fun () ->
          (try
             Executable_spec.main
               ~without_ownership_checking
               ~with_test_gen
               ~copy_source_dir
               filename
               ail_prog
               output_decorated
               output_decorated_dir
               prog5
               statement_locs
           with
           | e -> handle_error_with_user_guidance ~label:"CN-Exec" e);
          Or_TypeError.return ())
        ())


let run_seq_tests
  (* Common *)
    filename
  macros
  incl_dirs
  incl_files
  debug_level
  print_level
  csv_times
  log_times
  astprints
  no_inherit_loc
  magic_comment_char_dollar
  (* Executable spec *)
    without_ownership_checking
  (* Test Generation *)
    output_dir
  with_static_hack
  num_samples
  backtrack_attempts
  num_resets
  =
  (* flags *)
  Cerb_debug.debug_level := debug_level;
  Pp.print_level := print_level;
  Sym.executable_spec_enabled := true;
  let handle_error (e : TypeErrors.t) =
    let report = TypeErrors.pp_message e.msg in
    Pp.error e.loc report.short (Option.to_list report.descr);
    match e.msg with TypeErrors.Unsupported _ -> exit 2 | _ -> exit 1
  in
  with_well_formedness_check (* CLI arguments *)
    ~filename
    ~macros
    ~incl_dirs
    ~incl_files
    ~csv_times
    ~coq_export_file:None
    ~log_times
    ~astprints
    ~no_inherit_loc
    ~magic_comment_char_dollar (* Callbacks *)
    ~handle_error
    ~f:(fun ~cabs_tunit ~prog5 ~ail_prog ~statement_locs ~paused:_ ->
      Cerb_colour.without_colour
        (fun () ->
          let _, sigma = ail_prog in
          if
            List.is_empty
              (TestGeneration.functions_under_test
                 ~with_warning:true
                 cabs_tunit
                 sigma
                 prog5)
          then (
            print_endline "No testable functions, trivially passing";
            exit 0);
          if not (Sys.file_exists output_dir) then (
            print_endline ("Directory \"" ^ output_dir ^ "\" does not exist.");
            Sys.mkdir output_dir 0o777;
            print_endline
              ("Created directory \"" ^ output_dir ^ "\" with full permissions."));
          let _, sigma = ail_prog in
          Cn_internal_to_ail.augment_record_map (BaseTypes.Record []);
          Executable_spec.main
            ~without_ownership_checking
            ~with_test_gen:true
            ~copy_source_dir:false
            filename
            ail_prog
            None
            (Some output_dir)
            prog5
            statement_locs;
          let config : TestGeneration.seq_config =
            { with_static_hack;
              num_samples;
              max_backtracks = backtrack_attempts;
              num_resets
            }
          in
          TestGeneration.set_seq_config config;
          if TestGeneration.run_seq ~output_dir ~filename cabs_tunit sigma prog5 <> 0 then
            exit 123)
        ();
      Or_TypeError.return ())


let run_tests
  (* Common *)
    filename
  macros
  incl_dirs
  incl_files
  debug_level
  print_level
  csv_times
  log_times
  astprints
  no_inherit_loc
  magic_comment_char_dollar
  (* Executable spec *)
    without_ownership_checking
  (* Test Generation *)
    output_dir
  only
  skip
  dont_run
  num_samples
  max_backtracks
  max_unfolds
  max_array_length
  with_static_hack
  build_tool
  sanitizers
  input_timeout
  null_in_every
  seed
  logging_level
  trace_granularity
  progress_level
  until_timeout
  exit_fast
  max_stack_depth
  allowed_depth_failures
  max_generator_size
  sizing_strategy
  random_size_splits
  allowed_size_split_backtracks
  sized_null
  coverage
  disable_passes
  trap
  =
  (* flags *)
  Cerb_debug.debug_level := debug_level;
  Pp.print_level := print_level;
  Check.skip_and_only := (opt_comma_split skip, opt_comma_split only);
  Sym.executable_spec_enabled := true;
  let handle_error (e : TypeErrors.t) =
    let report = TypeErrors.pp_message e.msg in
    Pp.error e.loc report.short (Option.to_list report.descr);
    match e.msg with TypeErrors.Unsupported _ -> exit 2 | _ -> exit 1
  in
  with_well_formedness_check (* CLI arguments *)
    ~filename
    ~macros
    ~incl_dirs
    ~incl_files
    ~csv_times
    ~coq_export_file:None
    ~log_times
    ~astprints
    ~no_inherit_loc
    ~magic_comment_char_dollar (* Callbacks *)
    ~handle_error
    ~f:(fun ~cabs_tunit ~prog5 ~ail_prog ~statement_locs ~paused:_ ->
      let config : TestGeneration.config =
        { num_samples;
          max_backtracks;
          max_unfolds;
          max_array_length;
          with_static_hack;
          build_tool;
          sanitizers;
          input_timeout;
          null_in_every;
          seed;
          logging_level;
          trace_granularity;
          progress_level;
          until_timeout;
          exit_fast;
          max_stack_depth;
          allowed_depth_failures;
          max_generator_size;
          sizing_strategy;
          random_size_splits;
          allowed_size_split_backtracks;
          sized_null;
          coverage;
          disable_passes;
          trap
        }
      in
      TestGeneration.set_config config;
      let _, sigma = ail_prog in
      if
        List.is_empty
          (TestGeneration.functions_under_test ~with_warning:true cabs_tunit sigma prog5)
      then (
        print_endline "No testable functions, trivially passing";
        exit 0);
      if not (Sys.file_exists output_dir) then (
        print_endline ("Directory \"" ^ output_dir ^ "\" does not exist.");
        Sys.mkdir output_dir 0o777;
        print_endline ("Created directory \"" ^ output_dir ^ "\" with full permissions."));
      Cerb_colour.without_colour
        (fun () ->
          Cn_internal_to_ail.augment_record_map (BaseTypes.Record []);
          (try
             Executable_spec.main
               ~without_ownership_checking
               ~with_test_gen:true
               ~copy_source_dir:false
               filename
               ail_prog
               None
               (Some output_dir)
               prog5
               statement_locs
           with
           | e -> handle_error_with_user_guidance ~label:"CN-Exec" e);
          (try
             TestGeneration.run
               ~output_dir
               ~filename
               ~without_ownership_checking
               cabs_tunit
               sigma
               prog5
           with
           | e -> handle_error_with_user_guidance ~label:"CN-Test-Gen" e);
          if not dont_run then
            Unix.execv (Filename.concat output_dir "run_tests.sh") (Array.of_list []))
        ();
      Or_TypeError.return ())


open Cmdliner

(* some of these stolen from backend/driver *)
module Common_flags = struct
  let file =
    let doc = "Source C file" in
    Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)


  (* copied from cerberus' executable (backend/driver/main.ml) *)
  let macros =
    let macro_pair =
      let parser str =
        match String.index_opt str '=' with
        | None -> Result.Ok (str, None)
        | Some i ->
          let macro = String.sub str 0 i in
          let value = String.sub str (i + 1) (String.length str - i - 1) in
          let is_digit n = 48 <= n && n <= 57 in
          if i = 0 || is_digit (Char.code (String.get macro 0)) then
            Result.Error (`Msg "macro name must be a C identifier")
          else
            Result.Ok (macro, Some value)
      in
      let printer ppf = function
        | m, None -> Format.pp_print_string ppf m
        | m, Some v -> Format.fprintf ppf "%s=%s" m v
      in
      Arg.(conv (parser, printer))
    in
    let doc =
      "Adds  an  implicit  #define  into the predefines buffer which is read before the \
       source file is preprocessed."
    in
    Arg.(
      value
      & opt_all macro_pair []
      & info [ "D"; "define-macro" ] ~docv:"NAME[=VALUE]" ~doc)


  let incl_dirs =
    let doc = "Add the specified directory to the search path for theC preprocessor." in
    Arg.(value & opt_all string [] & info [ "I"; "include-directory" ] ~docv:"DIR" ~doc)


  let incl_files =
    let doc =
      "Adds  an  implicit  #include into the predefines buffer which is read before the \
       source file is preprocessed."
    in
    Arg.(value & opt_all string [] & info [ "include" ] ~doc)


  let debug_level =
    let doc =
      "Set the debug message level for cerberus to $(docv) (should range over [0-3])."
    in
    Arg.(value & opt int 0 & info [ "d"; "debug" ] ~docv:"N" ~doc)


  let print_level =
    let doc =
      "Set the debug message level for the type system to $(docv) (should range over \
       [0-15])."
    in
    Arg.(value & opt int 0 & info [ "p"; "print-level" ] ~docv:"N" ~doc)


  let print_sym_nums =
    let doc = "Print numeric IDs of Cerberus symbols (variable names)." in
    Arg.(value & flag & info [ "n"; "print-sym-nums" ] ~doc)


  let no_timestamps =
    let doc = "Disable timestamps in print-level debug messages" in
    Arg.(value & flag & info [ "no_timestamps" ] ~doc)


  let csv_times =
    let doc = "file in which to output csv timing information" in
    Arg.(value & opt (some string) None & info [ "times" ] ~docv:"FILE" ~doc)


  let log_times =
    let doc = "file in which to output hierarchical timing information" in
    Arg.(value & opt (some string) None & info [ "log-times" ] ~docv:"FILE" ~doc)


  (* copy-pasting from backend/driver/main.ml *)
  let astprints =
    let doc =
      "Pretty print the intermediate syntax tree for the listed languages (ranging over \
       {cabs, ail, core, types})."
    in
    Arg.(
      value
      & opt
          (list (enum [ ("cabs", Cabs); ("ail", Ail); ("core", Core); ("types", Types) ]))
          []
      & info [ "ast" ] ~docv:"LANG1,..." ~doc)


  let no_use_ity =
    let doc =
      "(this switch should go away) in WellTyped.BaseTyping, do not use\n\
      \  integer type annotations placed by the Core elaboration"
    in
    Arg.(value & flag & info [ "no-use-ity" ] ~doc)


  let no_inherit_loc =
    let doc =
      "debugging: stop mucore terms inheriting location information from parents"
    in
    Arg.(value & flag & info [ "no-inherit-loc" ] ~doc)


  let magic_comment_char_dollar =
    let doc = "Override CN's default magic comment syntax to be \"/*\\$ ... \\$*/\"" in
    Arg.(value & flag & info [ "magic-comment-char-dollar" ] ~doc)
end

module Verify_flags = struct
  let loc_pp =
    let doc = "Print pointer values as hexadecimal or as decimal values (hex | dec)" in
    Arg.(
      value
      & opt (enum [ ("hex", Pp.Hex); ("dec", Pp.Dec) ]) !Pp.loc_pp
      & info [ "locs" ] ~docv:"HEX" ~doc)


  let fail_fast =
    let doc = "Abort immediately after encountering a verification error" in
    Arg.(value & flag & info [ "fail-fast" ] ~doc)


  let quiet =
    let doc = "Only report success and failure, rather than rich errors" in
    Arg.(value & flag & info [ "quiet" ] ~doc)


  let diag =
    let doc = "explore branching diagnostics with key string" in
    Arg.(value & opt (some string) None & info [ "diag" ] ~doc)


  let solver_logging =
    let doc = "Log solver queries in SMT2 format to a directory." in
    Arg.(value & opt (some string) None & info [ "solver-logging" ] ~docv:"DIR" ~doc)


  let solver_flags =
    let doc =
      "Ovewrite default solver flags. Note that flags should enable at least incremental \
       checking."
    in
    Arg.(
      value & opt (some (list string)) None & info [ "solver-flags" ] ~docv:"X,Y,Z" ~doc)


  let solver_path =
    let doc = "Path to SMT solver executable" in
    Arg.(value & opt (some string) None & info [ "solver-path" ] ~docv:"FILE" ~doc)


  let solver_type =
    let doc = "Specify the SMT solver interface" in
    Arg.(
      value
      & opt (some (enum [ ("z3", Simple_smt.Z3); ("cvc5", Simple_smt.CVC5) ])) None
      & info [ "solver-type" ] ~docv:"z3|cvc5" ~doc)


  let only =
    let doc = "only type-check this function (or comma-separated names)" in
    Arg.(value & opt (some string) None & info [ "only" ] ~doc)


  let skip =
    let doc = "skip type-checking of this function (or comma-separated names)" in
    Arg.(value & opt (some string) None & info [ "skip" ] ~doc)


  (* TODO remove this when VIP impl complete *)
  let dont_use_vip =
    let doc = "(temporary) disable VIP rules" in
    Arg.(value & flag & info [ "no-vip" ] ~doc)


  let json =
    let doc = "output summary in JSON format" in
    Arg.(value & flag & info [ "json" ] ~doc)


  let json_trace =
    let doc = "output state trace files as JSON, in addition to HTML" in
    Arg.(value & flag & info [ "json-trace" ] ~doc)


  let output_dir =
    let doc = "directory in which to output state files" in
    Arg.(value & opt (some string) None & info [ "output-dir" ] ~docv:"FILE" ~doc)


  let disable_resource_derived_constraints =
    let doc = "disable resource-derived constraints" in
    Arg.(value & flag & info [ "disable-resource-derived-constraints" ] ~doc)
end

module Executable_spec_flags = struct
  let output_decorated_dir =
    let doc =
      "output a version of the translation unit decorated with C runtime\n\
      \  translations of the CN annotations to the provided directory"
    in
    Arg.(
      value & opt (some string) None & info [ "output-decorated-dir" ] ~docv:"FILE" ~doc)


  let output_decorated =
    let doc =
      "output a version of the translation unit decorated with C runtime\n\
      \  translations of the CN annotations."
    in
    Arg.(value & opt (some string) None & info [ "output-decorated" ] ~docv:"FILE" ~doc)


  let without_ownership_checking =
    let doc = "Disable ownership checking within CN runtime testing" in
    Arg.(value & flag & info [ "without-ownership-checking" ] ~doc)


  let with_test_gen =
    let doc =
      "Generate CN executable specifications in the correct format for feeding into \n\
      \  the CN test generation tool."
    in
    Arg.(value & flag & info [ "with-test-gen" ] ~doc)


  let copy_source_dir =
    let doc =
      "Copy non-CN annotated files into output_decorated_dir for CN runtime testing"
    in
    Arg.(value & flag & info [ "copy-source-dir" ] ~doc)
end

module Lemma_flags = struct
  let lemmata =
    let doc = "lemmata generation mode (target filename)" in
    Arg.(value & opt (some string) None & info [ "lemmata" ] ~docv:"FILE" ~doc)
end

module CoqExport_flags = struct
  let coq_export =
    let doc = "export to coq" in
    Arg.(value & opt (some string) None & info [ "coq-export-file" ] ~docv:"FILE" ~doc)
end

let wf_cmd =
  let open Term in
  let wf_t =
    const well_formed
    $ Common_flags.file
    $ Common_flags.macros
    $ Common_flags.incl_dirs
    $ Common_flags.incl_files
    $ Verify_flags.json
    $ Verify_flags.json_trace
    $ Verify_flags.output_dir
    $ Common_flags.csv_times
    $ Common_flags.log_times
    $ Common_flags.astprints
    $ Common_flags.no_inherit_loc
    $ Common_flags.magic_comment_char_dollar
  in
  let doc =
    "Runs CN's well-formedness check\n\
    \    which finds errors such as\n\
    \    ill-typing CN definitions\n\
    \    (predicates, specifications, lemmas)\n\
    \    and ill-formed recursion in datatypes.\n\
    \    It DOES NOT verify C functions,\n\
    \    which `cn verify` does."
  in
  let info = Cmd.info "wf" ~doc in
  Cmd.v info wf_t


let verify_t : unit Term.t =
  let open Term in
  const verify
  $ Common_flags.file
  $ Common_flags.macros
  $ Common_flags.incl_dirs
  $ Common_flags.incl_files
  $ Verify_flags.loc_pp
  $ Common_flags.debug_level
  $ Common_flags.print_level
  $ Common_flags.print_sym_nums
  $ Common_flags.no_timestamps
  $ Verify_flags.json
  $ Verify_flags.json_trace
  $ Verify_flags.output_dir
  $ Verify_flags.diag
  $ Lemma_flags.lemmata
  $ CoqExport_flags.coq_export
  $ Verify_flags.only
  $ Verify_flags.skip
  $ Common_flags.csv_times
  $ Common_flags.log_times
  $ Verify_flags.solver_logging
  $ Verify_flags.solver_flags
  $ Verify_flags.solver_path
  $ Verify_flags.solver_type
  $ Common_flags.astprints
  $ Verify_flags.dont_use_vip
  $ Common_flags.no_use_ity
  $ Verify_flags.fail_fast
  $ Verify_flags.quiet
  $ Common_flags.no_inherit_loc
  $ Common_flags.magic_comment_char_dollar
  $ Verify_flags.disable_resource_derived_constraints


let verify_cmd =
  let doc =
    "Verifies that functions meet\n\
    \    their CN specifications and the\n\
    \    absence of undefined behavior."
  in
  let info = Cmd.info "verify" ~doc in
  Cmd.v info verify_t


module Testing_flags = struct
  let output_test_dir =
    let doc = "Place generated tests in the provided directory" in
    Arg.(value & opt string "." & info [ "output-dir" ] ~docv:"DIR" ~doc)


  let only =
    let doc = "Only test this function (or comma-separated names)" in
    Arg.(value & opt (some string) None & info [ "only" ] ~doc)


  let skip =
    let doc = "Skip testing of this function (or comma-separated names)" in
    Arg.(value & opt (some string) None & info [ "skip" ] ~doc)


  let dont_run =
    let doc = "Do not run tests, only generate them" in
    Arg.(value & flag & info [ "no-run" ] ~doc)


  let gen_num_samples =
    let doc = "Set the number of samples to test" in
    Arg.(
      value & opt int TestGeneration.default_cfg.num_samples & info [ "num-samples" ] ~doc)


  let gen_backtrack_attempts =
    let doc =
      "Set the maximum attempts to satisfy a constraint before backtracking further, \
       during input generation"
    in
    Arg.(
      value
      & opt int TestGeneration.default_cfg.max_backtracks
      & info [ "max-backtrack-attempts" ] ~doc)


  let gen_max_unfolds =
    let doc = "Set the maximum number of unfolds for recursive generators" in
    Arg.(
      value
      & opt (some int) TestGeneration.default_cfg.max_unfolds
      & info [ "max-unfolds" ] ~doc)


  let max_array_length =
    let doc = "Set the maximum length for an array generated" in
    Arg.(
      value
      & opt int TestGeneration.default_cfg.max_array_length
      & info [ "max-array-length" ] ~doc)


  let with_static_hack =
    let doc =
      "(HACK) Use an `#include` instead of linking to build testing. Necessary until \
       https://github.com/rems-project/cerberus/issues/784 or equivalent."
    in
    Arg.(value & flag & info [ "with-static-hack" ] ~doc)


  let build_tool =
    let doc = "Set which build tool to use." in
    Arg.(
      value
      & opt (enum TestGeneration.Options.build_tool) TestGeneration.default_cfg.build_tool
      & info [ "build-tool" ] ~doc)


  let sanitize =
    let doc = "Forwarded to the '-fsanitize' argument of the C compiler" in
    Arg.(
      value
      & opt (some string) (fst TestGeneration.default_cfg.sanitizers)
      & info [ "sanitize" ] ~doc)


  let no_sanitize =
    let doc = "Forwarded to the '-fno-sanitize' argument of the C compiler" in
    Arg.(
      value
      & opt (some string) (snd TestGeneration.default_cfg.sanitizers)
      & info [ "no-sanitize" ] ~doc)


  let input_timeout =
    let doc = "Timeout for discarding a generation attempt (ms)" in
    Arg.(
      value
      & opt (some int) TestGeneration.default_cfg.input_timeout
      & info [ "input-timeout" ] ~doc)


  let null_in_every =
    let doc = "Set the likelihood of NULL being generated as 1 in every <n>" in
    Arg.(
      value
      & opt (some int) TestGeneration.default_cfg.null_in_every
      & info [ "null-in-every" ] ~doc)


  let seed =
    let doc = "Set the seed for random testing" in
    Arg.(value & opt (some string) TestGeneration.default_cfg.seed & info [ "seed" ] ~doc)


  let logging_level =
    let doc = "Set the logging level for failing inputs from tests" in
    Arg.(
      value
      & opt
          (some (enum TestGeneration.Options.logging_level))
          TestGeneration.default_cfg.logging_level
      & info [ "logging-level" ] ~doc)


  let trace_granularity =
    let doc = "Set the trace granularity for failing inputs from tests" in
    Arg.(
      value
      & opt
          (some (enum TestGeneration.Options.trace_granularity))
          TestGeneration.default_cfg.trace_granularity
      & info [ "trace-granularity" ] ~doc)


  let progress_level =
    let doc = "Set the frequency of progress updates." in
    Arg.(
      value
      & opt
          (some (enum TestGeneration.Options.progress_level))
          TestGeneration.default_cfg.progress_level
      & info [ "progress-level" ] ~doc)


  let until_timeout =
    let doc =
      "Keep rerunning tests until the given timeout (in seconds) has been reached"
    in
    Arg.(
      value
      & opt (some int) TestGeneration.default_cfg.until_timeout
      & info [ "until-timeout" ] ~doc)


  let exit_fast =
    let doc = "Stop testing upon finding the first failure" in
    Arg.(value & flag & info [ "exit-fast" ] ~doc)


  let max_stack_depth =
    let doc = "Maximum stack depth for generators" in
    Arg.(
      value
      & opt (some int) TestGeneration.default_cfg.max_stack_depth
      & info [ "max-stack-depth" ] ~doc)


  let allowed_depth_failures =
    let doc = "Maximum stack depth failures before discarding an attempt" in
    Arg.(
      value
      & opt (some int) TestGeneration.default_cfg.allowed_depth_failures
      & info [ "allowed-depth-failures" ] ~doc)


  let max_generator_size =
    let doc = "Maximum size for generated values" in
    Arg.(
      value
      & opt (some int) TestGeneration.default_cfg.max_generator_size
      & info [ "max-generator-size" ] ~doc)


  let sizing_strategy =
    let doc = "Strategy for deciding test case size." in
    Arg.(
      value
      & opt
          (some (enum TestGeneration.Options.sizing_strategy))
          TestGeneration.default_cfg.sizing_strategy
      & info [ "sizing-strategy" ] ~doc)


  let random_size_splits =
    let doc = "Randomly split sizes between recursive generator calls" in
    Arg.(value & flag & info [ "random-size-splits" ] ~doc)


  let allowed_size_split_backtracks =
    let doc =
      "Set the maximum attempts to split up a generator's size (between recursive calls) \
       before backtracking further, during input generation"
    in
    Arg.(
      value
      & opt (some int) TestGeneration.default_cfg.allowed_size_split_backtracks
      & info [ "allowed-size-split-backtracks" ] ~doc)


  let sized_null =
    let doc =
      "Scale the likelihood of [NULL] proportionally for a desired size (1/n for size n)"
    in
    Arg.(value & flag & info [ "sized-null" ] ~doc)


  let coverage =
    let doc = "(Experimental) Record coverage of tests via [lcov]" in
    Arg.(value & flag & info [ "coverage" ] ~doc)


  let disable_passes =
    let doc = "skip this optimization pass (or comma-separated names)" in
    Arg.(
      value
      & opt
          (list
             (enum
                [ ("reorder", "reorder");
                  ("picks", "picks");
                  ("flatten", "flatten");
                  ("consistency", "consistency");
                  ("lift_constraints", "lift_constraints")
                ]))
          []
      & info [ "disable" ] ~doc)


  let trap =
    let doc = "Raise SIGTRAP on test failure" in
    Arg.(value & flag & info [ "trap" ] ~doc)
end

module Seq_testing_flags = struct
  let output_test_dir =
    let doc = "Place generated tests in the provided directory" in
    Arg.(value & opt string "." & info [ "output-dir" ] ~docv:"DIR" ~doc)


  let with_static_hack =
    let doc =
      "(HACK) Use an `#include` instead of linking to build testing. Necessary until \
       https://github.com/rems-project/cerberus/issues/784 or equivalent."
    in
    Arg.(value & flag & info [ "with-static-hack" ] ~doc)


  let gen_num_samples =
    let doc = "Set the number of samples to test" in
    Arg.(
      value
      & opt int TestGeneration.default_seq_cfg.num_samples
      & info [ "num-samples" ] ~doc)


  let gen_backtrack_attempts =
    let doc =
      "Set the maximum attempts to satisfy a constraint before backtracking further, \
       during input generation"
    in
    Arg.(
      value
      & opt int TestGeneration.default_seq_cfg.max_backtracks
      & info [ "max-backtrack-attempts" ] ~doc)


  let num_resets =
    let doc = "Number of context resets for sequence testing" in
    Arg.(
      value
      & opt int TestGeneration.default_seq_cfg.num_resets
      & info [ "max-resets" ] ~doc)
end

let testing_cmd =
  let open Term in
  let test_t =
    const run_tests
    $ Common_flags.file
    $ Common_flags.macros
    $ Common_flags.incl_dirs
    $ Common_flags.incl_files
    $ Common_flags.debug_level
    $ Common_flags.print_level
    $ Common_flags.csv_times
    $ Common_flags.log_times
    $ Common_flags.astprints
    $ Common_flags.no_inherit_loc
    $ Common_flags.magic_comment_char_dollar
    $ Executable_spec_flags.without_ownership_checking
    $ Testing_flags.output_test_dir
    $ Testing_flags.only
    $ Testing_flags.skip
    $ Testing_flags.dont_run
    $ Testing_flags.gen_num_samples
    $ Testing_flags.gen_backtrack_attempts
    $ Testing_flags.gen_max_unfolds
    $ Testing_flags.max_array_length
    $ Testing_flags.with_static_hack
    $ Testing_flags.build_tool
    $ Term.product Testing_flags.sanitize Testing_flags.no_sanitize
    $ Testing_flags.input_timeout
    $ Testing_flags.null_in_every
    $ Testing_flags.seed
    $ Testing_flags.logging_level
    $ Testing_flags.trace_granularity
    $ Testing_flags.progress_level
    $ Testing_flags.until_timeout
    $ Testing_flags.exit_fast
    $ Testing_flags.max_stack_depth
    $ Testing_flags.allowed_depth_failures
    $ Testing_flags.max_generator_size
    $ Testing_flags.sizing_strategy
    $ Testing_flags.random_size_splits
    $ Testing_flags.allowed_size_split_backtracks
    $ Testing_flags.sized_null
    $ Testing_flags.coverage
    $ Testing_flags.disable_passes
    $ Testing_flags.trap
  in
  let doc =
    "Generates tests for all functions in [FILE] with CN specifications.\n\
    \    The tests use randomized inputs, which are guaranteed to satisfy the CN \
     precondition.\n\
    \    A script [run_tests.sh] for building and running the tests will be placed in \
     [output-dir]."
  in
  let info = Cmd.info "test" ~doc in
  Cmd.v info test_t


let seq_test_cmd =
  let open Term in
  let test_t =
    const run_seq_tests
    $ Common_flags.file
    $ Common_flags.macros
    $ Common_flags.incl_dirs
    $ Common_flags.incl_files
    $ Common_flags.debug_level
    $ Common_flags.print_level
    $ Common_flags.csv_times
    $ Common_flags.log_times
    $ Common_flags.astprints
    $ Common_flags.no_inherit_loc
    $ Common_flags.magic_comment_char_dollar
    $ Executable_spec_flags.without_ownership_checking
    $ Seq_testing_flags.output_test_dir
    $ Seq_testing_flags.with_static_hack
    $ Seq_testing_flags.gen_num_samples
    $ Seq_testing_flags.gen_backtrack_attempts
    $ Seq_testing_flags.num_resets
  in
  let doc =
    "Generates sequences of calls for the API in [FILE].\n\
    \    The tests use randomized inputs or previous calls.\n\
    \    A [.c] file containing the test harnesses will be placed in [output-dir]."
  in
  let info = Cmd.info "seq_test" ~doc in
  Cmd.v info test_t


let instrument_cmd =
  let open Term in
  let instrument_t =
    const generate_executable_specs
    $ Common_flags.file
    $ Common_flags.macros
    $ Common_flags.incl_dirs
    $ Common_flags.incl_files
    $ Verify_flags.loc_pp
    $ Common_flags.debug_level
    $ Common_flags.print_level
    $ Common_flags.print_sym_nums
    $ Common_flags.no_timestamps
    $ Verify_flags.json
    $ Verify_flags.json_trace
    $ Verify_flags.output_dir
    $ Verify_flags.diag
    $ Verify_flags.only
    $ Verify_flags.skip
    $ Common_flags.csv_times
    $ Common_flags.log_times
    $ Common_flags.astprints
    $ Verify_flags.dont_use_vip
    $ Common_flags.no_use_ity
    $ Verify_flags.fail_fast
    $ Common_flags.no_inherit_loc
    $ Common_flags.magic_comment_char_dollar
    $ Executable_spec_flags.output_decorated
    $ Executable_spec_flags.output_decorated_dir
    $ Executable_spec_flags.without_ownership_checking
    $ Executable_spec_flags.with_test_gen
    $ Executable_spec_flags.copy_source_dir
  in
  let doc =
    "Instruments [FILE] with runtime C assertions that check the properties provided in \
     CN specifications.\n"
  in
  let info = Cmd.info "instrument" ~doc in
  Cmd.v info instrument_t


let subcommands = [ wf_cmd; verify_cmd; testing_cmd; instrument_cmd; seq_test_cmd ]

let () =
  let version_str = Cn_version.git_version ^ " [" ^ Cn_version.git_version_date ^ "]" in
  let cn_info = Cmd.info "cn" ~version:version_str in
  Stdlib.exit @@ Cmd.(eval (group cn_info subcommands))
