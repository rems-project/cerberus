open Builtins
module CF=Cerb_frontend
module CB=Cerb_backend
open CB.Pipeline
open Setup
open Executable_spec_utils

module A=CF.AilSyntax 


let return = CF.Exception.except_return
let (let@) = CF.Exception.except_bind



type core_file = (unit,unit) CF.Core.generic_file
type mu_file = unit Mucore.mu_file


type file =
  | CORE of core_file
  | MUCORE of mu_file



let print_file filename file =
  match file with
  | CORE file ->
     Pp.print_file (filename ^ ".core") (CF.Pp_core.All.pp_file file);
  | MUCORE file ->
     Pp.print_file (filename ^ ".mucore")
       (Pp_mucore.pp_file file);


module Log : sig
  val print_log_file : (string * file) -> unit
end = struct
  let print_count = ref 0
  let print_log_file (filename, file) =
    if !Cerb_debug.debug_level > 0 then
      begin
        Cerb_colour.do_colour := false;
        let count = !print_count in
        let file_path =
          (Filename.get_temp_dir_name ()) ^
            Filename.dir_sep ^
            (string_of_int count ^ "__" ^ filename)
        in
        print_file file_path file;
        print_count := 1 + !print_count;
        Cerb_colour.do_colour := true;
      end
end

open Log






let frontend macros incl_dirs incl_files astprints do_peval filename magic_comment_char_dollar =
  let open CF in
  Cerb_global.set_cerb_conf "Cn" false Random false Basic false false false false false;
  Ocaml_implementation.set Ocaml_implementation.HafniumImpl.impl;
  Switches.set 
    (["inner_arg_temps"; "at_magic_comments"] 
     @ (if magic_comment_char_dollar then ["magic_comment_char_dollar"] else []))
  ;
  Core_peval.config_unfold_stdlib := Sym.has_id_with Setup.unfold_stdlib_name;
  let@ stdlib = load_core_stdlib () in
  let@ impl = load_core_impl stdlib impl_name in
  let conf = Setup.conf macros incl_dirs incl_files astprints in
  let@ (_, ail_prog_opt, prog0) = c_frontend_and_elaboration ~cnnames:cn_builtin_fun_names (conf, io) (stdlib, impl) ~filename in
  let@ () =  begin
    if conf.typecheck_core then
      let@ _ = Core_typing.typecheck_program prog0 in return ()
    else
      return ()
  end in
  let markers_env, (_, ail_prog) = Option.get ail_prog_opt in
  Tags.set_tagDefs prog0.Core.tagDefs;
  let prog1 = Remove_unspecs.rewrite_file prog0 in
  let prog2 = if do_peval then Core_peval.rewrite_file prog1 else prog1 in
  let prog3 = Milicore.core_to_micore__file Locations.update prog2 in
  let prog4 = Milicore_label_inline.rewrite_file prog3 in
  let statement_locs = CStatements.search ail_prog in
  print_log_file ("original", CORE prog0);
  print_log_file ("without_unspec", CORE prog1);
  print_log_file ("after_peval", CORE prog2);
  return (prog4, (markers_env, ail_prog), statement_locs)


let handle_frontend_error = function
  | CF.Exception.Exception ((_, CF.Errors.CORE_TYPING _) as err) ->
     prerr_string (CF.Pp_errors.to_string err);
     prerr_endline @@ Cerb_colour.(ansi_format ~err:true [Bold; Red] "error: ") ^
       "this is likely a bug in the Core elaboration.";
     exit 2
  | CF.Exception.Exception err ->
     prerr_endline (CF.Pp_errors.to_string err);
     exit 2
  | CF.Exception.Result result ->
     result




let opt_comma_split = function
  | None -> []
  | Some str -> String.split_on_char ',' str

let check_input_file filename =
  if not (Sys.file_exists filename) then
    CF.Pp_errors.fatal ("file \""^filename^"\" does not exist")
  else
    let ext = String.equal (Filename.extension filename) in
    if not (ext ".c" || ext ".h") then
      CF.Pp_errors.fatal ("file \""^filename^"\" has wrong file extension")



let main 
      filename
      macros
      incl_dirs
      incl_files
      loc_pp
      debug_level
      print_level
      print_sym_nums
      slow_smt_threshold
      slow_smt_dir
      no_timestamps
      json
      state_file
      diag
      lemmata
      only
      skip
      csv_times
      log_times
      random_seed
      solver_logging
      output_decorated
      astprints
      use_vip
      no_use_ity
      use_peval
      batch
      no_inherit_loc
      magic_comment_char_dollar
  =
  if json then begin
      if debug_level > 0 then
        CF.Pp_errors.fatal ("debug level must be 0 for json output");
      if print_level > 0 then
        CF.Pp_errors.fatal ("print level must be 0 for json output");
    end;
  begin (*flags *)
    Cerb_debug.debug_level := debug_level;
    Pp.loc_pp := loc_pp;
    Pp.print_level := print_level;
    CF.Pp_symbol.pp_cn_sym_nums := print_sym_nums;
    Pp.print_timestamps := not no_timestamps;
    Solver.set_slow_smt_settings slow_smt_threshold slow_smt_dir;
    Solver.random_seed := random_seed;
    Solver.log_to_temp := solver_logging;
    Check.skip_and_only := (opt_comma_split skip, opt_comma_split only);
    IndexTerms.use_vip := use_vip;
    Check.batch := batch;
    Diagnostics.diag_string := diag;
    WellTyped.use_ity := not no_use_ity
  end;
  check_input_file filename;
  let (prog4, (markers_env, ail_prog), statement_locs) =
    handle_frontend_error
      (frontend macros incl_dirs incl_files astprints use_peval filename magic_comment_char_dollar)
  in
  Cerb_debug.maybe_open_csv_timing_file ();
  Pp.maybe_open_times_channel
    (match (csv_times, log_times) with
     | (Some times, _) -> Some (times, "csv")
     | (_, Some times) -> Some (times, "log")
     | _ -> None);
  try
      let result =
        let open Resultat in
         let@ prog5 = Core_to_mucore.normalise_file ~inherit_loc:(not(no_inherit_loc)) (markers_env, ail_prog) prog4 in
         let (instrumentation, symbol_table) = Core_to_mucore.collect_instrumentation prog5 in
         print_log_file ("mucore", MUCORE prog5);
         Cerb_colour.do_colour := false; (* Needed for executable spec printing *)
         begin match output_decorated with
         | None -> ()
         | Some output_filename ->
            let oc = Stdlib.open_out output_filename in
            let cn_oc = Stdlib.open_out "cn.c" in
            let executable_spec = Executable_spec_internal.generate_c_specs_internal instrumentation symbol_table statement_locs ail_prog  in
            let c_datatypes = Executable_spec_internal.generate_c_datatypes ail_prog.cn_datatypes in
            let c_functions = Executable_spec_internal.generate_c_functions_internal ail_prog prog5.mu_logical_predicates in
            let c_predicates = Executable_spec_internal.generate_c_predicates_internal ail_prog prog5.mu_resource_predicates in
            (* TODO: Topological sort *)
            Stdlib.output_string cn_oc (generate_include_header ("alloc.c", false));
            Stdlib.output_string cn_oc c_datatypes;
            Stdlib.output_string cn_oc c_functions;
            Stdlib.output_string cn_oc c_predicates;

            let incls = [("assert.h", true); ("stdlib.h", true); ("stdbool.h", true); ("alloc.c", false); ("cn.c", false);] in
            let headers = List.map generate_include_header incls in
            Stdlib.output_string oc (List.fold_left (^) "" headers);
            Stdlib.output_string oc "\n";
            begin match
              Source_injection.(output_injections oc
                { filename; sigm= ail_prog
                ; pre_post=executable_spec.pre_post
                ; in_stmt=executable_spec.in_stmt}
              )
            with
            | Ok () ->
                ()
            | Error str ->
                (* TODO(Christopher/Rini): maybe lift this error to the exception monad? *)
                prerr_endline str
            end
         end;

        match output_decorated with 
          | None -> 
            let@ res = Typing.run Context.empty (Check.check prog5 statement_locs lemmata) in 
            return res
          | Some _ -> 
            return ()

       in
       Pp.maybe_close_times_channel ();
       match result with
       | Ok () -> exit 0
       | Error e ->
         if json then TypeErrors.report_json ?state_file e 
         else TypeErrors.report ?state_file e;
         match e.msg with
         | TypeErrors.Unsupported _ -> exit 2
         | _ -> exit 1
 with
     | exc ->
        Pp.maybe_close_times_channel ();
        Cerb_debug.maybe_close_csv_timing_file_no_err ();
        Printexc.raise_with_backtrace exc (Printexc.get_raw_backtrace ());


open Cmdliner


(* some of these stolen from backend/driver *)
let file =
  let doc = "Source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)


let incl_dirs =
  let doc = "Add the specified directory to the search path for the\
             C preprocessor." in
  Arg.(value & opt_all string [] & info ["I"; "include-directory"]
         ~docv:"DIR" ~doc)

let incl_files =
  let doc = "Adds  an  implicit  #include into the predefines buffer which is \
             read before the source file is preprocessed." in
  Arg.(value & opt_all string [] & info ["include"] ~doc)

let loc_pp =
  let doc = "Print pointer values as hexadecimal or as decimal values (hex | dec)" in
  Arg.(value & opt (enum ["hex", Pp.Hex; "dec", Pp.Dec]) !Pp.loc_pp &
       info ["locs"] ~docv:"HEX" ~doc)

let debug_level =
  let doc = "Set the debug message level for cerberus to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let print_level =
  let doc = "Set the debug message level for the type system to $(docv) (should range over [0-15])." in
  Arg.(value & opt int 0 & info ["p"; "print-level"] ~docv:"N" ~doc)

let print_sym_nums =
  let doc = "Print numeric IDs of Cerberus symbols (variable names)." in
  Arg.(value & flag & info ["n"; "print-sym-nums"] ~doc)

let batch =
  let doc = "Type check functions in batch/do not stop on first type error (unless `only` is used)" in
  Arg.(value & flag & info ["batch"] ~doc)


let slow_smt_threshold =
  let doc = "Set the time threshold (in seconds) for logging slow smt queries." in
  Arg.(value & opt (some float) None & info ["slow-smt"] ~docv:"TIMEOUT" ~doc)

let slow_smt_dir =
  let doc = "Set the destination dir for logging slow smt queries (default is in system temp-dir)." in
  Arg.(value & opt (some string) None & info ["slow-smt-dir"] ~docv:"FILE" ~doc)


let no_timestamps =
  let doc = "Disable timestamps in print-level debug messages"
 in
  Arg.(value & flag & info ["no_timestamps"] ~doc)


let json =
  let doc = "output in json format" in
  Arg.(value & flag & info["json"] ~doc)


let state_file =
  let doc = "file in which to output the state" in
  Arg.(value & opt (some string) None & info ["state-file"] ~docv:"FILE" ~doc)

let diag =
  let doc = "explore branching diagnostics with key string" in
  Arg.(value & opt (some string) None & info ["diag"] ~doc)

let lemmata =
  let doc = "lemmata generation mode (target filename)" in
  Arg.(value & opt (some string) None & info ["lemmata"] ~docv:"FILE" ~doc)

let csv_times =
  let doc = "file in which to output csv timing information" in
  Arg.(value & opt (some string) None & info ["times"] ~docv:"FILE" ~doc)

let log_times =
  let doc = "file in which to output hierarchical timing information" in
  Arg.(value & opt (some string) None & info ["log_times"] ~docv:"FILE" ~doc)

let random_seed =
  let doc = "Set the SMT solver random seed (default 1)." in
  Arg.(value & opt int 0 & info ["r"; "random-seed"] ~docv:"I" ~doc)

let solver_logging =
  let doc = "Have Z3 log in SMT2 format to a file in a temporary directory." in
  Arg.(value & flag & info ["solver-logging"] ~doc)

let only =
  let doc = "only type-check this function (or comma-separated names)" in
  Arg.(value & opt (some string) None & info ["only"] ~doc)

let skip =
  let doc = "skip type-checking of this function (or comma-separated names)" in
  Arg.(value & opt (some string) None & info ["skip"] ~doc)

(* TODO(Christopher/Rini): I'm adding a tentative cli option, rename/change it to whatever you prefer *)
let output_decorated =
  let doc = "output a version of the translation unit decorated with C runtime translations of the CN annotations" in
  Arg.(value & opt (some string) None & info ["output_decorated"] ~docv:"FILE" ~doc)

(* copy-pasting from backend/driver/main.ml *)
let astprints =
  let doc = "Pretty print the intermediate syntax tree for the listed languages \
             (ranging over {cabs, ail, core, types})." in
  Arg.(value & opt (list (enum [("cabs", Cabs); ("ail", Ail); ("core", Core); ("types", Types)])) [] &
       info ["ast"] ~docv:"LANG1,..." ~doc)

(* TODO remove this when VIP impl complete *)
let use_vip =
  let doc = "use experimental VIP rules" in
  Arg.(value & flag & info["vip"] ~doc)

let no_use_ity =
  let doc = "(this switch should go away) in WellTyped.BaseTyping, do not use integer type annotations placed by the Core elaboration" in
  Arg.(value & flag & info["no-use-ity"] ~doc)

let use_peval =
  let doc = "(this switch should go away) run the Core partial evaluation phase" in
  Arg.(value & flag & info["use-peval"] ~doc)

let no_inherit_loc =
  let doc = "debugging: stop mucore terms inheriting location information from parents" in
  Arg.(value & flag & info["no-inherit-loc"] ~doc)

let magic_comment_char_dollar =
  let doc = "Override CN's default magic comment syntax to be \"/*\\$ ... \\$*/\"" in
  Arg.(value & flag & info ["magic-comment-char-dollar"] ~doc)

(* copied from cerberus' executable (backend/driver/main.ml) *)
let macros =
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
      Arg.(conv (parser, printer)) in
  let doc = "Adds  an  implicit  #define  into the predefines buffer which is \
             read before the source file is preprocessed." in
  Arg.(value & opt_all macro_pair [] & info ["D"; "define-macro"]
         ~docv:"NAME[=VALUE]" ~doc)

let () =
  let open Term in
  let check_t =
    const main $
      file $
      macros $
      incl_dirs $
      incl_files $
      loc_pp $
      debug_level $
      print_level $
      print_sym_nums $
      slow_smt_threshold $
      slow_smt_dir $
      no_timestamps $
      json $
      state_file $
      diag $
      lemmata $
      only $
      skip $
      csv_times $
      log_times $
      random_seed $
      solver_logging $
      output_decorated $
      astprints $
      use_vip $
      no_use_ity $
      use_peval $
      batch $
      no_inherit_loc $
      magic_comment_char_dollar
  in
  Stdlib.exit @@ Cmd.(eval (v (info "cn") check_t))
