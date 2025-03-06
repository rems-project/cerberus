open Cerb_frontend
open Cerb_backend
open Cerb_global
open Cerb_runtime
open Pipeline

let (>>=) = Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = Exception.except_return

let io, get_progress =
  let open Pipeline in
  default_io_helpers, get_progress

let is_cheri_memory () =
  (* for compability with OCaml 4.12.0 using a local implementation of String.starts_with *)
  let starts_with ~prefix str =
    try
      String.(equal prefix (sub str 0 (length prefix)))
    with
      | Invalid_argument _ -> false in
  starts_with ~prefix:"cheri" Impl_mem.name

let frontend (conf, io) ~is_lib filename core_std =
  if not (Sys.file_exists filename) then
    error ("The file `" ^ filename ^ "' doesn't exist.");
  if Filename.check_suffix filename ".co" || Filename.check_suffix filename ".o" then
    read_core_object (conf, io) ~is_lib core_std filename
  else if Filename.check_suffix filename ".c" then
    c_frontend_and_elaboration (conf, io) core_std ~filename >>= fun (_, _, core_file) ->
    core_passes (conf, io) ~filename core_file
  else if Filename.check_suffix filename ".core" then
    core_frontend (conf, io) core_std ~filename
    >>= core_passes (conf, io) ~filename
  else
    Exception.fail (Cerb_location.unknown, Errors.UNSUPPORTED
                      "The file extention is not supported")

let create_cpp_cmd cpp_cmd nostdinc macros_def macros_undef incl_dirs incl_files nolibc =
  let libc_dirs = [in_runtime "bmc"; in_runtime "libc/include"; in_runtime "libc/include/posix"] in
  let incl_dirs = if nostdinc then incl_dirs else libc_dirs @ incl_dirs in
  let macros_def = if nolibc then macros_def else ("CERB_WITH_LIB", None) :: macros_def in
  let macros_def = if is_cheri_memory () then ("__CHERI__", None) :: macros_def else macros_def in
  String.concat " " begin
    cpp_cmd ::
    List.map (function
        | (str1, None)      -> "-D" ^ str1
        | (str1, Some str2) -> "-D" ^ str1 ^ "=" ^ str2
      ) macros_def @
    List.map (fun str -> "-U" ^ str) macros_undef @
    List.map (fun str -> "-I" ^ str) incl_dirs @
    List.map (fun str -> "-include " ^ str) (in_runtime "libc/include/builtins.h" :: incl_files)
  end

let core_libraries incl lib_paths libs =
  let lib_paths = if incl then in_runtime "libc" :: lib_paths else lib_paths in
  let libs =
    if incl then
      if Switches.is_CHERI () then
        let mname = Impl_mem.name in
        ("c-" ^ mname) :: libs
      else if Switches.(has_switch SW_inner_arg_temps) then
        "c_inner_arg_temps" :: libs
      else
        "c" :: libs
    else libs in
  List.map (fun lib ->
      true, match List.fold_left (fun acc path ->
          match acc with
          | Some _ -> acc
          | None ->
            let file = path ^ "/lib" ^ lib ^ ".co" in
            if Sys.file_exists file then Some file else None
        ) None lib_paths with
      | Some f -> f
      | None -> failwith @@ "file lib" ^ lib ^ ".co not found"
    ) libs

let print_file f =
  let ic = open_in f in
  let rec loop () =
    try print_endline @@ input_line ic; loop ()
    with End_of_file -> ()
  in loop ()

let create_executable out =
  let out = if Filename.is_relative out then Filename.concat (Unix.getcwd ()) out else out in
  let oc = open_out out in
  output_string oc "#!/bin/sh\n";
  output_string oc @@ "cerberus --nolibc --exec " ^ out ^ ".co\n";
  close_out oc;
  Unix.chmod out 0o755

let cerberus debug_level progress core_obj
             cpp_cmd syntax_only nostdinc nolibc agnostic macros macros_undef
             runtime_path_opt incl_dirs incl_files cpp_only
             link_lib_path link_core_obj
             impl_name
             exec exec_mode iso_switches switches batch concurrency
             astprints pprints ppflags pp_ail_out pp_core_out
             sequentialise_core rewrite_core typecheck_core defacto permissive ignore_bitfields
             fs_dump fs trace
             output_name
             files args_opt =
  Cerb_debug.debug_level := debug_level;
  begin if is_cheri_memory () then
    Cerb_runtime.set_package "cerberus-cheri"
  end;
  Cerb_runtime.specified_runtime := runtime_path_opt;
  let cpp_cmd =
    create_cpp_cmd cpp_cmd nostdinc macros macros_undef incl_dirs incl_files nolibc
  in
  let args = match args_opt with
    | None -> []
    | Some args -> Str.split (Str.regexp "[ \t]+") args
  in
  let ppouts =
    match pp_ail_out with
      | Some file -> [Ail, file]
      | None -> [] in
  let ppouts =
    match pp_core_out with
      | Some file -> (Core, file) :: ppouts
      | None -> ppouts in
  (* set global configuration *)
  set_cerb_conf ~backend_name:"Driver" ~exec exec_mode ~concurrency QuoteStd ~defacto ~permissive ~agnostic ~ignore_bitfields;
  let conf = { astprints; pprints; ppflags; ppouts; debug_level; typecheck_core;
               rewrite_core; sequentialise_core; cpp_cmd; cpp_stderr = true; cpp_save = None } in
  let prelude =
    (* Looking for and parsing the core standard library *)
    let switches =
      if is_cheri_memory () then begin
        Cerb_frontend.Ocaml_implementation.(set (MorelloImpl.impl));
        if not (List.mem "CHERI" switches) then
          "CHERI" :: switches
        else
          switches
      end else switches in
    begin if iso_switches then begin
      if switches <> [] then
        Cerb_debug.warn ~always:true [] (fun () -> "the --iso argument overrides --switches");
      Switches.set_iso_switches ()
    end else
      Switches.set switches
    end;
    io.pass_message (Printf.sprintf "Using '%s'" Impl_mem.name) >>
    load_core_stdlib () >>= fun core_stdlib ->
    io.pass_message "Core standard library loaded." >>
    (* Looking for and parsing the implementation file *)
    load_core_impl core_stdlib impl_name >>= fun core_impl ->
    io.pass_message "Implementation file loaded." >>
    return (core_stdlib, core_impl)
  in
  let main core_std =
    Exception.except_foldlM (fun core_files (is_lib, file) ->
      frontend ~is_lib (conf, io) file core_std >>= fun core_file ->
      return (core_file::core_files)
    ) [] (core_libraries (not nolibc && not core_obj) link_lib_path link_core_obj @ (List.map (fun z -> (false, z)) files))
  in
  let epilogue n =
    if batch = `Batch then
      Printf.fprintf stderr "Time spent: %f seconds\n" (Sys.time ());
    if progress then get_progress ()
    else n
  in
  let success = Either.Right 0 in
  let runM = function
    | Exception.Exception (loc, Errors.(DESUGAR (Desugar_UndefinedBehaviour ub))) when (batch = `Batch || batch = `CharonBatch || batch = `JsonBatch) ->
        let open Driver_ocaml in
        print_string begin
          string_of_batch_output ~json:(batch = `JsonBatch) ~is_charon:(batch = `CharonBatch) None
            ([], Undefined { ub; stderr= ""; loc })
        end;
        epilogue 1
    | Exception.Exception (loc, Errors.(AIL_TYPING (TypingError.TError_UndefinedBehaviour ub))) when (batch = `Batch || batch = `CharonBatch || batch = `JsonBatch) ->
        let open Driver_ocaml in
        print_string begin
          string_of_batch_output ~json:(batch = `JsonBatch) ~is_charon:(batch = `CharonBatch) None
            ([], Undefined { ub; stderr= ""; loc })
        end;
        epilogue 1
    | Exception.Exception err ->
        prerr_endline (Pp_errors.to_string err);
        epilogue 1
    | Exception.Result (Either.Left (batch_mode, execs)) ->
        let is_charon =
          match batch_mode with
            | `CharonBatch -> true
            | `JsonBatch -> false
            | `Batch -> false in
        let exit =
          let open Driver_ocaml in
          match execs with
            | [(_, Defined {exit= Specified n; _})] ->
                begin try
                  if is_charon then
                    Z.to_int n
                  else
                    0
                with
                  | Z.Overflow ->
                      Cerb_debug.warn [] (fun () -> "Return value overlows (wrapping it down to 255)");
                      Z .(to_int (n mod (of_int 256)))
                end
            | [(_, (Undefined _ | Error _))] ->
                1
            | _ ->
                0
          in
        let has_multiple = List.length execs > 1 in
        List.iteri (fun i (z3_strs, exec) ->
          let open Driver_ocaml in
          print_string begin
            string_of_batch_output ~json:(batch = `JsonBatch) ~is_charon
              (if has_multiple then Some i else None) (z3_strs, exec)
          end
        ) execs;
        epilogue exit
    | Exception.Result (Either.Right n) ->
        epilogue n 
  in
  runM @@ match files with
    | [] ->
      Pp_errors.fatal "no input file"
    | [file] when core_obj ->
      prelude >>= frontend (conf, io) ~is_lib:false file >>= fun core_file ->
      begin match output_name with
        | Some output_file ->
          write_core_object core_file output_file
        | None ->
          let output_file = Filename.remove_extension file ^ ".co" in
          write_core_object core_file output_file
      end;
      return success
    | files ->
      (* Run only CPP *)
      if cpp_only then
        Exception.except_foldlM (fun () filename ->
            cpp (conf, io) ~filename >>= fun processed_file ->
            print_file processed_file;
            return ()
          ) () files >>= fun () ->
        return success
      (* Dump a core object (-c) *)
      else if core_obj then
        prelude >>= fun core_std ->
        Exception.except_foldlM (fun () file ->
          frontend (conf, io) ~is_lib:false file core_std >>= fun core_file ->
          let output_file = Filename.remove_extension file ^ ".co" in
          write_core_object core_file output_file;
          return ()
          ) () files >>= fun () ->
        return success
      (* Parsing, Ail typing and stopping there *)
      else if syntax_only && List.for_all (fun z -> Filename.check_suffix z ".c") files then
        prelude >>= fun core_std ->
        Exception.except_mapM (fun filename ->
          c_frontend (conf, io) core_std ~filename
        ) files >>= fun _ ->
        return success
        (* Link and execute *)
      else
        begin if syntax_only then
          io.warn ~always:true (fun () -> "some of the translation units are Core or object files: ignoring --syntax-only")
        else
          return ()
        end >>= fun () ->
        prelude >>= main >>= begin function
          | [] -> assert false
          | f::fs ->
            Core_linking.link (f::fs)
        end >>= fun core_file ->
        if exec then
          let open Driver_ocaml in
          let () = Tags.reset_tagDefs () in (* TODO: check this *)
          let () = Tags.set_tagDefs core_file.tagDefs in
          let driver_conf = {concurrency; exec_mode; fs_dump; trace} in
          interp_backend io core_file ~args ~batch ~fs ~driver_conf
        else
          match output_name with
          | None ->
            return success
          | Some out -> begin
              if Filename.check_suffix out ".co" || Filename.check_suffix out ".o" then
                write_core_object core_file out
              else
                (write_core_object core_file (out ^ ".co"); create_executable out);
              return success
            end

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

let impl =
  let doc = "Set the C implementation file (to be found in CERB_COREPATH/impls\
             and excluding the .impl suffix)." in
  Arg.(value & opt string "gcc_4.9.0_x86_64-apple-darwin10.8.0" & info ["impl"]
         ~docv:"NAME" ~doc)

let core_obj =
  let doc = "Run frontend generating a target '.co' core object file." in
  Arg.(value & flag & info ["c"] ~doc)

let link_lib_path =
  let doc = "Adds a new library search path." in
  Arg.(value & opt_all string [] & info ["L"] ~docv:"X" ~doc)

let link_core_obj =
  let doc = "This option tells the core linker to search for lib$(docv).co \
             in the library search path." in
  Arg.(value & opt_all string [] & info ["l"] ~docv:"X" ~doc)

let output_file =
  let doc = "Write output to file." in
  Arg.(value & opt (some string) None & info ["o"] ~doc)

let cpp_cmd =
  let doc = "Command to call for the C preprocessing." in
  Arg.(value & opt string ("cc -std=c11 -E -CC -Werror -Wno-builtin-macro-redefined -nostdinc -undef -D__cerb__")
             & info ["cpp"] ~docv:"CMD" ~doc)

let cpp_only =
  let doc = "Run only the preprocessor stage." in
  Arg.(value & flag & info ["E"] ~doc)

let syntax_only =
  let doc = "Stop the pipeline after the Ail typechecking (only supported when called on .c files)" in
  Arg.(value & flag & info ["syntax-only"] ~doc)

let incl_dir =
  let doc = "Add the specified directory to the search path for the\
             C preprocessor." in
  Arg.(value & opt_all dir [] & info ["I"; "include-directory"]
         ~docv:"DIR" ~doc)

let macros =
  let doc = "Adds  an  implicit  #define  into the predefines buffer which is \
             read before the source file is preprocessed." in
  Arg.(value & opt_all macro_pair [] & info ["D"; "define-macro"]
         ~docv:"NAME[=VALUE]" ~doc)

let macros_undef =
  let doc = "Adds an implicit #undef into the predefines buffer which is read \
             before the source file is preprocessed." in
  Arg.(value & opt_all string [] & info ["U"] ~doc)

let incl_file =
  let doc = "Adds  an  implicit  #include into the predefines buffer which is \
             read before the source file is preprocessed." in
  Arg.(value & opt_all string [] & info ["include"] ~doc)

let nostdinc =
  let doc = "Do not search includes in the standard lib C directories." in
  Arg.(value & flag & info ["nostdinc"] ~doc)

let nolibc =
  let doc = "Do not search the standard system directories for include files." in
  Arg.(value & flag & info ["nolibc"] ~doc)

let runtime_path =
  let doc = "custom Cerberus runtime directory" in
  Arg.(value & opt (some string) None & info ["r";"runtime"] ~docv:"DIR" ~doc)

let agnostic =
  let doc = "Asks Cerberus to delay looking at implementation settings until as late \
             as possible. This makes the pipeline somewhat implementation agnostic." in
  Arg.(value & flag & info ["agnostic"] ~doc)

 let ignore_bitfields =
  let doc = "(DEBUG) accept and ignore bit-field width specifiers. \
             CAUTION: the constraints relating to bit-fields are NOT checked, \
             and the desugaring produces Ail struct/union types with \
             normal members. This flag will be removed when support \
             for bit-fields is added." in
  Arg.(value & flag & info ["dignore-bitfields"] ~doc)

let exec =
  let doc = "Execute the Core program after the elaboration." in
  Arg.(value & flag & info ["exec"] ~doc)

let exec_mode =
  let doc = "Set the Core evaluation mode (interactive | exhaustive | random)." in
  Arg.(value & opt (enum ["exhaustive", Exhaustive; "random", Random])
         Random & info ["mode"] ~docv:"MODE" ~doc)

let pprints =
  let open Pipeline in
  let doc = "Pretty print the intermediate programs for the listed languages \
             (ranging over {ail, core})." in
  Arg.(value & opt (list (enum ["ail", Ail; "core", Core])) [] &
       info ["pp"] ~docv:"LANG1,..." ~doc)

let astprints =
  let open Pipeline in
  let doc = "Pretty print the intermediate syntax tree for the listed languages \
             (ranging over {cabs, ail, core})." in
  Arg.(value & opt (list (enum ["cabs", Cabs; "ail", Ail; "core", Core])) [] &
       info ["ast"] ~docv:"LANG1,..." ~doc)

let fs =
  let doc = "Initialise the internal file system with the contents of the \
             directory DIR" in
  Arg.(value & opt (some string) None & info ["fs"] ~docv:"DIR" ~doc)

let ppflags =
  let open Pipeline in
  let doc = "Pretty print flags [annot: include location and ISO annotations, loc: include C source locations]." in
  Arg.(value & opt (list (enum ["annot", Annot; "loc", Loc; ])) [] &
       info ["pp_flags"] ~doc)

let pp_ail_out =
  let doc = "Write Ail pprint to a file." in
  Arg.(value & opt (some string) None & info ["pp_ail_out"] ~doc)

let pp_core_out =
  let doc = "Write Core pprint to a file." in
  Arg.(value & opt (some string) None & info ["pp_core_out"] ~doc)

let files =
  let doc = "source C or Core file" in
  Arg.(value & pos_all file [] & info [] ~docv:"FILE" ~doc)

let progress =
  let doc = "Progress mode: the return code indicate how far the source program \
             went through the pipeline \
             [1 = total failure, 10 = parsed, 11 = desugared, 12 = typed, \
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

let batch =
  let doc = "makes the execution driver produce batch friendly output" in
  Arg.(value & vflag `NotBatch & [(`Batch, info["batch"] ~doc);
                                  (`CharonBatch, info["charon-batch"] ~doc:(doc^" (for Charon)"));
                                  (`JsonBatch, info["json-batch"] ~doc:"outputs the executions in json") ])

let typecheck_core =
  let doc = "typecheck the elaborated Core program" in
  Arg.(value & flag & info["typecheck-core"] ~doc)

let defacto =
  let doc = "relax some of the ISO constraints (outside of the memory)" in
  Arg.(value & flag & info["defacto"] ~doc)

let permissive =
  let doc = "allow extensions to ISO (by default Cerberus behaves like compilers with -pedantic)" in
  Arg.(value & flag & info["permissive"] ~doc)

let fs_dump =
  let doc = "dump the file system at the end of the execution" in
  Arg.(value & flag & info["fs-dump"] ~doc)

let trace =
  let doc = "trace memory actions" in
  Arg.(value & flag & info["trace"] ~doc)

let switches =
  let doc = "list of semantics switches to turn on (see documentation for the list)" in
  Arg.(value & opt (list string) [] & info ["switches"] ~docv:"SWITCH1,..." ~doc)

let iso =
  let doc = "sets the switches corresponding to the ISO semantics (this overrides --switches if it is also present)" in
  Arg.(value & flag & info["iso"] ~doc)

let args =
  let doc = "List of arguments for the C program" in
  Arg.(value & opt (some string) None & info ["args"] ~docv:"\"ARG1 ARG2 ...\"" ~doc)

(* entry point *)
let () =
  let cerberus_t = Term.(const cerberus $ debug_level $ progress $ core_obj $
                         cpp_cmd $ syntax_only $ nostdinc $ nolibc $ agnostic $ macros $ macros_undef $
                         runtime_path $ incl_dir $ incl_file $ cpp_only $
                         link_lib_path $ link_core_obj $
                         impl $
                         exec $ exec_mode $ iso $ switches $ batch $
                         concurrency $
                         astprints $ pprints $ ppflags $ pp_ail_out $ pp_core_out $
                         sequentialise $ rewrite $ typecheck_core $ defacto $ permissive $ ignore_bitfields $
                         fs_dump $ fs $ trace $
                         output_file $
                         files $ args) in
  let version = Version.version in
  let info = Cmd.info "cerberus" ~version ~doc:"Cerberus C semantics"  in
  Stdlib.exit @@ Cmd.eval' (Cmd.v info cerberus_t)
