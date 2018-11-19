open Global_ocaml

(* BEGIN TMP MLM DEBUG *)
let mlm_dbg_oc =
  open_out (Unix.getenv "HOME" ^ "/.cerb")
(* END TMP MLM DEBUG *)


(* TODO: rewrite this file from scratch... *)

let (>>=) = Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = Exception.except_return


(* == Environment variables ===================================================================== *)
let cerb_path =
    try
      Sys.getenv "CERB_PATH"
    with Not_found ->
      error "expecting the environment variable CERB_PATH set to point to the location cerberus."

let corelib_path =
  Filename.concat cerb_path "include/core"


(* == Symbol counter for the Core parser ======================================================== *)
let core_sym_counter = ref 0


(* == load the Core standard library ============================================================ *)
let load_stdlib () =
  let filepath = Filename.concat corelib_path "std.core" in
  if not (Sys.file_exists filepath) then
    error ("couldn't find the Core standard library file\n (looked at: `" ^ filepath ^ "').")
  else
    Debug_ocaml.print_debug 5 [] (fun () -> "reading Core standard library from `" ^ filepath ^ "'.");
    Core_parser_driver.parse_stdlib core_sym_counter filepath >>= function
    | Core_parser_util.Rstd (ailnames, std_funs) ->
      return (ailnames, std_funs)
    | _ ->
      error "while parsing the Core stdlib, the parser didn't recognise it as a stdlib."

(* == load the implementation file ============================================================== *)
let load_impl core_stdlib impl_name =
  let iname = Filename.concat corelib_path ("impls/" ^ impl_name ^ ".impl") in
  if not (Sys.file_exists iname) then
    error ("couldn't find the implementation file\n (looked at: `" ^ iname ^ "').")
  else
    match Core_parser_driver.parse core_sym_counter core_stdlib iname with
    | Exception.Result (Core_parser_util.Rimpl impl_map) ->
      return impl_map
    | _ ->
      error "while parsing the Core impl, the parser didn't recognise it as an impl ."

let run_pp filename lang doc =
  let fout = List.mem FOut !!cerb_conf.ppflags in
  let oc   =
    if fout then
      open_out (Filename.chop_extension (Filename.basename filename) ^ "." ^ lang)
    else Pervasives.stdout
  in
  Colour.do_colour := not fout;
  (* TODO(someday): dynamically get the width of the terminal *)
  PPrint.ToChannel.pretty 1.0 150 oc doc;
  if fout then close_out oc

let set_progress str n =
  Exception.except_fmap (fun v ->
    output_string mlm_dbg_oc (str ^ "  ");
    progress_sofar := n;
    v
  )


(* == parse a C translation-unit and elaborate it into a Core program =========================== *)
let c_frontend (core_stdlib, core_impl) filename =
    let c_preprocessing filename =
      let temp_name = Filename.temp_file (Filename.basename filename) "" in
      Debug_ocaml.print_debug 5 [] (fun () -> "C prepocessor outputed in: `" ^ temp_name ^ "`");
      if Sys.command (!!cerb_conf.cpp_cmd ^ " " ^ filename ^ " 1> " ^ temp_name (*^ " 2> /dev/null"*)) <> 0 then
        error "the C preprocessor failed";
      temp_name in
    
       Exception.except_return (c_preprocessing filename)
    |> Exception.rbind Cparser_driver.parse
    |> set_progress "CPARS" 10
    |> pass_message "1. C Parsing completed!"
    |> pass_through_test (List.mem Cabs !!cerb_conf.pps) (run_pp filename "cabs" -| Pp_cabs.pp_translation_unit true (not $ List.mem FOut !!cerb_conf.ppflags))
      (*
  |> Exception.except_fmap (fun (z, _) -> z)
    *)
(* TODO TODO TODO *)
    |> Exception.rbind (fun z ->
         (* TODO: yuck *)
(*        let saved_exec_mode_opt = current_execution_mode () in
          cerb_conf := (fun () -> { !!cerb_conf with exec_mode_opt= Some Random }) ; *)
          let ret = Cabs_to_ail.desugar !core_sym_counter
            begin
              let (ailnames, stdlib_fun_map) = core_stdlib in
              (ailnames, stdlib_fun_map, core_impl)
            end "main" z in
(*        cerb_conf := (fun () -> { (!cerb_conf()) with exec_mode_opt= saved_exec_mode_opt }) ; *)
          ret)
    
    |> set_progress "DESUG" 11
    |> pass_message "2. Cabs -> Ail completed!"
    |> begin
      if !Debug_ocaml.debug_level > 4 then
        pass_through_test (List.mem Ail !!cerb_conf.pps) (run_pp filename "ail" -| Pp_ail_ast.pp_program true true -| snd)
      else
        Exception.except_fmap (fun z -> z)
    end
    |> Exception.rbind (fun (counter, z) ->
          Exception.except_bind (ErrorMonad.to_exception (fun (loc, err) -> (loc, Errors.AIL_TYPING err))
                             (GenTyping.annotate_program z))
          (fun z -> Exception.except_return (counter, z)))
    |> Exception.except_fmap (fun (counter, (z, annots)) -> (counter, z))
    |> begin
      if !Debug_ocaml.debug_level > 4 then
        Exception.except_fmap (fun z -> z)
      else
        let pp_ail = if !Debug_ocaml.debug_level = 4 then Pp_ail_ast.pp_program_with_annot else Pp_ail_ast.pp_program true true in
        pass_through_test (List.mem Ail !!cerb_conf.pps) (run_pp filename "ail" -| pp_ail -| snd)
    end
    |> set_progress "AILTY" 12
    |> pass_message "3. Ail typechecking completed!"
    
    |> Exception.except_fmap (Translation.translate core_stdlib core_impl)
    |> set_progress "ELABO" 13
    |> pass_message "4. Translation to Core completed!"

(*
(*
      |> Exception.except_fmap Core_simpl.simplify

      |> pass_message "5. Core to Core simplication completed!"
      |> pass_through_test !print_core (run_pp -| Pp_core.pp_file) *)
*)


let core_frontend (core_stdlib, core_impl) filename =
  Core_parser_driver.parse core_sym_counter core_stdlib filename >>= function
    | Core_parser_util.Rfile (sym_main, globs, funs, tagDefs) ->
        Tags.set_tagDefs tagDefs;
        Exception.except_return (Symbol.Symbol (!core_sym_counter, None), {
           Core.main=   Some sym_main;
           Core.tagDefs= tagDefs;
           Core.stdlib= snd core_stdlib;
           Core.impl=   core_impl;
           Core.globs=  globs;
           Core.funs=   funs;
           Core.funinfo= Pmap.empty Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.Lem_pervasives.compare_method;
         })
    
    | Core_parser_util.Rstd _ ->
        error "Found no main function in the Core program"
    | Core_parser_util.Rimpl _ ->
        failwith "core_frontend found a Rimpl"

(*
let run_test (run: string -> Exhaustive_driver.execution_result) (test:Tests.test) = 
  let ex_result = run test.Tests.file_name in
  let test_result = Tests.compare_results test.Tests.expected_result ex_result in
  match test_result with
  | Exception.Result _      -> 
      print_endline (Colour.ansi_format [Colour.Green] 
                                        ("Test succeeded (" ^ test.Tests.file_name ^ ")"))
  | Exception.Exception msg -> 
      print_endline (Colour.ansi_format [Colour.Red]   
                                        ("Test failed    (" ^ test.Tests.file_name ^ "): " ^ msg))
*)


let backend sym_supply core_file args =
  match !!cerb_conf.exec_mode_opt with
    | None ->
        0
    | Some exec_mode ->
        let dr_conf = {
          Exhaustive_driver.exec_mode= exec_mode;
          Exhaustive_driver.concurrency= !!cerb_conf.concurrency;
          Exhaustive_driver.experimental_unseq= !!cerb_conf.experimental_unseq
        } in
        match !!cerb_conf.batch with
          | (`Batch | `CharonBatch) as mode ->
              Exhaustive_driver.batch_drive mode sym_supply core_file ("cmdname" :: args) dr_conf
              |> List.iter print_string;
              0
          | `NotBatch ->
              (* TODO: temporary hack for the command name *)
              Core.(match Exhaustive_driver.drive sym_supply core_file ("cmdname" :: args) dr_conf with
                | Exception.Result (Vloaded (LVspecified (OVinteger ival)) :: _) ->
                  begin
                    (* TODO: yuck *)
                    try
                      int_of_string (String_mem.string_pretty_of_integer_value ival)
                    with | _ ->
                      Debug_ocaml.warn [] (fun () -> "Return value was not a (simple) specified integer");
                      0
                  end
                | Exception.Result (cval :: _) ->
                    Debug_ocaml.warn [] (fun () -> "HELLO> " ^ String_core.string_of_value cval); 0
                | Exception.Result [] ->
                    Debug_ocaml.warn [] (fun () -> "BACKEND FOUND EMPTY RESULT");
                    0
                | Exception.Exception _ ->
                    Debug_ocaml.warn [] (fun () -> "BACKEND FOUND EXCEPTION");
                    0
              )









let pipeline filename args core_std =
  if not (Sys.file_exists filename) then
    error ("The file `" ^ filename ^ "' doesn't exist.");

  let module Param_pp_core = Pp_core.Make(struct
    let show_std = List.mem Annot !!cerb_conf.ppflags
    (*let show_location = List.mem Annot !!cerb_conf.ppflags -- TODO! *)
    let show_include = false
    let handle_location _ _ = ()
    let handle_uid _ _ = ()
  end) in
  
  begin
    if Filename.check_suffix filename ".c" then (
      Debug_ocaml.print_debug 2 [] (fun () -> "Using the C frontend");
      c_frontend core_std filename
     ) else if Filename.check_suffix filename ".core" then (
       Debug_ocaml.print_debug 2 [] (fun () -> "Using the Core frontend");
       core_frontend core_std filename
      ) else
       Exception.fail (Location_ocaml.unknown, Errors.UNSUPPORTED "The file extention is not supported")
  end >>= fun ((sym_supply : Symbol.sym UniqueId.supply), core_file) ->
  
  begin
    if !!cerb_conf.typecheck_core then
      Core_typing.typecheck_program core_file |>
        pass_message "5. Core typechecking completed!" >>= fun _ ->
      Exception.except_return ()
    else
      Exception.except_return ()
  end >>= fun _ ->

  (* TODO: for now assuming a single order comes from indet expressions *)
  let rewritten_core_file = Core_indet.hackish_order
      (if !!cerb_conf.rewrite then Core_rewrite.rewrite_file core_file else core_file) in
  
  if !!cerb_conf.rewrite && !Debug_ocaml.debug_level >= 5 then
    if List.mem Core !!cerb_conf.pps then begin
      print_endline "BEFORE CORE REWRITE:";
      run_pp filename "core" $ Pp_core.Basic.pp_file core_file;
      print_endline "===================="
    end;
  
  (* TODO: do the sequentialised properly *)
  if List.mem Core !!cerb_conf.pps then (
    if !!cerb_conf.sequentialise then begin
      Debug_ocaml.warn [] (fun () -> "The normal backend is not actually using the sequentialised Core");
      match (Core_typing.typecheck_program rewritten_core_file) with
        | Exception.Result z ->
            run_pp filename "core" $ Param_pp_core.pp_file (Core_sequentialise.sequentialise_file z);
        | Exception.Exception _ ->
            ();
    end else
      run_pp filename "core" $ Param_pp_core.pp_file rewritten_core_file;
    if !!cerb_conf.rewrite && !Debug_ocaml.debug_level >= 5 then
      print_endline "====================";
   );
  
  if !!cerb_conf.ocaml then
    Core_typing.typecheck_program rewritten_core_file
    >>= Codegen_ocaml.gen filename !!cerb_conf.ocaml_corestd sym_supply
    -| Core_sequentialise.sequentialise_file
  
  else
    if !!cerb_conf.sequentialise then begin
      Core_typing.typecheck_program rewritten_core_file >>= fun z ->
      Exception.except_return (
        backend sym_supply  (Core_run_aux.convert_file (Core_sequentialise.sequentialise_file z)) args
      )
    end
    else
      Exception.except_return (backend sym_supply rewritten_core_file args)

let gen_corestd (stdlib, impl) =
  let sym_supply = UniqueId.new_supply_from
      Symbol.instance_Enum_Enum_Symbol_sym_dict !core_sym_counter
  in
  Core_typing.typecheck_program {
    Core.main=   None;
    Core.tagDefs= Pmap.empty Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.Lem_pervasives.compare_method;
    Core.stdlib= snd stdlib;
    Core.impl=   impl;
    Core.globs=  [];
    Core.funs=   Pmap.empty Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.Lem_pervasives.compare_method;
    Core.funinfo=Pmap.empty Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.Lem_pervasives.compare_method;
  }
  >>= fun typed_core ->
    let cps_core =
      Core_opt.run Codegen_ocaml.opt_passes typed_core
      |> Cps_core.cps_transform sym_supply []
    in
    Codegen_corestd.gen (Pp_ocaml.empty_globs "coreStd")
      cps_core.Cps_core.impl cps_core.Cps_core.stdlib;
    Exception.except_return 0

let cerberus debug_level cpp_cmd impl_name exec exec_mode switches pps ppflags file_opt progress rewrite
             sequentialise fs_dump concurrency preEx args ocaml ocaml_corestd batch experimental_unseq typecheck_core
             defacto default_impl action_graph =
  Debug_ocaml.debug_level := debug_level;
  (* TODO: move this to the random driver *)
  Random.self_init ();
  set_cerb_conf cpp_cmd pps ppflags exec exec_mode progress rewrite sequentialise fs_dump concurrency preEx ocaml ocaml_corestd
    (* TODO *) QuoteStd batch experimental_unseq typecheck_core defacto default_impl action_graph;
  let prelude =
    (* Looking for and parsing the core standard library *)
    load_stdlib () >>= fun core_stdlib ->
    Debug_ocaml.print_success "0.1. - Core standard library loaded.";
    Switches.set switches;
    (* Looking for and parsing the implementation file *)
    load_impl core_stdlib impl_name >>= fun core_impl ->
    Debug_ocaml.print_success "0.2. - Implementation file loaded.";
    return (core_stdlib, core_impl)
  in
  let runM = function
    | Exception.Exception err ->
        prerr_endline (Pp_errors.to_string err);
        if progress then
          !progress_sofar
        else
          1
    | Exception.Result n ->
        if progress then
          14
        else
          n
  in
  runM $ match file_opt with
    | None ->
      if ocaml_corestd then
        prelude >>= gen_corestd
      else
        Pp_errors.fatal "no input file"
    | Some file ->
        prelude >>= pipeline file args


(* CLI stuff *)
open Cmdliner

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
  let doc = "Set the C implementation file (to be found in CERB_COREPATH/impls and excluding the .impl suffix)." in
  Arg.(value & opt string "gcc_4.9.0_x86_64-apple-darwin10.8.0" & info ["impl"] ~docv:"NAME" ~doc)

let cpp_cmd =
  let doc = "Command to call for the C preprocessing." in
  (* TODO: use to be "gcc -DCSMITH_MINIMAL -E -I " ^ cerb_path ^ "/clib -I /Users/catzilla/Applications/Sources/csmith-2.2.0/runtime" *)
  Arg.(value & opt string ("cc -E -C -nostdinc -undef -D__cerb__ -I "  ^ cerb_path ^ "/include/c/libc -I "  ^ cerb_path ^ "/include/c/posix")
             & info ["cpp"] ~docv:"CMD" ~doc)

let exec =
  let doc = "Execute the Core program after the elaboration." in
  Arg.(value & flag & info ["exec"] ~doc)

let exec_mode =
  let doc = "Set the Core evaluation mode (interactive | exhaustive | random)." in
  Arg.(value & opt (enum [(*"interactive", Smt2.Interactive; *)"exhaustive", Smt2.Exhaustive; "random", Smt2.Random]) Smt2.Random & info ["mode"] ~docv:"MODE" ~doc)

let pprints =
  let doc = "Pretty print the intermediate programs for the listed languages (ranging over {cabs, ail, core})." in
  Arg.(value & opt (list (enum ["cabs", Cabs; "ail", Ail; "core", Core])) [] & info ["pp"] ~docv:"LANG1,..." ~doc)

let ppflags =
  let doc = "Pretty print flags [annot: include location and ISO annotations, fout: output in a file]." in
  Arg.(value & opt (list (enum ["annot", Annot; "fout", FOut])) [] & info ["pp_flags"] ~doc)

let file =
  let doc = "source C or Core file" in
  Arg.(value & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)

let progress =
  let doc = "Progress mode: the return code indicate how far the source program went through the pipeline \
             [1 = total failure, 10 = parsed, 11 = desugared, 12 = typed, 13 = elaborated, 14 = executed]" in
  Arg.(value & flag & info ["progress"] ~doc)

let rewrite =
  let doc = "Activate the Core to Core transformations" in
  Arg.(value & flag & info["rewrite"] ~doc)

let sequentialise =
  let doc = "Replace all unseq() with left to right wseq(s)" in
  Arg.(value & flag & info["sequentialise"] ~doc)

let concurrency =
  let doc = "Activate the C11 concurrency" in
  Arg.(value & flag & info["concurrency"] ~doc)

let preEx =
  let doc = "only generate and output the concurrency pre-execution (activates the C11 concurrency)" in
  Arg.(value & flag & info["preEx"] ~doc)

let batch =
  let doc = "makes the execution driver produce batch friendly output" in
  Arg.(value & vflag `NotBatch & [(`Batch, info["batch"] ~doc); (`CharonBatch, info["charon-batch"] ~doc:(doc^" (for Charon)"))])

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

let default_impl =
  let doc = "run cerberus with a default implementation choice" in
  Arg.(value & flag & info["defacto_impl"] ~doc)

let action_graph =
  let doc = "create a (dot) graph with all the possible executions" in
  Arg.(value & flag & info["graph"] ~doc)

let switches =
  let doc = "list of semantics switches to turn on (see documentation for the list)" in
  Arg.(value & opt (list string) [] & info ["switches"] ~docv:"SWITCH1,..." ~doc)


(*
let concurrency_tests =
  let doc = "Runs the concurrency regression tests" in
  Arg.(value & flag & info["regression-test"] ~doc)
*)

let args =
  let doc = "List of arguments for the C program" in
  Arg.(value & opt (list string) [] & info ["args"] ~docv:"ARG1,..." ~doc)

(* entry point *)
let () =
  let cerberus_t = Term.(pure cerberus
    $ debug_level $ cpp_cmd $ impl $ exec $ exec_mode $ switches
    $ pprints $ ppflags $ file $ progress $ rewrite $ sequentialise $ fs_dump
    $ concurrency $ preEx $ args $ ocaml $ ocaml_corestd
    $ batch $ experimental_unseq $ typecheck_core $ defacto $ default_impl $ action_graph ) in
  
  (* the version is "sed-out" by the Makefile *)
  let info = Term.info "cerberus" ~version:"<<GIT-HEAD>>" ~doc:"Cerberus C semantics"  in
  match Term.eval (cerberus_t, info) with
    | `Error _ ->
        output_string mlm_dbg_oc "\n";
        close_out mlm_dbg_oc;
        exit 1
    | `Ok n ->
        output_string mlm_dbg_oc "\n";
        close_out mlm_dbg_oc;
        (* TODO: hack *)
        begin match !!cerb_conf.batch with
          | `Batch ->
              Printf.fprintf stderr "Time spent: %f seconds\n" (Sys.time ())
          | _ ->
              ()
        end;
        exit n
    | `Version
    | `Help ->
        output_string mlm_dbg_oc "\n";
        close_out mlm_dbg_oc;
        exit 0
