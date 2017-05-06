open Global_ocaml

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
    Debug_ocaml.print_debug 5 [] ("reading Core standard library from `" ^ filepath ^ "'.");
    (* An preliminary instance of the Core parser *)
    let module Core_std_parser_base = struct
      include Core_parser.Make (struct
                                 let sym_counter = core_sym_counter
                                 let mode = Core_parser_util.StdMode
                                 let std = Pmap.empty Core_parser_util._sym_compare
                               end)
(*      type token = Core_parser_util.token *)
      type result = Core_parser_util.result
    end in
    let module Core_std_parser =
      Parser_util.Make (Core_std_parser_base) (Lexer_util.Make (Core_lexer)) in
    (* TODO: yuck *)
    match Core_std_parser.parse (Input.file filepath) with
      | Exception.Result (Core_parser_util.Rstd (ailnames, std_funs)) -> (ailnames, std_funs)
      | Exception.Result _ ->
          error "while parsing the Core stdlib, the parser didn't recognise it as a stdlib."
      | Exception.Exception (loc, err) ->
          begin match err with
            | Errors.PARSER msg ->
                error ("Core parsing error @ " ^ Pp_errors.location_to_string loc  ^ ": " ^ msg)
            | _ ->
                assert false
          end


(* == load the implementation file ============================================================== *)
let load_impl core_parse impl_name =
  let iname = Filename.concat corelib_path ("impls/" ^ impl_name ^ ".impl") in
  if not (Sys.file_exists iname) then
    error ("couldn't find the implementation file\n (looked at: `" ^ iname ^ "').")
  else
    (* TODO: yuck *)
    match core_parse (Input.file iname) with
      | Exception.Result (Core_parser_util.Rimpl impl_map) ->
          impl_map
      | Exception.Result (Core_parser_util.Rfile _ | Core_parser_util.Rstd _) ->
          assert false
      | Exception.Exception err ->
          error ("[Core parsing error: impl-file]" ^ Pp_errors.to_string err)


(* use this when calling a pretty printer *)
let run_pp =
  (* TODO(someday): dynamically get the width of the terminal *)
  PPrint.ToChannel.pretty 1.0 150 Pervasives.stdout


let set_progress n =
  Exception.fmap (fun v -> progress_sofar := n; v)


(* == parse a C translation-unit and elaborate it into a Core program =========================== *)
let c_frontend f =
    let c_preprocessing (f: Input.t) =
      let temp_name = Filename.temp_file (Filename.basename $ Input.name f) "" in
      Debug_ocaml.print_debug 5 [] ("C prepocessor outputed in: `" ^ temp_name ^ "`");
      if Sys.command (!!cerb_conf.cpp_cmd ^ " " ^ Input.name f ^ " 1> " ^ temp_name (*^ " 2> /dev/null"*)) <> 0 then
        error "the C preprocessor failed";
      Input.file temp_name in
    
       Exception.except_return (c_preprocessing f)
    |> Exception.rbind Cparser_driver.parse
    |> set_progress 10
    |> pass_message "1. C Parsing completed!"
    |> pass_through_test (List.mem Cabs !!cerb_conf.pps) (run_pp -| Pp_cabs.pp_translate_unit)
    
    |> Exception.rbind (Cabs_to_ail.desugar !core_sym_counter "main")
    |> set_progress 11
    |> pass_message "2. Cabs -> Ail completed!"
(*    |> pass_through_test (List.mem Ail !!cerb_conf.pps) (run_pp -| Pp_ail.pp_program -| snd) *)
    
    |> Exception.rbind (fun (counter, z) ->
          Exception.except_bind (ErrorMonad.to_exception (fun (loc, err) -> (loc, Errors.AIL_TYPING err))
                             (GenTyping.annotate_program Annotation.concrete_annotation z))
          (fun z -> Exception.except_return (counter, z)))
    |> pass_through_test (List.mem Ail !!cerb_conf.pps) (run_pp -| Pp_ail.pp_program_with_annot -| snd)
    |> set_progress 12
    |> pass_message "3. Ail typechecking completed!"
    
    |> Exception.fmap (Translation.translate !!cerb_conf.core_stdlib !!cerb_conf.sequentialise
                         (match !!cerb_conf.core_impl_opt with Some x -> x | None -> assert false))
    |> set_progress 13
    |> pass_message "4. Translation to Core completed!"

(*
(*
      |> Exception.fmap Core_simpl.simplify

      |> pass_message "5. Core to Core simplication completed!"
      |> pass_through_test !print_core (run_pp -| Pp_core.pp_file) *)
*)

let (>>=) = Exception.except_bind

let core_frontend f =
  !!cerb_conf.core_parser f >>= function
    | Core_parser_util.Rfile (sym_main, globs, funs) ->
(* TODO: probably can remove the commmented line, now this is done by the driver *)
(*        Tags.set_tagDefs (Pmap.empty (Symbol.instance_Basic_classes_SetType_Symbol_sym_dict.Lem_pervasives.setElemCompare_method)); *)
        Exception.except_return (Symbol.Symbol (!core_sym_counter, None), {
           Core.main=   Some sym_main;
           Core.tagDefs= (Pmap.empty (Symbol.instance_Basic_classes_SetType_Symbol_sym_dict.Lem_pervasives.setElemCompare_method));
           Core.stdlib= snd !!cerb_conf.core_stdlib;
           Core.impl=   (match !!cerb_conf.core_impl_opt with Some x -> x | None -> assert false);
           Core.globs=  globs;
           Core.funs=   funs
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
    | Some Interactive ->
        print_endline "Interactive mode not yet supported";
        exit 1
    | Some (Exhaustive | Random) ->
        if !!cerb_conf.batch then
          begin
            Exhaustive_driver.batch_drive sym_supply core_file ("cmdname" :: args) !!cerb_conf;
            0
          end
        else
          
        
        (* TODO: temporary hack for the command name *)
        Core.(match Exhaustive_driver.drive sym_supply core_file ("cmdname" :: args) !!cerb_conf with
          | Exception.Result (Pexpr (_, PEval (Vloaded (LVspecified (OVinteger ival)))) :: _) ->
            begin
              (* TODO: yuck *)
              try
                int_of_string (String_mem.string_pretty_of_integer_value ival)
              with | _ ->
                Debug_ocaml.warn [] "Return value was not a (simple) specified integer";
                0
            end
          | Exception.Result (pe :: _) ->
              Debug_ocaml.warn [] ("HELLO> " ^ String_core.string_of_pexpr pe); 0
          | Exception.Result [] ->
              Debug_ocaml.warn [] "BACKEND FOUND EMPTY RESULT";
              0
          | Exception.Exception _ ->
              Debug_ocaml.warn [] "BACKEND FOUND EXCEPTION";
              0
(*
          | _ ->
              Debug_ocaml.warn "Return value was not a specified integer or was an undef/error";
              0)
*)
)









let pipeline filename args =
  if not (Sys.file_exists filename) then
    error ("The file `" ^ filename ^ "' doesn't exist.");
  
  let f = Input.file filename in
  begin
    if Filename.check_suffix filename ".c" then (
      Debug_ocaml.print_debug 2 [] "Using the C frontend";
      c_frontend f
     ) else if Filename.check_suffix filename ".core" then (
       Debug_ocaml.print_debug 2 [] "Using the Core frontend";
       core_frontend f
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
      run_pp $ Pp_core.pp_file core_file;
      print_endline "===================="
    end;
  
  (* TODO: do the sequentialised properly *)
  if List.mem Core !!cerb_conf.pps then (
    if !!cerb_conf.sequentialise then begin
      Debug_ocaml.warn [] "The normal backend is not actually using the sequentialised Core";
      match (Core_typing.typecheck_program rewritten_core_file) with
        | Exception.Result z ->
            run_pp $ Pp_core.pp_file (Core_sequentialise.sequentialise_file z);
        | Exception.Exception _ ->
            ();
    end else
      run_pp $ Pp_core.pp_file rewritten_core_file;
    if !!cerb_conf.rewrite && !Debug_ocaml.debug_level >= 5 then
      print_endline "====================";
   );
  
  if !!cerb_conf.ocaml then
    Core_typing.typecheck_program rewritten_core_file
    >>= Codegen_ocaml.gen filename !!cerb_conf.ocaml_corestd sym_supply
    -| Core_sequentialise.sequentialise_file
  else
    Exception.except_return (backend sym_supply rewritten_core_file args)

let gen_corestd stdlib impl =
  let sym_supply = UniqueId.new_supply_from
      Symbol.instance_Enum_Enum_Symbol_sym_dict !core_sym_counter
  in
  Core_typing.typecheck_program {
    Core.main=   None;
    Core.tagDefs= Pmap.empty Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.Lem_pervasives.compare_method;
    Core.stdlib= stdlib;
    Core.impl=   impl;
    Core.globs=  [];
    Core.funs=   Pmap.empty Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.Lem_pervasives.compare_method;
  }
  >>= fun typed_core ->
    let opt_core = Core_opt.run Codegen_ocaml.opt_passes typed_core in
    let cps_core = Cps_core.cps_transform sym_supply opt_core [] in
    Codegen_corestd.gen [] cps_core.Cps_core.impl cps_core.Cps_core.stdlib;
    Exception.except_return 0

let cerberus debug_level cpp_cmd impl_name exec exec_mode pps file_opt progress rewrite
             sequentialise concurrency preEx args ocaml ocaml_corestd batch experimental_unseq typecheck_core =
  Debug_ocaml.debug_level := debug_level;
  (* TODO: move this to the random driver *)
  Random.self_init ();
  
  (* Looking for and parsing the core standard library *)
  let core_stdlib = load_stdlib () in
  Debug_ocaml.print_success "0.1. - Core standard library loaded.";
  
  (* An instance of the Core parser knowing about the stdlib functions we just parsed *)
  let module Core_parser_base = struct
    include Core_parser.Make (struct
        let sym_counter = core_sym_counter
        let mode = Core_parser_util.ImplORFileMode
        let std = List.fold_left (fun acc ((Symbol.Symbol (_, Some str)) as fsym, _) ->
          let std_pos = {Lexing.dummy_pos with Lexing.pos_fname= "core_stdlib"} in
          Pmap.add (str, (std_pos, std_pos)) fsym acc
        ) (Pmap.empty Core_parser_util._sym_compare) $ Pmap.bindings_list (snd core_stdlib)
      end)
    type result = Core_parser_util.result
  end in
  let module Core_parser =
    Parser_util.Make (Core_parser_base) (Lexer_util.Make (Core_lexer)) in
  set_cerb_conf cpp_cmd pps core_stdlib None exec exec_mode Core_parser.parse progress rewrite
    sequentialise concurrency preEx ocaml ocaml_corestd (* TODO *) RefStd batch experimental_unseq typecheck_core;
  
  (* Looking for and parsing the implementation file *)
  let core_impl = load_impl Core_parser.parse impl_name in
  Debug_ocaml.print_success "0.2. - Implementation file loaded.";

  set_cerb_conf cpp_cmd pps ((*Pmap.union impl_fun_map*) core_stdlib) (Some core_impl) exec
    exec_mode Core_parser.parse progress rewrite sequentialise concurrency preEx ocaml ocaml_corestd
    (* TODO *) RefStd batch experimental_unseq typecheck_core;
  (* Params_ocaml.setCoreStdlib core_stdlib; *)
  
(*
  if !!cerb_conf.concurrency_tests then
    (* Running the concurrency regression tests *)
    let tests = Tests.get_tests in
    List.iter (run_test (fun z -> pipeline z args)) tests
  else 
*)
  match file_opt with
    | None ->
      if !!cerb_conf.ocaml_corestd then
        match gen_corestd (snd core_stdlib) core_impl with
          | Exception.Exception err ->
              prerr_endline (Pp_errors.to_string err);
                exit 1
          | Exception.Result n -> n

      else (
        (* TODO: make this print the help *)
        prerr_endline "No filename given";
        exit 1
      )
    | Some file ->
        match pipeline file args with
          | Exception.Exception err ->
              prerr_endline (Pp_errors.to_string err);
              if progress then
                exit !progress_sofar
              else
                exit 1
          | Exception.Result n ->
              if progress then
                14
              else
                n

let gen_ocaml_corestd debug_level impl_name =
  Debug_ocaml.debug_level := debug_level;
  (* TODO: move this to the random driver *)
  Random.self_init ();
  
  (* Looking for and parsing the core standard library *)
  let core_stdlib = snd (load_stdlib ()) in
  Debug_ocaml.print_success "0.1. - Core standard library loaded.";
  
  (* An instance of the Core parser knowing about the stdlib functions we just parsed *)
  let module Core_parser_base = struct
    include Core_parser.Make (struct
        let sym_counter = core_sym_counter
        let mode = Core_parser_util.ImplORFileMode
        let std = List.fold_left (fun acc ((Symbol.Symbol (_, Some str)) as fsym, _) ->
          let std_pos = {Lexing.dummy_pos with Lexing.pos_fname= "core_stdlib"} in
          Pmap.add (str, (std_pos, std_pos)) fsym acc
        ) (Pmap.empty Core_parser_util._sym_compare) $ Pmap.bindings_list (core_stdlib)
      end)
    type result = Core_parser_util.result
  end in
  let module Core_parser =
    Parser_util.Make (Core_parser_base) (Lexer_util.Make (Core_lexer)) in
  
  (* Looking for and parsing the implementation file *)
  let core_impl = load_impl Core_parser.parse impl_name in
  Debug_ocaml.print_success "0.2. - Implementation file loaded.";

  ()

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
  Arg.(value & opt string ("cc -E -nostdinc -undef -I "  ^ cerb_path ^ "/include/c/libc -I "  ^ cerb_path ^ "/include/c/posix")
             & info ["cpp"] ~docv:"CMD" ~doc)

let exec =
  let doc = "Execute the Core program after the elaboration." in
  Arg.(value & flag & info ["exec"] ~doc)

let exec_mode =
  let doc = "Set the Core evaluation mode (interactive | exhaustive | random)." in
  Arg.(value & opt (enum ["interactive", Interactive; "exhaustive", Exhaustive; "random", Random]) Random & info ["mode"] ~docv:"MODE" ~doc)

let pprints =
  let doc = "Pretty print the intermediate programs for the listed languages (ranging over {cabs, ail, core})." in
  Arg.(value & opt (list (enum ["cabs", Cabs; "ail", Ail; "core", Core])) [] & info ["pp"] ~docv:"LANG1,..." ~doc)

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
  let doc = "Replace all unseq() with left to righ wseq(s)" in
  Arg.(value & flag & info["sequentialise"] ~doc)

let concurrency =
  let doc = "Activate the C11 concurrency" in
  Arg.(value & flag & info["concurrency"] ~doc)

let preEx =
  let doc = "only generate and output the concurrency pre-execution (activates the C11 concurrency)" in
  Arg.(value & flag & info["preEx"] ~doc)

let batch =
  let doc = "makes the execution driver produce batch friendly output" in
  Arg.(value & flag & info["batch"] ~doc)

let experimental_unseq =
  let doc = "use a new (experimental) semantics for unseq() in Core_run" in
  Arg.(value & flag & info["experimental-unseq"] ~doc)

let typecheck_core =
  let doc = "typecheck the elaborated Core program" in
  Arg.(value & flag & info["typecheck-core"] ~doc)

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
  let cerberus_t = Term.(pure cerberus $ debug_level $ cpp_cmd $ impl $ exec $ exec_mode $ pprints $ file $ progress $ rewrite $
                         sequentialise $ concurrency $ preEx $ args $ ocaml $ ocaml_corestd $ batch $ experimental_unseq $ typecheck_core) in


  let info       = Term.info "cerberus" ~version:"<<HG-IDENTITY>>" ~doc:"Cerberus C semantics"  in (* the version is "sed-out" by the Makefile *)
  match Term.eval (cerberus_t, info) with
    | `Error _ ->
        exit 1
    | `Ok n ->
        exit n
    | `Version
    | `Help ->
        exit 0
