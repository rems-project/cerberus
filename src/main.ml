open Global_ocaml

(* == Environment variables ===================================================================== *)
let cerb_path =
    try
      Sys.getenv "CERB_PATH"
    with Not_found ->
      error "expecting the environment variable CERB_PATH set to point to the location cerberus."

let corelib_path =
  Filename.concat cerb_path "corelib"


(* == Symbol counter for the Core parser ======================================================== *)
let core_sym_counter = ref 0


(* == load the Core standard library ============================================================ *)
let load_stdlib () =
  let filepath = Filename.concat corelib_path "std.core" in
  if not (Sys.file_exists filepath) then
    error ("couldn't find the Core standard library file\n (looked at: `" ^ filepath ^ "').")
  else
    Debug.print_debug 5 ("reading Core standard library from `" ^ filepath ^ "'.");
    (* An preliminary instance of the Core parser *)
    let module Core_std_parser_base = struct
      include Core_parser.Make (struct
                                 let sym_counter = core_sym_counter
                                 let std = Pmap.empty Core_parser_util._sym_compare
                               end)
      type token = Core_parser_util.token
      type result = Core_parser_util.result
    end in
    let module Core_std_parser =
      Parser_util.Make (Core_std_parser_base) (Lexer_util.Make (Core_lexer)) in
    (* TODO: yuck *)
    match Core_std_parser.parse (Input.file filepath) with
      | Exception.Result (Core_parser_util.Rstd z) -> z
      | Exception.Result _ ->
          error "while parsing the Core stdlib, the parser didn't recognise it as a stdlib."
      | Exception.Exception (loc, Errors.PARSER msg) ->
          error ("Core parsing error @ " ^ Pp_errors.location_to_string loc  ^ ": " ^ msg)


(* == load the implementation file ============================================================== *)
let load_impl core_parse impl_name =
  let iname = Filename.concat corelib_path ("impls/" ^ impl_name ^ ".impl") in
  if not (Sys.file_exists iname) then
    error ("couldn't find the implementation file\n (looked at: `" ^ iname ^ "').")
  else
    (* TODO: yuck *)
    match core_parse (Input.file iname) with
      | Exception.Result (Core_parser_util.Rimpl (impl_map, fun_map)) ->
          (fun_map, impl_map)
      | Exception.Exception err ->
          error ("[Core parsing error: impl-file]" ^ Pp_errors.to_string err)


(* use this when calling a pretty printer *)
let run_pp =
    PPrint.ToChannel.pretty 40.0 80 Pervasives.stdout


let set_progress n =
  Exception.fmap (fun v -> progress_sofar := n; v)


(* == parse a C translation-unit and elaborate it into a Core program =========================== *)
let c_frontend f =
    let c_preprocessing (f: Input.t) =
      let temp_name = Filename.temp_file (Filename.basename $ Input.name f) "" in
      Debug.print_debug 5 ("C prepocessor outputed in: `" ^ temp_name ^ "`");
      if Sys.command (!!cerb_conf.cpp_cmd ^ " " ^ Input.name f ^ " > " ^ temp_name ^ " 2> /dev/null") <> 0 then
        error "the C preprocessor failed";
      Input.file temp_name in
    
       Exception.return2 (c_preprocessing f)
    |> Exception.fmap Cparser_driver.parse
    |> set_progress 10
    |> pass_message "1. C Parsing completed!"
    |> pass_through_test (List.mem Cabs !!cerb_conf.pps) (run_pp -| Pp_cabs.pp_translate_unit)
    
    |> Exception.rbind (Cabs_to_ail.desugar !core_sym_counter "main")
    |> set_progress 11
    |> pass_message "2. Cabs -> Ail completed!"
(*    |> pass_through_test (List.mem Ail !!cerb_conf.pps) (run_pp -| Pp_ail.pp_program -| snd) *)
    
    |> Exception.rbind (fun (counter, z) ->
          Exception.bind2 (ErrorMonad.to_exception (fun (loc, err) -> (loc, Errors.AIL_TYPING err))
                             (GenTyping.annotate_program Annotation.concrete_annotation z))
          (fun z -> Exception.return2 (counter, z)))
    |> pass_through_test (List.mem Ail !!cerb_conf.pps) (run_pp -| Pp_ail.pp_program_with_annot -| snd)
    |> set_progress 12
    |> pass_message "3. Ail typechecking completed!"
    
    |> Exception.fmap (Translation.translate !!cerb_conf.core_stdlib !!cerb_conf.core_impl)
    |> set_progress 13
    |> pass_message "4. Translation to Core completed!"
(*



      
      
(*
      |> Exception.fmap Core_simpl.simplify

      |> pass_message "5. Core to Core simplication completed!"
      |> pass_through_test !print_core (run_pp -| Pp_core.pp_file) *)
*)

let (>>=) = Exception.bind2


let core_frontend f =
  !!cerb_conf.core_parser f >>= function
    | Rfile (sym_main, globs, funs) ->
        Exception.return2 (Symbol.Symbol (!core_sym_counter, None), {
           Core.main=   sym_main;
           Core.stdlib= !!cerb_conf.core_stdlib;
           Core.impl=   !!cerb_conf.core_impl;
           Core.globs=  globs;
           Core.funs=   funs
         })
    
    | Rstd _ ->
        error "Found no main function in the Core program"
    | Rimpl _ ->
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
(*
    | Some Interactive ->
        print_endline "Interactive mode not yet supported";
        exit 1
*)
    | Some (Exhaustive | Random | Interactive) ->
        (* TODO: temporary hack for the command name *)
        match Exhaustive_driver.drive sym_supply core_file ("cmdname" :: args) (!!cerb_conf.concurrency) with
          | Exception.Result (pe::_ | [pe]) ->
            begin
              (* TODO: yuck *)
              try
                int_of_string (String_core.string_of_pexpr pe)
              with | _ ->
                0
            end
          | _ ->
              0









let pipeline filename args =
  if not (Sys.file_exists filename) then
    error ("The file `" ^ filename ^ "' doesn't exist.");
  
  let f = Input.file filename in
  begin
    if Filename.check_suffix filename ".c" then (
      Debug.print_debug 2 "Using the C frontend";
      c_frontend f
     ) else if Filename.check_suffix filename ".core" then (
       Debug.print_debug 2 "Using the Core frontend";
       core_frontend f
      ) else
       Exception.fail0 (Location_ocaml.unknown, Errors.UNSUPPORTED "The file extention is not supported")
  end >>= fun (sym_supply, core_file) ->
  
  (* TODO: for now assuming a single order comes from indet expressions *)
  let rewritten_core_file = Core_indet.hackish_order
      (if !!cerb_conf.no_rewrite then core_file else Core_rewrite.rewrite_file core_file) in
  
  if !Debug.debug_level >= 5 then
    if List.mem Core !!cerb_conf.pps then begin
      print_endline "BEFORE CORE REWRITE:";
      run_pp $ Pp_core.pp_file core_file;
      print_endline "===================="
    end;
  
  if List.mem Core !!cerb_conf.pps then (
    run_pp $ Pp_core.pp_file rewritten_core_file;
    if !Debug.debug_level >= 5 then
      print_endline "====================";
   );
  
  
  Exception.return2 (backend sym_supply rewritten_core_file args)


let cerberus debug_level cpp_cmd impl_name exec exec_mode pps file_opt progress no_rewrite concurrency preEx args =
  Debug.debug_level := debug_level;
  (* TODO: move this to the random driver *)
  Random.self_init ();
  
  (* Looking for and parsing the core standard library *)
  let core_stdlib = load_stdlib () in
  Debug.print_success "0.1. - Core standard library loaded.";
  
  (* An instance of the Core parser knowing about the stdlib functions we just parsed *)
  let module Core_parser_base = struct
    include Core_parser.Make (struct
        let sym_counter = core_sym_counter
        let std = List.fold_left (fun acc ((Symbol.Symbol (_, Some str)) as fsym, _) ->
          let std_pos = {Lexing.dummy_pos with pos_fname= "core_stdlib"} in
          Pmap.add (str, (std_pos, std_pos)) fsym acc
        ) (Pmap.empty Core_parser_util._sym_compare) $ Pmap.bindings_list core_stdlib
      end)
    type token = Core_parser_util.token
    type result = Core_parser_util.result
  end in
  let module Core_parser =
    Parser_util.Make (Core_parser_base) (Lexer_util.Make (Core_lexer)) in
  
  (* Looking for and parsing the implementation file *)
  let (impl_fun_map, core_impl) = load_impl Core_parser.parse impl_name in
  Debug.print_success "0.2. - Implementation file loaded.";
  
  set_cerb_conf cpp_cmd pps (Pmap.union impl_fun_map core_stdlib) core_impl exec exec_mode Core_parser.parse progress no_rewrite concurrency preEx (* TODO *) RefStd;
  
(*
  if !!cerb_conf.concurrency_tests then
    (* Running the concurrency regression tests *)
    let tests = Tests.get_tests in
    List.iter (run_test (fun z -> pipeline z args)) tests
  else 
*)
  match file_opt with
    | None ->
        (* TODO: make this print the help *)
        prerr_endline "No filename given";
        exit 1
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



(* CLI stuff *)
open Cmdliner

let debug_level =
  let doc = "Set the debug message level to $(docv) (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let impl =
  let doc = "Set the C implementation file (to be found in CERB_COREPATH/impls and excluding the .impl suffix)." in
  Arg.(value & opt string "gcc_4.9.0_x86_64-apple-darwin10.8.0" & info ["impl"] ~docv:"NAME" ~doc)

let cpp_cmd =
  let doc = "Command to call for the C preprocessing." in
  Arg.(value & opt string ("gcc -DCSMITH_MINIMAL -E -I " ^ cerb_path ^ "/clib -I /Users/catzilla/Applications/Sources/csmith-2.2.0/runtime")
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

let no_rewrite =
  let doc = "Desactivate the Core to Core transformations" in
  Arg.(value & flag & info["no_rewrite"] ~doc)

let concurrency =
  let doc = "Activate the C11 concurrency" in
  Arg.(value & flag & info["concurrency"] ~doc)

let preEx =
  let doc = "only generate and output the concurrency pre-execution (activates the C11 concurrency)" in
  Arg.(value & flag & info["preEx"] ~doc)

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
  let cerberus_t = Term.(pure cerberus $ debug_level $ cpp_cmd $ impl $ exec $ exec_mode $ pprints $ file $ progress $ no_rewrite $
                         concurrency $ preEx $ args) in
  let info       = Term.info "cerberus" ~version:"8a716e356f94+ tip" ~doc:"Cerberus C semantics"  in (* the version is "sed-out" by the Makefile *)
  match Term.eval (cerberus_t, info) with
    | `Error _ ->
        exit 1
    | `Ok n ->
        exit n
    | _ ->
        exit 0











(* OLD *)

(*

(* command-line options *)
let impl_file        = ref ""

let print_version    = ref false
let print_cabs       = ref false
let print_ail        = ref false
let print_core       = ref false
let execute          = ref false
(* OLD: let execution_mode   = ref Core_run.E.Exhaustive *)
let sb_graph         = ref false
let skip_core_tcheck = ref false (* TODO: this is temporary, until I fix the typechecker (...) *)

let print_trace = ref false

(* Test mode of Kyndylan *)
let testing = ref false


(* command-line handler *)
let options = Arg.align [
  ("--impl",    Arg.Set_string impl_file          , "<name> Select an implementation definition");
  ("--debug",   Arg.Set_int Boot_ocaml.debug_level, "       Set the debug noise level (default: 0 = nothing)");
  ("--test",    Arg.Set testing                   , "       Activate Kyndylan's test mode");
  
  (* Core backend options *)
  ("--skip-core-tcheck", Arg.Set skip_core_tcheck,                                  "       Do not run the Core typechecker");
  ("--execute",          Arg.Set execute,                                           "       Execute the Core program");
(* OLD:   ("-r",                 Arg.Unit (fun () -> execution_mode := Core_run.E.Random ), "       Randomly choose a single execution path"); *)
  ("--sb-graph",         Arg.Set sb_graph,                                          "       Generate dot graphs of the sb orders");
  
  (* printing options *)
  ("--version", Arg.Set print_version, "       Print the mercurial version id");
  ("--pcabs",   Arg.Set print_cabs   , "       Pretty-print the Cabs intermediate representation");
  ("--pail",    Arg.Set print_ail    , "       Pretty-print the Ail intermediate representation");
  ("--pcore",   Arg.Set print_core   , "       Pretty-print the Code generated program");
  ("--trace",   Arg.Set print_trace  , "       Print the execute trace at the end")
]
let usage = "Usage: csem [OPTIONS]... [FILE]...\n"




(* some block functions used by the pipeline *)
let pass_through        f = Exception.fmap (fun v ->           f v        ; v)
let pass_through_test b f = Exception.fmap (fun v -> if b then f v else (); v)
let pass_message      m   = Exception.fmap (fun v -> debug_print (Colour.ansi_format [Colour.Green] m); v)
let return_none m         = Exception.bind0 m (fun _ -> Exception.return0 None)
let return_empty m        = Exception.bind0 m (fun _ -> Exception.return0 [])

let return_value m        = Exception.bind0 m (fun _ -> Exception.return0 [])


(* WIP
let catch_result m =
  match m with
  | Exception.Result [[(Undefined.Defined (Core.Econst (Cmm_aux.Cint n), _), _)]] ->
      exit (Nat_big_num.to_int n)
  | Exception.Result _ ->
     debug_print "[Main.catch_result] returning a fake return code";
     exit 0
  | Exception.Exception msg ->
      print_endline (Colour.ansi_format [Colour.Red] (Pp_errors.to_string msg))
*)


(* use this when calling a pretty printer *)
let run_pp =
    PPrint.ToChannel.pretty 40.0 80 Pervasives.stdout


(* WIP
(* for given traces: generated a temporary .dot file, call dot2tex on it and then pdflatex *)
let write_graph fname ts =
  debug_print (Colour.ansi_format [Colour.Green] "[generating the pdf of the execution-graph(s)]");
  
(*  let dot = List.fold_left (fun acc (n, (_, t)) -> *)
  let graphs = List.map (fun (i, (_, st)) ->
    Boot_pprint.to_plain_string $ Pp_sb.pp i (Sb.simplify0 $ Sb.extract2 st)
(*
    match u_t with
      | (Undefined.Defined _, st) ->
          
      | (Undefined.Undef _, st) ->
          acc
      | (Undefined.Error, st) ->
          acc
*)
  ) (Global.numerote ts) in
  
  let (tex_name, tex_chan) = Filename.open_temp_file fname ".tex" in
  
  output_string tex_chan
    "\\documentclass{article}\n\\usepackage[x11names,rgb,svgnames]{xcolor}\n\\usepackage[utf8]{inputenc}\n\\usepackage{tikz}\n\\usetikzlibrary{snakes,arrows,shapes}\n\\usepackage{amsmath}\n\\usepackage[active,tightpage]{preview}\n\\PreviewEnvironment{tikzpicture}\n\\setlength\\PreviewBorder{0pt}\n\\begin{document}\n\\pagestyle{empty}\n";
  close_out tex_chan;
  
  List.iter (fun g ->
    let (temp_name, temp_chan) = Filename.open_temp_file fname "" in
    debug_print (Colour.ansi_format [Colour.Blue] $ "Using temporary .dot file: " ^ temp_name);
    output_string temp_chan g;
    close_out temp_chan;
    (* TODO: using /dev/null here probably only work on Unix-like systems? *)
    if Sys.command ("dot2tex --figonly -fpgf -tmath --autosize " ^ temp_name ^ " >> " ^ tex_name) <> 0 then
      prerr_endline $ Colour.ansi_format [Colour.Red] "WARNING: an error occured while trying to generate a tex file for an execution-graph."
  ) graphs;
  
  let tex_chan = open_out_gen [Open_append] 0 tex_name in
  output_string tex_chan "\\end{document}\n";
  close_out tex_chan;
  
  if Sys.command ("pdflatex -halt-on-error --jobname=" ^ fname ^ " " ^ tex_name ^ " > /dev/null") <> 0 then
    prerr_endline $ Colour.ansi_format [Colour.Red] "WARNING: an error occured while trying to generate the pdf for the sb-graph."
  else
    (Sys.remove (fname ^ ".aux"); Sys.remove (fname ^ ".log"))
*)




let core_sym_counter = ref 0




(* load the Core standard library *)
let load_stdlib csemlib_path =
  let fname = Filename.concat csemlib_path "corelib/std.core" in
  if not (Sys.file_exists fname) then
    error $ "couldn't find the Core standard library file\n (looked at: `" ^ fname ^ "'."
  else
    Boot_ocaml.dprint ("reading Core stdlib from `"^ fname ^ "'.");
    (* An preliminary instance of the Core parser *)
    let module Core_std_parser_base = struct
      include Core_parser.Make (struct
                                 let sym_counter = core_sym_counter
                                 let std = Pmap.empty compare
                               end)
      type token = Core_parser_util.token
      type result = Core_parser_util.result
    end in
    let module Core_std_parser =
      Parser_util.Make (Core_std_parser_base) (Lexer_util.Make (Core_lexer)) in
    (* TODO: yuck *)
    match Core_std_parser.parse (Input.file fname) with
      | Exception.Result (Core_parser_util.Rstd z) -> z
      | _ -> error "(TODO_MSG) found an error while parsing the Core stdlib."

let load_impl core_parse csemlib_path =
    if !impl_file = "" then 
      error "expecting an implementation to be specified (using --impl <name>)."
    else
      let iname = Filename.concat csemlib_path ("corelib/impls/" ^ !impl_file ^ ".impl") in
      if not (Sys.file_exists iname) then
        error $ "couldn't find the implementation file\n (looked at: `" ^ iname ^ "'."
      else
      (* TODO: yuck *)
        match core_parse (Input.file iname) with
          | Exception.Result (Core_parser_util.Rimpl z) -> z
          | Exception.Exception err -> error $ "[Core parsing error: impl-file]" ^ Pp_errors.to_string err


let pipeline stdlib impl core_parse file_name =
  let frontend m =
    let c_frontend m =
      (* Calling a C preprocessor before running the parser
         (TODO: the choice of the compiler shouldn't be hardcoded) *)
      let c_preprocessing (f: Input.t) =
        let temp_name = Filename.temp_file (Filename.basename $ Input.name f) "" in
        (* TODO: add an command line option for custom include directories, for now
           I hardcode the location of csmith on AddaX *)
        if Sys.command ("gcc-4.8 -DCSMITH_MINIMAL -E -I $CSEMLIB_PATH/clib -I /Users/catzilla/Applications/csmith-2.1.0/runtime " ^
                           Input.name f ^ " > " ^ temp_name) <> 0 then
          error "the C preprocessor failed";
        Input.file temp_name in
          Exception.return0 (c_preprocessing m)
      |> Exception.fmap Cparser_driver.parse
      |> pass_message "1. Parsing completed!"
      |> pass_through_test !print_cabs (run_pp -| Pp_cabs0.pp_file)

      |> Exception.rbind (Cabs_to_ail.desugar "main")
      |> pass_message "2. Cabs -> Ail completed!"
      |> pass_through_test !print_ail (run_pp -| Pp_ail.pp_program -| snd)


(*      |> Exception.rbind Ail_typing.annotate *)


      |> Exception.rbind (fun (counter, z) ->
            Exception.bind0 (ErrorMonad.to_exception (GenTyping.annotate_program Annotation.concrete_annotation z))
                            (fun z -> Exception.return0 (counter, z))
          )
      |> pass_message "3. Ail typechecking completed!"
      
      
      |> Exception.fmap (Translation.translate stdlib impl)
      |> pass_message "4. Translation to Core completed!"
      |> pass_through_test !print_core (run_pp -| Pp_core.pp_file)
(*
      |> Exception.fmap Core_simpl.simplify

      |> pass_message "5. Core to Core simplication completed!"
      |> pass_through_test !print_core (run_pp -| Pp_core.pp_file) *) in
    
    let core_frontend m =
          core_parse m
      |> Exception.fmap (function
            | Core_parser_util.Rfile (a_main, funs) ->
              { Core.main= a_main; Core.stdlib= stdlib; Core.impl= impl; Core.globs= [(* TODO *)];Core.funs= funs }
            | _ -> assert false)
      |> pass_message "1-4. Parsing completed!"
      |> pass_through_test !print_core (run_pp -| Pp_core.pp_file) in
    if      Filename.check_suffix file_name ".c"    then (debug_print "Cmulator mode"    ; c_frontend    m)
    else if Filename.check_suffix file_name ".core" then (debug_print "Core runtime mode"; core_frontend m)
                                                    else Exception.fail (Location_ocaml.unknowned, Errors.UNSUPPORTED "The file extention is not supported") in
  let core_backend m =
(*
    ((m
    >?> !skip_core_tcheck)
      (pass_message "5. Skipping Core's typechecking")
      (fun m ->
            Exception.rbind Core_typing.typecheck m
        |> pass_message "5. Core's typechecking completed!")
    >?> !execute)
 *)
    (m
    >?> !execute)
      (fun m ->
        (pass_message "6. Enumerating indet orders:" m
        |> Exception.rbind Core_indet.order
        |> pass_message "7. Now running:"
	>?> !testing)
	  (* TODO: this is ridiculous *)
	  (Exception.rbind (Exception.map_list (fun (_,f) -> Core_run.run0 !execution_mode f)))
	  (Exception.rbind
             (Exception.map_list
		(fun (n,f) -> Core_run.run0 !execution_mode f
                              |> pass_message ("SB order #" ^ string_of_int n)
                              |> pass_through (Pp_run.pp_traces !print_trace)
(* WIP                             |> pass_through_test !sb_graph (write_graph file_name) *)
(*                              |> return_empty *)
		)
	     )
	  )
      )
      return_empty in
  
  file_name
  |> Input.file
  |> frontend
  |> core_backend
  
  

let run_test stdlib impl core_parse (test:Tests.test) = 
  let ex_result = pipeline stdlib impl core_parse test.Tests.file_name in
  let test_result = Tests.compare_results test.Tests.expected_result ex_result in
  match test_result with
  | Exception.Result _      -> print_endline (Colour.ansi_format [Colour.Green] ("Test succeeded (" ^ test.Tests.file_name ^ ")"))
  | Exception.Exception msg -> print_endline (Colour.ansi_format [Colour.Red]   ("Test failed    (" ^ test.Tests.file_name ^ "): " ^ msg))



(* the entry point *)
let () =
  (* this is for the random execution selection mode *)
  Random.self_init ();
  
  (* TODO: yuck *)
  let file = ref "" in
  Arg.parse options (fun z -> file := z) usage;
  
  if !print_version then print_endline "Csem (hg version: 8a716e356f94+ tip)"; (* this is "sed-out" by the Makefile *)
  
  
  let csemlib_path =
    try
      Sys.getenv "CSEMLIB_PATH"
    with Not_found ->
      error "expecting the environment variable CSEMLIB_PATH to point to the location of std.core." in
  
  (* Looking for and parsing the core standard library *)
  let stdlib = load_stdlib csemlib_path in
  debug_print (Colour.ansi_format [Colour.Green] "0.1. - Core standard library loaded.");
  
  (* An instance of the Core parser knowing about the stdlib functions we just parsed *)
  let module Core_parser_base = struct
    include Core_parser.Make (struct
        let sym_counter = core_sym_counter
        let std = List.fold_left (fun acc ((Symbol.Symbol (_, Some fname)) as fsym, _) ->
          Pmap.add fname fsym acc
        ) (Pmap.empty compare) $ Pmap.bindings_list stdlib
      end)
    type token = Core_parser_util.token
    type result = Core_parser_util.result
  end in
  let module Core_parser =
    Parser_util.Make (Core_parser_base) (Lexer_util.Make (Core_lexer)) in
  
  (* Looking for and parsing the implementation file *)
  let impl = load_impl Core_parser.parse csemlib_path in
  debug_print (Colour.ansi_format [Colour.Green] "0.2. - Implementation file loaded.");
  
(* WIP

  if !testing then
    List.iter (run_test stdlib impl Core_parser.parse) Tests.get_tests
  else
    (catch_result -| pipeline stdlib impl Core_parser.parse) !file;
*)
*)
