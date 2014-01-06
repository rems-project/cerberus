open Global

let ($) f x = f x
let (-|) f g x = f (g x)
let (>|>) x f = f x
let (>?>) x b f g = if b then f x else g x


(* use this to print a halting error message *)
let error str =
  prerr_endline $ Colour.ansi_format [Colour.Red] ("ERROR: " ^ str);
  exit 1


(* command-line options *)
let files            = ref [] (* TODO: now we seem to only execute single files. *)
let impl_file        = ref ""

let print_cabs       = ref false
let print_ail        = ref false
let print_core       = ref false
let execute          = ref false
let random_mode      = ref Core_run.E.Exhaustive
let sb_graph         = ref false
let skip_core_tcheck = ref false (* TODO: this is temporary, until I fix the typechecker (...) *)

(* Test mode of Kyndylan *)
let testing = ref false


(* command-line handler *)
let options = Arg.align [
  ("--impl",  Arg.Set_string impl_file          , "<name> Select an implementation definition");
  ("--debug", Arg.Set_int Boot_ocaml.debug_level, "       Set the debug noise level (default: 0 = nothing)");
  ("--test",  Arg.Set testing                   , "       Activate Kyndylan's test mode");
  
  (* Core backend options *)
  ("--skip-core-tcheck", Arg.Set skip_core_tcheck,                               "       Do not run the Core typechecker");
  ("--execute",          Arg.Set execute,                                        "       Execute the Core program");
  ("-r",                 Arg.Unit (fun () -> random_mode := Core_run.E.Random ), "       Randomly choose a single execution path"); 
  ("--sb-graph",         Arg.Set sb_graph,                                       "       Generate dot graphs of the sb orders");
  
  (* printing options *)
  ("--pcabs", Arg.Set print_cabs, "       Pretty-print the Cabs intermediate representation");
  ("--pail",  Arg.Set print_ail,  "       Pretty-print the Ail intermediate representation");
  ("--pcore", Arg.Set print_core, "       Pretty-print the Code generated program")
]
let usage = "Usage: csem [OPTIONS]... [FILE]...\n"


let debug_print str =
  if !Boot_ocaml.debug_level > 0 then
    print_endline str


(* some block functions used by the pipeline *)
let pass_through        f = Exception.fmap0 (fun v ->           f v        ; v)
let pass_through_test b f = Exception.fmap0 (fun v -> if b then f v else (); v)
let pass_message      m   = Exception.fmap0 (fun v -> debug_print (Colour.ansi_format [Colour.Green] m); v)
let return_none m         = Exception.bind0 m (fun _ -> Exception.return2 None)
let return_empty m        = Exception.bind0 m (fun _ -> Exception.return2 [])


let catch m =
  match Exception.catch m with
  | Some msg -> print_endline (Colour.ansi_format [Colour.Red] (Pp_errors.to_string msg))
  | None     -> ()


(* use this when calling a pretty printer *)
let run_pp =
    PPrint.ToChannel.pretty 40.0 80 Pervasives.stdout


(* for given traces: generated a temporary .dot file, call dot2tex on it and then pdflatex *)
let write_graph fname ts =
  debug_print (Colour.ansi_format [Colour.Green] "[generating the pdf of the execution-graph(s)]");
  
(*  let dot = List.fold_left (fun acc (n, (_, t)) -> *)
  let graphs = List.map (fun (i, (_, st)) ->
    Boot_ocaml.to_plain_string $ Pp_sb.pp i (Sb.simplify0 $ Sb.extract2 st)
(*
    match u_t with
      | (Undefined.Defined _, st) ->
          
      | (Undefined.Undef _, st) ->
          acc
      | (Undefined.Error, st) ->
          acc
*)
  ) (numerote ts) in
  
  let (tex_name, tex_chan) = Filename.open_temp_file fname ".tex" in
  
  output_string tex_chan
    "\\documentclass{article}\n\\usepackage[x11names,rgb,svgnames]{xcolor}\n\\usepackage[utf8]{inputenc}\n\\usepackage{tikz}\n\\usetikzlibrary{snakes,arrows,shapes}\n\\usepackage{amsmath}\n\\usepackage[active,tightpage]{preview}\n\\PreviewEnvironment{tikzpicture}\n\\setlength\PreviewBorder{0pt}\n\\begin{document}\n\\pagestyle{empty}\n";
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
  output_string tex_chan "\end{document}\n";
  close_out tex_chan;
  
  if Sys.command ("pdflatex -halt-on-error --jobname=" ^ fname ^ " " ^ tex_name ^ " > /dev/null") <> 0 then
    prerr_endline $ Colour.ansi_format [Colour.Red] "WARNING: an error occured while trying to generate the pdf for the sb-graph."
  else
    (Sys.remove (fname ^ ".aux"); Sys.remove (fname ^ ".log"))










(* load the Core standard library *)
let load_stdlib csemlib_path =
  let fname = Filename.concat csemlib_path "corelib/std.core" in
  if not (Sys.file_exists fname) then
    error $ "couldn't find the Core standard library file\n (looked at: `" ^ fname ^ "'."
  else
    (* An preliminary instance of the Core parser *)
    let module Core_parser_base = struct
      include Core_parser.Make (struct let std = Pmap.empty compare end)
      type token = Core_parser_util.token
      type result = Core_parser_util.result
    end in
    let module Core_parser =
      Parser_util.Make (Core_parser_base) (Lexer_util.Make (Core_lexer)) in
    (* TODO: yuck *)
    match Core_parser.parse (Input.file fname) with
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
        if Sys.command ("gcc -E -I $CSEMLIB_PATH/clib -I /Users/catzilla/Applications/csmith-2.1.0/runtime " ^
                           Input.name f ^ " > " ^ temp_name) <> 0 then
          error "the C preprocessor failed";
        Input.file temp_name in
          Exception.return2 (c_preprocessing m)
      >|> Exception.fmap0 Driver.parse
      >|> pass_message "1. Parsing completed!"
      >|> pass_through_test !print_cabs (run_pp -| Pp_cabs0.pp_file)

      >|> Exception.rbind (Cabs_to_ail.desugar "main")
      >|> pass_message "2. Cabs -> Ail completed!"
      >|> pass_through_test !print_ail (run_pp -| Pp_ail.pp_program)


(*      >|> Exception.rbind Ail_typing.annotate *)


      >|> Exception.rbind (fun z ->
            Exception.of_option (Location.dummy, Errors.CSEM_HIP "Ail Typing error") $
              GenTyping.annotate_program Annotation.concrete_annotation z)
      >|> pass_message "3. Ail typechecking completed!"
      
      
      >|> Exception.fmap0 (Translation.translate stdlib impl)
      >|> pass_message "4. Translation to Core completed!"
      >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file)
      >|> Exception.fmap0 Core_simpl.simplify

      >|> pass_message "5. Core to Core simplication completed!"
      >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file) in
    
    let core_frontend m =
          core_parse m
      >|> Exception.fmap0 (function
            | Core_parser_util.Rfile (a_main, funs) ->
              { Core.main= a_main; Core.stdlib= stdlib; Core.impl= impl; Core.funs= funs }
            | _ -> assert false)
      >|> pass_message "1-4. Parsing completed!"
      >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file) in
    if      Filename.check_suffix file_name ".c"    then (debug_print "Cmulator mode"    ; c_frontend    m)
    else if Filename.check_suffix file_name ".core" then (debug_print "Core runtime mode"; core_frontend m)
                                                    else Exception.fail (Location.unknowned, Errors.UNSUPPORTED "The file extention is not supported") in
  let core_backend m =
    ((m
    >?> !skip_core_tcheck)
      (pass_message "5. Skipping Core's typechecking")
      (fun m ->
            Exception.rbind Core_typing.typecheck m
        >|> pass_message "5. Core's typechecking completed!")
    >?> !execute)
      (fun m ->
        (pass_message "6. Enumerating indet orders:" m
        >|> Exception.rbind Core_indet.order
        >|> pass_message "7. Now running:"
	>?> !testing)
	  (* TODO: this is ridiculous *)
	  (Exception.rbind (Exception.map_list (fun (_,f) -> Core_run.run0 !random_mode f)))
	  (Exception.rbind
             (Exception.map_list
		(fun (n,f) -> Core_run.run0 !random_mode f
                              >|> pass_message ("SB order #" ^ string_of_int n)
                              >|> pass_through Pp_run.pp_traces
                              >|> pass_through_test !sb_graph (write_graph file_name)
                              >|> return_empty
		)
	     )
	  )
      )
      return_empty in
  
  file_name
  >|> Input.file
  >|> frontend
  >|> core_backend
  
  

let run_test stdlib impl core_parse (test:Tests.test) = 
  let ex_result = pipeline stdlib impl core_parse test.Tests.file_name in
  let test_result = Tests.compare_results test.Tests.expected_result ex_result in
  match test_result with
  | Exception.Result _      -> print_endline (Colour.ansi_format [Colour.Green] ("Test succeeded (" ^ test.Tests.file_name ^ ")"))
  | Exception.Exception msg -> print_endline (Colour.ansi_format [Colour.Red]   ("Test failed    (" ^ test.Tests.file_name ^ "): " ^ msg))



(* the entry point *)
let () =
  print_endline "Csem (hg version: <<HG-IDENTITY>>)"; (* this is "sed-out" by the Makefile *)
  
  (* this is for the random execution selection mode *)
  Random.self_init ();
  
  Arg.parse options (fun x -> files := [x]) usage;
  
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
  
  if !testing then
    List.iter (run_test stdlib impl Core_parser.parse) Tests.get_tests
  else 
    List.iter (catch -| pipeline stdlib impl Core_parser.parse) !files;
