open Global



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


(* command-line handler *)
let options = Arg.align [
  ("--impl",  Arg.Set_string impl_file,   "<name> Select an implementation definition");
  ("--debug", Arg.Set_int Settings.debug, "       Set the debug noise level (default: 0 = nothing)");
  
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


(* some block functions used by the pipeline *)
let pass_through        f = Exception.fmap (fun v ->           f v        ; v)
let pass_through_test b f = Exception.fmap (fun v -> if b then f v else (); v)
let pass_message      m   = Exception.fmap (fun v -> print_endline (Colour.ansi_format [Colour.Green] m); v)
let return_unit m         = Exception.bind m (fun _ -> Exception.return ())

let catch m =
  match Exception.catch m with
  | Some msg -> print_endline (Colour.ansi_format [Colour.Red] (Errors.to_string msg))
  | None     -> ()


(* use this when calling a pretty printer *)
let run_pp =
    PPrint.ToChannel.pretty 40.0 80 Pervasives.stdout


(* for given traces: generated a temporary .dot file, call dot2tex on it and then pdflatex *)
let write_sb fname ts =
  print_endline (Colour.ansi_format [Colour.Green] "[generating the pdf of the sb-graph(s)]");
  let dot = List.fold_left (fun acc (n, (_, t)) ->
    (Boot.to_plain_string $ Pp_sb.pp n (Sb.simplify $ Sb.extract t)) ^ "\n\n" ^ acc
  ) "" (numerote ts) in
  let (temp_name, temp_chan) = Filename.open_temp_file fname "" in
  output_string temp_chan dot;
  close_out temp_chan;
  (* TODO: using /dev/null here probably only work on Unix-like systems? *)
  if Sys.command ("dot2tex --autosize -tmath " ^ temp_name ^ " | pdflatex -halt-on-error --jobname=" ^ fname ^ " > /dev/null") <> 0 then
    prerr_endline $ Colour.ansi_format [Colour.Red] "WARNING: an error occured while trying to generate the pdf for the sb-graph.";
  Sys.remove (fname ^ ".aux");
  Sys.remove (fname ^ ".log")


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
  let stdlib =
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
        | _ -> error "(TODO_MSG) found an error while parsing the Core stdlib." in
  print_endline (Colour.ansi_format [Colour.Green] "0.1. - Core standard library loaded.");
  
  (* An instance of the Core parser knowing about the stdlib functions we just parsed *)
  let module Core_parser_base = struct
    include Core_parser.Make (struct
        let std = List.fold_left (fun acc ((_, Some fname) as fsym, _) ->
          Pmap.add fname fsym acc
        ) (Pmap.empty compare) $ Pmap.bindings stdlib
      end)
    type token = Core_parser_util.token
    type result = Core_parser_util.result
  end in
  let module Core_parser =
    Parser_util.Make (Core_parser_base) (Lexer_util.Make (Core_lexer)) in
  
  (* Looking for and parsing the implementation file *)
  let impl =
    if !impl_file = "" then 
      error "expecting an implementation to be specified (using --impl <name>)."
    else
      let iname = Filename.concat csemlib_path ("corelib/impls/" ^ !impl_file ^ ".impl") in
      if not (Sys.file_exists iname) then
        error $ "couldn't find the implementation file\n (looked at: `" ^ iname ^ "'."
      else
      (* TODO: yuck *)
        match Core_parser.parse (Input.file iname) with
          | Exception.Result (Core_parser_util.Rimpl z) -> z
          | _ -> error "(TODO_MSG) found an error while parsing the implementation file." in
  print_endline (Colour.ansi_format [Colour.Green] "0.2. - Implementation file loaded.");
  
  
  let pipeline file_name =
    let frontend m =
      let c_frontend m =
        (* Calling a C preprocessor before running the parser
           (TODO: the choice of the compiler shouldn't be hardcoded) *)
        let c_preprocessing (f: Input.t) =
          let temp_name = Filename.temp_file (Filename.basename $ Input.name f) "" in
          (* TODO: add an command line option for custom include directories, for now
             I hardcode the location of csmith on AddaX *)
          if Sys.command ("gcc -E -I $CSEMLIB_PATH/clib -I ~/Applications/Builds/Formal/csmith-git/include/csmith-2.2.0 " ^
                             Input.name f ^ " > " ^ temp_name) <> 0 then
            error "the C preprocessor failed";
          Input.file temp_name in
            Exception.return (c_preprocessing m)
        >|> Exception.fmap Cparser.Driver.parse
        >|> pass_message "1. Parsing completed!"

        >|> pass_through_test !print_cabs (run_pp -| Pp_cabs0.pp_file)

        >|> Exception.fmap Cabs_transform.transform_file
        >|> pass_message "1.5. Cabs AST transform completed!"
        >|> pass_through_test !print_cabs (run_pp -| Pp_cabs.pp_file)

        >|> Exception.rbind (Cabs_to_ail.desugar "main")
        >|> pass_message "2. Cabs -> Ail completed!"
        >|> pass_through_test !print_ail (run_pp -| Pp_ail.pp_file)
        >|> Exception.rbind Ail_typing.annotate
        >|> pass_message "3. Ail typechecking completed!"
        >|> Exception.fmap (Translation.translate stdlib impl)
        >|> pass_message "4. Translation to Core completed!"
        >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file)
        >|> Exception.fmap Core_simpl.simplify
        >|> pass_message "5. Core to Core simplication completed!"
        >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file) in
        
      let core_frontend m =
            Core_parser.parse m
        >|> Exception.fmap (function
          | Core_parser_util.Rfile (a_main, funs) ->
              { Core.main= a_main; Core.stdlib= stdlib; Core.impl= impl; Core.funs= funs }
          | _ -> assert false)
        >|> pass_message "1-4. Parsing completed!"
        >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file) in
      
      if      Filename.check_suffix file_name ".c"    then (print_endline "Cmulator mode"    ; c_frontend    m)
      else if Filename.check_suffix file_name ".core" then (print_endline "Core runtime mode"; core_frontend m)
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
          pass_message "6. Enumerating indet orders:" m
          >|> Exception.rbind Core_indet.order
          >|> pass_message "7. Now running:"
          >|> Exception.rbind
              (Exception.map_list
                 (fun (n,f) -> Core_run.run !random_mode f
                               >|> pass_message ("SB order #" ^ string_of_int n)
                               >|> pass_through Pp_run.pp_traces
                               >|> pass_through_test !sb_graph (write_sb file_name)))
          >|> return_unit)
        return_unit in
    
    file_name
    >|> Input.file
    >|> frontend
    >|> core_backend in
  List.iter (catch -| pipeline) !files;
