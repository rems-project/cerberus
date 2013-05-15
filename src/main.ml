open Global
  
(* command-line options *)
let files            = ref []
let stdlib_file      = ref ""
let print_cabs       = ref false
let print_ail        = ref false
let print_core       = ref false
let execute          = ref false
let random_mode      = ref Core_run.E.Exhaustive
let sb_graph         = ref false
let skip_core_tcheck = ref false (* TODO: this is for debug purpose *)

let add_file n =
  files := n :: !files

let set_stdlib_file fname =
  stdlib_file := fname

(* command-line handler *)
let options = Arg.align [
  ("-i", Arg.String add_file,           "<file> Input file");
  ("--std", Arg.String set_stdlib_file, "<file> Core standard library");
  
  (* Core backend options *)
  ("--skip-core-tcheck", Arg.Set skip_core_tcheck,                               "       Do not run the Core typechecker");
  ("--execute",          Arg.Set execute,                                        "       Execute the Core program");
  ("-r",                 Arg.Unit (fun () -> random_mode := Core_run.E.Random ), "       Randomly choose a single execution path"); 
  
  ("--sb-graph",         Arg.Set sb_graph, "       Generate dot graphs of the sb orders");
  
  ("--debug",            Arg.Set_int Settings.debug, "       Set the debug noise level (default: 0 = nothing)");
  
  (* printing options *)
  ("--pcabs", Arg.Set print_cabs, "       Pretty-print the Cabs intermediate representation");
  ("--pail",  Arg.Set print_ail,  "       Pretty-print the Ail intermediate representation");
  ("--pcore", Arg.Set print_core, "       Pretty-print the Code generated program")
]
let usage = "Usage: csem [OPTIONS]... [FILE]...\n"


let pass_through        f = Exception.fmap (fun v ->           f v        ; v)
let pass_through_test b f = Exception.fmap (fun v -> if b then f v else (); v)
let pass_message      m   = Exception.fmap (fun v -> print_endline (Colour.ansi_format [Colour.Green] m); v)

let return_unit m = Exception.bind m (fun _ -> Exception.return ())

let catch m =
  match Exception.catch m with
  | Some msg -> print_endline (Colour.ansi_format [Colour.Red] (Errors.to_string msg))
  | None   -> ()

let run_pp =
    PPrint.ToChannel.pretty 40.0 80 Pervasives.stdout


let write_sb file_name ts =
  Output.write (List.fold_left (fun acc (n, (_, t)) ->
    (Boot.to_plain_string $ Pp_sb.pp n (Sb.simplify $ Sb.extract t)) ^ "\n\n" ^ acc
  ) "" (numerote ts))
  (Output.file $ file_name ^ ".dot")


module Core_parser = Parser_util.Make (Core_parser_base) (Lexer_util.Make (Core_lexer))

let () =
  print_endline "Csem (hg version: <<HG-IDENTITY>>)";
  
  (* required when using the random execution selection mode *)
  Random.self_init ();
  
  let () = Arg.parse options add_file usage in
  
  (* parsing the core standard library *)
  let core_stdlib =
    if Sys.file_exists !stdlib_file then
      (* TODO: yuck *)
      match Core_parser.parse (Input.file !stdlib_file) with
        | Exception.Result (Right z) -> z
        | _                          -> failwith "TODO_MSG: found an error while parsing the Core stdlib"
    else
      failwith "TODO_MSG: couldn't find the core std lib file" in  
  let pipeline file_name =
    let frontend m =
      let c_frontend m =
            Exception.return (Cparser.Driver.parse m)
        >|> pass_message "1. Parsing completed!"
        >|> Exception.fmap Cabs_transform.transform_file
        >|> pass_message "1.5 Cabs AST transform completed!"
        >|> pass_through_test !print_cabs (run_pp -| Pp_cabs.pp_file)
        >|> Exception.rbind (Cabs_to_ail.desugar "main")
        >|> pass_message "2. Cabs -> Ail completed!"
        >|> pass_through_test !print_ail (run_pp -| Pp_ail.pp_file)
        >|> Exception.rbind Ail_typing.annotate
        >|> pass_message "3. Ail typechecking completed!"
        >|> Exception.fmap (Translation.translate core_stdlib)
        >|> pass_message "4. Translation to Core completed!"
        >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file)
        >|> Exception.fmap Core_simpl.simplify
        >|> pass_message "5. Core to Core simplication completed!"
        >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file) in
        
      let core_frontend m =
            Core_parser.parse m
        >|> Exception.fmap (function
                              | Left z  -> z
                              | Right _ -> failwith "TODO_MSG: (Core parser) main is missing")
        >|> pass_message "1-4. Parsing completed!"
        >|> pass_through_test !print_core (run_pp -| Pp_core.pp_file) in
      
      if      Filename.check_suffix file_name ".c"    then (print_endline "Cmulator mode"    ; c_frontend    m)
      else if Filename.check_suffix file_name ".core" then (print_endline "Core runtime mode"; core_frontend m)
                                                      else Exception.fail (Errors.UNSUPPORTED "The file extention is not supported") in
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
                               >|> pass_through_test !sb_graph (write_sb file_name)
                               >|> pass_through Pp_run.pp_traces))
          >|> return_unit)
        return_unit in
    
    file_name
    >|> Input.file
    >|> frontend
    >|> core_backend in
  List.iter (catch -| pipeline) !files;
