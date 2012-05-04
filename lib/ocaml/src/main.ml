open Global

(* command-line options *)
let files = ref []
let add_file n = files := n :: !files

let bound = ref 5
let set_bound n = bound := n

let dot = ref false
let set_dot () = dot := true

let output = ref false
let set_output () = output := true

let debug = ref false
let set_debug () = debug := true

let print_cabs = ref false
let set_print_cabs () = print_cabs := true

let print_ail = ref false
let set_print_ail () = print_ail := true

let print_core = ref false
let set_print_core () = print_core := true

let core = ref false
let set_core () = core := true

let core_run = ref false
let set_core_run () = core := true; core_run := true

let core_graph = ref false
let set_core_graph () = core_graph := true

let core_skip_typecheck = ref false
let set_core_skip_typecheck () = core_skip_typecheck := true


(* command-line handler *)
let options = Arg.align [
  ("-i", Arg.String add_file,   "<file> Input file");
  
  (* original backend options *)
  ("-n", Arg.Int    set_bound,  "<nat>  Set call and iteration depth (original backend)");
  ("-d", Arg.Unit   set_dot,    "       Generate dot graphs          (original backend)");
  ("-o", Arg.Unit   set_output, "       Print m-sets                 (original backend)");
  
  (* core backend options *)
  ("--core",                Arg.Unit   set_core,                "       Use the Core backend");
  ("--core-run",            Arg.Unit   set_core_run,            "       Execute the Core program (adds --core)");
  ("--core-graph",          Arg.Unit   set_core_graph,          "       Generate dot graphs of the executions (adds --core)");
  ("--core-skip-typecheck", Arg.Unit   set_core_skip_typecheck, "       Do not run the Core typechecker");
  
  (* printing options *)
  ("--print-cabs", Arg.Unit   set_print_cabs, "       Pretty-print the Cabs intermediate representation");
  ("--print-ail",  Arg.Unit   set_print_ail,  "       Pretty-print the Ail intermediate representation");
  ("--print-core", Arg.Unit   set_print_core,  "       Pretty-print the Code generated program (needs --core)");
  ("--debug",      Arg.Unit   set_debug,      "       Display some debug noise")
]
let usage = "Usage: csem [OPTIONS]... [FILE]...\n"


let pass_through        f = Exception.map (fun v ->           f v        ; v)
let pass_through_test b f = Exception.map (fun v -> if b then f v else (); v)
let pass_message      m   = Exception.map (fun v -> print_endline (Hack.ansi_format [Hack.Green] m); v)

let return_unit m = Exception.bind m (fun _ -> Exception.return ())

let catch m =
  match Exception.catch m with
  | Some msg -> print_endline (Hack.ansi_format [Hack.Red] (Errors.to_string msg))
  | None   -> ()


let rec numerote_ n = function
  | []    -> []
  | x::xs -> (n,x) :: numerote_ (n+1) xs
let numerote = numerote_ 1

let () =
  let () = Arg.parse options add_file usage in
  let pipeline file_name =
    let pp_cabs = Document.print -| Hack.Print.pp_file in
    let pp_ail  = Document.print -| Ail.Print.pp_file in
    let pp_core = Document.print -| Core.Print.pp_file in
    let pp_dot  = Meaning.Graph.to_file file_name in
    let pp_out  = Document.print -| Meaning.Print.pp in
    let pp_res  = Document.print -| Constraint.Print.pp in
    
    let run_core g =
      print_endline (Hack.ansi_format [Hack.Blue] ("Core run: found " ^ string_of_int (List.length g) ^ " sb-order(s)."));
      let chan = open_out "out.dot" in
      output_string chan "digraph G{node[style=filled,color=white];";
      List.iter (fun (n,g) -> output_string chan (Cmulator.toDot n g)) (numerote g);
      output_string chan "}";
      close_out chan in
    (file_name
    >|> Input.file
    >|> Lexer.make
    >|> Parser.parse
    >|> pass_through_test !print_cabs pp_cabs
    >|> pass_message "1. Parsing completed!"
       
    >|> Exception.rbind (Cabs_to_ail.desugar "main")
    >|> pass_message "2. Cabs -> Ail completed!"
       
    >|> pass_through_test !print_ail pp_ail
    >|> Exception.rbind Typing.annotate
    >|> pass_message "3. Ail typechecking completed!"
    
    >?> !core)
      (* Core backend *)
      (fun m ->
        Exception.map Translation.translate m (* TODO: map is bad *)
        >|> pass_message "4. Translation to Core completed!"
        >|> pass_through_test !print_core pp_core
        >|> Exception.rbind Core_typing.typecheck
        >|> pass_message "5. Core typechecking completed!"
        >|> Exception.rbind Core_run.run
        >|> pass_through_test !core_run run_core
        >|> return_unit
      )
      
      (* Original backend *)
      (fun m ->
        Exception.map (Reduction.reduce !bound) m
        >|> pass_message "4. Opsem completed!"
        >|> pass_through_test !dot    pp_dot
        >|> pass_through_test !output pp_out
        >|> Exception.map Meaning.Solve.simplify_all
        >|> Exception.map (Program.iter_list pp_res)
        >|> return_unit
      )
  in
  List.iter (catch -| pipeline) !files;
