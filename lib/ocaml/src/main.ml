open Global

(* command-line options *)
let files = ref []
let add_file n = files := n :: !files

(* TODO: part of the old backend *)
let bound = ref 5
let set_bound n = bound := n

(* TODO: part of the old backend *)
let dot = ref false
let set_dot () = dot := true

(* TODO: part of the old backend *)
let output = ref false
let set_output () = output := true


(* TODO: will be useless once we remove the old backend *)
let core = ref true
let unset_core () = core := false

let debug = ref false
let set_debug () = debug := true

let print_cabs = ref false
let set_print_cabs () = print_cabs := true

let print_ail = ref false
let set_print_ail () = print_ail := true

let print_core = ref false
let set_print_core () = print_core := true

let core_run = ref false
let set_core_run () = core := true; core_run := true

let core_graph = ref false
let set_core_graph () = core_graph := true

(* TODO: this is for debug purpose *)
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
  ("--old",            Arg.Unit   unset_core,              "       Use the Old backend");
  ("--run",            Arg.Unit   set_core_run,            "       Execute the Core program");
  ("--graph",          Arg.Unit   set_core_graph,          "       Generate dot graphs of sb orders");
  ("--no-core-tcheck", Arg.Unit   set_core_skip_typecheck, "       Do not run the Core typechecker");
  
  (* printing options *)
  ("--print-cabs", Arg.Unit   set_print_cabs, "       Pretty-print the Cabs intermediate representation");
  ("--print-ail",  Arg.Unit   set_print_ail,  "       Pretty-print the Ail intermediate representation");
  ("--print-core", Arg.Unit   set_print_core,  "       Pretty-print the Code generated program");
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



let rec string_of_dyn_rule = function
  | Core_run.Rule_Pos        -> "pos"
  | Core_run.Rule_Neg        -> "neg"
  | Core_run.Rule_WseqL r    -> "wseq_l[ " ^ string_of_dyn_rule r ^ " ]"
  | Core_run.Rule_Neg_Wseq r -> "neg_wseq[ " ^ string_of_dyn_rule r ^ " ]"
  | Core_run.Rule_Unseq r    -> "unseq[ " ^ string_of_dyn_rule r ^ " ]"


let string_of_trace_action = function
  | Core_run.Tcreate (ty, o)   -> "@" ^ string_of_int o ^ " <= create {" ^ (Document.to_plain_string $ Ail.Print.pp_type ty) ^ "}"
  | Core_run.Talloc (n, o)     -> "@" ^ string_of_int o ^ " <= alloc " ^ string_of_int n
  | Core_run.Tkill o           -> "kill @" ^ string_of_int o
  | Core_run.Tstore (ty, o, n) -> "store {" ^ (Document.to_plain_string $ Ail.Print.pp_type ty) ^ "} @" ^ string_of_int o ^ " " ^ string_of_int n
  | Core_run.Tload (ty, o, v)  -> "load {" ^ (Document.to_plain_string $ Ail.Print.pp_type ty) ^ "} @" ^ string_of_int o ^ " = " ^ string_of_int v

let rec string_of_trace (t: Core_run.E.trace) =
  let rec f = function
    | []      -> ""
    | [b]     -> string_of_trace_action b
    | b :: bs -> string_of_trace_action b ^ ", " ^ f bs
  in match t with
       | []               -> ""
       | (r, bs, a) :: xs -> "\x1b[34m" ^ string_of_dyn_rule r ^
                             "\x1b[0m ==> \x1b[32m<" ^ (f $ Pset.elements bs) ^
                             ">\x1b[0m " ^ string_of_trace_action a ^ "\n" ^
                             string_of_trace xs







let () =
  let () = Arg.parse options add_file usage in
  let pipeline file_name =
    let pp_cabs = Document.print -| Hack.Print.pp_file in
    let pp_ail  = Document.print -| Ail.Print.pp_file in
    let pp_core = Document.print -| Core.Print.pp_file in
    let pp_dot  = Meaning.Graph.to_file file_name in
    let pp_out  = Document.print -| Meaning.Print.pp in
    let pp_res  = Document.print -| Constraint.Print.pp in
    let pp_sb ts =  Output.write (List.fold_left (fun acc (n, t) -> (Document.to_plain_string $ Sb.Print.pp n (Sb.simplify $ Sb.extract t)) ^ "\n\n" ^ acc)
                                                 "" (numerote ts))
                                 (Output.file $ file_name ^ ".dot") in
    let pp_traces ts = List.map (fun (i, t) -> print_endline $ "Trace #" ^ string_of_int i ^ "\n" ^ string_of_trace t) $ numerote ts in
    (file_name
    >|> Input.file
    >|> Lexer.make
    >|> Parser.parse
    >|> pass_message "1. Parsing completed!"
    >|> pass_through_test !print_cabs pp_cabs
    
    >|> Exception.rbind (Cabs_to_ail.desugar "main")
    >|> pass_message "2. Cabs -> Ail completed!"
    >|> pass_through_test !print_ail pp_ail
    
    >|> Exception.rbind Typing.annotate
    >|> pass_message "3. Ail typechecking completed!"
    
    >?> !core)
      (* Core backend *)
      (fun m ->
        (Exception.map Translation.translate m (* TODO: map is bad *)
        >|> pass_message "4. Translation to Core completed!"
        >|> pass_through_test !print_core pp_core
        >|> pass_message "-------------------------- POST SIMPLIFICATION --------------------------"
        >|> Exception.map (Core_simpl.simplify)
        >|> pass_through_test !print_core pp_core
        >?> not !core_skip_typecheck)
          (fun m ->
            Exception.rbind Core_typing.typecheck m
            >|> pass_message "5. Core's typechecking completed!"
          )
          (pass_message "5. Skipping Core's typechecking completed!")
        >|> pass_message "6. Now running:"
        >|> Exception.rbind Core_run.run
        >|> pass_through_test !core_graph pp_sb
        >|> pass_through pp_traces
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
