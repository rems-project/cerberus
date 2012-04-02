open Global

let files = ref []
let add_file n = files := n :: !files

let bound = ref 5
let set_bound n = bound := n

let dot = ref false
let set_dot () = dot := true

let output = ref false
let set_output () = output := true

let hack = ref false
let set_hack () = hack := true

let print_cabs = ref false
let set_print_cabs () = print_cabs := true

let print_ail = ref false
let set_print_ail () = print_ail := true

let core = ref false
let set_core () = core := true


let options = Arg.align [
  ("-i", Arg.String add_file,   "<file> Input file");
  ("-n", Arg.Int    set_bound,  "<nat>  Set call and iteration depth");
  ("-d", Arg.Unit   set_dot,    "       Generate dot graphs");
  ("-o", Arg.Unit   set_output, "       Print m-sets");
  
  ("--core",       Arg.Unit   set_core,       "       Use the Core backend");
  ("--print-cabs", Arg.Unit   set_print_cabs, "       Pretty-print the Cabs intermediate representation");
  ("--print-ail",  Arg.Unit   set_print_ail,  "       Pretty-print the Ail intermediate representation");
  ("--hack",       Arg.Unit   set_hack,       "       Display some hacking noise")
]

let usage = "Usage: csem [OPTIONS]... [FILE]...\n"

let pass_through        f = Exception.map (fun v ->           f v        ; v)
let pass_through_test b f = Exception.map (fun v -> if b then f v else (); v)
let pass_message      m   = Exception.map (fun v -> print_endline (Hack.ansi_format [Hack.Green] m); v)

let return_unit _ = Exception.return ()

let catch m =
  match Exception.catch m with
  | Some m -> print_endline m
  | None   -> ()



let (>?>) x b f g = if b then f x else g x

let () =
  let () = Arg.parse options add_file usage in
  let pipeline file_name =
    let pp_hack = Document.print -| Hack.Print.pp_file in
    let pp_ail = Document.print -| Ail.Print.pp_file in
    let pp_core = Document.print -| Core.Print.pp_statement in
    let pp_dot  = Meaning.Graph.to_file file_name in
    let pp_out  = Document.print -| Meaning.Print.pp in
    let pp_res  = Document.print -| Constraint.Print.pp in
    (file_name
    >> Input.file
    >> Lexer.make
    >> Parser.parse
    >> pass_through_test !hack pp_hack
    >> pass_message "1. Parsing completed!"
       
    >> Exception.rbind (Cabs_to_ail.desugar "main")
    >> pass_message "2. Cabs -> Ail completed!"
       
    >> pass_through_test !print_ail pp_ail
    >> Exception.rbind (
         Exception.rbind_exception (Exception.fail -| Type_error.to_string)
         -| Typing.annotate
       )
    >> pass_message "3. Type checking completed!"
    
    >?> !core)
      (* Core backend *)
      (fun m ->
        Exception.map Translation.translate m
        >> pass_message "4. Translation to Core completed!"
        >> pass_through pp_core
        >> return_unit
      )
      
      (* Original backend *)
      (fun m ->
        Exception.map (Reduction.reduce !bound) m
        >> pass_message "4. Opsem completed!"
        >> pass_through_test !dot    pp_dot
        >> pass_through_test !output pp_out
        >> Exception.map Meaning.Solve.simplify_all
        >> Exception.map (Program.iter_list pp_res)
        >> return_unit
      )
  in
  List.iter (catch -| pipeline) !files
