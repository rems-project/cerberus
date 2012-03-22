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


let options = Arg.align [
  ("-i", Arg.String add_file,   "<file> Input file");
  ("-n", Arg.Int    set_bound,  "<nat>  Set call and iteration depth");
  ("-d", Arg.Unit   set_dot,    "       Generate dot graphs");
  ("-o", Arg.Unit   set_output, "       Print m-sets");
  
  ("--print-cabs", Arg.Unit   set_print_cabs, "       Pretty-print the Cabs intermediate representation");
  ("--print-ail",  Arg.Unit   set_print_ail,  "       Pretty-print the Ail intermediate representation");
  ("--hack",       Arg.Unit   set_hack,       "       Display some hacking noise")
]

let usage = "Usage: csem [OPTIONS]... [FILE]...\n"

let pass_through        f = Exception.map (fun v ->           f v        ; v)
let pass_through_test b f = Exception.map (fun v -> if b then f v else (); v)
let pass_message      m   = Exception.map (fun v -> print_endline (Hack.ansi_format [Hack.Green] m); v)

let catch m =
  match Exception.catch m with
  | Some m -> print_endline m
  | None   -> ()



let () =
  let () = Arg.parse options add_file usage in
  let pipeline file_name =
    let pp_hack = Document.print -| Hack.Print.pp_file in
    let pp_file = Document.print -| Ail.Print.pp_file in
    let pp_dot  = Meaning.Graph.to_file file_name in
    let pp_out  = Document.print -| Meaning.Print.pp in
    let pp_res  = Document.print -| Constraint.Print.pp in
    file_name
    >> Input.file
    >> Lexer.make
    >> Parser.parse
    >> pass_through_test !hack pp_hack
    >> pass_message "1. Parsing completed!"
    >> Exception.rbind (Cabs_to_ail.desugar "main")
    >> pass_message "2. Cabs -> Ail completed!"
    >> pass_through_test !print_ail pp_file
    >> Exception.rbind (
         Exception.rbind_exception (Exception.fail -| Type_error.to_string)
         -| Typing.annotate
       )
    >> pass_message "3. Type checking completed!"



(*
    >> Exception.map (Reduction2.reduce !bound)
    >> pass_message "4. Translation to Core completed!" in
*)





    >> Exception.map (Reduction.reduce !bound)
    >> pass_message "4. Opsem completed!"
    >> pass_through_test !dot    pp_dot
    >> pass_through_test !output pp_out
    >> Exception.map Meaning.Solve.simplify_all
    >> Exception.map (Program.iter_list pp_res) in
(*
    >> Exception.map (fun s -> Program.iter_list pp_res (Pset.elements s)) in
*)

  List.iter (catch -| pipeline) !files



(*
open Core

let test_ail = Ail.EXPRESSION (error "", Ail.BINARY (Cabs.ARITHMETIC Cabs.ADD,
                                           (fail "", Ail.CONSTANT (Cabs.CONST_INT (32, None))),
                                           (fail "", Ail.CONSTANT (Cabs.CONST_INT (10, None)))
                                           )
                               )
let test_core = LET (1, CREATE TY, LET (2, EXPR (CONST 42), STORE (TY, 1, 2)))

let _ =
  Document.print (Core.Print.pp_statement test);
  print_newline ()
*)

(*
open Run_core

let _ =
  print_endline "hello"
*)
