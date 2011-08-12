open Global

let files = ref []
let add_file n = files := n :: !files

let bound = ref 5
let set_bound n = bound := n

let dot = ref false
let set_dot () = dot := true

let output = ref false
let set_output () = output := true

let options = Arg.align [
  ("-i", Arg.String add_file,   "<file> Input file");
  ("-n", Arg.Int    set_bound,  "<nat>  Set call and iteration depth");
  ("-d", Arg.Unit   set_dot,    "       Generate dot graphs");
  ("-o", Arg.Unit   set_output, "       Print m-sets")
]

let usage = "Usage: chickenpox [OPTIONS]... [FILE]...\n"

let () =
  let () = Arg.parse options add_file usage in
  let pass_through f v = f v; v in
  let pass_through_test b f v = if b then f v else (); v in
  let pipeline file_name =
    file_name
    >> Input.file
    >> Lexer.make
    >> Parser.parse
    >> Cabs_to_ail.desugar "main"
    >> Exception.rbind Typing.annotate
    >> Exception.map (Reduction.reduce !bound) in
(*
    >> pass_through
        (List.iter (Document.print -| Ail.Print.pp -| snd))
*)
    
(*
    >> pass_through_test !dot
        (List.iter (Meaning.Graph.dot_result file_name))
    >> pass_through_test !output
        (List.iter
           (Document.print -| Ail.Print.pp_result Meaning.Print.pp))
    >> List.map (Meaning.Solve.simplify_result)
    >> List.iter
        (Document.print -|
            Ail.Print.pp_result Constraint.Print.pp_set) in
*)
  List.iter (ignore -| pipeline) !files
