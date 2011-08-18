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

let pass_through f v = f v; v
let pass_through_test b f v = if b then f v else (); v

let () =
  let () = Arg.parse options add_file usage in
  let pipeline file_name =
    let pp_file = Document.print -| Ail.Print.pp_file in
    let pp_dot  = Meaning.Graph.to_file file_name in
    let pp_out  = Document.print -| Meaning.Print.pp in
    let pp_res  = List.iter (Document.print -| Constraint.Print.pp_set) in
    file_name
    >> Input.file
    >> Lexer.make
    >> Parser.parse
    >> Cabs_to_ail.desugar "main"
    >> Exception.map (pass_through pp_file)
    >> Exception.rbind Typing.annotate
    >> Exception.map (Reduction.reduce !bound)
    >> Exception.map (pass_through_test !dot    pp_dot)
    >> Exception.map (pass_through_test !output pp_out)
    >> Exception.map Meaning.Solve.simplify_all
    >> Exception.map pp_res in
  List.iter (ignore -| pipeline) !files
