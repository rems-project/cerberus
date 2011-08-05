open CpPervasives

module Log = CpLogger.StdOut

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
(*
    try
*)
      file_name
      |> CpInput.file
      |> CpLexer.make
      |> CpParser.parse
      |> CpCabsToAil.desugar "main"
      |> CpAilTyping.annotate
      |> pass_through
          (List.iter (CpDocument.print -| CpAilPrint.pp -| snd))
      |> List.map (CpAilReduction.reduce !bound)
      |> pass_through_test !dot
          (List.iter (CpAilMeaning.Graph.dot_result file_name))
      |> pass_through_test !output
          (List.iter
             (CpDocument.print -| CpAilPrint.pp_result CpAilMeaning.Print.pp))
      |> List.map (CpAilMeaning.Solve.simplify_result)
      |> List.iter
          (CpDocument.print -|
              CpAilPrint.pp_result CpAilConstraint.Print.pp_set)
(*
    with BUG | ERROR | Frontc.ParseError _ ->
      Pervasives.exit 1 in
*) in
  List.iter (ignore -| pipeline) !files
