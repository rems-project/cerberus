let foo2 (Symbol.Symbol (_, _, Some id), (_, _, attrs, _)) =
  print_string (id ^ ": " ^ string_of_int (List.length attrs) ^ "\n")

let foo fs =
  List.iter foo2 fs

let run_rustic ail_file =
  match ail_file with
  | (id, s) ->
    let fs = s.AilSyntax.function_definitions in
    foo fs;
    ()

