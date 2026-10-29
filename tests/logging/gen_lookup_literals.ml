(* Generate native string constants, rather than heap strings made at runtime.
   Shared by correctness checks and the optional memory/lookup benchmark. *)
let () =
  print_endline "let names = [|";
  for i = 0 to 16_383 do
    Printf.printf "  \"Lookup_literals.function%03d\";\n" i
  done;
  print_endline "|]"
