open Global

let pickList = function
  | []  -> failwith ""
  | [x] -> ([], x, [])
  | xs  -> let l = List.length xs in
           let (ys,z::zs) = Lem_list.split_at (Random.int l) xs in
           (ys, z, zs)


let output_string str =
  print_string (Scanf.unescaped str)


let sort_assoc_list xs =
  List.stable_sort (fun (a, _) (b, _) -> Pervasives.compare a b) xs


let random_select xs =
(*  Printf.printf "random_select >> %d\n" (List.length xs); *)
  if List.length xs > 1 then
    Debug_ocaml.print_debug 4 ("CALLED ND.random_select (|xs| = " ^ string_of_int (List.length xs) ^ ")");
  List.nth xs (Random.int (List.length xs))
