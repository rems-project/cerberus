open Global

let assert_false str =
  print_endline ("ERROR>\n" ^ str);
  exit (-1)

(*
let debug_level = ref 0


let dprint n str =
  if !debug_level >= n then
    Pervasives.output_string Pervasives.stderr ("\x1b[31m" ^ str ^ "\x1b[0m\n")

let print_debug str k =
  if !debug_level > 0 then
    let _ = Pervasives.output_string Pervasives.stderr ("\x1b[31mDEBUG: " ^ str ^ "\x1b[0m\n") in k
  else
    k
*)

let pickList = function
  | []  -> failwith ""
  | [x] -> ([], x, [])
  | xs  -> let l = List.length xs in
           let (ys,z::zs) = Lem_list.split_at (Random.int l) xs in
           (ys, z, zs)




let output_string str =
  print_string (Scanf.unescaped str)

(*
let output_string2 str =
  if !debug_level > 0 then
    print_string str
*)


(*
(* TODO: this is massive hack, just to make csmith programs work *)
let fake_printf str args =
  match (str, args) with
  | ("\"%d\"", [Cmm_aux.Cint n]) ->
      Big_int.string_of_big_int n

  | ("\"checksum = %x\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "checksum = %x\n" (Big_int.int_of_big_int n)

  | ("\"checksum = %X\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "checksum = %X\n" (Big_int.int_of_big_int n)

  | ("\"...checksum after hashing %s : %X\\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "...checksum after hashing %s : %X\n" (Xstring.implode str) (Big_int.int_of_big_int n)

  | ("\"...checksum after hashing %s : %lX\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "...checksum after hashing %s : %LX\n" (Xstring.implode str) (Big_int.int64_of_big_int n)

  | ("\"%s %d\\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "%s %ld\n" (Xstring.implode str) (Big_int.int32_of_big_int n)

  (* --- *)

  | ("\"DEBUG> %ld\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "DEBUG> %Ld\n" (Big_int.int64_of_big_int n)

  | ("\"DEBUG> %d\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "DEBUG> %ld\n" (Big_int.int32_of_big_int n)

  | ("\"DEBUG> %u\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "DEBUG> %lu\n" (Big_int.int32_of_big_int n)

  | ("\"DEBUG> %lu\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "DEBUG> %Lu\n" (Big_int.int64_of_big_int n)

  | (str, []) ->
      Scanf.unescaped (String.sub str 1 (String.length str - 2))
  | _ ->
      print_endline "TODO: error in Boot_ocaml.fake_printf";
      Printf.printf "str= %s\n" str;
      Printf.printf "|args|= %d\n" (List.length args);
      exit 1
*)




let sort_assoc_list xs =
  List.stable_sort (fun (a, _) (b, _) -> Pervasives.compare a b) xs


let random_select xs =
(*  Printf.printf "random_select >> %d\n" (List.length xs); *)
  List.nth xs (Random.int (List.length xs))


open Str
(* TODO: ridiculous hack *)
let pseudo_printf (frmt : string) (args : string list (* Big_int.big_int list *)) : string =
  let rexp = regexp "%d" in
  let rec f str args acc =
    if String.length str = 0 then
      List.rev acc
    else
      try
        let n    = search_forward rexp str 0 in
        let pre  = String.sub str 0 n    in
        let str' = String.sub str (n+2) (String.length str - n - 2) in
        
        match args with
          | [] ->
              print_endline "PRINTF WITH NOT ENOUGH ARGUMENTS";
              List.rev (str :: acc)
          | arg :: args' ->
              f str' args' ((* Big_int.string_of_big_int *) arg :: pre :: acc)
      with
        Not_found ->
          if List.length args <> 0 then
            print_endline "PRINTF WITH TOO MANY ARGUMENTS";
          List.rev (str :: acc)
  in
  let frmt' =
    try
      let n = search_forward (regexp "\000") frmt 0 in
      String.sub frmt 0 n
    with
      Not_found ->
        frmt (* TODO: technically that should be invalid *)
  in
  String.concat "" (f frmt' args [])
