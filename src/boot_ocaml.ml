open Global


(*
  print_endline ("ERROR>\n" ^ str);
  exit (-1)
*)

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
      Nat_big_num.to_string n

  | ("\"checksum = %x\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "checksum = %x\n" (Nat_big_num.to_int n)

  | ("\"checksum = %X\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "checksum = %X\n" (Nat_big_num.to_int n)

  | ("\"...checksum after hashing %s : %X\\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "...checksum after hashing %s : %X\n" (Xstring.implode str) (Nat_big_num. n)

  | ("\"...checksum after hashing %s : %lX\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "...checksum after hashing %s : %LX\n" (Xstring.implode str) (Nat_big_num.to_int64 n)

  | ("\"%s %d\\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "%s %ld\n" (Xstring.implode str) (Nat_big_num.to_int32 n)

  (* --- *)

  | ("\"DEBUG> %ld\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "DEBUG> %Ld\n" (Nat_big_num.to_int64 n)

  | ("\"DEBUG> %d\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "DEBUG> %ld\n" (Nat_big_num.to_int32 n)

  | ("\"DEBUG> %u\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "DEBUG> %lu\n" (Nat_big_num.to_int32 n)

  | ("\"DEBUG> %lu\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "DEBUG> %Lu\n" (Nat_big_num.to_int64 n)

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
(*
let pseudo_printf (frmt : string) (args : string list (* Nat_big_num.num list *)) : string =
  let rexp = regexp "%\(d\|llx\)" in
  let rec f str args acc =
    if String.length str = 0 then
      List.rev acc
    else
      try
        let n    = search_forward rexp str 0 in
        let pre  = String.sub str 0 n    in
        let str' =
          let offset = match_end () in
          String.sub str offset (String.length str - offset) in
        
        match args with
          | [] ->
              print_endline "PRINTF WITH NOT ENOUGH ARGUMENTS";
              List.rev (str :: acc)
          | arg :: args' ->
              f str' args' ((* Nat_big_num.to_string *) arg :: pre :: acc)
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
*)

(* TODO: ridiculous hack (v2) *)
(*
let pseudo_printf (frmt : string) (args : string list (* Nat_big_num.num list *)) : string =
  let rexp = regexp "%\(d\|llx\)" in
  let rec f str args acc =
    if String.length str = 0 then
      List.rev acc
    else
      try
        let n    = search_forward rexp str 0 in
        let pre  = String.sub str 0 n    in
        let str' =
          let offset = match_end () in
          String.sub str offset (String.length str - offset) in
        
        match args with
          | [] ->
              print_endline "PRINTF WITH NOT ENOUGH ARGUMENTS";
              List.rev (str :: acc)
          | arg :: args' ->
              let arg = match matched_group 0 str with
                | "%d" ->
                    Printf.sprintf "%Ld" (Int64.of_string arg)
                | "%llx" ->
                    Printf.sprintf "%Lx" (Int64.of_string arg)
              in 
              f str' args' ((* Nat_big_num.to_string *) arg :: pre :: acc)
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
*)




open Core_ctype
open AilTypes


let ctype_of_specifier = function
  | "%d"
  | "%i" -> Basic0 (Integer (Signed AilTypes.Int_))
  | "%o"
  | "%u"
  | "%x"
  | "%X" -> Basic0 (Integer (Unsigned Int_))
  | "%f"
  | "%F"
  | "%e"
  | "%E"
  | "%g"
  | "%G"
  | "%a"
  | "%A" -> Basic0 (Floating (RealFloating Double))
(*  | "c" -> *)
(*  | "s" -> *)
  | "%p" -> Pointer0 (AilTypes.no_qualifiers, Void0)
(*  | "n" -> *)
  | "%llx" -> Basic0 (Integer (Unsigned LongLong))
  | "%s" -> Pointer0 (AilTypes.no_qualifiers, Core_ctype.char)
  | str ->
    failwith ("BOOM: " ^ str)



let recombiner xs ys =
  let rec aux xs ys = match (xs, ys) with
    | ([], []) ->
        []
    | (x::xs, y::ys) ->
        x::y::(aux xs ys)
    | ([], ys) ->
        ys
    | (xs, []) ->
        xs in
  String.concat "" (aux xs ys)
(*
let recombiner (xs: string list ) : string list -> string =
(*  let n = List.length xs in *)
  let rec aux z n = function
    | []  ->
        ""
    | [x] ->
        x
    | (x::xs) ->
        x ^ List.nth z n ^ aux z (n+1) xs in
  fun z -> aux z 0 xs
*)
  

let pseudo_printf (frmt : string) : Core_ctype.ctype0 list * (string list -> string) =
  let rexp = regexp ("%\\(" ^ String.concat "\\|"
    ["d"; "i"; "o"; "u"; "x"; "X"; "f"; "F"; "e"; "E";
     "g"; "G"; "a"; "A"; "c"; "s"; "p"; "n"; "%"; "llx"] ^ "\\)") in
  let rec f str (tys_acc, str_acc) =
    if String.length str = 0 then
      (* we've reach the end of the format string *)
      (List.rev tys_acc, List.rev str_acc)
    else
      try
        let spec_pos    = search_forward rexp str 0 in
        let frmt_prefix = String.sub str 0 spec_pos in
        let str' =
          let offset = match_end () in
          String.sub str offset (String.length str - offset) in
        
        let spec = matched_group 0 str in
        
        f str' (ctype_of_specifier spec :: tys_acc, frmt_prefix :: str_acc)


(*
          | "%d" ->
              (Core_ctype.(Basic0 (AilTypes.Integer (AilTypes.Signed AilTypes.Int_))) :: tys_acc,
               fun str ->
                 Printf.sprintf "%Ld" (Int64.of_string str) ^

 (* Printf.sprintf "%Ld" (Int64.of_string arg) *)
(*
                | "%llx" ->
                    "long" (* Printf.sprintf "%Lx" (Int64.of_string arg) *)
*)
                | "%p" ->
                    Core_ctype.(Pointer0 (AilTypes.no_qualifiers, Void0))
              in 
              f str' (* args' *) ((* Nat_big_num.to_string *) arg :: (* pre :: *) acc)
*)
      with
        Not_found ->
          (* there are no more conversion specifiers in the remainder of the format string *)
          (List.rev tys_acc, List.rev (str :: str_acc))
  in
  let frmt' =
    try
      let n = search_forward (regexp "\000") frmt 0 in
      String.sub frmt 0 n
    with
      Not_found ->
        frmt (* TODO: technically that should be invalid *)
  in
  let (tys, strs) = f frmt' ([], []) in
  (tys, recombiner strs)





