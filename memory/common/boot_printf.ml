open Core_ctype
open AilSyntax
open AilTypes

type formatting = {
  basis:     basis option;
  use_upper: bool;
}



let ctype_of_specifier = function
  | "%d"
  | "%i" ->
      ({basis= Some Decimal; use_upper= false}, Basic0 (Integer (Signed AilTypes.Int_)))
  | "%o" ->
      ({basis= Some Octal; use_upper= false}, Basic0 (Integer (Unsigned Int_)))
  | "%u" ->
      ({basis= Some Decimal; use_upper= false}, Basic0 (Integer (Unsigned Int_)))
  | "%x" ->
      ({basis= Some Hexadecimal; use_upper= false}, Basic0 (Integer (Unsigned Int_)))
  | "%X" ->
      ({basis= Some Hexadecimal; use_upper= true}, Basic0 (Integer (Unsigned Int_)))
  | "%f"
  | "%F"
  | "%e"
  | "%E"
  | "%g"
  | "%G"
  | "%a"
  | "%A" ->
      ({basis= None; use_upper= false}, Basic0 (Floating (RealFloating Double))) (* TODO: the formatting is wrong *)
(*  | "c" -> *)
(*  | "s" -> *)
  | "%p" ->
      ({basis= None; use_upper= false}, Pointer0 (AilTypes.no_qualifiers, Void0))
(*  | "n" -> *)
  | "%llx" ->
      ({basis= Some Hexadecimal; use_upper= false}, Basic0 (Integer (Unsigned LongLong)))
  | "%llX" ->
      ({basis= Some Hexadecimal; use_upper= true}, Basic0 (Integer (Unsigned LongLong)))
  | "%s" ->
      ({basis= None; use_upper= false}, Pointer0 (AilTypes.no_qualifiers, Core_ctype.char))
  | str ->
      failwith ("Boot_ocaml.ctype_of_specifier, TODO: " ^ str)



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
  

let pseudo_printf (frmt : string) : (formatting * Core_ctype.ctype0) list * (string list -> string) =
  let rexp = Str.regexp ("%\\(" ^ String.concat "\\|"
    ["d"; "i"; "o"; "u"; "x"; "X"; "f"; "F"; "e"; "E";
     "g"; "G"; "a"; "A"; "c"; "s"; "p"; "n"; "%"; "llx"] ^ "\\)") in
  let rec f str (format_tys_acc, str_acc) =
    if String.length str = 0 then
      (* we've reach the end of the format string *)
      (List.rev format_tys_acc, List.rev str_acc)
    else
      try
        let spec_pos    = Str.search_forward rexp str 0 in
        let frmt_prefix = String.sub str 0 spec_pos in
        let str' =
          let offset = Str.match_end () in
          String.sub str offset (String.length str - offset) in
        
        let spec = Str.matched_group 0 str in
        
        f str' (ctype_of_specifier spec :: format_tys_acc, frmt_prefix :: str_acc)


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
          (List.rev format_tys_acc, List.rev (str :: str_acc))
  in
  let frmt' =
    try
      let n = Str.search_forward (Str.regexp "\000") frmt 0 in
      String.sub frmt 0 n
    with
      Not_found ->
        frmt (* TODO: technically that should be invalid *)
  in
  let (format_tys, strs) = f frmt' ([], []) in
  (format_tys, recombiner strs)



