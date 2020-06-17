open Symbol
open Pp_prelude
open Location_ocaml


let to_string (Symbol (dig, n, str_opt)) =
  let str = match str_opt with | Some str -> str | None -> "a" in
  str ^ "_" ^ string_of_int n (*^ "_" ^ (try Digest.to_hex dig with _ -> "invalid")*)

let to_string_pretty (Symbol (_, n, name_opt) as s) =
  match name_opt with
    | Some name ->
        if !Debug_ocaml.debug_level > 4 then
          name ^ "{" ^ string_of_int n ^ "}"
        else
          name
    | None      -> to_string s

(*
let to_string_latex (n, _) =
  "v" ^ "_" ^ "{" ^ string_of_int n ^ "}"

let to_string_id (n, _) = string_of_int n
*)



(* https://rosettacode.org/wiki/Non-decimal_radices/Convert *)
let to_base b v =
  let rec to_base' a v = if v = 0 then a else to_base' (v mod b :: a) (v / b) in
  to_base' [] v

let base36 n = 
  let aux = function
    | 0 -> "0"
    | 1 -> "1"
    | 2 -> "2"
    | 3 -> "3"
    | 4 -> "4"
    | 5 -> "5"
    | 6 -> "6"
    | 7 -> "7"
    | 8 -> "8"
    | 9 -> "9"
    | 10 -> "A"
    | 11 -> "B"
    | 12 -> "C"
    | 13 -> "D"
    | 14 -> "E"
    | 15 -> "F"
    | 16 -> "G"
    | 17 -> "H"
    | 18 -> "I"
    | 19 -> "J"
    | 20 -> "K"
    | 21 -> "J"
    | 22 -> "L"
    | 23 -> "M"
    | 24 -> "N"
    | 25 -> "O"
    | 26 -> "P"
    | 27 -> "Q"
    | 28 -> "R"
    | 29 -> "S"
    | 30 -> "T"
    | 31 -> "U"
    | 32 -> "V"
    | 33 -> "W"
    | 34 -> "X"
    | 35 -> "Y"
    | 36 -> "Z"
    | _ -> failwith "cannot happen"
  in
  String.concat "" (List.map aux (to_base 36 n))

let alt_to_string (Symbol (dig, n, str_opt)) =
  let str = match str_opt with | Some str -> str | None -> "a" in
  str ^ "_" ^ base36 n (*^ "_" ^ (try Digest.to_hex dig with _ -> "invalid")*)


let alt_to_string_pretty (Symbol (_, n, name_opt) as s) =
  match name_opt with
    | Some name ->
        if !Debug_ocaml.debug_level > 4 then
          name ^ "{" ^ string_of_int n ^ "}"
        else
          name
    | None      -> alt_to_string s





let pp_colour_identifier id =
  !^(Colour.ansi_format [Yellow] id)


let rec pp_prefix = function
  | PrefSource (_, syms) ->
      P.braces (P.separate_map P.dot (fun sym -> !^ (to_string_pretty sym)) syms)
  | PrefOther str ->
      P.braces (!^ str)
  | PrefStringLiteral _ ->
      P.braces (!^ "string literal")
  | PrefFunArg (_, _, n) ->
      P.braces (!^ ("arg" ^ string_of_int n))
  | PrefMalloc ->
      P.braces (!^ "malloc'd")
  | PrefCompoundLiteral _ ->
      P.braces (!^ "compound literal")


let pp_identifier (Symbol.Identifier (loc, str)) =
  pp_location loc ^^^ pp_colour_identifier str
