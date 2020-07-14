open Symbol
open Pp_prelude
open Location_ocaml


(* https://rosettacode.org/wiki/Non-decimal_radices/Convert *)
let to_base b v =
  let rec to_base' a v = if v = 0 then a else to_base' (v mod b :: a) (v / b) in
  to_base' [] v

let base26 n = 
  let aux = function
    | 0 -> "A"
    | 1 -> "B"
    | 2 -> "C"
    | 3 -> "D"
    | 4 -> "E"
    | 5 -> "F"
    | 6 -> "G"
    | 7 -> "H"
    | 8 -> "I"
    | 9 -> "J"
    | 10 -> "K"
    | 11 -> "L"
    | 12 -> "M"
    | 13 -> "N"
    | 14 -> "O"
    | 15 -> "P"
    | 16 -> "Q"
    | 17 -> "R"
    | 18 -> "S"
    | 19 -> "T"
    | 20 -> "U"
    | 21 -> "V"
    | 22 -> "W"
    | 23 -> "X"
    | 24 -> "Y"
    | 25 -> "Z"
    | _ -> failwith "cannot happen"
  in
  String.concat "" (List.map aux (to_base 26 n))

let to_string ?(compact = false) (Symbol (dig, n, str_opt)) =
  if compact then 
    let str = match str_opt with 
      | Some str -> str 
      | None -> ""
    in
    str ^ base26 n
  else
    let str = match str_opt with 
      | Some str -> str 
      | None -> "a" 
    in
    str ^ "_" ^ string_of_int n (*^ "_" ^ (try Digest.to_hex dig with _ -> "invalid")*)

let to_string_pretty ?(compact = false) (Symbol (_, n, name_opt) as s) =
  match name_opt with
  | Some name ->
      if compact && !Debug_ocaml.debug_level > 4 then
        name ^ "{" ^ base26 n ^ "}"
      else if !Debug_ocaml.debug_level > 4 then
        name ^ "{" ^ string_of_int n ^ "}"
      else
        name
  | None -> 
     to_string ~compact:compact s

(*
let to_string_latex (n, _) =
  "v" ^ "_" ^ "{" ^ string_of_int n ^ "}"

let to_string_id (n, _) = string_of_int n
*)


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
