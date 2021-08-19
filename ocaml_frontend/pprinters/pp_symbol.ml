open Symbol
open Pp_prelude
open Location_ocaml





let to_string (Symbol (dig, n, sd)) =
  let symbol_description_to_string = function
    | SD_None -> 
       "a" 
    | SD_Id str -> 
       str 
    | SD_ObjectAddress name -> 
       "&" ^ name
    | SD_Return -> 
       "return"
    (* | SD_Pointee (env, descr) -> 
     *    "(" ^ symbol_description_to_string descr ^ ")@" ^ env
     * | SD_PredOutput (env, pred, output) ->
     *    "(" ^ pred ^ ".." ^ output ^ ")@" ^ env        *)
    | SD_FunArg i ->
       "ARG" ^ string_of_int i
  in
  let str = symbol_description_to_string sd in
  str ^ "_" ^ string_of_int n (*^ "_" ^ (try Digest.to_hex dig with _ -> "invalid")*)

let to_string_pretty (Symbol (_, n, sd) as s) =
  let add_number name = name ^ "{" ^ string_of_int n ^ "}" in
  let maybe_add_number name = 
     if !Debug_ocaml.debug_level > 4 
     then add_number name
     else name
  in
  let symbol_description = function
    | SD_None -> 
       to_string s
    | SD_Id name -> 
       name
    | SD_ObjectAddress name -> 
       "&" ^ name
    | SD_Return -> 
       "return"
    (* | SD_Pointee (env, descr) -> 
     *    "(" ^ symbol_description descr ^ ")@" ^ env
     * | SD_PredOutput (env, pred, output) ->
     *    "(" ^ pred ^ ".." ^ output ^ ")@" ^ env        *)
    | SD_FunArg i ->
       "ARG" ^ string_of_int i
  in
  match sd with
  | SD_None -> to_string s
  | _ -> maybe_add_number (symbol_description sd)

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
