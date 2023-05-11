open Symbol
open Cerb_pp_prelude
open Cerb_location

let pp_cn_sym_nums = ref false

let to_string (Symbol (_, n, sd)) =
  match sd with
    | SD_Id str | SD_ObjectAddress str | SD_FunArgValue str ->
        str ^ "_" ^ string_of_int n
    | _ ->
        "a_" ^ string_of_int n

let to_string_pretty ?(is_human=false) ?(executable_spec=false) (Symbol (_, n, sd)) =
  let add_number name = name ^ "{" ^ string_of_int n ^ "}" in
  let maybe_add_number name = 
   if !Cerb_debug.debug_level > 4 then
      add_number name
     else
      name
  in
  match sd with
    | SD_Id str 
    | SD_ObjectAddress str
    | SD_FunArgValue str ->
        maybe_add_number str
    | SD_unnamed_tag loc ->
        if is_human then
          "(unnamed tag at " ^ Cerb_location.location_to_string loc ^ ")"
        else
          "__cerbty_unnamed_tag_" ^ string_of_int n
    | SD_CN_Id str -> 
        if executable_spec then
          str
        else
          (Printf.printf "In non executable spec case\n";
          "a_" ^ string_of_int n
          )
    | _ ->
        Printf.printf "In default pp_id case";
        "a_" ^ string_of_int n

(* enriched versions used by the CN backend *)
let to_string_cn (Symbol (dig, n, sd)) =
  let symbol_description_to_string = function
    | SD_None -> 
        "a"
    | SD_unnamed_tag _ ->
        "__cerbty_unnamed_tag_" ^ string_of_int n
    | SD_Id str -> 
        str 
    | SD_CN_Id str -> 
        str 
    | SD_ObjectAddress name -> 
        "&" ^ name
    | SD_Return -> 
        "return"
    (* | SD_Pointee (env, descr) -> 
      *    "(" ^ symbol_description_to_string descr ^ ")@" ^ env
      * | SD_PredOutput (env, pred, output) ->
      *    "(" ^ pred ^ ".." ^ output ^ ")@" ^ env        *)
    | SD_FunArgValue str ->
       str
    | SD_FunArg (_, i) ->
        "ARG" ^ string_of_int i
  in
  let str = symbol_description_to_string sd in
  str ^ "_" ^ string_of_int n (*^ "_" ^ (try Digest.to_hex dig with _ -> "invalid")*)
  
let to_string_pretty_cn (Symbol (_, n, sd) as s) =
  let add_number name = name ^ "{" ^ string_of_int n ^ "}" in
  let maybe_add_number name = 
      if (!pp_cn_sym_nums) || (!Cerb_debug.debug_level > 4)
      then add_number name
      else name
  in
  let symbol_description = function
    | SD_None -> 
        to_string s
    | SD_unnamed_tag _ ->
        "__cerbty_unnamed_tag_" ^ string_of_int n
    | SD_Id name -> 
        name
    | SD_CN_Id name -> 
        name
    | SD_ObjectAddress name -> 
        "&" ^ name
    | SD_Return -> 
        "return"
    (* | SD_Pointee (env, descr) -> 
      *    "(" ^ symbol_description descr ^ ")@" ^ env
      * | SD_PredOutput (env, pred, output) ->
      *    "(" ^ pred ^ ".." ^ output ^ ")@" ^ env        *)
    | SD_FunArgValue str ->
       str
    | SD_FunArg (_, i) ->
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
  !^(Cerb_colour.ansi_format [Yellow] id)


let pp_prefix = function
  | PrefSource (_, syms) ->
      P.braces (P.separate_map P.dot (fun sym -> !^ (to_string_pretty sym)) syms)
  | PrefOther str ->
      P.braces (!^ str)
  | PrefStringLiteral _ ->
      P.braces (!^ "string literal")
  | PrefTemporaryLifetime _ ->
      P.braces (!^ "rvalue temporary")
  | PrefFunArg (_, _, n) ->
      P.braces (!^ ("arg" ^ string_of_int n))
  | PrefMalloc ->
      P.braces (!^ "malloc'd")
  | PrefCompoundLiteral _ ->
      P.braces (!^ "compound literal")


let pp_identifier ?(clever=false) (Symbol.Identifier (loc, str)) =
  begin if Cerb_debug.get_debug_level () >= 5 then
    pp_location ~clever loc ^^ P.space
  else
    P.empty
  end ^^ pp_colour_identifier str
