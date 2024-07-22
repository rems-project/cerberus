module IT = IndexTerms
open Constraints
open Utils
module CF = Cerb_frontend
open CF

type gen =
  | Arbitrary of Ctype.ctype
  | Return of Ctype.ctype * IT.t
  | Filter of Sym.sym * Ctype.ctype * IT.t * gen
  | Map of Sym.sym * Ctype.ctype * IT.t * gen
  | Alloc of Ctype.ctype * Sym.sym
  | Struct of Ctype.ctype * (string * Sym.sym) list

let rec string_of_gen (g : gen) : string =
  match g with
  | Arbitrary ty ->
    "arbitrary<" ^ string_of_ctype ty ^ ">"
  | Return (ty, e) ->
    "return<"
    ^ string_of_ctype ty
    ^ ">("
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ")"
  | Filter (x, ty, e, g') ->
    "filter("
    ^ "|"
    ^ codify_sym x
    ^ ": "
    ^ string_of_ctype ty
    ^ "| "
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ", "
    ^ string_of_gen g'
    ^ ")"
  | Map (x, ty, e, g') ->
    "map("
    ^ "|"
    ^ codify_sym x
    ^ ": "
    ^ string_of_ctype ty
    ^ "| "
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ", "
    ^ string_of_gen g'
    ^ ")"
  | Alloc (ty, x) ->
    "alloc<" ^ string_of_ctype ty ^ ">(" ^ codify_sym x ^ ")"
  | Struct (ty, ms) ->
    "struct<"
    ^ string_of_ctype ty
    ^ ">("
    ^ String.concat ", " (List.map (fun (x, g') -> "." ^ x ^ ": " ^ codify_sym g') ms)
    ^ ")"


type gen_context = (Symbol.sym * gen) list

let string_of_gen_context (gtx : gen_context) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, g) -> "\"" ^ codify_sym x ^ "\" <- \"" ^ string_of_gen g ^ "\"")
         gtx)
  ^ " }"


let filter_gen (x : Symbol.sym) (ty : Ctype.ctype) (cs : constraints) : gen =
  match cs with
  | _ :: _ ->
    Filter (x, ty, IT.and_ cs (Cerb_location.other __FUNCTION__), Arbitrary ty)
  | [] ->
    Arbitrary ty


let compile_gen (x : Symbol.sym) (ty : Ctype.ctype) (e : IT.t) (cs : constraints) : gen =
  match e with
  | IT (Sym x', _, _) when sym_codified_equal x x' ->
    filter_gen x ty cs
  | _ ->
    Return (ty, e)
