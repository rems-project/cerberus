open List
open PPrint
open Pp_tools
module Loc=Location


type field_access = {pointer: Sym.t; strct: Sym.t; field: Sym.t}

type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  | List of t
  | Tuple of t list
  | Struct of Sym.t
  | StructField of field_access

let is_unit = function Unit -> true | _ -> false
let is_bool = function Bool -> true | _ -> false
let is_int = function Int -> true | _ -> false
let is_loc = function Loc -> true | _ -> false
let is_array = function Array -> true | _ -> false
let is_struct = function Struct s -> Some s | _ -> None
let is_structfield = function StructField p -> Some p | _ -> None


let rec pp = function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "int"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  | List bt -> parens ((!^ "list") ^^^ pp bt)
  | Tuple nbts -> parens (!^ "tuple" ^^^ flow_map (break 1) pp (nbts))
  | Struct sym -> parens (!^ "struct" ^^^ Sym.pp sym)
  | StructField sf -> 
     let args = Sym.pp sf.pointer ^^ dot ^^ Sym.pp sf.field in
     parens (squotes (Sym.pp sf.strct) ^^ minus ^^ !^"field" ^^^ args)


let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

let subst _sym _sym' bt = bt


