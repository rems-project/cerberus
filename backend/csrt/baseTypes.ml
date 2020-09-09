open List
open Pp
module Loc=Locations


type tag = Tag of Sym.t
type member = Member of string

let pp_tag (Tag s) = 
  Sym.pp s


type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  | List of t
  | Tuple of t list
  | Struct of tag
  | FunctionPointer of Sym.t


let is_struct = function
  | Struct tag -> Some tag
  | _ -> None

(* TODO *)
let rec equal t1 t2 = 
  match t1, t2 with
  | Unit, Unit -> true
  | Bool, Bool -> true
  | Int, Int -> true
  | Loc, Loc -> true
  | Array, Array -> true
  | List t1', List t2' -> equal t1' t2'
  | Tuple ts1', Tuple ts2' -> equals ts1' ts2'
  | Struct (Tag tag1), Struct (Tag tag2) -> Sym.equal tag1 tag2
  | FunctionPointer s1, FunctionPointer s2 -> Sym.equal s1 s2
  | _, _ -> false

and equals ts1 ts2 = 
  match ts1, ts2 with
  | [], [] -> true
  | t1::ts1', t2::ts2' -> equal t1 t2 && equals ts1' ts2'
  | _, _ -> false


let equals ts1 ts2 = 
  List.length ts1 = List.length ts2 &&
  for_all (fun (t1,t2) -> equal t1 t2) (combine ts1 ts2)

let rec pp atomic = 
  let mparens pped = if atomic then parens pped else pped in
  function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "integer"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  | List bt -> mparens ((!^ "list") ^^^ pp true bt)
  | Tuple nbts -> mparens (!^ "tuple" ^^^ flow_map (comma ^^ break 1) (pp false) (nbts))
  | Struct (Tag sym) -> 
     mparens (!^"struct" ^^^ Sym.pp sym)
  | FunctionPointer p ->
     parens (!^"function" ^^^ Sym.pp p)




