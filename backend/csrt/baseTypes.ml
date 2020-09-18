open Pp
module Loc=Locations


type tag = Tag of Sym.t
type member = Member of string

let pp_tag (Tag s) = Sym.pp s
let tag_equal (Tag s) (Tag s') = Sym.equal s s'


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
  | Tuple ts1', Tuple ts2' -> List.equal equal ts1' ts2'
  | Struct t1, Struct t2 -> tag_equal t1 t2
  | FunctionPointer s1, FunctionPointer s2 -> Sym.equal s1 s2
  | _, _ -> false

let rec pp atomic = 
  let mparens pped = if atomic then parens pped else pped in
  function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "integer"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  | List bt -> mparens ((!^ "list") ^^^ pp true bt)
  | Tuple nbts -> 
     mparens (!^ "tuple" ^^^ parens (flow_map (comma ^^ break 1) (pp false) nbts))
  | Struct (Tag sym) -> 
     mparens (!^"struct" ^^^ Sym.pp sym)
  | FunctionPointer p ->
     parens (!^"function" ^^^ Sym.pp p)




