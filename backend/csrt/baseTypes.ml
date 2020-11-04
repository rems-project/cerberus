open Pp


type tag = Tag of Sym.t
type member = Member of string

let pp_tag (Tag s) = Sym.pp s
let tag_equal (Tag s) (Tag s') = Sym.equal s s'

let pp_member (Member s) = !^s

type t =
  | Unit 
  | Bool
  | Integer
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
  | Integer, Integer -> true
  | Loc, Loc -> true
  | Array, Array -> true
  | List t1', List t2' -> equal t1' t2'
  | Tuple ts1', Tuple ts2' -> List.equal equal ts1' ts2'
  | Struct t1, Struct t2 -> tag_equal t1 t2
  | FunctionPointer s1, FunctionPointer s2 -> Sym.equal s1 s2
  | _, _ -> false

let rec pp atomic bt = 
  let mparens pped = if atomic then parens pped else pped in
  match bt with
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Loc -> !^"location"
  | Array -> !^ "array"
  | List bt -> mparens ((!^ "list") ^/^ pp true bt)
  | Tuple nbts -> parens (flow_map (comma) (pp false) nbts)
  | Struct (Tag sym) -> mparens (!^"struct" ^/^ Sym.pp sym)
  | FunctionPointer p -> mparens (!^"function" ^/^ Sym.pp p)




