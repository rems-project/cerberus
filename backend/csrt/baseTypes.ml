open Pp

type tag = Sym.t
type member = Id.t


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
  | Set of t

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
  | Struct t1, Struct t2 -> Sym.equal t1 t2
  | FunctionPointer s1, FunctionPointer s2 -> Sym.equal s1 s2
  | Set t1, Set t2 -> equal t1 t2

  | Unit, _
  | Bool, _
  | Integer, _
  | Loc, _
  | Array, _
  | List _, _
  | Tuple _, _
  | Struct _, _
  | FunctionPointer _, _
  | Set _, _ ->
     false

let rec pp atomic bt = 
  let mparens pped = if atomic then parens pped else pped in
  match bt with
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Loc -> !^"pointer"
  | Array -> !^ "array"
  | List bt -> mparens ((!^ "list") ^^^ pp true bt)
  | Tuple nbts -> parens (flow_map (comma) (pp false) nbts)
  | Struct sym -> mparens (!^"struct" ^^^ Sym.pp sym)
  | FunctionPointer p -> mparens (!^"function" ^^^ Sym.pp p)
  | Set t -> mparens (!^"set" ^^^ parens (pp false t))




open Sctypes

let of_sct (Sctype (_, sct_)) = 
  match sct_ with
  | Void -> Unit
  | Integer _ -> Integer
  | Pointer _ -> Loc
  | Struct tag -> Struct tag


