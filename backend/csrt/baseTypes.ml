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
  | Set t1, Set t2 -> equal t1 t2

  | Unit, _
  | Bool, _
  | Integer, _
  | Loc, _
  | Array, _
  | List _, _
  | Tuple _, _
  | Struct _, _
  | Set _, _ ->
     false


let compare bt1 bt2 =
  match bt1, bt2 with
  | Unit, Unit -> 0
  | Unit, _ -> -1

  | Bool, Bool -> 0
  | Bool, _ -> -1

  | Integer, Integer -> 0
  | Integer, _ -> -1

  | Loc, Loc -> 0
  | Loc, _ -> -1

  | Array, Array -> 0
  | Array, _ -> -1

  | List bt1', List bt2' -> compare bt1' bt2'
  | List _, _ -> -1

  | Tuple bts1, Tuple bts2 ->
     List.compare compare bts1 bts2
  | Tuple _, _ -> -1

  | Struct tag1, Struct tag2 -> Sym.compare tag1 tag2
  | Struct _, _ -> -1

  | Set bt1, Set bt2 -> compare bt1 bt2
  | Set _, _ -> 1



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
  | Set t -> mparens (!^"set" ^^^ parens (pp false t))



let json bt : Yojson.Safe.t =
  `String (Pp.plain (pp false bt))

open Sctypes

let of_sct (Sctype (_, sct_)) = 
  match sct_ with
  | Void -> Unit
  | Integer _ -> Integer
  | Pointer _ -> Loc
  | Struct tag -> Struct tag
  | Function _ -> Debug_ocaml.error "todo: function types"
