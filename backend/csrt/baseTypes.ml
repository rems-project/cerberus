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
  | Map of t * t

let is_struct = function
  | Struct tag -> Some tag
  | _ -> None

let rec equal t t' = 
  match t, t' with
  | Unit, Unit -> true
  | Bool, Bool -> true
  | Integer, Integer -> true
  | Loc, Loc -> true
  | Array, Array -> true
  | List t, List t' -> equal t t'
  | Tuple ts, Tuple ts' -> List.equal equal ts ts'
  | Struct t, Struct t' -> Sym.equal t t'
  | Set t, Set t' -> equal t t'
  | Map (t1, t2), Map (t1', t2') -> equal t1 t1' && equal t2 t2'

  | Unit, _
  | Bool, _
  | Integer, _
  | Loc, _
  | Array, _
  | List _, _
  | Tuple _, _
  | Struct _, _
  | Set _, _
  | Map _, _ ->
     false


let compare bt bt' =
  match bt, bt' with
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

  | List bt, List bt' -> compare bt bt'
  | List _, _ -> -1

  | Tuple ts, Tuple ts' ->
     List.compare compare ts ts'
  | Tuple _, _ -> -1

  | Struct t, Struct t' -> Sym.compare t t'
  | Struct _, _ -> -1

  | Set t, Set t' -> compare t t'
  | Set _, _ -> -1

  | Map (t1,t2), Map (t1',t2') -> 
     let c = compare t1 t1' in
     if c = 0 then compare t2 t2' else c
  | Map _, _ -> -1



let pp bt = 
  let rec aux atomic bt = 
    let mparens pped = if atomic then parens pped else pped in
    match bt with
    | Unit -> !^"void"
    | Bool -> !^"bool"
    | Integer -> !^"integer"
    | Loc -> !^"pointer"
    | Array -> !^ "array"
    | List bt -> mparens ((!^ "list") ^^^ aux true bt)
    | Tuple nbts -> parens (flow_map (comma) (aux false) nbts)
    | Struct sym -> mparens (!^"struct" ^^^ Sym.pp sym)
    | Set t -> mparens (!^"set" ^^^ parens (aux false t))
    | Map (t1,t2) -> mparens (!^"map" ^^ langle ^^ aux false t1 ^^ comma ^^ aux false t2 ^^ rangle)
  in
  aux false bt


let json bt : Yojson.Safe.t =
  `String (Pp.plain (pp bt))

open Sctypes

let of_sct (Sctype (_, sct_)) = 
  match sct_ with
  | Void -> Unit
  | Integer _ -> Integer
  | Pointer _ -> Loc
  | Struct tag -> Struct tag
  | Function _ -> Debug_ocaml.error "todo: function types"
