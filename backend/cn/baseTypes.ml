open Pp

type tag = Sym.t
type member = Id.t


type t =
  | Unit 
  | Bool
  | Integer
  | Real
  | Loc
  | Struct of tag
  | Map of t * t
  | List of t
  | Tuple of t list
  | Set of t
  | Option of t


let is_struct = function
  | Struct tag -> Some tag
  | _ -> None

let rec equal t t' = 
  match t, t' with
  | Unit, Unit -> true
  | Bool, Bool -> true
  | Integer, Integer -> true
  | Real, Real -> true
  | Loc, Loc -> true
  | Struct t, Struct t' -> Sym.equal t t'
  | Map (t1,t2), Map (t1',t2') -> equal t1 t1' && equal t2 t2'
  | List t, List t' -> equal t t'
  | Tuple ts, Tuple ts' -> List.equal equal ts ts'
  | Set t, Set t' -> equal t t'
  | Option t, Option t' -> equal t t'
  | Unit, _
  | Bool, _
  | Integer, _
  | Real, _
  | Loc, _
  | Struct _, _
  | Map _, _
  | List _, _
  | Tuple _, _
  | Set _, _
  | Option _, _ 
    ->
     false



let rec pp = function
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Real -> !^"real"
  | Loc -> !^"pointer"
  | Struct sym -> !^"struct" ^^^ Sym.pp sym
  | Map (abt, rbt) -> !^"map" ^^ angles (pp abt ^^ comma ^^^ pp rbt)
  | List bt -> !^"list" ^^ angles (pp bt)
  | Tuple nbts -> !^"tuple" ^^ angles (flow_map comma pp nbts)
  | Set t -> !^"set" ^^ angles (pp t)
  | Option t -> !^"option" ^^ angles (pp t)



let json bt : Yojson.Safe.t =
  `String (Pp.plain (pp bt))




let struct_bt = function
  | Struct tag -> tag 
  | bt -> Debug_ocaml.error 
           ("illtyped index term: not a struct type: " ^ Pp.plain (pp bt))

let is_map_bt = function
  | Map (abt, rbt) -> Some (abt, rbt)
  | _ -> None

let map_bt = function
  | Map (abt, rbt) -> (abt, rbt) 
  | bt -> Debug_ocaml.error 
           ("illtyped index term: not a map type: " ^ Pp.plain (pp bt))

let option_bt = function
  | Option bt -> bt 
  | bt -> Debug_ocaml.error 
           ("illtyped index term: not an option type: " ^ Pp.plain (pp bt))



let rec of_sct (Sctypes.Sctype (_, sct_)) = 
  match sct_ with
  | Void -> Unit
  | Integer _ -> Integer
  | Array (sct, _) -> Map (Integer, of_sct sct)
  | Pointer _ -> Loc
  | Struct tag -> Struct tag
  | Function _ -> Debug_ocaml.error "todo: function types"



let rec hash = function
  | Unit -> 0
  | Bool -> 1
  | Integer -> 2
  | Real -> 3
  | Loc -> 4
  | List _ -> 5
  | Tuple _ -> 6
  | Set _ -> 7
  | Option _ -> 8
  | Struct tag -> 1000 + Sym.num tag
  | Map (abt,rbt) -> 2000 + hash abt + hash rbt
