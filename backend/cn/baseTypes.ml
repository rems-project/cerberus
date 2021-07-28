open Pp

type tag = Sym.t
type member = Id.t


type t =
  | Unit 
  | Bool
  | Integer
  | Real
  | Loc
  | List of t
  | Tuple of t list
  | Struct of tag
  | Set of t
  | Option of t
  | Array of t * t

let is_struct = function
  | Struct tag -> Some tag
  | _ -> None

let get_option_type = function
  | Option bt -> bt
  | _ -> Debug_ocaml.error "not an option type"

let rec equal t t' = 
  match t, t' with
  | Unit, Unit -> true
  | Bool, Bool -> true
  | Integer, Integer -> true
  | Real, Real -> true
  | Loc, Loc -> true
  | List t, List t' -> equal t t'
  | Tuple ts, Tuple ts' -> List.equal equal ts ts'
  | Struct t, Struct t' -> Sym.equal t t'
  | Set t, Set t' -> equal t t'
  | Option t, Option t' -> equal t t'
  | Array (ts,t), Array (ts',t') -> 
     equal ts ts' && equal t t'

  | Unit, _
  | Bool, _
  | Integer, _
  | Real, _
  | Loc, _
  | List _, _
  | Tuple _, _
  | Struct _, _
  | Set _, _
  | Option _, _ 
  | Array _, _
    ->
     false



let rec pp bt = 
  match bt with
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Real -> !^"real"
  | Loc -> !^"pointer"
  | List bt -> !^"list" ^^ angles (pp bt)
  | Tuple nbts -> !^"tuple" ^^ angles (flow_map comma pp nbts)
  | Struct sym -> !^"struct" ^^^ Sym.pp sym
  | Set t -> !^"set" ^^ angles (pp t)
  | Option t -> !^"option" ^^ angles (pp t)
  | Array (abt,rbt) -> 
     begin match abt with
     | Integer -> pp rbt ^^ lbracket ^^ rbracket
     | _ -> pp rbt ^^ parens (pp abt)
     end



let json bt : Yojson.Safe.t =
  `String (Pp.plain (pp bt))






let array_bt = function
  | Array (abt, rbt) -> (abt, rbt) 
  | _ -> Debug_ocaml.error "illtyped index term: not an array"



open Sctypes

let rec of_sct (Sctype (_, sct_)) = 
  match sct_ with
  | Void -> Unit
  | Integer _ -> Integer
  | Array (sct, _) -> Array (Integer, of_sct sct)
  | Pointer _ -> Loc
  | Struct tag -> Struct tag
  | Function _ -> Debug_ocaml.error "todo: function types"



let hash = function
  | Unit -> 0
  | Bool -> 1
  | Integer -> 2
  | Real -> 3
  | Loc -> 4
  | List _ -> 5
  | Tuple _ -> 6
  | Struct _ -> 7
  | Set _ -> 8
  | Option _ -> 9
  | Array _ -> 10
