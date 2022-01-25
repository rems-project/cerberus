open Pp


type tag = Sym.t
let equal_tag = Sym.equal
let compare_tag = Sym.compare

type member = Id.t
let equal_member = Id.equal
let compare_member = Id.compare


type basetype =
  | Unit 
  | Bool
  | Integer
  | Real
  | Loc
  | Struct of tag
  | Map of basetype * basetype
  | List of basetype
  | Tuple of basetype list
  | Set of basetype
  (* | Option of basetype *)
[@@deriving eq, ord]

type t = basetype


let equal = equal_basetype
let compare = compare_basetype


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
  (* | Option t -> !^"option" ^^ angles (pp t) *)



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

(* let option_bt = function *)
(*   | Option bt -> bt  *)
(*   | bt -> Debug_ocaml.error  *)
(*            ("illtyped index term: not an option type: " ^ Pp.plain (pp bt)) *)



let rec of_sct = function
  | Sctypes.Void -> Unit
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
  (* | Option _ -> 8 *)
  | Struct tag -> 1000 + Sym.num tag
  | Map (abt,rbt) -> 2000 + hash abt + hash rbt
