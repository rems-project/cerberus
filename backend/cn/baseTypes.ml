open Pp

type sign =
  | Signed
  | Unsigned
[@@deriving eq, ord]

type basetype =
  | Unit 
  | Bool
  | Integer
  | Bits of sign * int
  | Real
  | Alloc_id
  | Loc
  | CType
  | Struct of Sym.t
  | Datatype of Sym.t
  | Record of member_types
  | Map of basetype * basetype
  | List of basetype
  | Tuple of basetype list
  | Set of basetype
  (* | Option of basetype *)
[@@deriving eq, ord]

and member_types =
  (Id.t * basetype) list


type t = basetype


let equal = equal_basetype
let compare = compare_basetype


type datatype_info = {
  dt_constrs: Sym.t list;
  dt_all_params: member_types;
}
type constr_info = {
  c_params: member_types;
  c_datatype_tag: Sym.t
}

let cons_dom_rng info =
  (Record info.c_params, Datatype info.c_datatype_tag)


let rec pp = function
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Bits (Signed, n) -> !^("i"^string_of_int n)
  | Bits (Unsigned, n) -> !^("u"^string_of_int n)
  | Real -> !^"real"
  | Loc -> !^"pointer"
  | Alloc_id -> !^"alloc_id"
  | CType -> !^"ctype"
  | Struct sym -> !^"struct" ^^^ Sym.pp sym
  | Datatype sym -> !^"datatype" ^^^ Sym.pp sym
  | Record members -> braces (flow_map comma (fun (s, bt) -> pp bt ^^^ Id.pp s) members)
  | Map (abt, rbt) -> !^"map" ^^ angles (pp abt ^^ comma ^^^ pp rbt)
  | List bt -> !^"list" ^^ angles (pp bt)
  | Tuple nbts -> !^"tuple" ^^ angles (flow_map comma pp nbts)
  | Set t -> !^"set" ^^ angles (pp t)
  (* | Option t -> !^"option" ^^ angles (pp t) *)



let json bt : Yojson.Safe.t =
  `String (Pp.plain (pp bt))




let struct_bt = function
  | Struct tag -> tag 
  | bt -> Cerb_debug.error 
           ("illtyped index term: not a struct type: " ^ Pp.plain (pp bt))

let record_bt = function
  | Record members -> members
  | bt -> Cerb_debug.error 
           ("illtyped index term: not a member type: " ^ Pp.plain (pp bt))

let is_map_bt = function
  | Map (abt, rbt) -> Some (abt, rbt)
  | _ -> None

let map_bt = function
  | Map (abt, rbt) -> (abt, rbt) 
  | bt -> Cerb_debug.error 
           ("illtyped index term: not a map type: " ^ Pp.plain (pp bt))

let is_datatype_bt = function
  | Datatype sym -> Some sym
  | _ -> None

let datatype_bt = function
  | Datatype sym -> sym
  | bt -> Cerb_debug.error 
            ("illtyped index term: not a datatype: " ^ Pp.plain (pp bt))

let is_list_bt = function
  | List bt -> Some bt
  | _ -> None

let is_tuple_bt = function
  | Tuple bts -> Some bts
  | _ -> None


let make_map_bt abt rbt = Map (abt, rbt)

(* let option_bt = function *)
(*   | Option bt -> bt  *)
(*   | bt -> Cerb_debug.error  *)
(*            ("illtyped index term: not an option type: " ^ Pp.plain (pp bt)) *)


let rec of_sct is_signed size_of = function
  | Sctypes.Void -> Unit
  | Integer ity -> Bits ((if is_signed ity then Signed else Unsigned), size_of ity)
  | Array (sct, _) -> Map (Integer, of_sct is_signed size_of sct)
  | Pointer _ -> Loc
  | Struct tag -> Struct tag
  | Function _ -> Cerb_debug.error "todo: function types"



let rec hash = function
  | Unit -> 0
  | Bool -> 1
  | Integer -> 2
  | Real -> 3
  | Alloc_id -> 4
  | Loc -> 5
  | CType -> 6
  | List _ -> 7
  | Tuple _ -> 8
  | Set _ -> 9
  (* | Option _ -> 8 *)
  | Struct tag -> 1000 + Sym.num tag
  | Datatype tag -> 4000 + Sym.num tag
  | Record _ -> 3000
  | Map (abt,rbt) -> 2000 + hash abt + hash rbt
  | Bits (Signed, n) -> 5000 + n
  | Bits (Unsigned, n) -> 6000 + n




