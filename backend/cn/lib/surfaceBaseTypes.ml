(* copy of baseTypes.ml, adjusted *)

open Pp

type basetype =
  | Unit
  | Bool
  | Integer
  | Bits of BaseTypes.sign * int
  | Real
  | CType
  | Alloc_id
  | Loc of Sctypes.t option
  | Struct of Sym.t
  | Datatype of Sym.t
  | Record of member_types
  | Map of basetype * basetype
  | List of basetype
  | Tuple of basetype list
  | Set of basetype (* | Option of basetype *)
[@@deriving eq, ord]

and member_types = (Id.t * basetype) list

type t = basetype

let equal = equal_basetype

let compare = compare_basetype

type datatype_info =
  { constrs : Sym.t list;
    all_params : member_types
  }

type constr_info =
  { params : member_types;
    datatype_tag : Sym.t
  }

let cons_dom_rng info = (Record info.params, Datatype info.datatype_tag)

let rec pp = function
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Bits (Signed, n) -> !^("i" ^ string_of_int n)
  | Bits (Unsigned, n) -> !^("u" ^ string_of_int n)
  | Real -> !^"real"
  | CType -> !^"ctype"
  | Alloc_id -> !^"alloc_id"
  | Loc (Some ct) -> !^"pointer" ^^ angles (Sctypes.pp ct)
  | Loc None -> !^"pointer"
  | Struct sym -> !^"struct" ^^^ Sym.pp sym
  | Datatype sym -> !^"datatype" ^^^ Sym.pp sym
  | Record members -> braces (flow_map comma (fun (s, bt) -> pp bt ^^^ Id.pp s) members)
  | Map (abt, rbt) -> !^"map" ^^ angles (pp abt ^^ comma ^^^ pp rbt)
  | List bt -> !^"cn_list" ^^ angles (pp bt)
  | Tuple nbts -> !^"cn_tuple" ^^ angles (flow_map comma pp nbts)
  | Set t -> !^"cn_set" ^^ angles (pp t)


(* | Option t -> !^"option" ^^ angles (pp t) *)

let json bt : Yojson.Safe.t = `String (Pp.plain (pp bt))

let struct_bt = function
  | Struct tag -> tag
  | bt -> Cerb_debug.error ("illtyped index term: not a struct type: " ^ Pp.plain (pp bt))


let record_bt = function
  | Record members -> members
  | bt -> Cerb_debug.error ("illtyped index term: not a member type: " ^ Pp.plain (pp bt))


let is_map_bt = function Map (abt, rbt) -> Some (abt, rbt) | _ -> None

let map_bt = function
  | Map (abt, rbt) -> (abt, rbt)
  | bt -> Cerb_debug.error ("illtyped index term: not a map type: " ^ Pp.plain (pp bt))


let is_datatype_bt = function Datatype sym -> Some sym | _ -> None

let is_bits_bt = function Bits (sign, sz) -> Some (sign, sz) | _ -> None

let make_map_bt abt rbt = Map (abt, rbt)

let rec of_sct is_signed size_of = function
  | Sctypes.Void -> Unit
  | Integer ity -> Bits ((if is_signed ity then Signed else Unsigned), size_of ity * 8)
  | Array (sct, _) -> Map (uintptr_bt is_signed size_of, of_sct is_signed size_of sct)
  | Pointer ct -> Loc (Some ct)
  | Struct tag -> Struct tag
  | Function _ -> Cerb_debug.error "todo: function types"


and uintptr_bt is_signed size_of =
  of_sct is_signed size_of Sctypes.(Integer (Unsigned Intptr_t))


and intptr_bt is_signed size_of =
  of_sct is_signed size_of Sctypes.(Integer (Signed Intptr_t))


and size_bt is_signed size_of = of_sct is_signed size_of Sctypes.(Integer Size_t)

module BT = BaseTypes

let rec of_basetype = function
  | BT.Unit -> Unit
  | BT.Bool -> Bool
  | BT.Integer -> Integer
  | BT.Bits (sign, n) -> Bits (sign, n)
  | BT.Real -> Real
  | BT.CType -> CType
  | BT.Alloc_id -> Alloc_id
  | BT.Loc -> Loc None
  | BT.Struct tag -> Struct tag
  | BT.Datatype tag -> Datatype tag
  | BT.Record member_types -> Record (List.map_snd of_basetype member_types)
  | BT.Map (bt1, bt2) -> Map (of_basetype bt1, of_basetype bt2)
  | BT.List bt -> List (of_basetype bt)
  | BT.Tuple bts -> Tuple (List.map of_basetype bts)
  | BT.Set bt -> Set (of_basetype bt)


let rec to_basetype = function
  | Unit -> BT.Unit
  | Bool -> BT.Bool
  | Integer -> BT.Integer
  | Bits (sign, n) -> BT.Bits (sign, n)
  | Real -> BT.Real
  | CType -> BT.CType
  | Alloc_id -> BT.Alloc_id
  | Loc _ -> BT.Loc
  | Struct tag -> BT.Struct tag
  | Datatype tag -> BT.Datatype tag
  | Record member_types -> BT.Record (List.map_snd to_basetype member_types)
  | Map (bt1, bt2) -> BT.Map (to_basetype bt1, to_basetype bt2)
  | List bt -> BT.List (to_basetype bt)
  | Tuple bts -> BT.Tuple (List.map to_basetype bts)
  | Set bt -> BT.Set (to_basetype bt)
