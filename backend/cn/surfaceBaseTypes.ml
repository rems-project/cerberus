(* copy of baseTypes.ml, adjusted *)

open Pp



type structrecord = BaseTypes.structrecord
let equal_structrecord = BaseTypes.equal_structrecord
let compare_structrecord = BaseTypes.compare_structrecord

type basetype =
  | Unit 
  | Bool
  | Integer
  | Real
  | Loc of Sctypes.t option
  | Datatype of Sym.t
  | Record of structrecord * member_types
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
  (Record (Nothing, info.c_params), 
   Datatype info.c_datatype_tag)


let rec pp = function
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Real -> !^"real"
  | Loc None -> !^"pointer"
  | Loc (Some ct) -> !^"pointer" ^^ angles (Sctypes.pp ct)
  | Datatype sym -> !^"datatype" ^^^ Sym.pp sym
  | Record (Struct sym, _) -> !^"struct" ^^^ Sym.pp sym
  | Record (Nothing, members) -> braces (flow_map comma (fun (s, bt) -> pp bt ^^^ Id.pp s) members)
  | Map (abt, rbt) -> !^"map" ^^ angles (pp abt ^^ comma ^^^ pp rbt)
  | List bt -> !^"list" ^^ angles (pp bt)
  | Tuple nbts -> !^"tuple" ^^ angles (flow_map comma pp nbts)
  | Set t -> !^"set" ^^ angles (pp t)
  (* | Option t -> !^"option" ^^ angles (pp t) *)



let json bt : Yojson.Safe.t =
  `String (Pp.plain (pp bt))



(*
let struct_bt = function
  | Struct tag -> tag 
  | bt -> Debug_ocaml.error 
           ("illtyped index term: not a struct type: " ^ Pp.plain (pp bt))

let record_bt = function
  | Record members -> members
  | bt -> Debug_ocaml.error 
           ("illtyped index term: not a member type: " ^ Pp.plain (pp bt))
*)

let is_map_bt = function
  | Map (abt, rbt) -> Some (abt, rbt)
  | _ -> None

let map_bt = function
  | Map (abt, rbt) -> (abt, rbt) 
  | bt -> Debug_ocaml.error 
           ("illtyped index term: not a map type: " ^ Pp.plain (pp bt))

let is_datatype_bt = function
  | Datatype sym -> Some sym
  | _ -> None

let is_list_bt = function
  | List bt -> Some bt
  | _ -> None


let make_map_bt abt rbt = Map (abt, rbt)

(* let option_bt = function *)
(*   | Option bt -> bt  *)
(*   | bt -> Debug_ocaml.error  *)
(*            ("illtyped index term: not an option type: " ^ Pp.plain (pp bt)) *)




let of_sct struct_decls = 
  let rec aux = function
    | Sctypes.Void -> Unit
    | Integer _ -> Integer
    | Array (sct, _) -> Map (Integer, aux sct)
    | Pointer ct -> Loc (Some ct)
    | Struct tag -> 
        let member_cts = Memory.(member_types (SymMap.find tag struct_decls)) in
        let member_bts = List.map_snd aux member_cts in
        Record (Struct tag, member_bts)
    | Function _ -> Debug_ocaml.error "todo: function types"
  in
  aux


let rec hash = function
  | Unit -> 0
  | Bool -> 1
  | Integer -> 2
  | Real -> 3
  | Loc _ -> 4
  | List _ -> 5
  | Tuple _ -> 6
  | Set _ -> 7
  (* | Option _ -> 8 *)
  | Record (Struct tag, _) -> 1000 + Sym.num tag
  | Record (Nothing, members) -> 3000 + List.length members
  | Datatype tag -> 4000 + Sym.num tag
  | Map (abt,rbt) -> 2000 + hash abt + hash rbt








module BT = BaseTypes

let rec of_basetype = function
  | BT.Unit -> Unit
  | BT.Bool -> Bool
  | BT.Integer -> Integer
  | BT.Real -> Real
  | BT.Loc -> Loc None
  | BT.Datatype tag -> Datatype tag
  | BT.Record (sr,member_types) -> Record (sr,List.map_snd of_basetype member_types)
  | BT.Map (bt1, bt2) -> Map (of_basetype bt1, of_basetype bt2)
  | BT.List bt -> List (of_basetype bt)
  | BT.Tuple bts -> Tuple (List.map of_basetype bts)
  | BT.Set bt -> Set (of_basetype bt)


let rec to_basetype = function
  | Unit -> BT.Unit
  | Bool -> BT.Bool
  | Integer -> BT.Integer
  | Real -> BT.Real
  | Loc _ -> BT.Loc
  | Datatype tag -> BT.Datatype tag
  | Record (sr,member_types) -> BT.Record (sr,List.map_snd to_basetype member_types)
  | Map (bt1, bt2) -> BT.Map (to_basetype bt1, to_basetype bt2)
  | List bt -> BT.List (to_basetype bt)
  | Tuple bts -> BT.Tuple (List.map to_basetype bts)
  | Set bt -> BT.Set (to_basetype bt)
