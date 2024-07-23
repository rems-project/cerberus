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
  | Set of basetype (* | Option of basetype *)
[@@deriving eq, ord]

and member_types = (Id.t * basetype) list

type t = basetype

let equal = equal_basetype

let compare = compare_basetype

(* This seems to require that variables aren't simply unique to the constructor, but to
   the entire datatype declaration. This is weird, and is probably an arbitrary
   restriction that should be lifted, but it will require effort. *)
type datatype_info =
  { dt_constrs : Sym.t list;
    dt_all_params : member_types
  }

type constr_info =
  { c_params : member_types;
    c_datatype_tag : Sym.t
  }

let cons_dom_rng info = (Record info.c_params, Datatype info.c_datatype_tag)

let rec pp = function
  | Unit -> !^"void"
  | Bool -> !^"bool"
  | Integer -> !^"integer"
  | Bits (Signed, n) -> !^("i" ^ string_of_int n)
  | Bits (Unsigned, n) -> !^("u" ^ string_of_int n)
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

let rec contained : t -> t list = function
  | Unit -> []
  | Bool -> []
  | Integer -> []
  | Bits _ -> []
  | Real -> []
  | Alloc_id -> []
  | Loc -> []
  | CType -> []
  | Struct _ -> []
  | Datatype _ -> []
  | Record ms ->
    let mts = List.map snd ms in
    mts @ containeds mts
  | Map (abt, rbt) -> abt :: rbt :: containeds [ abt; rbt ]
  | List bt -> bt :: contained bt
  | Tuple bts -> bts @ containeds bts
  | Set bt -> bt :: contained bt


and containeds bts = List.concat_map contained bts

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

let datatype_bt = function
  | Datatype sym -> sym
  | bt -> Cerb_debug.error ("illtyped index term: not a datatype: " ^ Pp.plain (pp bt))


let is_list_bt = function List bt -> Some bt | _ -> None

let is_tuple_bt = function Tuple bts -> Some bts | _ -> None

let is_bits_bt = function Bits (sign, n) -> Some (sign, n) | _ -> None

let make_map_bt abt rbt = Map (abt, rbt)

(* let option_bt = function *)
(*   | Option bt -> bt  *)
(*   | bt -> Cerb_debug.error  *)
(*            ("illtyped index term: not an option type: " ^ Pp.plain (pp bt)) *)

let rec of_sct is_signed size_of = function
  | Sctypes.Void -> Unit
  | Integer ity -> Bits ((if is_signed ity then Signed else Unsigned), size_of ity * 8)
  | Array (sct, _) -> Map (uintptr_bt is_signed size_of, of_sct is_signed size_of sct)
  | Pointer _ -> Loc
  | Struct tag -> Struct tag
  | Function _ -> Cerb_debug.error "todo: function types"


and uintptr_bt is_signed size_of =
  of_sct is_signed size_of Sctypes.(Integer (Unsigned Intptr_t))


and intptr_bt is_signed size_of =
  of_sct is_signed size_of Sctypes.(Integer (Signed Intptr_t))


and size_bt is_signed size_of = of_sct is_signed size_of Sctypes.(Integer Size_t)

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
  | Map (abt, rbt) -> 2000 + hash abt + hash rbt
  | Bits (Signed, n) -> 5000 + n
  | Bits (Unsigned, n) -> 6000 + n


(* checking/coercing numeric literals into bits range *)
let bits_cardinality n = Z.pow (Z.of_int 2) n

let bits_range = function
  | Unsigned, sz -> (Z.zero, Z.sub (bits_cardinality sz) Z.one)
  | Signed, sz ->
    let half_card = bits_cardinality (sz - 1) in
    (Z.sub Z.zero half_card, Z.sub half_card Z.one)


let fits_range (sign, sz) z =
  let minInt, maxInt = bits_range (sign, sz) in
  Z.leq minInt z && Z.leq z maxInt


let normalise_to_range (sign, sz) z =
  let card = bits_cardinality sz in
  let rec norm_u z =
    if Z.leq Z.zero z then
      Z.rem z card
    else
      norm_u (Z.sub card (norm_u (Z.sub Z.zero z)))
  in
  let norm z =
    match sign with
    | Unsigned -> norm_u z
    | Signed ->
      let z = norm_u z in
      let _, maxInt = bits_range (sign, sz) in
      if Z.leq z maxInt then z else Z.sub z card
  in
  let z2 = norm z in
  assert (fits_range (sign, sz) z2);
  if fits_range (sign, sz) z then
    assert (Z.equal z2 z)
  else
    ();
  z2


let normalise_to_range_bt bt z =
  match is_bits_bt bt with
  | Some (sign, sz) -> normalise_to_range (sign, sz) z
  | _ -> failwith ("normalise_to_range: not bits type: " ^ Pp.plain (pp bt))


let pick_integer_encoding_type z =
  match
    List.find_opt
      (fun k -> fits_range k z)
      [ (Signed, 32); (Unsigned, 64); (Signed, 64); (Unsigned, 128); (Signed, 128) ]
  with
  | Some (sign, sz) -> Some (Bits (sign, sz))
  | _ -> None
