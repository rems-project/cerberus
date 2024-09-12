type sign =
  | Signed
  | Unsigned
[@@deriving eq, ord]

type 'a t_gen =
  | Unit
  | Bool
  | Integer
  | Bits of sign * int
  | Real
  | Alloc_id
  | Loc of 'a
  | CType
  | Struct of Sym.t
  | Datatype of Sym.t
  | Record of 'a member_types_gen
  | Map of 'a t_gen * 'a t_gen
  | List of 'a t_gen
  | Tuple of 'a t_gen list
  | Set of 'a t_gen
[@@deriving eq, ord, map]

and 'a member_types_gen = (Id.t * 'a t_gen) list

(* This seems to require that variables aren't simply unique to the constructor, but to
   the entire datatype declaration. This is weird, and is probably an arbitrary
   restriction that should be lifted, but it will require effort. *)
module Datatype = struct
  type 'a info =
    { constrs : Sym.t list;
      all_params : 'a member_types_gen
    }

  type 'a constr_info =
    { params : 'a member_types_gen;
      datatype_tag : Sym.t
    }
end

let rec pp pp_loc =
  let open Pp in
  function
  | Unit -> !^"void"
  | Bool -> !^"boolean"
  | Integer -> !^"integer"
  | Bits (Signed, n) -> !^("i" ^ string_of_int n)
  | Bits (Unsigned, n) -> !^("u" ^ string_of_int n)
  | Real -> !^"real"
  | Loc x -> pp_loc x
  | Alloc_id -> !^"alloc_id"
  | CType -> !^"ctype"
  | Struct sym -> !^"struct" ^^^ Sym.pp sym
  | Datatype sym -> !^"datatype" ^^^ Sym.pp sym
  | Record members ->
    braces (flow_map comma (fun (s, bt) -> pp pp_loc bt ^^^ Id.pp s) members)
  | Map (abt, rbt) -> !^"map" ^^ angles (pp pp_loc abt ^^ comma ^^^ pp pp_loc rbt)
  | List bt -> !^"cn_list" ^^ angles (pp pp_loc bt)
  | Tuple nbts -> !^"cn_tuple" ^^ angles (flow_map comma (pp pp_loc) nbts)
  | Set t -> !^"cn_set" ^^ angles (pp pp_loc t)


(* | Option t -> !^"option" ^^ angles (pp t) *)

let rec contained =
  let containeds bts = List.concat_map contained bts in
  function
  | Unit -> []
  | Bool -> []
  | Integer -> []
  | Bits _ -> []
  | Real -> []
  | Alloc_id -> []
  | Loc _ -> []
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


let json pp_loc bt = `String (Pp.plain (pp pp_loc bt))

let struct_bt pp_loc = function
  | Struct tag -> tag
  | bt ->
    Cerb_debug.error ("illtyped index term: not a struct type: " ^ Pp.plain (pp pp_loc bt))


let record_bt pp_loc = function
  | Record members -> members
  | bt ->
    Cerb_debug.error ("illtyped index term: not a member type: " ^ Pp.plain (pp pp_loc bt))


let is_map_bt = function Map (abt, rbt) -> Some (abt, rbt) | _ -> None

let map_bt pp_loc = function
  | Map (abt, rbt) -> (abt, rbt)
  | bt ->
    Cerb_debug.error ("illtyped index term: not a map type: " ^ Pp.plain (pp pp_loc bt))


let is_datatype_bt = function Datatype sym -> Some sym | _ -> None

let datatype_bt pp_loc = function
  | Datatype sym -> sym
  | bt ->
    Cerb_debug.error ("illtyped index term: not a datatype: " ^ Pp.plain (pp pp_loc bt))


let is_list_bt = function List bt -> Some bt | _ -> None

let is_tuple_bt = function Tuple bts -> Some bts | _ -> None

let is_bits_bt = function Bits (sign, n) -> Some (sign, n) | _ -> None

let make_map_bt abt rbt = Map (abt, rbt)

(* let option_bt = function *)
(*   | Option bt -> bt  *)
(*   | bt -> Cerb_debug.error  *)
(*            ("illtyped index term: not an option type: " ^ Pp.plain (pp bt)) *)

let rec of_sct loc is_signed size_of = function
  | Sctypes.Void -> Unit
  | Integer ity -> Bits ((if is_signed ity then Signed else Unsigned), size_of ity * 8)
  | Array (sct, _) ->
    Map (uintptr_bt loc is_signed size_of, of_sct loc is_signed size_of sct)
  | Pointer sct -> Loc (loc sct)
  | Struct tag -> Struct tag
  | Function _ -> Cerb_debug.error "todo: function types"


and uintptr_bt loc is_signed size_of =
  of_sct loc is_signed size_of Sctypes.(Integer (Unsigned Intptr_t))


and intptr_bt loc is_signed size_of =
  of_sct loc is_signed size_of Sctypes.(Integer (Signed Intptr_t))


and size_bt loc is_signed size_of = of_sct loc is_signed size_of Sctypes.(Integer Size_t)

let rec hash = function
  | Unit -> 0
  | Bool -> 1
  | Integer -> 2
  | Real -> 3
  | Alloc_id -> 4
  | Loc () -> 5
  | CType -> 6
  | List _ -> 7
  | Tuple _ -> 8
  | Set _ -> 9
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


let normalise_to_range_bt pp_loc bt z =
  match is_bits_bt bt with
  | Some (sign, sz) -> normalise_to_range (sign, sz) z
  | _ -> failwith ("normalise_to_range: not bits type: " ^ Pp.plain (pp pp_loc bt))


let pick_integer_encoding_type z =
  match
    List.find_opt
      (fun k -> fits_range k z)
      [ (Signed, 32); (Unsigned, 64); (Signed, 64); (Unsigned, 128); (Signed, 128) ]
  with
  | Some (sign, sz) -> Some (Bits (sign, sz))
  | _ -> None


module Surface = struct
  type loc_t = Sctypes.t option

  type t = loc_t t_gen

  type member_types = loc_t member_types_gen

  let equal : t -> t -> _ = equal_t_gen (Option.equal Sctypes.equal)

  let compare : t -> t -> _ = compare_t_gen (Option.compare Sctypes.compare)

  type nonrec datatype_info = loc_t Datatype.info

  type nonrec constr_info = loc_t Datatype.constr_info

  let pp_loc =
    Pp.(
      Option.fold ~none:!^"pointer" ~some:(fun sct ->
        !^"pointer" ^^ angles (Sctypes.pp sct)))


  let pp : t -> _ = pp pp_loc

  let json (bt : t) = json pp_loc bt

  let is_map_bt = is_map_bt

  let map_bt = map_bt pp_loc

  let is_datatype_bt = is_datatype_bt

  let is_bits_bt = is_bits_bt

  let make_map_bt = make_map_bt

  let of_sct = of_sct Option.some

  let unintptr_bt = uintptr_bt Option.some

  let intptr_bt = intptr_bt Option.some

  let size_bt = size_bt Option.some

  let inj x : t = map_t_gen (Fun.const None) x

  let proj : t -> _ = map_t_gen (Fun.const ())
end

module Unit = struct
  type nonrec t = unit t_gen

  type member_types = unit member_types_gen

  let equal : t -> t -> _ = equal_t_gen (fun () () -> true)

  let compare : t -> t -> _ = compare_t_gen (fun () () -> 0)

  type dt_info = unit Datatype.info

  type constr_info = unit Datatype.constr_info

  let pp_loc () = Pp.(!^"pointer")

  let pp = pp pp_loc

  let json = json pp_loc

  let struct_bt = struct_bt pp_loc

  let record_bt = record_bt pp_loc

  let map_bt = map_bt pp_loc

  let datatype_bt = datatype_bt pp_loc

  let of_sct = of_sct (Fun.const ())

  let uintptr_bt = uintptr_bt (Fun.const ())

  let intptr_bt = intptr_bt (Fun.const ())

  let size_bt = size_bt (Fun.const ())

  let normalise_to_range_bt = normalise_to_range_bt pp_loc
end

include Unit
