(* Module BaseTypes -- CN base type syntax *)

(* Used to define the sign of a bit vector in cn *)
type sign =
  | Signed
  | Unsigned

val equal_sign : sign -> sign -> Ppx_deriving_runtime.bool

val compare_sign : sign -> sign -> Ppx_deriving_runtime.int

(* CN basetypes *)
type basetype =
  | Unit (* equalivalent to C's void *)
  | Bool (* true | false *)
  | Integer (* Unused nowadays since change to Bits (bit vectors) *)
  | Bits of sign * int
    (* How CN represents C's ints : sign = int sign, int = int size.
       Ex: u32 means unsigned int of size 32 bits *)
  | Real (* Unused *)
  | Alloc_id (* Memory model stuff*)
  | Loc (* C's pointers*)
  | CType
  | Struct of Sym.t (* C's struct : C's user-defined datatypes*)
  | Datatype of Sym.t (* CN's datatype : CN's user-defined datatypes *)
  | Record of member_types (* How CN datatypes are usually constructed *)
  | Map of basetype * basetype (* how Arrays are stored within CN *)
  | List of basetype
  | Tuple of basetype list
  | Set of basetype

and member_types = (Id.t * basetype) list (* Values within Records *)

(* Automatically generated *)
val equal_basetype : basetype -> basetype -> Ppx_deriving_runtime.bool

val compare_basetype : basetype -> basetype -> Ppx_deriving_runtime.int

val equal_member_types : member_types -> member_types -> Ppx_deriving_runtime.bool

val compare_member_types : member_types -> member_types -> Ppx_deriving_runtime.int

type t = basetype

(* In original file, equal = equal_basetype & compare = compare_basetype. *)
val equal : basetype -> basetype -> Ppx_deriving_runtime.bool

val compare : basetype -> basetype -> Ppx_deriving_runtime.int

(* This seems to require that variables aren't simply unique to the
   constructor, but to the entire datatype declaration.
   This is weird, and is probably an arbitrary restriction that should be
   lifted, but it will require effort. *)
type datatype_info =
  { dt_constrs : Sym.t list;
    dt_all_params : member_types
  }

type constr_info =
  { c_params : member_types;
    c_datatype_tag : Sym.t
  }

val cons_dom_rng : constr_info -> basetype * basetype

val pp : basetype -> Pp.document (* how the basetypes are printed Ex: Unit -> !^"void" *)

val contained : t -> t list

val containeds : t list -> t list

val json : basetype -> Yojson.Safe.t

(* functions remove constructor and returns its arguments *)
(* is_* functions return an option of the arguments, while the others return the arguments*)
val struct_bt : basetype -> Sym.t

val record_bt : basetype -> member_types

val is_map_bt : basetype -> (basetype * basetype) option

val map_bt : basetype -> basetype * basetype

val is_datatype_bt : basetype -> Sym.t option

val datatype_bt : basetype -> Sym.t

val is_list_bt : basetype -> basetype option

val is_tuple_bt : basetype -> basetype list option

val is_bits_bt : basetype -> (sign * int) option

(* Creates a map basetype given two basetypes *)
val make_map_bt : basetype -> basetype -> basetype

(* Converts from cerberus/C ctype to CN basetypes *)
val of_sct
  :  (Sctypes.IntegerTypes.integerType -> bool) ->
  (Sctypes.IntegerTypes.integerType -> int) ->
  Sctypes.ctype ->
  basetype

(* Converts from cerberus/C pointer to CN basetypes *)
val uintptr_bt
  :  (Sctypes.IntegerTypes.integerType -> bool) ->
  (Sctypes.IntegerTypes.integerType -> int) ->
  basetype

val intptr_bt
  :  (Sctypes.IntegerTypes.integerType -> bool) ->
  (Sctypes.IntegerTypes.integerType -> int) ->
  basetype

(* Converts from cerberus/C size_t to CN basetypes *)
val size_bt
  :  (Sctypes.IntegerTypes.integerType -> bool) ->
  (Sctypes.IntegerTypes.integerType -> int) ->
  basetype

(* converts basetypes to unique integer hash values *)
val hash : basetype -> int

(* checking/coercing numeric literals into bits range *)
val bits_cardinality : int -> Z.t

(* Defines the bit range for a Bit vector*)
val bits_range : sign * int -> Z.t * Z.t

(* Determines whether an integer is within a Bit vector's range*)
val fits_range : sign * int -> Z.t -> bool

(* Ensures that an integer is adjusted to fit within a bit-vectors bit range *)
val normalise_to_range : sign * int -> Z.t -> Z.t

val normalise_to_range_bt : basetype -> Z.t -> Z.t

(* Depending on the given integers size, it will return a Bits option that handle the size*)
val pick_integer_encoding_type : Z.t -> basetype option
