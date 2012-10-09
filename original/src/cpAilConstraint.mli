type t

type constr
type constant

val compare_const : constant -> constant -> int

val empty : t
val make : constr -> t
val from_list : constr list -> t

val compare : t -> t -> int
val union : t -> t -> t
val add : t -> constr -> t

val fresh_name : unit -> constant
val fresh_named : string -> constant
val fresh_address : unit -> constant
val const : BatBig_int.t -> constant
val fn : string -> constant list -> constant

val tt : constr

val eq  : constant -> constant -> constr
val neq : constant -> constant -> constr

val null : constant

val offset : constant -> constant -> constant -> constant

(* Integer specific assertions. *)
val zero : constant
val one  : constant

val plus  : constant -> constant -> constant
val minus : constant -> constant -> constant
val modulo : constant -> constant -> constant
val mult : constant -> constant -> constant
val div : constant -> constant -> constant
val pow : constant -> constant

val bit_and : constant -> constant -> constant
val bit_or : constant -> constant -> constant
val bit_xor : constant -> constant -> constant

val le : constant -> constant -> constr
val lt : constant -> constant -> constr
val ge : constant -> constant -> constr
val gt : constant -> constant -> constr

val neg : constr -> constr
val conj    : constr -> constr -> constr
val disj    : constr -> constr -> constr
val implies : constr -> constr -> constr
val case : constr -> constr -> constr -> constr

val conv_int : CpRange.range -> constr -> constant -> constr

val undef : constr

val mem : constr -> t -> bool

module Print : sig
  val pp_constant : constant -> Pprint.document
  val pp_constr : constr -> Pprint.document
  val pp : t -> Pprint.document

  val pp_set : t BatSet.t -> Pprint.document

  val pp_constant_latex : constant -> Pprint.document
end

module Process : sig
  exception Invalid
  exception Partial of t

  type p
  type address =
    | Base of CpSymbol.t
    | Displaced of CpSymbol.t * int * constant
    | NullAddress

  val make : t -> p

  val conj : p -> constr -> p
  val union : p -> t -> p
  val address : p -> constant -> p * address

  val complete : p -> t
end
