open Ctype

type type_alias_map = {
  intN_t_alias: int -> integerBaseType option;
  int_leastN_t_alias: int -> integerBaseType option;
  int_fastN_t_alias: int -> integerBaseType option;
  intmax_t_alias: integerBaseType;
  intptr_t_alias: integerBaseType;
  wchar_t_alias: integerType;
  wint_t_alias: integerType;
  size_t_alias: integerType;
  ptrdiff_t_alias: integerType;
}

type implementation = {
  name: string;
  details: string;
  sizeof_pointer: int option;
  alignof_pointer: int option;
  max_alignment: int;
  is_signed_ity: integerType -> bool;
  sizeof_ity: integerType -> int option;
  precision_ity: integerType -> int option;
  sizeof_fty: floatingType -> int option;
  alignof_ity: integerType -> int option;
  alignof_fty: floatingType -> int option;
  register_enum: Symbol.sym -> Nat_big_num.num list -> bool;
  typeof_enum: Symbol.sym -> integerType;
  type_alias_map: type_alias_map;
}

val normalise_integerType: implementation -> integerType -> integerType

module type Implementation = sig
  val impl: implementation
end

module DefaultImpl: Implementation
(* module DefactoImpl: Implementation *)
module MorelloImpl: Implementation
module HafniumImpl: Implementation

val hafniumIntImpl: IntegerImpl.implementation

val set: implementation -> unit
val get: unit -> implementation

val alignof_proxy: (union_tag, (alignment option * ctype) list) Pmap.map -> ctype -> int option

