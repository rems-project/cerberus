open Datatypes
open Peano

type 'u coq_U_list = 'u list

type 'u coq_U_enumerable = 'u coq_U_list

val coq_U_in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 coq_U_list -> bool

val coq_U_sum : ('a1 -> nat) -> 'a1 coq_U_list -> nat

val coq_U_enumerable_sum : ('a1 -> nat) -> 'a1 coq_U_enumerable -> nat

