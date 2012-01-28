open BinInt
open BinPos
open Datatypes
open Peano

type __ = Obj.t

val coq_ZL4_inf : positive -> nat

val coq_Z_of_nat_complete_inf : coq_Z -> nat

val coq_Z_of_nat_set : (nat -> 'a1) -> coq_Z -> 'a1

val natlike_rec : 'a1 -> (coq_Z -> __ -> 'a1 -> 'a1) -> coq_Z -> 'a1

val natlike_rec2 : 'a1 -> (coq_Z -> __ -> 'a1 -> 'a1) -> coq_Z -> 'a1

val natlike_rec3 : 'a1 -> (coq_Z -> __ -> 'a1 -> 'a1) -> coq_Z -> 'a1

val coq_Zlt_0_rec :
  (coq_Z -> (coq_Z -> __ -> 'a1) -> __ -> 'a1) -> coq_Z -> 'a1

val coq_Z_lt_rec : (coq_Z -> (coq_Z -> __ -> 'a1) -> 'a1) -> coq_Z -> 'a1

val coq_Zlt_lower_bound_rec :
  coq_Z -> (coq_Z -> (coq_Z -> __ -> 'a1) -> __ -> 'a1) -> coq_Z -> 'a1

