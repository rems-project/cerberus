open BinNat
open BinPos
open Datatypes

type coq_Z =
| Z0
| Zpos of positive
| Zneg of positive

val coq_Z_rect :
  'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> coq_Z -> 'a1

val coq_Z_rec : 'a1 -> (positive -> 'a1) -> (positive -> 'a1) -> coq_Z -> 'a1

val coq_Zdouble_plus_one : coq_Z -> coq_Z

val coq_Zdouble_minus_one : coq_Z -> coq_Z

val coq_Zdouble : coq_Z -> coq_Z

val coq_ZPminus : positive -> positive -> coq_Z

val coq_Zplus : coq_Z -> coq_Z -> coq_Z

val coq_Zopp : coq_Z -> coq_Z

val coq_Zsucc : coq_Z -> coq_Z

val coq_Zpred : coq_Z -> coq_Z

val coq_Zminus : coq_Z -> coq_Z -> coq_Z

val coq_Zmult : coq_Z -> coq_Z -> coq_Z

val coq_Zcompare : coq_Z -> coq_Z -> comparison

val coq_Zsgn : coq_Z -> coq_Z

val coq_Zsucc' : coq_Z -> coq_Z

val coq_Zpred' : coq_Z -> coq_Z

val coq_Zplus' : coq_Z -> coq_Z -> coq_Z

val coq_Zabs_nat : coq_Z -> nat

val coq_Zabs : coq_Z -> coq_Z

val coq_Z_of_nat : nat -> coq_Z

val coq_Zabs_N : coq_Z -> coq_N

val coq_Z_of_N : coq_N -> coq_Z

