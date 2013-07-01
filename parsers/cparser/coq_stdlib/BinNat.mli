open BinPos
open Datatypes
open Specif

type coq_N =
| N0
| Npos of positive

val coq_N_rect : 'a1 -> (positive -> 'a1) -> coq_N -> 'a1

val coq_N_rec : 'a1 -> (positive -> 'a1) -> coq_N -> 'a1

val coq_Ndiscr : coq_N -> positive sumor

val coq_Ndouble_plus_one : coq_N -> coq_N

val coq_Ndouble : coq_N -> coq_N

val coq_Nsucc : coq_N -> coq_N

val coq_Npred : coq_N -> coq_N

val coq_Nplus : coq_N -> coq_N -> coq_N

val coq_Nminus : coq_N -> coq_N -> coq_N

val coq_Nmult : coq_N -> coq_N -> coq_N

val coq_Neqb : coq_N -> coq_N -> bool

val coq_Ncompare : coq_N -> coq_N -> comparison

val coq_Nmin : coq_N -> coq_N -> coq_N

val coq_Nmax : coq_N -> coq_N -> coq_N

val coq_N_eq_dec : coq_N -> coq_N -> bool

val coq_N_rec_double :
  coq_N -> 'a1 -> (coq_N -> 'a1 -> 'a1) -> (coq_N -> 'a1 -> 'a1) -> 'a1

val coq_Nrect : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1

val coq_Nrec : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1

val coq_Ndiv2 : coq_N -> coq_N

