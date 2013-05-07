open BinInt
open BinPos
open Datatypes

val coq_Zeven_bool : coq_Z -> bool

val coq_Zodd_bool : coq_Z -> bool

val coq_Zeven_odd_dec : coq_Z -> bool

val coq_Zeven_dec : coq_Z -> bool

val coq_Zodd_dec : coq_Z -> bool

val coq_Zdiv2 : coq_Z -> coq_Z

val coq_Z_modulo_2 : coq_Z -> (coq_Z, coq_Z) sum

val coq_Zsplit2 : coq_Z -> (coq_Z*coq_Z)

