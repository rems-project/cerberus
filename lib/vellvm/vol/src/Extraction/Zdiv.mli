open BinInt
open BinPos
open ZArith_dec
open Zbool

val coq_Zdiv_eucl_POS : positive -> coq_Z -> coq_Z*coq_Z

val coq_Zdiv_eucl : coq_Z -> coq_Z -> coq_Z*coq_Z

val coq_Zdiv : coq_Z -> coq_Z -> coq_Z

val coq_Zmod : coq_Z -> coq_Z -> coq_Z

val coq_Zdiv_eucl_exist : coq_Z -> coq_Z -> (coq_Z*coq_Z)

val coq_Zmod_POS : positive -> coq_Z -> coq_Z

val coq_Zmod' : coq_Z -> coq_Z -> coq_Z

val coq_Zdiv_eucl_extended : coq_Z -> coq_Z -> (coq_Z*coq_Z)

