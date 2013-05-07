open BinInt
open Datatypes
open Sumbool
open ZArith_dec
open Zeven

val coq_Z_lt_ge_bool : coq_Z -> coq_Z -> bool

val coq_Z_ge_lt_bool : coq_Z -> coq_Z -> bool

val coq_Z_le_gt_bool : coq_Z -> coq_Z -> bool

val coq_Z_gt_le_bool : coq_Z -> coq_Z -> bool

val coq_Z_eq_bool : coq_Z -> coq_Z -> bool

val coq_Z_noteq_bool : coq_Z -> coq_Z -> bool

val coq_Zeven_odd_bool : coq_Z -> bool

val coq_Zle_bool : coq_Z -> coq_Z -> bool

val coq_Zge_bool : coq_Z -> coq_Z -> bool

val coq_Zlt_bool : coq_Z -> coq_Z -> bool

val coq_Zgt_bool : coq_Z -> coq_Z -> bool

val coq_Zeq_bool : coq_Z -> coq_Z -> bool

val coq_Zneq_bool : coq_Z -> coq_Z -> bool

val coq_Zle_bool_total : coq_Z -> coq_Z -> bool

