open BinInt
open BinPos
open Datatypes
open List0
open ZArith_dec
open Zdiv

val peq : positive -> positive -> bool

val plt : positive -> positive -> bool

val positive_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1

val zeq : coq_Z -> coq_Z -> bool

val zlt : coq_Z -> coq_Z -> bool

val zle : coq_Z -> coq_Z -> bool

val coq_Zdivide_dec : coq_Z -> coq_Z -> bool

val nat_of_Z : coq_Z -> nat

val coq_ZRdiv : coq_Z -> coq_Z -> coq_Z

val align : coq_Z -> coq_Z -> coq_Z

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val sum_left_map : ('a1 -> 'a2) -> ('a1, 'a3) sum -> ('a2, 'a3) sum

val list_length_z_aux : 'a1 list -> coq_Z -> coq_Z

val list_length_z : 'a1 list -> coq_Z

val list_nth_z : 'a1 list -> coq_Z -> 'a1 option

val list_disjoint_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val list_norepet_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

val list_drop : nat -> 'a1 list -> 'a1 list

val list_repeat : nat -> 'a1 -> 'a1 list

val proj_sumbool : bool -> bool

