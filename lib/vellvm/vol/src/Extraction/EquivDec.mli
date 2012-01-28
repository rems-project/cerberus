open Bool
open Datatypes
open Peano_dec

type 'a coq_EqDec = 'a -> 'a -> bool

val equiv_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool

val swap_sumbool : bool -> bool

val nequiv_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool

val equiv_decb : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool

val nequiv_decb : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool

val nat_eq_eqdec : nat coq_EqDec

val bool_eqdec : bool coq_EqDec

val unit_eqdec : unit coq_EqDec

val prod_eqdec : 'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1*'a2) coq_EqDec

val sum_eqdec : 'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1, 'a2) sum coq_EqDec

val bool_function_eqdec : 'a1 coq_EqDec -> (bool -> 'a1) coq_EqDec

val list_eqdec : 'a1 coq_EqDec -> 'a1 list coq_EqDec

