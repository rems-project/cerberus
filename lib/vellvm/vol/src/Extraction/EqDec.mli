open Datatypes

type 'a dec_eq = bool

type 'a coq_EqDec = 'a -> 'a -> bool

val eq_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool

val nat_eqdec : nat coq_EqDec

val bool_eqdec : bool coq_EqDec

val unit_eqdec : unit coq_EqDec

val list_eqdec : 'a1 coq_EqDec -> 'a1 list coq_EqDec

val coq_K_dec : 'a1 coq_EqDec -> 'a1 -> 'a2 -> 'a2

