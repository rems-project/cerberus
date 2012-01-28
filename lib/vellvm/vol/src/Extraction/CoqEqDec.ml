open EquivDec

type 'a coq_EqDec_eq = 'a -> 'a -> bool

(** val eq_dec : 'a1 coq_EqDec_eq -> 'a1 -> 'a1 -> bool **)

let eq_dec eqDec_eq =
  eqDec_eq

(** val coq_EqDec_eq_of_EqDec : 'a1 coq_EqDec -> 'a1 coq_EqDec_eq **)

let coq_EqDec_eq_of_EqDec h =
  h

