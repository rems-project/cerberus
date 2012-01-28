open Datatypes
open Specif

(** val coq_O_or_S : nat -> nat sumor **)

let coq_O_or_S = function
  | O -> Coq_inright
  | S n0 -> Coq_inleft n0

(** val eq_nat_dec : nat -> nat -> bool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> true
              | S m0 -> false)
    | S n0 -> (match m with
                 | O -> false
                 | S m0 -> eq_nat_dec n0 m0)

