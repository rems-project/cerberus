open BinNat
open BinPos
open Datatypes

(** val nat_of_N : coq_N -> nat **)

let nat_of_N = function
  | N0 -> O
  | Npos p -> nat_of_P p

(** val coq_N_of_nat : nat -> coq_N **)

let coq_N_of_nat = function
  | O -> N0
  | S n' -> Npos (coq_P_of_succ_nat n')

