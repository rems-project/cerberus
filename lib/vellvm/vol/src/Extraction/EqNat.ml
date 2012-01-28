open Datatypes

(** val eq_nat_decide : nat -> nat -> bool **)

let rec eq_nat_decide n m =
  match n with
    | O -> (match m with
              | O -> true
              | S n0 -> false)
    | S n0 -> (match m with
                 | O -> false
                 | S n1 -> eq_nat_decide n0 n1)

(** val beq_nat : nat -> nat -> bool **)

let rec beq_nat n m =
  match n with
    | O -> (match m with
              | O -> true
              | S n0 -> false)
    | S n1 -> (match m with
                 | O -> false
                 | S m1 -> beq_nat n1 m1)

