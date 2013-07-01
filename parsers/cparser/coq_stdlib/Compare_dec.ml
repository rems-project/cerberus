open Datatypes
open Specif

(** val zerop : nat -> bool **)

let zerop = function
| O -> true
| S n0 -> false

(** val lt_eq_lt_dec : nat -> nat -> bool sumor **)

let rec lt_eq_lt_dec n m =
  match n with
  | O ->
    (match m with
     | O -> Coq_inleft false
     | S m0 -> Coq_inleft true)
  | S n0 ->
    (match m with
     | O -> Coq_inright
     | S m0 -> lt_eq_lt_dec n0 m0)

(** val gt_eq_gt_dec : nat -> nat -> bool sumor **)

let gt_eq_gt_dec n m =
  lt_eq_lt_dec n m

(** val le_lt_dec : nat -> nat -> bool **)

let rec le_lt_dec n m =
  match n with
  | O -> true
  | S n0 ->
    (match m with
     | O -> false
     | S m0 -> le_lt_dec n0 m0)

(** val le_le_S_dec : nat -> nat -> bool **)

let le_le_S_dec n m =
  le_lt_dec n m

(** val le_ge_dec : nat -> nat -> bool **)

let le_ge_dec n m =
  le_lt_dec n m

(** val le_gt_dec : nat -> nat -> bool **)

let le_gt_dec n m =
  le_lt_dec n m

(** val le_lt_eq_dec : nat -> nat -> bool **)

let le_lt_eq_dec n m =
  let s = lt_eq_lt_dec n m in
  (match s with
   | Coq_inleft s0 -> s0
   | Coq_inright -> assert false (* absurd case *))

(** val le_dec : nat -> nat -> bool **)

let le_dec n m =
  le_gt_dec n m

(** val lt_dec : nat -> nat -> bool **)

let lt_dec n m =
  le_dec (S n) m

(** val gt_dec : nat -> nat -> bool **)

let gt_dec n m =
  lt_dec m n

(** val ge_dec : nat -> nat -> bool **)

let ge_dec n m =
  le_dec m n

(** val nat_compare : nat -> nat -> comparison **)

let rec nat_compare n m =
  match n with
  | O ->
    (match m with
     | O -> Eq
     | S n0 -> Lt)
  | S n' ->
    (match m with
     | O -> Gt
     | S m' -> nat_compare n' m')

(** val nat_compare_alt : nat -> nat -> comparison **)

let nat_compare_alt n m =
  match lt_eq_lt_dec n m with
  | Coq_inleft s -> if s then Lt else Eq
  | Coq_inright -> Gt

(** val leb : nat -> nat -> bool **)

let rec leb m x =
  match m with
  | O -> true
  | S m' ->
    (match x with
     | O -> false
     | S n' -> leb m' n')

