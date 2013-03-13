open Datatypes

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
  | O -> m
  | S p -> S (plus p m)

(** val mult : nat -> nat -> nat **)

let rec mult n m =
  match n with
  | O -> O
  | S p -> plus m (mult p m)

(** val minus : nat -> nat -> nat **)

let rec minus n m =
  match n with
  | O -> n
  | S k ->
    (match m with
     | O -> n
     | S l -> minus k l)

