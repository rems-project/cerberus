Require Import BaseTypes.
Require Import IndexTerms.
Require Import Symbol.

(* Define the logical constraint type *)
Inductive logical_constraint : Type :=
  | T : IndexTerms.t -> logical_constraint
  | Forall : (sym * BaseTypes.t) -> IndexTerms.t -> logical_constraint. 

Definition t := logical_constraint.
