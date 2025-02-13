Require Import BaseTypes.
Require Import IndexTerms.
Require Import Sym.

(* Define the logical constraint type *)
Inductive logical_constraint : Type :=
  | T : IndexTerms.t -> logical_constraint
  | Forall : (Sym.t * BaseTypes.t) -> IndexTerms.t -> logical_constraint. 

Definition t := logical_constraint.
