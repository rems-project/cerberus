Require Import BaseTypes.
Require Import IndexTerms.
Require Import Symbol.
Require Import LogicalConstraints.
Require Import LogicalArgumentTypes.
Require Import Locations.
Require Import ReturnTypes.
Require Import LogicalReturnTypes.
Require Import False.

(* Define the argument type *)
Inductive argument_type (i : Type) : Type :=
  | Computational : (Symbol.t * BaseTypes.t) -> info -> argument_type i -> argument_type i
  | L : LogicalArgumentTypes.t i -> argument_type i.

(* Type alias for the main type *)
Definition t (i : Type) := argument_type i.

(* Additional type aliases *)
Definition ift := argument_type IndexTerms.t.
Definition ft := argument_type ReturnTypes.t.
Definition lt := argument_type False.t.
Definition lemmat := argument_type LogicalReturnTypes.t. 
