Require Import BaseTypes.
Require Import Sym.
Require Import IndexTerms.
Require Import LogicalReturnTypes.
Require Import Locations.

(* Define the return type *)
Inductive return_type : Type :=
  | Computational : (Sym.t * BaseTypes.t) -> info -> LogicalReturnTypes.t -> return_type.

(* Type alias for the main type *)
Definition t := return_type. 