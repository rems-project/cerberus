Require Import BaseTypes.
Require Import IndexTerms.
Require Import LogicalConstraints.
Require Import Symbol.
Require Import Locations.
Require Import Request.

(* Define the logical return type *)
Inductive logical_return_type : Type :=
  | Define : (sym * IndexTerms.t) -> info -> logical_return_type -> logical_return_type
  | Resource : (sym * (request_t * BaseTypes.t)) -> info -> logical_return_type -> logical_return_type
  | Constraint : LogicalConstraints.logical_constraint -> info -> logical_return_type -> logical_return_type
  | I : logical_return_type.

Definition t := logical_return_type.
    