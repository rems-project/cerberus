Require Import BaseTypes.
Require Import IndexTerms.
Require Import Sym.
Require Import LogicalConstraints.
Require Import Locations.
Require Import Request.
Require Import ReturnTypes.

(* Define the logical argument type *)
Inductive logical_argument_type (i : Type) : Type :=
  | Define : (Sym.t * IndexTerms.t) -> info -> logical_argument_type i -> logical_argument_type i
  | Resource : (Sym.t * (Request.t * BaseTypes.t)) -> info -> logical_argument_type i -> logical_argument_type i
  | Constraint : LogicalConstraints.logical_constraint -> info -> logical_argument_type i -> logical_argument_type i
  | I : i -> logical_argument_type i.

(* Type alias for the main type *)
Definition t (i : Type) := logical_argument_type i.

(* Additional type aliases *)
Definition packing := logical_argument_type IndexTerms.t.
Definition lft := logical_argument_type LogicalReturnTypes.t.
