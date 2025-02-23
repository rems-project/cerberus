Require Import Request.
Require Import IndexTerms.

Inductive output : Type := | O: IndexTerms.t -> output.

Definition predicate : Type := Request.Predicate.t * output.

Definition qpredicate : Type := Request.QPredicate.t * output.

Definition t : Type := Request.t * output.

