Require Import List.
Require Import String.

Require Import BaseTypes.
Require Import IndexTerms.
Require Import Cerberus.Symbol.
Require Import Locations.
Require Import SCtypes.

Inductive init : Type :=
  | Init
  | Uninit.

Inductive name : Type :=
  | Owned : SCtypes.t -> init -> name 
  | PName : sym -> name.

Module Predicate.
  Record t : Type := mk {
    name : name;
    pointer : IndexTerms.t;
    iargs : list IndexTerms.t
  }.
End Predicate.

Module QPredicate.
  Record t : Type := mk {
    name : name;
    pointer : IndexTerms.t;
    q : Symbol.t * BaseTypes.t;
    q_loc : Locations.t;
    step : IndexTerms.t;
    permission : IndexTerms.t;
    iargs : list IndexTerms.t
  }.
End QPredicate.

Inductive request_t : Type :=
  | P : Predicate.t -> request_t
  | Q : QPredicate.t -> request_t.

Definition t := request_t. 

Inductive subsumed : name -> name -> Prop :=
  | Subsumed_equal : forall n1 n2,
    n1 = n2 ->
    subsumed n1 n2
  | Subsumed_owned : forall ct ct',
    ct = ct' -> subsumed (Owned ct Uninit) (Owned ct' Init).

