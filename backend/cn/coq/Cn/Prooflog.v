Require Import ZArith.
Require Import String.
Require Import List.
Import ListNotations.

From Cerberus Require Import Location.
Require Import ErrorCommon.
Require Import Request.
Require Import Resource.


Definition Context_t := unit. (* TODO: placeholder *)

Inductive resource_inference_type : Type :=
  | PredicateRequest : ErrorCommon.situation ->
                       Request.Predicate.t ->
                       option (Location.t * string) ->
                       (Resource.predicate * list Z) ->
                       resource_inference_type.

Inductive log_entry : Type :=
  | ResourceInferenceStep : Context_t -> resource_inference_type -> Context_t -> log_entry.

Definition log : Type := list log_entry.

