Require Import String.
Require Import List.
Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.DecidableTypeEx.

Require Import Cerberus.Location.

Definition t := Location.t.

Module Locations_t_as_MiniDecidableType <: MiniDecidableType.
  Definition t := t.
  Definition eq := @eq t.
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    intros x y.
    unfold eq.
    repeat decide equality.
  Qed.
End Locations_t_as_MiniDecidableType.

(* Define the info type *)
Definition info := (t * option string)%type.

Definition path := list t.
