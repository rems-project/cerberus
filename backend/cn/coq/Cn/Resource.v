Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.FSets.FSetDecide.

Require Import Request.
Require Import IndexTerms.

Inductive output : Type := | O: IndexTerms.t -> output.

Definition predicate : Type := Request.Predicate.t * output.

Definition qpredicate : Type := Request.QPredicate.t * output.

Definition t : Type := Request.t * output.

Module Resource_as_MiniDecidableType <: MiniDecidableType.
  Definition t := t.
  Definition eq := @eq t.
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq.
    decide equality.
    -
      subst.
      decide equality.
      apply IndexTerm_as_MiniDecidableType.eq_dec.
    -
      admit.
  Admitted.
End Resource_as_MiniDecidableType.

Module Resource_as_DecidableType := Make_UDT Resource_as_MiniDecidableType.
Module ResSet := FSetWeakList.Make Resource_as_DecidableType.
Module ResSetDecide := FSetDecide.WDecide(ResSet).

Definition set_from_list (l : list t) : ResSet.t :=
  List.fold_left (fun s c => ResSet.add c s) l ResSet.empty.
