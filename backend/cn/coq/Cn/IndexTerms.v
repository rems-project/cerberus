Require Import List.
Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.DecidableTypeEx.

Require Import BaseTypes.
Require Import Terms.
Require Import Locations.

(* Type aliases *)
Definition t' := term BaseTypes.t.
Definition t := annot BaseTypes.t.

(* Pattern-related types *)
Definition bindings (bt: Type) := list (pattern bt * option (annot bt)).
Definition t_bindings := bindings BaseTypes.t. 

Module IndexTerm_as_MiniDecidableType <: MiniDecidableType.
  Definition t := t.
  Definition eq := @eq t.
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq.
    decide equality; subst.
    -
      repeat decide equality.
    -
      apply BasetTypes_t_as_MiniDecidableType.eq_dec.
    -
      admit.
  Admitted.
End IndexTerm_as_MiniDecidableType. 

Module IndexTerm_as_DecidableType := Make_UDT IndexTerm_as_MiniDecidableType.

