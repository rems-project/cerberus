Require Import Common.
Require Import AilTypes.
Require Import Implementation_defns Implementation.

Lemma signed_correct P it : boolSpec (signed P it) (Implementation_defns.signed P it).
Proof.
  unfold_goal.
  set (signed_Bool P).
  set (signed_Signed P).
  set (signed_Unsigned P).
  destruct it; my_auto.
Qed.
