Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Vectors.Vector.
Require Import Coq.Strings.Ascii.

Require Import StructTact.StructTactics.

Import ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma ascii_eq_refl: forall x : ascii, Ascii.compare x x = Eq.
Proof.
  intros x.
  unfold compare.
  apply N.compare_eq_iff.
  reflexivity.
Qed.

Lemma string_eq_refl: forall x : string, String.compare x x = Eq.
Proof.
  intros x.
  induction x.
  -
    auto.
  -
    cbn.
    rewrite ascii_eq_refl.
    assumption.
Qed.

Lemma string_eq_trans: forall x y z : string,
    String.compare x y = Eq ->
    String.compare y z = Eq ->
    String.compare x z = Eq.
Proof.
  intros x y z H0 H1.
  apply String.compare_eq_iff in H0, H1.
  rewrite H0, H1.
  apply string_eq_refl.
Qed.

(** Helper function to split a list at given position.
      List.split_at in Lem.
 *)
Definition split_at {A:Type} (n:nat) (l:list A)
  := (List.firstn n l, List.skipn n l).
