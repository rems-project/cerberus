Require Import ZArith Omega.

Require Import AilTypes.
Require Import Implementation.

Local Open Scope Z.

Lemma precision_ge_one P it : 1 <= precision P it.
Proof.
  destruct it.
  + set (precision_Char P) as Hchar;
    case_eq (is_signed P Char); intros Heq; rewrite Heq in Hchar; clear Heq;
    set (precision_Signed P Ichar) as Hmin; simpl in Hmin;
    [|set (lePrecision_Signed_Unsigned P Ichar)];
    omega.
  + exact (precision_Bool P).
  + set (precision_Signed P ibt) as Hmin.
    destruct ibt; simpl in Hmin; omega.
  + set (precision_Signed P ibt) as Hmin.
    set (lePrecision_Signed_Unsigned P ibt).
    destruct ibt; simpl in Hmin; omega.
Defined.

Lemma two_p_ge_one : forall {p}, 0 <= p -> 1 <= 2^p.
Proof.
  apply (natlike_rec2).
  + simpl; omega.
  + intros z Hge_zero IH.
    rewrite (Z.pow_succ_r _ _ Hge_zero).
    omega.
Qed.

Definition integerTypeRange_unsigned {p} : 1 <= p -> 0 <= 2^p - 1.
Proof.
  intros.
  assert (0 <= p) as Hge_zero by omega.
  set (two_p_ge_one Hge_zero).
  omega.
Qed.

Definition integerTypeRange_signed_upper {p} : 1 <= p -> 0 <= 2^(p-1) - 1.
Proof.
  intros.
  assert (0 <= p - 1) as Hge_zero by omega.
  set (two_p_ge_one Hge_zero).
  omega.
Qed.

Definition integerTypeRange_signed_lower1 {p} : 1 <= p -> -2^(p-1) <= 0.
Proof.
  intros.
  assert (0 <= p - 1) as Hge_zero by omega.
  set (two_p_ge_one Hge_zero).
  omega.
Qed.

Definition integerTypeRange_signed_lower2 {p} : 1 <= p -> -2^(p-1) + 1 <= 0.
Proof.
  intros.
  assert (0 <= p - 1) as Hge_zero by omega.
  set (two_p_ge_one Hge_zero).
  omega.
Qed.

Definition integerTypeRange_signed1 {p} : 1 <= p -> -2^(p-1) <= 2^(p-1) - 1.
Proof.
  intros Hge_one.
  set (integerTypeRange_signed_upper  Hge_one).
  set (integerTypeRange_signed_lower1 Hge_one).
  apply (Z.le_trans _ 0 _); assumption.
Qed.

Definition integerTypeRange_signed2 {p} : 1 <= p -> -2^(p-1) + 1 <= 2^(p-1) - 1.
Proof.
  intros Hge_one.
  set (integerTypeRange_signed_upper  Hge_one).
  set (integerTypeRange_signed_lower2 Hge_one).
  apply (Z.le_trans _ 0 _); assumption.
Qed.
