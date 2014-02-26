Require Import Bool.
Require Import Omega.
Require Import RelationClasses.

Require Import Common.
Require Import Implementation.
Require Import Range_defns Range_proof.
Require Import AilTypes AilTypes_proof.
Require Import AilTypesAux.

Local Open Scope Z.

Require AilTypesAux_defns.
Module D := AilTypesAux_defns.

Lemma signed_correct P it : boolSpec (signed P it) (D.signed P it).
Proof.
  unfold_goal.
  set (signed_Bool P).
  set (signed_Signed P).
  set (signed_Unsigned P).
  destruct it; my_auto.
Qed.

Lemma unqualified_correct q :
  boolSpec (unqualified q) (D.unqualified q).
Proof. do 2 unfold_goal; repeat context_destruct. Qed.

Lemma integer_correct t : boolSpec (integer t) (D.integer t).
Proof. destruct t; my_auto. Qed.

Lemma void_correct t : boolSpec (void t) (D.void t).
Proof. destruct t; my_auto. Qed.

Lemma pointer_correct t : boolSpec (pointer t) (D.pointer t).
Proof. destruct t; my_auto. Qed.

Lemma boolean_correct t : boolSpec (boolean t) (D.boolean t).
Proof. destruct t; my_auto. Qed.

Lemma signed_incl {P} {it} : D.signedType it -> D.signed P it.
Proof. inversion 1; my_auto. Qed.

Lemma signed_type_correct it : boolSpec (signed_type it) (D.signedType it).
Proof. do 2 unfold_goal; my_auto. Qed.

Lemma unsigned_correct P it : boolSpec (unsigned P it) (D.unsigned P it).
Proof.
  do 3 unfold_goal.
  unfold signed.
  set (signed_Bool P).
  set (signed_Signed P).
  set (signed_Unsigned P).
  destruct it; my_auto.
Qed.

Lemma unsigned_incl {P} {it} : D.unsignedType it -> D.unsigned P it.
Proof. inversion 1; my_auto. Qed.

Lemma unsigned_type_correct it : boolSpec (unsigned_type it) (D.unsignedType it).
Proof. do 3 unfold_goal; my_auto. Qed.

Ltac unfold_integer_range_hyp H :=
    unfold integer_range      in H;
    repeat rewrite signed_Signed   in H;
    repeat rewrite signed_Unsigned in H;
    repeat rewrite signed_Bool     in H;
    match goal with 
    | [ R    : signed ?P Char =  true
      , notR : signed ?P Char <> true |- _] => destruct (notR R)
    | [ R    : signed ?P Char  = true |- _] => rewrite R                       in H; simpl in H
    | [ R    : signed ?P Char <> true |- _] => rewrite (not_true_is_false _ R) in H; simpl in H
    | _ => idtac
    end;
    match goal with
    | P : implementation |- _ => destruct (binary_mode P) in H;
                                 simpl                    in H
    end;
    repeat rewrite max_make_range in H;
    repeat rewrite min_make_range in H.

Ltac unfold_integer_range :=
    unfold integer_range;
    repeat rewrite signed_Signed;
    repeat rewrite signed_Unsigned;
    repeat rewrite signed_Bool;
    match goal with 
    | [ R    : signed ?P Char =  true
      , notR : signed ?P Char <> true |- _] => destruct (notR R)
    | [ R    : signed ?P Char  = true |- _] => rewrite R                      ; simpl
    | [ R    : signed ?P Char <> true |- _] => rewrite (not_true_is_false _ R); simpl
    | _ => idtac
    end;
    match goal with
    | P : implementation |- _ => destruct (binary_mode P); simpl
    end;
    repeat rewrite max_make_range;
    repeat rewrite min_make_range.

Lemma integer_range_precision_signed {P} {it1} {it2} :
  D.signed P it1 ->
  D.signed P it2 ->
  precision P it1 <= precision P it2 ->
  sub (integer_range P it1) (integer_range P it2).
Proof.
  inversion 1; inversion 1; subst;
  constructor;
  match goal with
  | |- _ -> sub (integer_range P Char) (integer_range P Char) =>
      omega
  | _ =>
      unfold_integer_range;
      solve
        [ apply Z.sub_le_mono;
          [apply Z.pow_le_mono_r|]; omega
        | apply (proj1 (Z.opp_le_mono _ _));
          apply Z.pow_le_mono_r; omega
        | apply Z.add_le_mono; [|omega];
          apply (proj1 (Z.opp_le_mono _ _));
          apply Z.pow_le_mono_r; omega]
  end.
Qed.

Lemma integer_range_precision_signed_inv {P} {it1} {it2} :
  D.signed P it1 ->
  D.signed P it2 ->
  sub (integer_range P it1) (integer_range P it2) ->
  precision P it1 <= precision P it2.
Proof.
  set (precision_ge_one P it1).
  set (precision_ge_one P it2).
  inversion 1;
  inversion 1;
  inversion 1;
  subst;
  match goal with
  | [ H : Range.max (_ _ ?it1) <= Range.max (_ _ ?it2) |- _] =>
      unfold_integer_range_hyp H;
      apply (Z.le_le_sub_lt 1 1 _ _ (Z.le_refl 1)) in H;
      apply (Z.le_le_sub_lt 1 1 _ _ (Z.le_refl 1));
      apply (Z.pow_le_mono_r_iff 2); omega
  end.
Qed.

Lemma integer_range_precision_unsigned {P} {it1} {it2} :
  D.unsigned P it1 ->
  D.unsigned P it2 ->
  precision P it1 <= precision P it2 ->
  sub (integer_range P it1) (integer_range P it2).
Proof.
  inversion 1; inversion 1;
  constructor;
  unfold_integer_range;
  solve
    [ apply Z.sub_le_mono  ; [|omega];
      apply Z.pow_le_mono_r;   omega
    | omega].
Qed.

Lemma integer_range_precision_unsigned_inv {P} {it1} {it2} :
  D.unsigned P it1 ->
  D.unsigned P it2 ->
  sub (integer_range P it1) (integer_range P it2) ->
  precision P it1 <= precision P it2.
Proof.
  set (precision_ge_one P it1).
  set (precision_ge_one P it2).
  inversion 1;
  inversion 1;
  inversion 1; subst;
  match goal with
  | [ H : Range.max (_ _ ?it1) <= Range.max (_ _ ?it2) |- _] =>
      unfold_integer_range_hyp H;
      apply (Z.pow_le_mono_r_iff 2); omega
  end.
Qed.

Lemma precision_signed_ge_two {P} {it} : D.signed P it -> 2 <= precision P it.
Proof.
  destruct 1;
  match goal with
  | [H : signed ?P Char = true |- _] =>
      let Hprec := fresh in
      let Hmin := fresh in
      set (precision_Char P) as Hprec; rewrite H in Hprec; simpl in Hprec;
      set (precision_Signed P Ichar) as Hmin; simpl in Hmin
  | [|- _ <= precision ?P _] =>
      let Hmin := fresh in
      set (precision_Signed P ibt) as Hmin; destruct ibt; simpl in Hmin
  end; omega.
Qed.

Lemma integer_range_precision_signed_unsigned {P} {it1} {it2} :
  D.signed   P it1 ->
  D.unsigned P it2 ->
  ~ sub (integer_range P it1) (integer_range P it2).
Proof.
  inversion 1;
  inversion 1;
  inversion 1; subst;
  match goal with
  | [ H : D.signed _ _ |- _] => set (precision_signed_ge_two H)
  end;
  match goal with
  | [ H : Range.min (integer_range P _) <= Range.min (integer_range P _) |- _] =>
      unfold_integer_range_hyp H
  end;
  match goal with
  | [ H : 0 <= - 2 ^ (precision P ?it - 1) |- _] =>
      rewrite <- Z.opp_0  in H;
      apply Z.opp_le_mono in H;
      set (integer_range_signed_upper (precision_ge_one P it));
      omega
  | [ H : 0 <= - 2 ^ (precision P _ - 1) + 1 |- _] =>
      apply (Z.sub_le_mono_r _ _ 1)     in H;
      rewrite <- Z.add_sub_assoc        in H;
      rewrite Z.sub_diag                in H;
      rewrite Z.sub_0_l                 in H;
      rewrite Zplus_0_r                 in H;
      rewrite <- (Z.pow_0_r 2)          in H at 1;
      apply (proj2 (Z.opp_le_mono _ _)) in H;
      apply Z.pow_le_mono_r_iff         in H;
      omega
  | _ => contradiction
  end.
Qed.

Lemma integer_range_precision_unsigned_signed {P} {it1} {it2} :
  D.unsigned P it1 ->
  D.signed   P it2 ->
  precision P it1 < precision P it2 ->
  sub (integer_range P it1) (integer_range P it2).
Proof.
  inversion 1;
  inversion 1; subst;
  constructor;
  unfold_integer_range;
  solve [
      apply integer_range_signed_lower1; apply precision_ge_one
    | apply integer_range_signed_lower2; apply precision_ge_one
    | apply Z.sub_le_mono_r;
      apply Z.pow_le_mono_r; omega
    | omega ].
Qed.

Lemma integer_range_precision_unsigned_signed_inv {P} {it1} {it2} :
  D.unsigned P it1 ->
  D.signed   P it2 ->
  sub (integer_range P it1) (integer_range P it2) ->
  precision P it1 < precision P it2.
Proof.
  set (precision_ge_one P it2).
  inversion 1;
  inversion 1;
  inversion 1; subst;
  match goal with
  | [H : Range.max _ <= Range.max _|- _] =>
    unfold_integer_range_hyp H;
    apply (proj2 (Z.sub_le_mono_r _ _ 1)) in H;
    apply Z.lt_le_pred;
    rewrite <- Z.sub_1_r;
    apply (Z.pow_le_mono_r_iff 2); omega
  end.
Qed.

Lemma integer_range_precision_Unsigned_Signed_eq {P} {ibt} :
  ~ precision P (Unsigned ibt) = precision P (Signed ibt) ->
  ~ sub (integer_range P (Unsigned ibt)) (integer_range P (Signed ibt)).
Proof.
  intros Hneq HleRange.
  assert (~ precision P (Unsigned ibt) < precision P (Signed ibt)) as Hnlt
  by apply (Zle_not_lt _ _ (le_precision_Signed_Unsigned P ibt)).
  exact (Hnlt (integer_range_precision_unsigned_signed_inv (D.Unsigned_Int P ibt) (D.Signed_Int P ibt) HleRange)).
Qed.

Lemma in_integer_range_correct P n it : boolSpec (in_integer_range P n it) (D.inIntegerRange P n it).
Proof.
  do 2 unfold_goal.
  set (mem_nat_correct n (integer_range P it)).
  my_auto' fail ltac:(progress boolSpec_simpl).
Qed.

Lemma inIntegerRange_inversion {P} {n} {it}:
  D.inIntegerRange P n it ->
  memNat n (integer_range P it).
Proof. my_auto. Qed.

Lemma min_integer_range_sub P it :
  sub (min_integer_range it) (integer_range P it).
Proof.
  unfold integer_range.
  pose proof (precision_Char P).
  pose proof (precision_ge_one P it).
  case_eq (Implementation.signed P Char); intros Hsigned;
  constructor;
  destruct it;
  rewrite_all Hsigned;
  match goal with
  | |- context[Bool] =>
      idtac
  | |- context[Char] =>
      pose proof (precision_Signed P Ichar);
      pose proof (precision_Unsigned P Ichar)
  | |- context[Signed ?ibt] =>
      pose proof (precision_Signed P ibt);
      destruct ibt
  | |- context[Unsigned ?ibt] =>
      pose proof (precision_Unsigned P ibt);
      destruct ibt
  end;
  unfold min_integer_range;
  unfold min_range_signed;
  unfold integer_range_signed_upper;
  unfold min_range_unsigned;
  repeat match goal with
  | |- context[binary_mode P] => destruct (binary_mode P)
  | |- context[Implementation.signed P Char] => rewrite_all Hsigned
  | |- context[Implementation.signed P Bool] => rewrite (signed_Bool P)
  | |- context[Implementation.signed P (Signed ?ibt)] => rewrite (signed_Signed P ibt)
  | |- context[Implementation.signed P (Unsigned ?ibt)] => rewrite (signed_Unsigned P ibt)
  end;
  repeat rewrite max_make_range;
  repeat rewrite min_make_range;
  now match goal with
  | |- 2 ^ _ - 1 <= _ - 1 => 
      apply Z.sub_le_mono; [|omega];
      apply Z.pow_le_mono; [omega|];
      simpl in *; omega
  | |- 1 <= 2 ^ precision _ Bool - 1 =>
      assert (1 = 2 - 1)%Z as Heq by omega; rewrite Heq at 1;
      apply Z.sub_le_mono; [|omega];
      assert (2 = 2 ^ 1)%Z as Heq' by reflexivity; rewrite Heq' at 1;
      apply Z.pow_le_mono; [omega|];
      exact (precision_Bool P)
  | |- 0 <= 0 => omega
  | |- - 2 ^ (precision P Char - 1) <= 0 =>
      assert (0 = -0)%Z as Heq by reflexivity;
      rewrite Heq;
      apply (proj1 (Z.opp_le_mono _ _));
      apply (Z.le_trans _ 1); [omega|];
      assert (1 = 2^0)%Z as Heq' by reflexivity;
      rewrite Heq' at 1;
      apply Z.pow_le_mono_r; omega
  | |- - 2 ^ (precision P Char - 1) + 1 <= 0 =>
      apply (Z.le_le_sub_lt 1 1 _ _ (Z.le_refl 1));
      rewrite <- Z.add_sub_assoc;
      rewrite Zplus_0_r;
      apply (proj1 (Z.opp_le_mono _ _));
      assert (1 = 2^0)%Z as Heq' by reflexivity;
      rewrite Heq' at 1;
      apply Z.pow_le_mono_r; omega
  | |- - 2 ^ (precision _ (Signed ?ibt) - 1) <= _ =>
      apply (Z.le_trans _ (- 2 ^ (min_precision ibt - 1 - 1))); [|simpl; omega];
      apply (proj1 (Z.opp_le_mono _ _));
      apply Z.pow_le_mono_r; omega
  | |- - 2 ^ (precision _ (Signed _) - 1) + 1 <= _ =>
      apply Z.add_le_mono; [|omega];
      apply (proj1 (Z.opp_le_mono _ _));
      apply Z.pow_le_mono_r; simpl in *; omega
  end.
Qed.

Lemma in_min_integer_range_correct n it :
  boolSpec (in_min_integer_range n it) (D.inMinIntegerRange n it).
Proof.
  do 2 unfold_goal.
  pose proof (mem_nat_correct n (Implementation.min_integer_range it)) as Hmem.
  boolSpec_destruct.
  - constructor.
    eapply sub_mem.
    eapply min_integer_range_sub.
    assumption.
  - destruct (mem_neg Hmem);
    intros Hrange;
    pose proof (Hrange min_implementation_signed_char)   as Hsigned;
    pose proof (Hrange min_implementation_unsigned_char) as Hunsigned;
    inversion_clear Hunsigned;
    inversion_clear Hsigned;
    repeat match goal with
    | H : Range_defns.memNat _ _ |- _ => inversion_clear H
    end;
    repeat match goal with
    | it  : integerType     |- _ => destruct it
    | ibt : integerBaseType |- _ => destruct ibt
    end;
    repeat match goal with
    | H : _ (Range.max ?r) _ |- _ =>
        let z := eval compute in (Range.max r) in
        replace (Range.max r) with z in *; [|reflexivity]
    | H : _ _ (Range.max ?r) |- _ =>
        let z := eval compute in (Range.max r) in
        replace (Range.max r) with z in *; [|reflexivity]
    | H : _ (Range.min ?r) _ |- _ =>
        let z := eval compute in (Range.min r) in
        replace (Range.min r) with z in *; [|reflexivity]
    | H : _ _ (Range.min ?r) |- _ =>
        let z := eval compute in (Range.min r) in
        replace (Range.min r) with z in *; [|reflexivity]
    end; omega.
Qed.

Lemma le_integer_range_correct P it1 it2 :
  boolSpec (le_integer_range P it1 it2) (D.leIntegerRange P it1 it2).
Proof.
  do 2 unfold_goal.
  set (unsigned_correct P it1) as Hunsigned1.
  set (unsigned_correct P it2) as Hunsigned2.
  set (signed_correct   P it1) as Hsigned1.
  set (signed_correct   P it2) as Hsigned2.
  destruct_integerType;
  unfold unsigned in *;
  rewrite_all (signed_Signed   P);
  rewrite_all (signed_Unsigned P);
  rewrite_all (signed_Bool     P);
  match goal with
  | [|- context [Char]] =>
      let Heq := fresh in
      set (precision_Char P);
      case_eq (signed P Char);
      intros Heq; repeat rewrite Heq in *
  | _ => idtac
  end; simpl;
  match goal with
  | [|- context[lt_Z ?x ?y] ] =>
      let Heq := fresh in
      set (lt_Z_correct x y);
      case_eq (lt_Z x y); intros Heq; rewrite Heq in *; clear Heq
  | [|- context[eq_Z ?x ?y] ] =>
      let Heq := fresh in
      set (eq_Z_correct x y);
      case_eq (eq_Z x y); intros Heq; rewrite Heq in *; clear Heq
  | _ => idtac
  end; boolSpec_simpl; simpl;
  match goal with
  | [|- D.leIntegerRange _ ?it ?it ] =>
      constructor; constructor; apply Z.le_refl
  | [ Hunsigned1 : D.unsigned ?P ?it1, Hunsigned2 : D.unsigned ?P ?it2 |- D.leIntegerRange ?P ?it1 ?it2 ] =>
      constructor;
      apply (integer_range_precision_unsigned Hunsigned1 Hunsigned2);
      set (le_precision_Unsigned_Long_LongLong P);
      set (le_precision_Unsigned_Int_Long      P);
      set (le_precision_Unsigned_Short_Int     P);
      set (le_precision_Unsigned_Ichar_Short   P);
      set (le_precision_Unsigned_Bool_Ichar    P);
      omega
  | [ Hunsigned1 : D.unsigned ?P ?it1, Hunsigned2 : D.unsigned ?P ?it2 |- ~ D.leIntegerRange ?P ?it1 ?it2 ] =>
      inversion 1; subst;
      match goal with
      | [H : sub _ _ |- _] => set (integer_range_precision_unsigned_inv Hunsigned1 Hunsigned2 H)
      end;
      set (le_precision_Unsigned_Long_LongLong P);
      set (le_precision_Unsigned_Int_Long      P);
      set (le_precision_Unsigned_Short_Int     P);
      set (le_precision_Unsigned_Ichar_Short   P);
      set (le_precision_Unsigned_Bool_Ichar    P);
      match goal with
      | [ H : _ <> _ |- _ ] => apply H
      end;
      omega
  | [ Hsigned1 : D.signed ?P ?it1, Hsigned2 : D.signed ?P ?it2 |- D.leIntegerRange ?P ?it1 ?it2 ] =>
      constructor;
      apply (integer_range_precision_signed Hsigned1 Hsigned2);
      set (le_precision_Signed_Long_LongLong P);
      set (le_precision_Signed_Int_Long      P);
      set (le_precision_Signed_Short_Int     P);
      set (le_precision_Signed_Ichar_Short   P);
      omega
  | [ Hsigned1 : D.signed ?P ?it1, Hsigned2 : D.signed ?P ?it2 |- ~ D.leIntegerRange ?P ?it1 ?it2 ] =>
      inversion 1; subst;
      match goal with
      | [H : sub _ _ |- _] => set (integer_range_precision_signed_inv Hsigned1 Hsigned2 H)
      end;
      set (le_precision_Signed_Long_LongLong P);
      set (le_precision_Signed_Int_Long      P);
      set (le_precision_Signed_Short_Int     P);
      set (le_precision_Signed_Ichar_Short   P);
      match goal with
      | [ H : _ <> _ |- _ ] => apply H
      end;
      omega
  | [ Hsigned1 : D.signed ?P ?it1, Hunsigned2 : D.unsigned ?P ?it2 |- ~ D.leIntegerRange ?P ?it1 ?it2 ] =>
      set (integer_range_precision_signed_unsigned Hsigned1 Hunsigned2);
      inversion 1; contradiction
  | [ Hunsigned1 : D.unsigned ?P ?it1, Hsigned2 : D.signed ?P ?it2 |- ~ D.leIntegerRange ?P ?it1 ?it2 ] =>
      inversion 1; subst;
      match goal with
      | [H : sub _ _ |- _] => set (integer_range_precision_unsigned_signed_inv Hunsigned1 Hsigned2 H)
      end;
      match it1 with
      | Unsigned ?ibt => set (le_precision_Signed_Unsigned P ibt)
      | _ => idtac
      end;
      set (le_precision_Signed_Unsigned_Ichar  P);
      set (le_precision_Unsigned_Long_LongLong P);
      set (le_precision_Unsigned_Int_Long      P);
      set (le_precision_Unsigned_Short_Int     P);
      set (le_precision_Unsigned_Ichar_Short   P);
      set (le_precision_Unsigned_Bool_Ichar    P);
      solve [ contradiction | omega]
  | [ Hunsigned1 : D.unsigned ?P ?it1, Hsigned2 : D.signed ?P ?it2 |- D.leIntegerRange ?P ?it1 ?it2 ] =>
      constructor;
      apply (integer_range_precision_unsigned_signed Hunsigned1 Hsigned2); assumption
  end.
Qed.

Instance eqIntegerRankBase_irrefl : Irreflexive D.eqIntegerRankBase.
Proof. inversion 1. Qed.

Lemma eq_integer_rank_base_correct it1 it2 : boolSpec (eq_integer_rank_base it1 it2) (D.eqIntegerRankBase it1 it2).
Proof.
  do 2 unfold_goal;
  repeat match goal with
  | |- eq_integerBaseType ?x ?y = _ -> _ => case_fun (eq_integerBaseType_correct x y)
  | _ => context_destruct
  end;
  my_auto.
Qed.

Ltac eqIntegerRankBase_false :=
  match goal with
  | [ H : D.eqIntegerRankBase ?a ?b |- _ ] => inversion H; congruence
  end.

Ltac eqIntegerRank_finish :=
  solve [ eqIntegerRankBase_false 
        | apply D.EqIntegerRank_Sym; my_auto
        | intros; apply D.EqIntegerRank_Refl].
Ltac eqIntegerRank_tac := my_auto' eqIntegerRank_finish fail.

Lemma eqIntegerRank_dec_aux it1 it2 : D.eqIntegerRankBase it1 it2 \/ D.eqIntegerRankBase it2 it1 \/ (it1 = it2) \/ ~ D.eqIntegerRank it1 it2.
Proof.
  set (eq_integerType_correct it1 it2); boolSpec_destruct.
  - right; right; left; assumption.
  - set (eq_integer_rank_base_correct it1 it2); boolSpec_destruct.
    + left; assumption.
    + set (eq_integer_rank_base_correct it2 it1); boolSpec_destruct.
      * right; left;  assumption.
      * right; right; right; my_auto.
Qed.

Lemma eq_integer_rank_correct it1 it2 :
  boolSpec (eq_integer_rank it1 it2) (D.eqIntegerRank it1 it2).
Proof.
  do 2 unfold_goal.
  unfold orb.
  repeat match goal with
  | |- eq_integer_rank_base ?x ?y = _ -> _ => case_fun (eq_integer_rank_base_correct x y)
  | |- eq_integerType       ?x ?y = _ -> _ => case_fun (eq_integerType_correct       x y)
  | _ => context_destruct
  end;
  eqIntegerRank_tac.
Qed.

Require Import RelationClasses.

Instance eqIntegerRank_trans : Transitive D.eqIntegerRank.
Proof.
  intros it1 it it2.
  generalize (eqIntegerRank_dec_aux it1 it);
  generalize (eqIntegerRank_dec_aux it it2);
  intuition;
  solve [
      congruence
    | repeat (
        match goal with
        | it : integerType      |- _                        => destruct it
        |                       |- D.eqIntegerRank _ _ -> _ => inversion 1
        | ibt : integerBaseType |- _                        => destruct ibt
        end; eqIntegerRank_tac
      )
  ].
Qed.

Instance eqIntegerRank_sym : Symmetric D.eqIntegerRank.
Proof. inversion 1; eqIntegerRank_tac. Qed.

Instance eqIntegerRank_equiv : Equivalence D.eqIntegerRank := {
  Equivalence_Reflexive  := D.EqIntegerRank_Refl;
  Equivalence_Symmetric  := eqIntegerRank_sym   ;
  Equivalence_Transitive := eqIntegerRank_trans
}.

Instance ltIntegerRankBase_irrefl {P} : Irreflexive (D.ltIntegerRankBase P).
Proof. generalize Z.lt_irrefl; inversion 2; my_auto; intuition. Qed.

Ltac precision_tac :=
  match goal with
  | [P : implementation, _ : _ < _ |- _ ] =>
      generalize (le_precision_Signed_Ichar_Short    P); 
      generalize (le_precision_Signed_Short_Int      P);
      generalize (le_precision_Signed_Int_Long       P);
      generalize (le_precision_Signed_Long_LongLong  P);
      omega
  | _ => idtac
  end.

Instance ltIntegerRankBase_asymm {P} : Asymmetric (D.ltIntegerRankBase P).
Proof. intros; inversion 1; inversion 1; my_auto; precision_tac; intuition. Qed.

Lemma ltIntegerRankBase_least P it : ~ D.ltIntegerRankBase P it Bool.
Proof. inversion 1; intuition. Qed.

Ltac ltIntegerRankBase_tac :=
  match goal with
  | [ |- D.ltIntegerRankBase ?P (Signed  Long) (Signed LongLong) ] => exact (D.LtIntegerRankBase_LongLong P)
  | [ |- D.ltIntegerRankBase ?P (Signed   Int) (Signed     Long) ] => exact (D.LtIntegerRankBase_Long     P)
  | [ |- D.ltIntegerRankBase ?P (Signed Short) (Signed      Int) ] => exact (D.LtIntegerRankBase_Int      P)
  | [ |- D.ltIntegerRankBase ?P (Signed Ichar) (Signed    Short) ] => exact (D.LtIntegerRankBase_Short    P)
  end.

Lemma lt_integer_rank_base_correct P it1 it2 : boolSpec (lt_integer_rank_base P it1 it2) (D.ltIntegerRankBase P it1 it2).
Proof.
  do 2 unfold_goal; my_auto; intros;
  match goal with
  | [ H : lt_Z ?z ?z = true  |- _ ] => unfold lt_Z; rewrite Z.ltb_irrefl in H
  | [ H : lt_Z ?x ?y = true  |- _ ] => unfold lt_Z; set (proj1 (Z.ltb_lt  x y) H)
  | [ H : lt_Z ?x ?y = false |- _ ] => unfold lt_Z; set (proj1 (Z.ltb_nlt x y) H)
  | _ => ltIntegerRankBase_tac
  end; my_auto.
Qed.

Ltac ltIntegerRankCongruence_destruct :=
  match goal with
  | [ H : D.eqIntegerRank     _ _ |- _ ] => inversion H; clear H
  | [ H : D.eqIntegerRankBase _ _ |- _ ] => inversion H; clear H
  | [ H : D.ltIntegerRankBase _  _  (Unsigned _) |- _ ] => inversion H; clear H
  | [ H : D.ltIntegerRankBase _  _  Char |- _ ] => inversion H; clear H
  end.

Ltac ltIntegerRankCongruence_finish :=
  match goal with
  | [ H : D.ltIntegerRankBase _  _   _    |- _     ] => now inversion H
  | [ H : D.ltIntegerRankBase ?P ?it Bool |- _     ] => destruct (ltIntegerRankBase_least P it H)
  | [ H : D.ltIntegerRankBase _  ?x  ?x   |- False ] => exact (ltIntegerRankBase_irrefl x H)
(*
TODO Coq can't find instance for
  exact (irreflexive x H)
*)
  | [ H1 : D.ltIntegerRankBase _ ?x ?y , H2 : D.ltIntegerRankBase _ ?y ?x |- False ] => exact (ltIntegerRankBase_asymm x y H1 H2)
(*
TODO Coq can't find instance for
  exact (asymmetric x y H1 H2)
*)
  end.

Ltac ltIntegerRankCongruence_tac := repeat (ltIntegerRankCongruence_destruct; my_auto); try ltIntegerRankCongruence_finish; my_auto.

(* Slower than the above! :(
Ltac ltIntegerRankCongruence_tac' := my_auto' ltac:(idtac; ltIntegerRankCongruence_finish) ltac:(idtac; ltIntegerRankCongruence_destruct).
*)

Instance ltIntegerRankCongruence_irrefl {P} : Irreflexive (D.ltIntegerRankCongruence P).
Proof. inversion 1; ltIntegerRankCongruence_tac. Qed.

Instance ltIntegerRankCongruence_asymm {P} : Asymmetric (D.ltIntegerRankCongruence P).
Proof. intros ? ?; inversion 1; inversion 1; ltIntegerRankCongruence_tac. Qed.

Definition ltIntegerRankCongruence_incl {P} {it1 it2} : D.ltIntegerRankBase P it1 it2 -> D.ltIntegerRankCongruence P it1 it2.
Proof.
  intros; econstructor.
  - apply D.EqIntegerRank_Refl.
  - apply D.EqIntegerRank_Refl.
  - assumption.
Qed.

Lemma ltIntegerRankCongruence_Unsigned_Unsigned {P} {ibt1} {ibt2} :
  D.ltIntegerRankBase P (Signed ibt1) (Signed ibt2) ->
  D.ltIntegerRankCongruence P (Unsigned ibt1) (Unsigned ibt2).
Proof.
  intros.
  econstructor.
  - constructor; constructor.
  - constructor; constructor.
  - assumption.
Qed.

Lemma ltIntegerRankCongruence_Unsigned1 {P} {ibt1} {it2} :
  D.ltIntegerRankBase P (Signed ibt1) it2 ->
  D.ltIntegerRankCongruence P (Unsigned ibt1) it2.
Proof.
  intros.
  econstructor.
  - constructor; constructor.
  - constructor 3.
  - assumption.
Qed.

Lemma ltIntegerRankCongruence_Unsigned2 {P} {it1} {ibt2} :
  D.ltIntegerRankBase P it1 (Signed ibt2) ->
  D.ltIntegerRankCongruence P it1 (Unsigned ibt2).
Proof.
  intros.
  econstructor.
  - constructor 3.
  - constructor; constructor.
  - assumption.
Qed.

Lemma ltIntegerRankBaseCongruence_Char1 {P} {it2} :
  D.ltIntegerRankBase P (Signed Ichar) it2 ->
  D.ltIntegerRankCongruence P Char it2.
Proof.
  intros.
  econstructor.
  - constructor 2. constructor 3.
  - constructor 3.
  - assumption.
Qed.

Lemma ltIntegerRankBaseCongruence_Char_Unsigned {P} {ibt2} :
  D.ltIntegerRankBase P (Signed Ichar) (Signed ibt2) ->
  D.ltIntegerRankCongruence P Char (Unsigned ibt2).
Proof.
  intros.
  econstructor.
  - constructor 2. constructor 3.
  - constructor 1; constructor 1.
  - assumption.
Qed.

Ltac ltIntegerRankCongruence_dec_tac :=
  ltIntegerRankCongruence_tac;
  try solve
    [ inversion 1; ltIntegerRankCongruence_tac
    | intros; apply_ctx; constructor; inversion 1
    | inversion 2; ltIntegerRankCongruence_tac
    | inversion 1; ltIntegerRankCongruence_tac;
      match goal with
      | [ H : D.ltIntegerRankBase _ (Signed ?ibt) (Signed Ichar) |- _ ] =>
          destruct ibt; inversion H;
          ltIntegerRankCongruence_tac;
          precision_tac;
          intuition
      end].

Ltac ltIntegerRankCongruence_pos_tac tac :=
  match goal with
  | [ |- D.ltIntegerRankCongruence ?P Bool ?it2 ] => apply ltIntegerRankCongruence_incl; apply (D.LtIntegerRankBase_Bool P it2); inversion 1
  | [ |- D.ltIntegerRankCongruence _ Char         (Signed   _) ] => apply ltIntegerRankBaseCongruence_Char1        ; tac
  | [ |- D.ltIntegerRankCongruence _ Char         (Unsigned _) ] => apply ltIntegerRankBaseCongruence_Char_Unsigned; tac
  | [ |- D.ltIntegerRankCongruence _ (Signed   _) (Signed   _) ] => apply ltIntegerRankCongruence_incl             ; tac
  | [ |- D.ltIntegerRankCongruence _ (Unsigned _) (Unsigned _) ] => apply ltIntegerRankCongruence_Unsigned_Unsigned; tac
  | [ |- D.ltIntegerRankCongruence _ (Unsigned _) (Signed   _) ] => apply ltIntegerRankCongruence_Unsigned1        ; tac
  | [ |- D.ltIntegerRankCongruence _ (Signed   _) (Unsigned _) ] => apply ltIntegerRankCongruence_Unsigned2        ; tac
  end.

Lemma lt_integer_rank_congruence_correct P it1 it2 :
  boolSpec (lt_integer_rank_congruence P it1 it2) (D.ltIntegerRankCongruence P it1 it2).
Proof.
  do 2 unfold_goal; destruct it1; destruct it2;
  repeat match goal with
  | |- context[lt_integer_rank_base ?P ?x ?y] => set (lt_integer_rank_base_correct P x y); boolSpec_destruct
  | _ => ltIntegerRankCongruence_pos_tac assumption
  | _ => ltIntegerRankCongruence_dec_tac
  end.
Qed.

Ltac ltIntegerRank_pos_tac :=
  match goal with
  | [ |- D.ltIntegerRank _ _                _] =>
      apply D.LtIntegerRank_Base;
      ltIntegerRankCongruence_pos_tac idtac;
      now ltIntegerRankBase_tac
  | [ |- D.ltIntegerRank _ Char             _] => ltIntegerRank_pos_tac_iter (Signed    Short)
  | [ |- D.ltIntegerRank _ (Signed   Ichar) _] => ltIntegerRank_pos_tac_iter (Signed    Short)
  | [ |- D.ltIntegerRank _ (Unsigned Ichar) _] => ltIntegerRank_pos_tac_iter (Signed    Short)
  | [ |- D.ltIntegerRank _ (Signed   Short) _] => ltIntegerRank_pos_tac_iter (Signed      Int)
  | [ |- D.ltIntegerRank _ (Unsigned Short) _] => ltIntegerRank_pos_tac_iter (Signed      Int)
  | [ |- D.ltIntegerRank _ (Signed     Int) _] => ltIntegerRank_pos_tac_iter (Signed     Long)
  | [ |- D.ltIntegerRank _ (Unsigned   Int) _] => ltIntegerRank_pos_tac_iter (Signed     Long)
  | [ |- D.ltIntegerRank _ (Signed    Long) _] => ltIntegerRank_pos_tac_iter (Signed LongLong)
  | [ |- D.ltIntegerRank _ (Unsigned  Long) _] => ltIntegerRank_pos_tac_iter (Signed LongLong)
  end
with ltIntegerRank_pos_tac_iter t :=
  apply (D.LtIntegerRank_Transitive _ _ _ t);
  [ ltIntegerRankCongruence_pos_tac idtac; ltIntegerRankBase_tac
  | ltIntegerRank_pos_tac ].

Ltac ltIntegerRank_neg_tac :=
  match goal with
  | _ => contradiction
  | [ H  : D.ltIntegerRankCongruence _ ?x ?x |- False ] => exact (ltIntegerRankCongruence_irrefl x H)
  | [ H : D.ltIntegerRankCongruence _ _ _         |- _] => inversion H; ltIntegerRankCongruence_tac; clear H
  | [ ibt : integerBaseType                     |- _] => destruct ibt
  | [ it : integerType                          |- _] => destruct it
  | [ H : D.ltIntegerRankBase _ _ _               |- _] => ltIntegerRankCongruence_finish
  | [ H1 : precision ?P ?it1 < precision ?P ?it2, H2 : D.ltIntegerRankBase ?P ?it1 ?it2 |- _] => (now precision_tac) || (clear H1; clear H2)
  | [ H : D.ltIntegerRankBase _ _ _               |- _] => inversion H; now precision_tac
  | [ H : D.ltIntegerRankBase _ _ _               |- _] => clear H
  | [ H : D.ltIntegerRank _ _ _                   |- _] => inversion H; subst; clear H
  end.

Definition lt_integer_rank_neg_next it : option integerType :=
  match it with
  | Unsigned ibt    => Some (Signed ibt)
  | Signed LongLong => Some (Unsigned Long)
  | Signed Long     => Some (Unsigned Int)
  | Signed Int      => Some (Unsigned Short)
  | Signed Short    => Some (Unsigned Ichar)
  | Signed Ichar    => Some Char
  | Char            => Some Bool
  | Bool            => None
  end.

Ltac ltIntegerRank_neg_tac_next P it1 it2 :=
  let next := eval compute in (lt_integer_rank_neg_next it1) in
  assert (~ D.ltIntegerRank P it1 it2) by (clear_integerType; intros ?; now abstract (do 5 ltIntegerRank_neg_tac));
  match next with
  | Some ?it1' =>
      let eq      := eval compute in (eq_integer_rank it1  it2) in
      let eq_next := eval compute in (eq_integer_rank it1' it2) in
      match eval compute in (andb eq (negb eq_next)) with
      | true  => idtac
      | false => ltIntegerRank_neg_tac_next P it1' it2
      end
  | None => idtac
  end.

Lemma lt_integer_rank_correct P it1 it2 : boolSpec (lt_integer_rank it1 it2) (D.ltIntegerRank P it1 it2).
Proof.
  unfold_goal; scatter fail.
  - destruct_integerType; my_auto; ltIntegerRank_pos_tac.
  - destruct_integerType_hyp it2;
    abstract (
      match goal with
      | [ |- context[D.ltIntegerRank ?P ?H ?it2]] =>
          ltIntegerRank_neg_tac_next P (Unsigned LongLong) it2; destruct_integerType; my_auto
      end
    ).
Qed.

Instance ltIntegerRank_asymm P : Asymmetric (D.ltIntegerRank P).
Proof.
  intros x y ? ?.
  set (lt_integer_rank_correct P x y).
  set (lt_integer_rank_correct P y x).
  destruct_integerType;
  boolSpec_simpl;
  contradiction.
Qed.

Instance ltIntegerRank_irrefl P : Irreflexive (D.ltIntegerRank P) :=
  fun it H => ltIntegerRank_asymm P it it H H.

Instance ltIntegerRank_trans P : Transitive (D.ltIntegerRank P).
Proof.
  unfold Transitive; fix IH 4.
  inversion 1; subst.
  + econstructor 2; eassumption.
  +  match goal with
    | [ _ : D.ltIntegerRankCongruence ?P _ ?it1, H1 : D.ltIntegerRank ?P ?it1 ?it |- D.ltIntegerRank ?P ?it ?it2 -> _] =>
        let H2 := fresh in
        intros H2; set (IH it1 it it2 H1 H2)
    end.
    econstructor 2; eassumption.
Qed.

Lemma ltIntegerRank_cong1 P it1 it it2 : D.eqIntegerRank it1 it -> D.ltIntegerRank P it it2 -> D.ltIntegerRank P it1 it2.
Proof.
  inversion 2; subst;
  match goal with
  | [H : D.ltIntegerRankCongruence _ _ _ |- _] => inversion H; subst; clear H
  end;
  match goal with
  | [ E  : D.eqIntegerRank       ?it1 ?it
    , Eb : D.eqIntegerRank       ?itb ?it
    , Ee : D.eqIntegerRank       ?ite ?it2
    , L  : D.ltIntegerRankBase P ?itb ?ite |- D.ltIntegerRank ?P ?it1 _] =>
    set (D.LtIntegerRankCongruence _ _ _ _ _ (eqIntegerRank_trans _ _ _ Eb (eqIntegerRank_sym _ _ E)) Ee L)
  end.
  + constructor  1;  assumption.
  + econstructor 2; eassumption.
Qed.

Lemma ltIntegerRank_cong2 P :
  forall it1 it it2, D.eqIntegerRank it it2 -> D.ltIntegerRank P it1 it -> D.ltIntegerRank P it1 it2.
Proof.
  fix IH 5.
  inversion 2; subst.
  + match goal with
    | [H :D.ltIntegerRankCongruence _ _ _ |- _] => inversion H; subst; clear H
    end.
    match goal with
    | [ E  : D.eqIntegerRank       ?it ?it2
      , Eb : D.eqIntegerRank       ?itb ?it1
      , Ee : D.eqIntegerRank       ?ite _
      , L  : D.ltIntegerRankBase P ?itb ?ite |- D.ltIntegerRank ?P ?it1 ?it2] =>
        set (D.LtIntegerRankCongruence _ _ _ _ _ Eb (eqIntegerRank_trans _ _ _ Ee E) L)
    end; constructor 1; assumption.
  + match goal with
    | [ E : D.eqIntegerRank ?it _
      , _ : D.ltIntegerRankCongruence ?P ?it1 ?itn
      , L : D.ltIntegerRank           ?P ?itn ?it  |- _] => set (IH _ _ _ E L); econstructor 2; eassumption
    end.
Qed.

Lemma le_integer_rank_correct P it1 it2 : boolSpec (le_integer_rank it1 it2) (D.leIntegerRank P it1 it2).
Proof.
  do 2 unfold_goal.
  set (eq_integer_rank_correct   it1 it2).
  set (lt_integer_rank_correct P it1 it2).
  repeat (boolSpec_destruct; my_auto).
Qed.

Instance leIntegerRank_refl P : Reflexive (D.leIntegerRank P).
Proof. intros ?; constructor; apply D.EqIntegerRank_Refl. Qed.

Instance leIntegerRank_trans P : Transitive (D.leIntegerRank P).
Proof.
  inversion 1; inversion 1; my_auto.
  + constructor 1; eapply eqIntegerRank_trans; eassumption.
  + constructor 2; eapply ltIntegerRank_cong1; eassumption.
  + constructor 2; eapply ltIntegerRank_cong2; eassumption.
  + constructor 2; eapply ltIntegerRank_trans; eassumption.
Qed.

Lemma leIntegerRank_cong1 P it1 it it2 : D.eqIntegerRank it1 it -> D.leIntegerRank P it it2 -> D.leIntegerRank P it1 it2.
Proof.
  inversion 2; subst.
  + constructor 1; eapply eqIntegerRank_trans; eassumption.
  + constructor 2; eapply ltIntegerRank_cong1; eassumption.
Qed.

Lemma leIntegerRank_cong2 P it1 it it2 : D.eqIntegerRank it it2 -> D.leIntegerRank P it1 it -> D.leIntegerRank P it1 it2.
Proof.
  inversion 2; subst.
  + constructor 1; eapply eqIntegerRank_trans; eassumption.
  + constructor 2; eapply ltIntegerRank_cong2; eassumption.
Qed.

Lemma arithmetic_correct t : boolSpec (arithmetic t) (D.arithmetic t).
Proof.
  do 2 unfold_goal.
  set (integer_correct t).
  boolSpec_destruct; my_auto.
Qed.  

Lemma scalar_correct t : boolSpec (scalar t) (D.scalar t).
Proof.
  do 2 unfold_goal.
  set (pointer_correct    t).
  set (arithmetic_correct t).
  repeat (boolSpec_destruct; my_auto).
Qed.

Lemma array_correct t : boolSpec (array t) (D.array t).
Proof. destruct t; my_auto. Qed.

Lemma function_correct t : boolSpec (function t) (D.function t).
Proof. destruct t; my_auto. Qed.

Lemma is_corresponding_unsigned_correct it1 it2 : boolSpec (is_corresponding_unsigned it1 it2) (D.correspondingUnsigned it1 it2).
Proof.
  do 2 unfold_goal;
  repeat match goal with
  | [|- eq_integerBaseType ?x ?y = _ -> _] => case_fun (eq_integerBaseType_correct x y)
  | _ => context_destruct
  end; my_auto.
Qed.

Lemma corresponding_unsigned_correct it :
  optionSpec (corresponding_unsigned it) (D.correspondingUnsigned it).
Proof. destruct it; my_auto. Qed.

Lemma corresponding_unsigned_unique it :
  optionUnique (corresponding_unsigned it) (D.correspondingUnsigned it).
Proof. destruct 1; reflexivity. Qed.

Lemma make_corresponding_unsigned_Signed_correct ibt :
  D.correspondingUnsigned (Signed ibt) (make_corresponding_unsigned (Signed ibt)).
Proof. my_auto. Qed.

Lemma make_corresponding_unsigned_unique {it1} :
  findUnique (make_corresponding_unsigned it1) (D.correspondingUnsigned it1).
Proof. intros it2. destruct it1, it2; inversion 1; reflexivity. Qed.

Lemma integerPromotion_promoted {P} {it1} {it2} :
  D.integerPromotion P it1 it2 ->
  D.promoted it2.
Proof.
  inversion 1; my_auto.
  set (le_integer_rank_correct P it2 (Signed Int)).
  destruct_integerType_hyp it2; my_auto.
Qed.

Lemma promoted_integerPromotion {P} {it} :
  D.promoted it ->
  D.integerPromotion P it it.
Proof.
  pose (le_integer_rank_correct P it (Signed Int)).
  inversion 1; econstructor (now my_auto).
Qed.

Lemma is_integer_promotion_correct P it1 it2 : boolSpec (is_integer_promotion P it1 it2) (D.integerPromotion P it1 it2).
Proof.
  do 2 unfold_goal.
  set (le_integer_rank_correct       P it1 (Signed Int)).
  set (le_integer_range_correct P it1 (Signed Int)).
  destruct_integerType;
  match goal with
  | [ |- D.integerPromotion _ (Signed   Int) (Signed   Int) ] => apply D.IntegerPromotion_SignedInt
  | [ |- D.integerPromotion _ (Unsigned Int) (Unsigned Int) ] => apply D.IntegerPromotion_UnsignedInt
  | _ => repeat boolSpec_destruct; my_auto
  end.
Qed.  

Lemma integer_promotion_correct P it :
  findSpec (integer_promotion P it) (D.integerPromotion P it).
Proof.
  do 2 unfold_goal.
  set (le_integer_rank_correct       P it (Signed Int)).
  set (le_integer_range_correct P it (Signed Int)).
  destruct_integerType;
  match goal with
  | [ |- D.integerPromotion _ (Signed   Int) (Signed   Int) ] => apply D.IntegerPromotion_SignedInt
  | [ |- D.integerPromotion _ (Unsigned Int) (Unsigned Int) ] => apply D.IntegerPromotion_UnsignedInt
  | _ => repeat boolSpec_destruct; my_auto
  end.
Qed.

Lemma integer_promotion_unique {P} {it1} :
  findUnique (integer_promotion P it1) (D.integerPromotion P it1).
Proof.
  do 2 unfold_goal.
  set (le_integer_rank_correct       P it1 (Signed Int)).
  set (le_integer_range_correct P it1 (Signed Int)).
  destruct_integerType; boolSpec_destruct; my_auto.
Qed.

Lemma integerPromotion_functional {P} {it1 it2 it2'} :
  D.integerPromotion P it1 it2  ->
  D.integerPromotion P it1 it2' ->
  it2 = it2'.
Proof.
  intros H1 H2.
  set (integer_promotion_unique _ H1).
  set (integer_promotion_unique _ H2).
  congruence.
Qed.

Lemma is_promotion_correct P t1 t2 : boolSpec (is_promotion P t1 t2) (D.promotion P t1 t2).
Proof.
  do 2 unfold_goal.
  my_auto; intros Heq; [
    set (boolSpec_elim1 (is_integer_promotion_correct P _ _) Heq)
  | set (boolSpec_elim2 (is_integer_promotion_correct P _ _) Heq)]; my_auto.
Qed.

Lemma promotion_correct P t1 :
  optionSpec (promotion P t1) (D.promotion P t1).
Proof.
  do 2 unfold_goal.
  repeat var_destruct.
  constructor.
  apply integer_promotion_correct.
Qed.

Lemma promotion_unique {P} {t1} :
  optionUnique (promotion P t1) (D.promotion P t1).
Proof.
  do 2 unfold_goal.
  inversion_clear 1.
  repeat apply f_equal.
  apply (integer_promotion_unique).
  assumption.
Qed.

Lemma promotion_functional {P} {t1 t2 t2'} :
  D.promotion P t1 t2  ->
  D.promotion P t1 t2' ->
  t2 = t2'.
Proof.
  intros H1 H2.
  set (promotion_unique _ H1).
  set (promotion_unique _ H2).
  congruence.
Qed.

Lemma is_usual_arithmetic_promoted_integer_correct P it1 it2 it3 :
  D.promoted it1 ->
  D.promoted it2 ->
  boolSpec (is_usual_arithmetic_promoted_integer P it1 it2 it3)
           (D.usualArithmeticPromotedInteger     P it1 it2 it3).
Proof.
  do 2 unfold_goal.
  set (lt_integer_rank_correct P it1 it2).
  set (lt_integer_rank_correct P it2 it1).
  set (le_integer_rank_correct P it1 it2).
  set (le_integer_rank_correct P it2 it1).
  set (le_integer_range_correct P it1 it2).
  set (le_integer_range_correct P it2 it1).
  inversion 1;
  inversion 1;
  subst;
  abstract (
    simpl in *;
    match goal with
    | |- context[lt_Z (precision P ?it1) (precision P ?it2)] =>
           let Heq := fresh in
           case_eq (lt_Z (precision P it1) (precision P it2));
           intros Heq; rewrite_all Heq; clear Heq
    | _ => idtac
    end;
    match goal with
    | |- context [D.usualArithmeticPromotedInteger P (Unsigned  _) (Signed ?ibt) _] => set (make_corresponding_unsigned_Signed_correct ibt)
    | |- context [D.usualArithmeticPromotedInteger P (Signed ?ibt) (Unsigned  _) _] => set (make_corresponding_unsigned_Signed_correct ibt)
    | _ => idtac
    end;
    destruct_integerType_hyp it3;
    solve [inversion 1; my_auto | econstructor (now my_auto)]
  ).
Qed.

Lemma usual_arithmetic_promoted_integer_correct P {it1 it2} :
  D.promoted it1 ->
  D.promoted it2 ->
  findSpec (usual_arithmetic_promoted_integer P it1 it2) (D.usualArithmeticPromotedInteger P it1 it2).
Proof.
  do 2 unfold_goal.
  set (lt_integer_rank_correct P it1 it2).
  set (lt_integer_rank_correct P it2 it1).
  set (le_integer_rank_correct P it1 it2).
  set (le_integer_rank_correct P it2 it1).
  set (le_integer_range_correct P it1 it2).
  set (le_integer_range_correct P it2 it1).
  inversion 1;
  inversion 1;
  subst;
  abstract (
    simpl in *;
    match goal with
    | |- context[lt_Z (precision P ?it1) (precision P ?it2)] =>
           let Heq := fresh in
           case_eq (lt_Z (precision P it1) (precision P it2));
           intros Heq; rewrite_all Heq; clear Heq
    | _ => idtac
    end;
    match goal with
    | |- context [D.usualArithmeticPromotedInteger P (Unsigned  _) (Signed ?ibt) _] => set (make_corresponding_unsigned_Signed_correct ibt)
    | |- context [D.usualArithmeticPromotedInteger P (Signed ?ibt) (Unsigned  _) _] => set (make_corresponding_unsigned_Signed_correct ibt)
    | _ => idtac
    end;
    solve [inversion 1; my_auto | econstructor (now my_auto)]      
  ).
Qed.

Lemma usual_arithmetic_promoted_integer_unique {P} {it1 it2} :
  D.promoted it1 ->
  D.promoted it2 ->
  findUnique (usual_arithmetic_promoted_integer P it1 it2) (D.usualArithmeticPromotedInteger P it1 it2).
Proof.
  do 2 unfold_goal.
  set (signed_type_correct it1).
  set (signed_type_correct it2).
  set (unsigned_type_correct it1).
  set (unsigned_type_correct it2).
  set (lt_integer_rank_correct P it1 it2).
  set (lt_integer_rank_correct P it2 it1).
  set (le_integer_rank_correct P it1 it2).
  set (le_integer_rank_correct P it2 it1).
  set (le_integer_range_correct P it2 it1).
  set (le_integer_range_correct P it1 it2).
  inversion 1;
  inversion 1;
  inversion 1;
  subst; simpl in *;
  repeat match goal with
  | H : D.correspondingUnsigned _ ?it |- _ => is_var it; inversion_clear H
  | |- context[lt_Z (precision P ?it1) (precision P ?it2)] =>
      let Heq := fresh in
      case_eq (lt_Z (precision P it1) (precision P it2));
      intros Heq; rewrite_all Heq; clear Heq
  | _ => solve [congruence|contradiction]
  end.
Qed.

Lemma usualArithmeticPromotedInteger_functional P {it1 it2 it3 it3'} :
  D.promoted it1 ->
  D.promoted it2 ->
  D.usualArithmeticPromotedInteger P it1 it2 it3  ->
  D.usualArithmeticPromotedInteger P it1 it2 it3' ->
  it3 = it3'.
Proof.
  intros P1 P2 H1 H2.
  set (usual_arithmetic_promoted_integer_unique P1 P2 _ H1).
  set (usual_arithmetic_promoted_integer_unique P1 P2 _ H2).
  congruence.
Qed.

Lemma is_usual_arithmetic_integer_correct P it1 it2 it3 :
  boolSpec (is_usual_arithmetic_integer P it1 it2 it3) (D.usualArithmeticInteger P it1 it2 it3).
Proof.
  set (integer_promotion_correct P it1) as A1.
  set (integer_promotion_correct P it2) as A2.
  set (is_usual_arithmetic_promoted_integer_correct P _ _ it3
         (integerPromotion_promoted A1)
         (integerPromotion_promoted A2)) as A.
  do 2 unfold_goal.
  boolSpec_destruct.
  - econstructor; eassumption.
  - inversion_clear 1.
    match goal with
    | H1 : D.integerPromotion P it1 _
    , H2 : D.integerPromotion P it2 _
    , H  : D.usualArithmeticPromotedInteger _ _ _ _  |- _ =>
      rewrite_all (integerPromotion_functional H1 A1);
      rewrite_all (integerPromotion_functional H2 A2);
      apply A; assumption
  end.
Qed.

Lemma usual_arithmetic_integer_correct P it1 it2 :
  findSpec (usual_arithmetic_integer P it1 it2) (D.usualArithmeticInteger P it1 it2).
Proof.
  set (integer_promotion_correct P it1) as P1.
  set (integer_promotion_correct P it2) as P2.
  set (usual_arithmetic_promoted_integer_correct P
         (integerPromotion_promoted P1)
         (integerPromotion_promoted P2)).
  econstructor; eassumption.
Qed.

Lemma usual_arithmetic_integer_unique P it1 it2 :
  findUnique (usual_arithmetic_integer P it1 it2) (D.usualArithmeticInteger P it1 it2).
Proof.
  inversion_clear 1.
  set (integer_promotion_correct P it1) as A1.
  set (integer_promotion_correct P it2) as A2.
  match goal with
  | H1 : D.integerPromotion P it1 _
  , H2 : D.integerPromotion P it2 _
  , H  : D.usualArithmeticPromotedInteger _ _ _ _  |- _ =>
      rewrite_all (integerPromotion_functional H1 A1);
      rewrite_all (integerPromotion_functional H2 A2);
      set (usual_arithmetic_promoted_integer_correct P
             (integerPromotion_promoted A1)
             (integerPromotion_promoted A2)) as A;
      exact (usualArithmeticPromotedInteger_functional P
               (integerPromotion_promoted A1)
               (integerPromotion_promoted A2) A H)
  end.
Qed.

Lemma usualArithmeticInteger_functional P {it1 it2 it3 it3'} :
  D.usualArithmeticInteger P it1 it2 it3  ->
  D.usualArithmeticInteger P it1 it2 it3' ->
  it3 = it3'.
Proof.
  intros H1 H2.
  set (usual_arithmetic_integer_unique P it1 it2 _ H1).
  set (usual_arithmetic_integer_unique P it1 it2 _ H2).
  congruence.
Qed.

Definition is_usual_arithmetic_correct P t1 t2 t3:
  boolSpec (is_usual_arithmetic P t1 t2 t3) (D.usualArithmetic P t1 t2 t3).
Proof.
  do 2 unfold_goal.
  repeat context_destruct.  
  match goal with
  | |- is_usual_arithmetic_integer P ?it1 ?it2 ?it3 = _ -> _ => case_fun (is_usual_arithmetic_integer_correct P it1 it2 it3)
  end; my_auto.
Qed.

Definition usual_arithmetic_correct P t1 t2 :
  optionSpec (usual_arithmetic P t1 t2) (D.usualArithmetic P t1 t2).
Proof.
  do 2 unfold_goal; repeat context_destruct.
  constructor; apply usual_arithmetic_integer_correct.
Qed.

Definition usual_arithmetic_unique {P} {t1 t2} :
  optionUnique (usual_arithmetic P t1 t2) (D.usualArithmetic P t1 t2).
Proof.
  intros ? H.
  do 2 unfold_goal;
  repeat context_destruct;
  repeat match goal with 
  | H : D.usualArithmetic        _ _ _ _ |- _ => inversion_clear H
  | H : D.usualArithmeticInteger _ _ _ _ |- _ => inversion_clear H
  end.
  do 3 apply f_equal.
  match goal with
  | H1 : D.integerPromotion _ ?it1 ?it1'
  , H2 : D.integerPromotion _ ?it2 ?it2'
  , H  : D.usualArithmeticPromotedInteger _ ?it1' ?it2' _ |- _ =>
      set (integer_promotion_correct P it1) as A1;
      set (integer_promotion_correct P it2) as A2;
      rewrite_all (integerPromotion_functional H1 A1);
      rewrite_all (integerPromotion_functional H2 A2);
      set (usual_arithmetic_promoted_integer_correct P
             (integerPromotion_promoted A1)
             (integerPromotion_promoted A2)) as A;
      eapply (usualArithmeticPromotedInteger_functional P
                (integerPromotion_promoted A1)
                (integerPromotion_promoted A2) A H)
  end.
Qed.

Definition usualArithmetic_functional {P} {t1 t2 t3 t3'} :
  D.usualArithmetic P t1 t2 t3  ->
  D.usualArithmetic P t1 t2 t3' ->
  t3 = t3'.
Proof.
  intros H1 H2.
  set (usual_arithmetic_unique _ H1).
  set (usual_arithmetic_unique _ H2).
  congruence.
Qed.

Lemma usualArithmetic_Integer P it1 it2 :
  {t : ctype & D.usualArithmetic P (Basic (Integer it1)) (Basic (Integer it2)) t}.
Proof.
  exists (Basic (Integer (usual_arithmetic_integer P it1 it2))).
  constructor.
  eapply usual_arithmetic_integer_correct.
Qed.

Lemma usual_arithmetic_Integer_Some {P} {it1 it2} :
  exists t : ctype, usual_arithmetic P (Basic (Integer it1)) (Basic (Integer it2)) = Some t.
Proof.
  exists (Basic (Integer (usual_arithmetic_integer P it1 it2))).
  reflexivity.
Qed.

Lemma usual_arithmetic_Integer_None {P} {it1 it2} :
  usual_arithmetic P (Basic (Integer it1)) (Basic (Integer it2)) <> None.
Proof.
  destruct (usualArithmetic_Integer P it1 it2) as [t H].
  set (usual_arithmetic_unique _ H).
  intros ?; congruence.
Qed.

Lemma object_correct t : boolSpec (object t) (D.object t).
Proof. destruct t; my_auto. Qed.

Lemma complete_correct t : boolSpec (complete t) (D.complete t).
Proof. destruct t; my_auto. Qed.

Lemma incomplete_correct t : boolSpec (incomplete t) (D.incomplete t).
Proof. destruct t; my_auto. Qed.

Lemma modifiable_correct qs t : boolSpec (modifiable qs t) (D.modifiable qs t).
Proof.
  do 2 unfold_goal.
  set (object_correct t).
  set (array_correct t).
  set (incomplete_correct t).
  case_eq (const qs); intros ?;
  repeat (boolSpec_destruct; my_auto).
Qed.

Lemma real_correct t : boolSpec (real t) (D.real t).
Proof.
  do 2 unfold_goal.
  generalize (integer_correct t).
  destruct (integer t); my_auto.
Qed.

Lemma compatible_correct :
  forall t1 t2, boolSpec (compatible t1 t2) (D.compatible t1 t2).
Proof.
  apply (ctype_nrect (fun x => forall y, boolSpec (compatible        x y) (D.compatible       x y))
                     (fun x => forall y, boolSpec (compatible_params x y) (D.compatibleParams x y)));
  intros; destruct y;
  unfold_goal; simpl;
  fold compatible_params; unfold andb;
  repeat match goal with
  | [|- eq_basicType ?x ?y = _ -> _] => case_fun (eq_basicType_correct x y)
  | [|- eq_nat ?x ?y = _ -> _] => case_fun (eq_nat_correct x y)
  | [|- eq_qualifiers ?x ?y = _ -> _] => case_fun (eq_qualifiers_correct x y)
  | [IH : forall _, boolSpec (compatible ?t1 _) _ |- compatible ?t1 ?t2 = _ -> _] => case_fun (IH t2)
  | [IH : forall _, boolSpec (compatible_params ?p1 _) _ |- compatible_params ?t1 ?t2 = _ -> _] =>  case_fun (IH t2)
  | _ => context_destruct
  end; now my_auto.
Qed.

Lemma is_composite_correct :
  forall t1 t2 t3, boolSpec (is_composite t1 t2 t3) (D.composite t1 t2 t3).
Proof.
  apply (ctype_nrect (fun x => forall y z, boolSpec (is_composite x y z) (D.composite x y z))
                     (fun x => forall y z, boolSpec (is_composite_params x y z) (D.compositeParams x y z)));
  intros; destruct y, z;
  unfold_goal; simpl;
  fold is_composite_params; unfold andb;
  repeat match goal with
  | [|- eq_nat ?x ?y = _ -> _] => case_fun (eq_nat_correct x y)
  | [|- eq_qualifiers ?x ?y = _ -> _] => case_fun (eq_qualifiers_correct x y)
  | [|- eq_basicType ?x ?y = _ -> _] => case_fun (eq_basicType_correct x y)
  | [|- unqualified ?x = _ -> _] => case_fun (unqualified_correct x)
  | [IH : forall _ _, boolSpec (is_composite ?x _ _) _ |- is_composite ?x ?y ?z = _ -> _] => case_fun (IH y z)
  | [IH : forall _ _, boolSpec (is_composite_params ?x _ _) _|- is_composite_params ?x ?y ?z = _ -> _] => case_fun (IH y z)
  | _ => context_destruct
  end; now my_auto.
Qed.

Lemma composite_correct :
  forall t1 t2, optionSpec (composite t1 t2) (D.composite t1 t2).
Proof.
  apply (ctype_nrect
           (fun x => forall y, optionSpec (composite        x y) (D.composite       x y))
           (fun x => forall y, optionSpec (composite_params x y) (D.compositeParams x y)));
  intros; destruct y;
  unfold_goal; simpl;
  fold composite_params; unfold andb; unfold option_map;
  repeat match goal with
  | [|- eq_nat ?x ?y = _ -> _] => case_fun (eq_nat_correct x y); [subst|]
  | [|- eq_qualifiers ?x ?y = _ -> _] => case_fun (eq_qualifiers_correct x y); [subst|]
  | [|- eq_basicType ?x ?y = _ -> _] => case_fun (eq_basicType_correct x y); [subst|]
  | [IH : forall _, optionSpec (composite ?x _) _ |- composite ?x ?y = _  -> _] => case_fun (IH y)
  | [IH : forall _, optionSpec (composite_params ?x _) _ |- composite_params ?x ?y = _ -> _] => case_fun (IH y)
  | _ => context_destruct
  end; solve [congruence | inversion 1; subst; now firstorder | econstructor (now my_auto) ].
Qed.

Lemma composite_unique :
  forall t1 t2, optionUnique (composite t1 t2) (D.composite t1 t2).
Proof.
  apply (ctype_nrect
           (fun x => forall y, optionUnique (composite        x y) (D.composite       x y))
           (fun x => forall y, optionUnique (composite_params x y) (D.compositeParams x y)));
  intros; destruct y;
  unfold_goal; simpl;
  fold composite_params; unfold andb; unfold option_map;
  inversion 1; subst;
  repeat match goal with
  | [|- eq_nat ?x ?y = _ -> _] => case_fun (eq_nat_correct x y); [subst|]
  | [|- eq_qualifiers ?x ?y = _ -> _] => case_fun (eq_qualifiers_correct x y); [subst|]
  | [|- eq_basicType ?x ?y = _ -> _] => case_fun (eq_basicType_correct x y); [subst|]
  | [IH : forall _, optionUnique (composite ?x _) _ |- composite ?x ?y = _  -> _] => case_fun (IH y)
  | [IH : forall _, optionUnique (composite_params ?x _) _ |- composite_params ?x ?y = _ -> _] => case_fun (IH y)
  | _ => context_destruct
  | [H : D.unqualified _ |- _] => inversion_clear H
  | [Heq : optionUnique (Some ?t) (D.composite ?ty1 ?ty2) , H : D.composite ?ty1 ?ty2 ?ty3 |- _] => notSame t ty3; injection (Heq _ H); intros; subst
  | [Heq : optionUnique None (D.composite ?ty1 ?ty2) , H : D.composite ?ty1 ?ty2 _ |- _] => discriminate (Heq _ H)
  | [Heq : optionUnique (Some ?p) (D.compositeParams ?p1 ?p2) , H : D.compositeParams ?p1 ?p2 ?p' |- _] => notSame p p'; injection (Heq _ H); intros; subst
  | [Heq : optionUnique None (D.compositeParams ?p1 ?p2)  , H : D.compositeParams ?p1 ?p2 _ |- _] => discriminate (Heq _ H)
  end; congruence.
Qed.

Lemma composite_functional {t1 t2 t3 t3'} :
  D.composite t1 t2 t3  ->
  D.composite t1 t2 t3' ->
  t3 = t3'.
Proof.
  intros H1 H2.
  set (composite_unique _ _ _ H1).
  set (composite_unique _ _ _ H2).
  congruence.
Qed.

Lemma lvalue_convertible_correct t : boolSpec (lvalue_convertible t) (D.lvalueConvertible t).
Proof.
  do 2 unfold_goal.
  set (array_correct t).
  set (complete_correct t).
  repeat (boolSpec_destruct; my_auto).
Qed.

Lemma pointer_conversion_correct t1 : findSpec (pointer_conversion t1) (D.pointerConversion t1).
Proof. destruct t1; my_auto. Qed.

Lemma pointer_conversion_unique t1 : findUnique (pointer_conversion t1) (D.pointerConversion t1).
Proof.
  destruct t1;
  inversion_clear 1;
  match goal with
  | H : D.unqualified _ |- _ => inversion_clear H
  | H : ~ D.array (Array _ _) |- _ => exfalso; apply H; constructor
  | H : ~ D.function (Function _ _) |- _ => exfalso; apply H; constructor
  | _ => idtac
  end; my_auto.
Qed.

Lemma pointerConversion_functional {t t1 t2} :
  D.pointerConversion t t1 ->
  D.pointerConversion t t2 ->
  t1 = t2.
Proof.
  intros H1 H2.
  set (pointer_conversion_unique _ _ H1).
  set (pointer_conversion_unique _ _ H2).
  congruence.
Qed.

Lemma lvalue_conversion_correct t1 : optionSpec (lvalue_conversion t1) (D.lvalueConversion t1).
Proof.
  do 2 unfold_goal.
  set (pointer_conversion_correct t1).
  set (lvalue_convertible_correct t1).
  boolSpec_destruct; my_auto.
Qed.

Lemma lvalue_conversion_unique t1 : optionUnique (lvalue_conversion t1) (D.lvalueConversion t1).
Proof.
  do 2 unfold_goal.
  set (lvalue_convertible_correct t1).
  inversion_clear 1; boolSpec_destruct; my_auto.
  match goal with
  | H : D.pointerConversion _ _ |- _ => set (pointer_conversion_unique t1 _ H1); congruence
  end.
Qed.

Lemma lvalueConversion_functional {t t1 t2} :
  D.lvalueConversion t t1 ->
  D.lvalueConversion t t2 ->
  t1 = t2.
Proof.
  intros H1 H2.
  set (lvalue_conversion_unique _ _ H1).
  set (lvalue_conversion_unique _ _ H2).
  congruence.
Qed.

(* Lemma: it doesn't matter whether we check 'pointer' before or after lvalue conversion. *)
Lemma lvalue_conversion_pointer t : D.lvalueConvertible t -> (D.pointer t <-> D.pointer (pointer_conversion t)).
Proof.
  inversion_clear 1 as [? Hnarray Hcomplete].
  destruct t; split;
  solve [ trivial
        | exfalso; apply Hnarray; constructor
        | inversion Hcomplete ].
Qed.

(* Pointer conversion leaves pointers untouched. *)
Lemma pointer_conversion_pointer {t} : D.pointer t -> pointer_conversion t = t.
Proof. inversion 1; reflexivity. Qed.

Lemma lvalueConversion_pointer t1 t2 : D.lvalueConversion t1 t2 -> (D.pointer t1 <-> D.pointer t2).
Proof.
  inversion_clear 1 as [? ? ? Hpointer].
  rewrite <- (pointer_conversion_unique _ _ Hpointer).
  apply lvalue_conversion_pointer.
  assumption.
Qed.

(* Pointer conversion leaves integers untouched. *)
Lemma pointer_conversion_integer_id {t} : D.integer t -> pointer_conversion t = t.
Proof. inversion 1; reflexivity. Qed.

Lemma pointer_conversion_integer {t} : D.integer (pointer_conversion t) -> D.integer t.
Proof. destruct t; my_auto. Qed.

Lemma pointer_conversion_arithmetic_id {t} : D.arithmetic t -> pointer_conversion t = t.
Proof. inversion 1; apply pointer_conversion_integer_id; assumption. Qed.

Lemma pointer_conversion_arithmetic {t} : D.arithmetic (pointer_conversion t) -> D.arithmetic t.
Proof. inversion 1; constructor; apply pointer_conversion_integer; assumption. Qed.

Lemma inIntegerRange_leIntegerRange {P} {it1 it2} {n} :
  D.leIntegerRange P it1 it2 ->
  D.inIntegerRange P n it1 ->
  D.inIntegerRange P n it2.
Proof.
  inversion 1; inversion 1; subst.
  repeat match goal with
  | [H : sub    _ _ |- _ ] => inversion_clear H
  | [H : memNat _ _ |- _ ] => inversion_clear H
  end.
  constructor; constructor;
  eapply Z.le_trans; eassumption.
Qed.

Definition inIntegerRange_Signed_Int_Long {P} {n} :=
  inIntegerRange_leIntegerRange (n:=n) (
    D.LeIntegerRange _ _ _
      (integer_range_precision_signed (D.Signed_Int P _) (D.Signed_Int P _) (le_precision_Signed_Int_Long P))
  ).

Definition inIntegerRange_Signed_Long_LongLong {P} {n} :=
  inIntegerRange_leIntegerRange (n:=n) (
    D.LeIntegerRange _ _ _
      (integer_range_precision_signed (D.Signed_Int P _) (D.Signed_Int P _) (le_precision_Signed_Long_LongLong P))
  ).

Definition inIntegerRange_Unsigned_Int_Long {P} {n} :=
  inIntegerRange_leIntegerRange (n:=n) (
    D.LeIntegerRange _ _ _
      (integer_range_precision_unsigned (D.Unsigned_Int P _) (D.Unsigned_Int P _) (le_precision_Unsigned_Int_Long P))
  ).

Definition inIntegerRange_Unsigned_Long_LongLong {P} {n} :=
  inIntegerRange_leIntegerRange (n:=n) (
    D.LeIntegerRange _ _ _
      (integer_range_precision_unsigned (D.Unsigned_Int P _) (D.Unsigned_Int P _) (le_precision_Unsigned_Long_LongLong P))
  ).

Local Close Scope Z.

Lemma pointer_to_complete_object_correct t :
  if pointer_to_complete_object t
    then exists q t', (t = Pointer q t') /\ D.complete t'
    else ~ D.pointer t \/ forall q t', t = Pointer q t' -> ~ D.complete t'.
Proof.
  unfold_goal.
  repeat match goal with
  | [|- complete ?t = _ -> _] => case_fun (complete_correct t)
  | [|- _ /\ _] => split
  | [|- exists _, _] => eexists; eexists; now intuition
  | _ => context_destruct
  end; right; congruence.
Qed.

Lemma pointers_to_compatible_complete_objects_correct t1 t2 :
  if pointers_to_compatible_complete_objects t1 t2
    then exists q1' t1' q2' t2',
           t1 = Pointer q1' t1' /\ t2 = Pointer q2' t2' /\
           D.complete t1' /\ D.complete t2' /\ D.compatible t1' t2'
    else ~ D.pointer t1 \/ ~ D.pointer t2
         \/ (forall q1' t1', t1 = Pointer q1' t1' -> ~ D.complete t1')
         \/ (forall q2' t2', t2 = Pointer q2' t2' -> ~ D.complete t2')
         \/ (forall q1' q2' t1' t2',
              t1 = Pointer q1' t1' ->
              t2 = Pointer q2' t2' -> ~ D.compatible t1' t2').
Proof.
  unfold_goal.
  unfold andb.
  repeat match goal with
  | [|- complete ?t = _ -> _] => case_fun (complete_correct t)
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (compatible_correct t1 t2)
  | [|- _ /\ _] => split
  | [|- exists _, _] => eexists; eexists; eexists; eexists; now intuition
  | [|- ~ D.pointer ?t \/ _ ] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; inversion 1
      end
  | [|- _ \/ ~ D.pointer ?t \/ _] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => right; left; inversion 1
      end
  | [_ : ~ D.complete ?t1       |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; left; intros; congruence
  | [_ : ~ D.complete ?t2       |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; right; left; intros; congruence
  | [_ : ~ D.compatible ?t1 ?t2 |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; right; right; intros; congruence
  | _ => context_destruct
  end.
Qed.

Lemma pointers_to_compatible_objects_correct t1 t2 :
  if pointers_to_compatible_objects t1 t2
    then exists q1' t1' q2' t2',
           t1 = Pointer q1' t1' /\ t2 = Pointer q2' t2' /\
           D.object t1'  /\ D.object t2' /\ D.compatible t1' t2'
    else ~ D.pointer t1 \/ ~ D.pointer t2
         \/ (forall q1' t1', t1 = Pointer q1' t1' -> ~ D.object t1')
         \/ (forall q2' t2', t2 = Pointer q2' t2' -> ~ D.object t2')
         \/ (forall q1' q2' t1' t2',
              t1 = Pointer q1' t1' ->
              t2 = Pointer q2' t2' -> ~ D.compatible t1' t2').
Proof.
  unfold_goal.
  unfold andb.
  repeat match goal with
  | [|- object ?t = _ -> _] => case_fun (object_correct t)
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (compatible_correct t1 t2)
  | [|- _ /\ _] => split
  | [|- exists _, _] => eexists; eexists; eexists; eexists; intuition
  | [|- ~ D.pointer ?t \/ _] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; inversion 1
      end
  | [|- _ \/ ~ D.pointer ?t \/ _ ] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => right; left; inversion 1
      end
  | [_ : ~ D.object t1        |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; left; intros; congruence
  | [_ : ~ D.object t2        |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; right; left; intros; congruence
  | [_ : ~ D.compatible t1 t2 |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; right; right; intros; congruence
  | _ => context_destruct
  end.
Qed.

Lemma pointer_to_object_correct t :
  if pointer_to_object t
    then exists q t', t = Pointer q t' /\ D.object t'
    else ~ D.pointer t \/ forall q t', t = Pointer q t' -> ~ D.object t'.
Proof.
  unfold_goal.
  repeat match goal with
  | [|- object ?t = _ -> _] => case_fun (object_correct t)
  | [|- _ /\ _] => split
  | [|- exists _, _] => eexists; eexists; intuition
  | [|- ~ D.pointer ?t \/ _] =>
      match t with
      | Pointer _ _ => right
      | _           => left; inversion 1
      end
  | _ => context_destruct
  end; congruence.
Qed.

Lemma pointer_to_void_correct t :
  if pointer_to_void t
    then exists q t', t = Pointer q t' /\ D.void t'
    else ~ D.pointer t \/ forall q t', t = Pointer q t' -> ~ D.void t'.
Proof.
  unfold_goal.
  repeat match goal with
  | [|- void ?t = _ -> _] => case_fun (void_correct t)
  | [|- ~ _] => intros [? [? [? ?]]]
  | [|- _ /\ _] => split
  | [|- exists _, _] => eexists; eexists; now intuition
  | [|- ~ D.pointer ?t \/ _] =>
      match t with
      | Pointer _ _ => right; intros; inversion 1
      | _           => left; inversion 1
      end
  | _ => context_destruct
  end; congruence.
Qed.

Lemma pointers_to_compatible_types_correct t1 t2 :
  if pointers_to_compatible_types t1 t2
    then exists q1' t1' q2' t2',
           t1 = Pointer q1' t1' /\ t2 = Pointer q2' t2' /\
           D.compatible t1' t2'
    else ~ D.pointer t1 \/ ~ D.pointer t2
         \/ (forall q1' q2' t1' t2',
              t1 = Pointer q1' t1' ->
              t2 = Pointer q2' t2' -> ~ D.compatible t1' t2').
Proof.
  unfold_goal.
  repeat match goal with
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (compatible_correct t1 t2)
  | [|- _ /\ _] => split
  | [|- exists _, _] => repeat eexists; now intuition 
  | [|- ~ D.pointer ?t \/ _ ] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; inversion 1
      end
  | [|- _ \/ ~ D.pointer ?t \/ _ ] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => right; left; inversion 1
      end
  | [_ : ~ D.compatible t1 t2 |- _ \/ _ \/ _ ] => right; right; intros; congruence
  | _ => context_destruct
  end.
Qed.
