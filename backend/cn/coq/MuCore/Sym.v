Require Import Coq.ZArith.ZArith.
From Coq Require Import Arith Bool List String.

Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Require Import StructTact.StructTactics.
Require Import Lia.

Require Import Location Utils Symbol.


Definition t := Symbol.t.

Module Symbol_sym_as_OT <: OrderedType.
  Definition t := Symbol.t.

  Definition eq: t -> t -> Prop := fun a b => is_true (symbolEquality a b).
  Definition lt (a b: t): Prop := match symbol_compare a b with
                               | Lt => True
                               | _ => False
                               end.

  Lemma eq_refl: forall x : t, eq x x.
  Proof.
    intros.
    unfold eq, is_true, symbolEquality.
    destruct x as [d1 n1 z1].
    apply andb_true_intro.
    split.
    -
      unfold digest_compare.
      break_match.
      + apply Z.eqb_refl.
      + exfalso.
        clear z1 n1.
        induction d1.
        * inversion Heqc.
        * cbn in Heqc.
          break_match.
          -- auto.
          -- unfold Ascii.compare in *.
             rewrite N.compare_lt_iff in Heqc0.
             lia.
          -- inversion Heqc.
      + exfalso.
        clear z1 n1.
        induction d1.
        * inversion Heqc.
        * cbn in Heqc.
          break_match.
          -- auto.
          -- inversion Heqc.
          -- unfold Ascii.compare in *.
             rewrite N.compare_gt_iff in Heqc0.
             lia.
    -
      lia.
  Qed.

  Lemma eq_sym: forall x y : t, eq x y -> eq y x.
  Proof.
    unfold eq, symbolEquality, is_true.
    intros x y H.
    destruct x,y.
    apply andb_prop in H.
    destruct H as [D ZE].
    apply andb_true_intro.
    split.
    -
      clear - D.
      apply Z.eqb_eq in D.
      apply Z.eqb_eq.
      unfold digest_compare in *.
      repeat break_match;try lia.
      +
        rewrite compare_antisym in Heqc0.
        unfold CompOpp in Heqc0.
        rewrite Heqc in Heqc0.
        inversion Heqc0.
      +
        rewrite compare_antisym in Heqc0.
        unfold CompOpp in Heqc0.
        rewrite Heqc in Heqc0.
        inversion Heqc0.
    -
      apply Z.eqb_eq in ZE.
      lia.
  Qed.

  Lemma eq_trans: forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq, symbolEquality, is_true.
    intros x y z H H0.
    destruct x, y, z.

    apply andb_prop in H, H0.
    destruct H as [D0 ZE0].
    destruct H0 as [D1 ZE1].
    apply andb_true_intro.
    split.
    -
      clear - D0 D1.
      apply Z.eqb_eq in D0, D1.
      apply Z.eqb_eq.
      unfold digest_compare in *.
      repeat break_match;try lia.
      +
        erewrite string_eq_trans in Heqc; eauto.
        inversion Heqc.
      +
        erewrite string_eq_trans in Heqc; eauto.
        inversion Heqc.
    -
      apply Z.eqb_eq in ZE0, ZE1.
      lia.
  Qed.

 Ltac Z_compare_iff :=
    match goal with
    | [H: (_ ?= _)%Z = Lt |- _] => rewrite Z.compare_lt_iff in H
    | [H: (_ ?= _)%Z = Gt |- _] => rewrite Z.compare_gt_iff in H
    | [H: (_ ?= _)%Z = Eq |- _] => rewrite Z.compare_eq_iff in H
    | [H: (_ =? _)%Z = true |- _] => rewrite Z.eqb_eq in H
    | [H: (_ =? _)%Z = false |- _] => rewrite Z.eqb_neq in H
    | [H: (_ <? _)%Z = true |- _] => rewrite Z.ltb_lt in H
    | [H: (_ <? _)%Z = false |- _] => rewrite Z.ltb_nlt in H
    end.

  Lemma digest_compare_eq_iff:
    forall x y, digest_compare x y = 0%Z -> x = y.
  Proof.
    intros x y H.
    unfold digest_compare in *.
    repeat break_match_hyp;subst;try lia.
    clear H.
    apply compare_eq_iff in Heqc.
    auto.
  Qed.

  Lemma digest_compare_eq_sym:
    forall x y, digest_compare x y = 0%Z -> digest_compare y x = 0%Z.
  Proof.
    intros x y H.
    unfold digest_compare in *.
    repeat break_match_hyp;subst;try lia.
    clear H.
    apply compare_eq_iff in Heqc.
    subst y.
    rewrite string_eq_refl.
    reflexivity.
  Qed.

  Lemma digest_compare_eq_transitive:
    forall x y z, digest_compare x y = 0%Z -> digest_compare y z = 0%Z -> digest_compare x z = 0%Z.
  Proof.
    intros x y z H H0.
    unfold digest_compare in *.
    repeat break_match_hyp;subst;try lia.
    clear H H0.
    break_match_goal.
    1: reflexivity.
    1,2:
      pose proof (string_eq_trans x y z) as T;
      specialize (T Heqc0 Heqc);
      congruence.
  Qed.

  Lemma digest_compare_lt_gt:
    forall x y,
      (digest_compare x y < 0)%Z -> (digest_compare y x > 0)%Z.
  Proof.
    intros x y H.
    unfold digest_compare in *.
    repeat break_match_hyp;subst;try lia.
    clear H.
    rewrite String_as_OT.cmp_antisym in Heqc.
    unfold CompOpp in Heqc.
    repeat break_match_hyp; try discriminate.
    unfold String_as_OT.cmp in Heqc0.
    rewrite Heqc0.
    lia.
  Qed.

  Lemma digest_compare_lt_transitive:
    forall x y z, (digest_compare x y < 0)%Z -> (digest_compare y z < 0)%Z -> (digest_compare x z < 0)%Z.
  Proof.
    intros x y z H H0.
    unfold digest_compare in *.
    repeat break_match_hyp;subst;try lia.
    clear H H0.
    break_match_goal.
    2: lia.
    1,2: exfalso.
    -
      apply String_as_OT.cmp_lt in Heqc, Heqc0.
      pose proof(String_as_OT.lt_trans x y z Heqc0 Heqc) as T.
      clear Heqc Heqc0 y.
      apply String_as_OT.lt_not_eq in T.
      unfold String_as_OT.eq in T.
      apply compare_eq_iff in Heqc1.
      congruence.
    -
      apply String_as_OT.cmp_lt in Heqc, Heqc0.
      pose proof(String_as_OT.lt_trans x y z Heqc0 Heqc) as T.
      clear Heqc Heqc0 y.
      rewrite <- String_as_OT.cmp_lt in T.
      unfold String_as_OT.cmp in T.
      congruence.
  Qed.

  Lemma digest_compare_eq_bool_sym:
    forall d1 d2,
      (digest_compare d1 d2 =? 0)%Z = true ->
      (digest_compare d2 d1 =? 0)%Z = true.
  Proof.
    unfold digest_compare.
    intros d1 d2.
    rewrite compare_antisym.
    destruct (d2 ?= d1)%string; auto.
  Qed.

  Lemma digest_compare_lt_bool_antisym:
    forall d1 d2,
      (digest_compare d1 d2 =? 0)%Z = false ->
      (digest_compare d1 d2 <? 0 = negb (digest_compare d2 d1 <? 0))%Z.
  Proof.
    unfold digest_compare.
    intros d1 d2.
    rewrite compare_antisym.
    destruct (d2 ?= d1)%string; auto.
  Qed.


  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    intros x y z H H0.
    repeat break_match_hyp; try tauto.
    clear H0 H.
    rename Heqc0 into Hxy, Heqc into Hyz.
    break_match_goal; try tauto.
    -
      unfold symbol_compare in *.
      repeat break_match_hyp; subst; try congruence;repeat Z_compare_iff; subst.
      +
        lia.
      +
        apply digest_compare_eq_sym in Heqb0.
        pose proof (digest_compare_eq_transitive d d0 d1) as D.
        lia.
      +
        apply digest_compare_eq_sym in Heqb2.
        pose proof (digest_compare_eq_transitive d1 d d0) as D.
        lia.
      +
        apply digest_compare_eq_iff in Heqb.
        subst d0.
        clear - Heqb1 Heqb3.
        apply digest_compare_lt_gt in Heqb3.
        congruence.
    -
      unfold symbol_compare in *.
      repeat break_match_hyp; subst; try congruence;repeat Z_compare_iff.
      +
        lia.
      +
        apply digest_compare_eq_sym in Heqb0.
        pose proof (digest_compare_eq_transitive d d0 d1) as D.
        lia.
      +
        apply digest_compare_eq_sym in Heqb2.
        pose proof (digest_compare_eq_transitive d1 d d0) as D.
        lia.
      +
        apply digest_compare_eq_iff in Heqb.
        subst d0.
        clear - Heqb1 Heqb3.
        apply digest_compare_lt_gt in Heqb3.
        congruence.
      +
        apply digest_compare_eq_iff in Heqb2.
        subst d1.
        congruence.
      +
        apply digest_compare_eq_iff in Heqb1.
        subst d1.
        lia.
      +
        apply digest_compare_eq_iff in Heqb3.
        subst d1.
        congruence.
      +
        pose proof (digest_compare_lt_transitive d d1 d0) as T.
        lia.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H.
    unfold lt in H.
    destruct (symbol_compare x y) eqn:D; auto. clear H.
    unfold not, eq, is_true, symbolEquality.
    destruct x as [d1 n1 z1].
    destruct y as [d2 n2 z2].
    unfold symbol_compare in D.
    intros E.
    apply andb_prop in E.
    destruct E as [E1 E2].
    break_if.
    + clear E1.
      rewrite Z.compare_lt_iff in D.
      rewrite Z.eqb_eq in E2.
      lia.
    + lia.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y.
    case_eq (symbol_compare x y); intro.
    - apply EQ.
      unfold symbol_compare in H.
      destruct x as [d1 n1].
      destruct y as [d2 n2].
      break_if.
      + unfold eq, is_true, symbolEquality.
        apply andb_true_intro.
        split.
        * assumption.
        * apply Z.compare_eq in H.
          apply Z.eqb_eq.
          assumption.
      + break_if; inversion H.
    - apply LT.
      unfold symbol_compare in H.
      destruct x as [d1 n1].
      destruct y as [d2 n2].
      break_if.
      + unfold lt, is_true.
        break_match.
        * cbn in Heqc.
          break_if.
          -- rewrite H in Heqc. inversion Heqc.
          -- break_if; inversion Heqc.
        * trivial.
        * cbn in Heqc.
          break_if.
          -- rewrite H in Heqc. inversion Heqc.
          -- inversion Heqb.
      + break_if.
        * unfold lt.
          break_match.
          -- cbn in Heqc.
             break_if.
             ++ inversion Heqb.
             ++ break_if;inversion Heqc.
          -- trivial.
          -- cbn in Heqc.
             break_if.
             ++ inversion Heqb.
             ++ break_if.
                inversion Heqc.
                inversion Heqb0.
        * inversion H.
    - apply GT.
      unfold symbol_compare in H.
      destruct x as [d1 n1].
      destruct y as [d2 n2].
      break_if.
      + unfold lt, is_true.
        apply Zcompare_Gt_Lt_antisym in H.
        break_match.
        * cbn in Heqc.
          break_if.
          -- rewrite H in Heqc. inversion Heqc.
          -- break_if; inversion Heqc.
        * trivial.
        * cbn in Heqc.
          break_if.
          -- rewrite H in Heqc. inversion Heqc.
          -- break_if.
             inversion Heqc.
             apply digest_compare_eq_bool_sym in Heqb.
             rewrite Heqb in Heqb0.
             inversion Heqb0.
      + break_if.
        * inversion H.
        * unfold lt.
          break_match.
          -- cbn in Heqc.
             break_if.
             ++ apply digest_compare_eq_bool_sym in Heqb1.
                rewrite Heqb in Heqb1.
                inversion Heqb1.
             ++ break_if;inversion Heqc.
          -- trivial.
          -- cbn in Heqc.
             break_if.
             ++ apply digest_compare_eq_bool_sym in Heqb1.
                rewrite Heqb in Heqb1.
                inversion Heqb1.
             ++ break_if.
                inversion Heqc.
                rewrite digest_compare_lt_bool_antisym in Heqb0.
                rewrite Heqb2 in Heqb0.
                cbv in Heqb0.
                inversion Heqb0.
                assumption.
  Defined.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y.
    destruct x, y.
    unfold eq, symbolEquality, digest_compare.
    break_match; cbn.
    destruct (z =? z0)%Z; cbv.
    + left; trivial.
    + right; lia.
    + right; cbv; lia.
    + right; cbv; lia.
  Defined.

End Symbol_sym_as_OT.

Module SymMap := FMapAVL.Make(Symbol_sym_as_OT).

Definition map_from_list {T:Type}: (list (sym*T)) -> SymMap.t T.
Admitted. (* TODO *)
