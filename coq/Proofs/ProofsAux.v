Require Import Coq.Strings.String.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Program.Equality. (* for dep. destruction *)
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.

Require Import ExtLib.Data.List.

Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

Require Import Lia.

Require Import Common.SimpleError.
Require Import Common.Utils.
Require Import Common.ZMap.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import Coq.Relations.Relation_Definitions.

Require Import StructTact.StructTactics.
Require Import Tactics.

Section ListAux.

  #[global] Instance List_fold_left_proper
    {A B : Type}
    (Eb: relation B)
    (Ae: relation A)
    `{Equivalence A Ae}
    `{Equivalence B Eb}
    (f : A -> B -> A)
    `{f_mor: !Proper ((Ae) ==> (Eb) ==> (Ae)) f}
  :
  Proper (eqlistA Eb ==> Ae ==> Ae) (List.fold_left f).
  Proof.
    intros x y Exy.
    intros a b Eab.
    dependent induction Exy.
    -
      apply Eab.
    -
      cbn.
      apply IHExy.
      apply f_mor.
      apply Eab.
      apply H1.
  Qed.

  #[global] Instance List_fold_left_eq_proper
    {A B : Type}
    (Eb: relation B)
    (Ae: relation A)
    `{Equivalence A Ae}
    `{Equivalence B Eb}
    (f : A -> B -> A)
    `{f_mor: !Proper ((Ae) ==> (Eb) ==> (Ae)) f}
    :
    Proper ((eq) ==> (Ae) ==> (Ae)) (List.fold_left f).
  Proof.
    intros x y Exy.
    destruct Exy.
    intros a b Eab.
    -
      dependent induction x.
      +
        apply Eab.
      +
        cbn.
        apply IHx.
        apply f_mor.
        assumption.
        reflexivity.
  Qed.

  Lemma mapi_cons  {A B : Type} x l {f: nat -> A -> B}:
    mapi f (x :: l) = f 0 x :: mapi (compose f S) l.
  Proof. auto. Qed.

  #[global] Instance list_mapi_Proper
    {A B : Type}
    (pA: relation A)
    (pB: relation B)
    :
    Proper (pointwise_relation _ (pA ==> pB) ==> (eqlistA pA ==> eqlistA pB))
      mapi.
  Proof.
    intros f f' Hf l l' Hl. revert f f' Hf.
    induction Hl as [|x1 x2 l1 l2 ?? IH]; intros f f' Hf.
    - constructor.
    -
      cbn.
      constructor.
      +
        apply Hf, H.
      +
        apply IH. intros i y y' ?.
        apply Hf, H0.
  Qed.

  #[global] Instance list_map_Proper
    {A B : Type}
    (pA: relation A)
    (pB: relation B)
    :
    Proper ((pA ==> pB) ==> (eqlistA pA ==> eqlistA pB)) (@map A B).
  Proof.
    intros f f' Hf l l' Hl. revert f f' Hf.
    induction Hl as [|x1 x2 l1 l2 ?? IH]; intros f f' Hf.
    - constructor.
    -
      cbn.
      constructor.
      + apply Hf, H.
      + apply IH, Hf.
  Qed.

  #[global] Instance list_init_proper
    {A:Type}
    (Ae: relation A)
    :
    Proper ( eq ==> (eq ==> (Ae)) ==> eqlistA Ae) list_init.
  Proof.
    intros n n' En f f' f_mor.
    subst n'.
    induction n.
    -
      constructor.
    -
      simpl.
      constructor; auto.
  Qed.

  #[global] Instance eqlistA_Reflexive
    {T:Type}
    (R: relation T)
    `{RR: Reflexive T R}:
    Reflexive (eqlistA R ).
  Proof.
    intros a.
    induction a;constructor.
    apply RR.
    apply IHa.
  Qed.

  Lemma ealistA_concat:
    forall (A:Type) (l0 l1: list (list A)) (R:relation A),
      eqlistA (eqlistA R) l0 l1 -> eqlistA R (concat l0) (concat l1).
  Proof.
    intros A l0 l1 R E.
    apply eqlistA_altdef in E.
    apply eqlistA_altdef.

    induction E.
    -
      constructor.
    -
      cbn.
      apply Forall2_app.
      +
        apply eqlistA_altdef in H.
        assumption.
      +
        apply IHE.
  Qed.

  Lemma equlistA_concat_rev:
    forall (A:Type) (l0 l1: list (list A)) (R:relation A),
      eqlistA (eqlistA R) l0 l1 ->
      eqlistA R (concat (rev l0)) (concat (rev l1)).
  Proof.
    intros A l0 l1 R H.
    apply ealistA_concat.
    apply eqlistA_rev.
    assumption.
  Qed.

  (* Proper for [monadic_fold_left], postulating that `f` must be proper only for elements from the list.
     C.f. to more naive formulation:
     [Proper ((Ea ==> Eb ==> EMa) ==> (eqlistA Eb) ==> Ea ==> EMa) monadic_fold_left]
   *)
  Lemma monadic_fold_left_proper
    (A B : Type)
    (Eb : relation B)
    (Ea : relation A)
    (m : Type -> Type)
    (M : Monad m)
    (EMa : relation (m A))
    (RetProper: Proper (Ea ==> EMa) ret)
    (BindProper: Proper ((EMa) ==> (Ea ==> EMa) ==> (EMa)) (@bind m M A A))
    (f f' : A -> B -> m A)
    (l l' : list B)
    (El : eqlistA Eb l l')
    {a a' : A}
    {Ex : Ea a a'}
    (Ef : forall (a a' : A), (Ea a a') -> Forall2 (fun b b' => EMa (f a b) (f' a' b')) l l')
    :
    EMa (monadic_fold_left f l a) (monadic_fold_left f' l' a').
  Proof.
    revert a a' Ex.
    induction El.
    -
      intros.
      apply RetProper.
      assumption.
    -
      intros a a' EA.
      cbn.
      apply BindProper.
      +
        specialize (Ef a a' EA).
        invc Ef.
        assumption.
      +
        intros b b' EB.
        apply IHEl.
        *
          intros a0 a0' EA0.
          specialize (Ef a0 a0' EA0).
          invc Ef.
          assumption.
        *
          assumption.
  Qed.


  (* Proper for [monadic_fold_left2], postulating that `f` must be proper only for elements from the list.
   *)
  Lemma monadic_fold_left2_proper
    {A B C:Type}
    (Eb : relation B)
    (Ea : relation A)
    (Ec : relation C)
    (m : Type -> Type)
    (M : Monad m)
    (ML: MonadLaws M)
    (EMa : relation (m A))
    (RetProper: Proper (Ea ==> EMa) ret)
    (BindProper: Proper ((EMa) ==> (Ea ==> EMa) ==> (EMa)) (@bind m M A A))
    (f f': A -> B -> C -> m A)
    (l1 l1' : list B)
    (l2 l2' : list C)
    (El1 : eqlistA Eb l1 l1')
    (El2 : eqlistA Ec l2 l2')
    {x x' : A}
    {Ex : Ea x x'}
    (Ef : forall (a a' : A), (Ea a a') ->
                        Forall2 (fun b b' =>
                                   Forall2 (fun c c' =>
                                              EMa (f a b c) (f' a' b' c')) l2 l2') l1 l1')
    :
    EMa (monadic_fold_left2 f x l1 l2) (monadic_fold_left2 f' x' l1' l2').
  Proof.
  Admitted.


End ListAux.

Module Import ZP := FMapFacts.WProperties_fun(Z_as_OT)(ZMap).
Module Import WZP := FMapFacts.WFacts_fun(Z_as_OT)(ZMap).

Section ZMapAux.

  (* TODO: maybe not needed! *)
  (*
  #[global] Instance zmap_mapi_Proper
    {A B : Type}
    (pA: relation A)
    (pB: relation B)
    (f : ZMap.key -> A -> B)
    {Hf: Proper (eq ==> pA ==> pB) f}
    :
    Proper ((ZMap.Equiv pA) ==> (ZMap.Equiv pB)) (ZMap.mapi f).
  Proof.
  Admitted.
   *)

  (* Simple case *)
  #[global] Instance zmap_mapi_Proper_equal
    {A B : Type}
    (f : ZMap.key -> A -> B)
  :
  Proper ((ZMap.Equal) ==> (ZMap.Equal)) (ZMap.mapi f).
  Proof.
    intros a1 a2 H.
    unfold ZMap.Equal in *.
    intros k.
    specialize (H k).
    rewrite mapi_o.
    rewrite mapi_o.
    -
      unfold option_map.
      repeat break_match;invc H; reflexivity.
    -
      intros x y e HF;rewrite HF;reflexivity.
    -
      intros x y e HF;rewrite HF;reflexivity.
  Qed.

  Lemma In_m_Proper_Equiv
    (elt : Type)
    (R: relation elt)
    :
    Proper (eq ==> ZMap.Equiv R ==> iff) (ZMap.In (elt:=elt)).
  Proof.
    intros k1 k2 EE m1 m2 [ME1 _].
    subst. rename k2 into k.
    specialize (ME1 k).
    assumption.
  Qed.

  #[global] Instance zmap_Equiv_Reflexive
    (elt: Type)
    (R: relation elt)
    `{EE: Equivalence elt R}
    :
    Reflexive (ZMap.Equiv R).
  Proof.
    intros m.
    constructor.
    +
      intros k.
      split; auto.
    +
      intros k e e' H0 H1.
      auto.
      assert(E: e = e') by (eapply MapsTo_fun;eauto).
      rewrite E.
      reflexivity.
  Qed.

  #[global] Instance zmap_Equiv_Symmetric
    (elt: Type)
    (R: relation elt)
    `{EE: Equivalence elt R}
    :
    Symmetric (ZMap.Equiv R).
  Proof.
    intros a b [H1 H2].
    split.
    +
      intros k.
      specialize (H1 k).
      symmetry.
      apply H1.
    +
      intros k e e'.
      specialize (H2 k e' e).
      intros H H0.
      symmetry.
      apply H2;assumption.
  Qed.

  #[global] Instance zmap_Equiv_Transitive
    (elt: Type)
    (R: relation elt)
    `{EE: Equivalence elt R}
    :
    Transitive (ZMap.Equiv R).
  Proof.
    intros a b c.
    intros Eab Ebc.
    split.
    +
      destruct Eab as [H1 _], Ebc as [H3 _].
      intros k.
      specialize (H1 k).
      specialize (H3 k).
      split; intros HH.
      * apply H3, H1, HH.
      * apply H1, H3, HH.
    +
      destruct Eab as [H1 H2], Ebc as [H3 H4].
      intros k e1 e3.
      specialize (H1 k).
      specialize (H2 k).
      specialize (H3 k).
      specialize (H4 k).
      intros Ha Hc.

      destruct EE as [_ _ RT].
      unfold Transitive in RT.

      destruct (ZMap.find k b) eqn:Hb.
      *
        rename e into e2.
        apply ZMap.find_2 in Hb.
        specialize (H2 e1 e2 Ha Hb).
        eapply RT.
        eapply H2.
        eapply H4; assumption.
      *
        apply not_find_in_iff in Hb.
        destruct H1 as [H1 _].

        assert(ZMap.In (elt:=elt) k a) as HaI.
        {
          clear -Ha.
          apply in_find_iff.
          apply ZMap.find_1 in Ha.
          rewrite Ha.
          intros H.
          inv H.
        }

        contradict Hb.
        apply H1.
        apply HaI.
  Qed.

  #[global] Instance zmap_Equiv_Equivalence
    (elt: Type)
    (R: relation elt)
    `{H: Equivalence elt R}
    :
    Equivalence (ZMap.Equiv R).
  Proof.
    split;typeclasses eauto.
  Qed.

  #[global] Instance zmap_range_init_Proper:
    forall [elt : Type], Proper (eq ==> eq ==> eq ==> eq ==> ZMap.Equal ==> ZMap.Equal)
                           (zmap_range_init (T:=elt)).
  Proof.
    intros elt a1 a0 EA n0 n EN s0 s ES v0 v EV m0 m1 EM k.
    subst.
    dependent induction n.
    -
      cbn.
      apply EM.
    -
      cbn.
      apply IHn.
      apply F.add_m;auto.
  Qed.

  #[global] Instance zmap_add_Proper
    {elt : Type}
    (R: relation elt)
    :
    Proper ((eq) ==> R ==> (ZMap.Equiv R) ==> (ZMap.Equiv R)) (ZMap.add (elt:=elt)).
  Proof.
    intros k' k Ek e e' Ee m m' [Em1 Em2].
    subst.
    split.
    -
      intros k0.
      destruct (Z.eq_dec k k0); subst; split; intros H; apply add_in_iff.
      1,2: left; reflexivity.
      1,2: right; apply Em1; apply add_in_iff in H;
      destruct H; [congruence|assumption].
    -
      intros k0 e0 e'0 H H0.
      destruct (Z.eq_dec k k0).
      + (* k=k0 *)
        clear Em1.
        subst k0.
        apply add_mapsto_iff in H.
        apply add_mapsto_iff in H0.
        destruct H as [ [Hk He] | [Hk He]],
            H0 as [ [H0k H0e] | [H0k H0e]]; subst; try congruence.
      + (* k<>k0 *)
        apply ZMap.add_3 in H ; [|assumption].
        apply ZMap.add_3 in H0 ; [|assumption].
        apply Em2 with (k:=k0);assumption.
  Qed.

  #[global] Instance zmap_fold_proper
    {A elt : Type}
    (Ae: relation A)
    (Eelt: relation elt)
    :
    Proper (((eq) ==> Eelt ==> Ae ==> Ae) ==> ZMap.Equal ==> Ae ==> Ae) (@ZMap.fold elt A).
  Proof.
  Admitted.


End ZMapAux.

Section SimpleError.

  #[global] Instance serr_ret_proper {T R}:
  Proper (R ==> serr_eq R) ((@ret serr (Monad_either string) T)).
  Proof.
    intros x y E.
    unfold Monad_either, ret.
    unfold serr_eq.
    assumption.
  Qed.

  #[global] Instance serr_bind_proper {T:Type} {R: relation T}:
    Proper (serr_eq R ==> (R ==> serr_eq R) ==> serr_eq R) bind.
  Proof.

    intros x y Exy f f' Ef.
    unfold serr_eq in *.
    cbn.
    repeat break_match; try inl_inr;
      repeat inl_inr_inv; subst; try reflexivity; try tauto.

    -
      specialize (Ef t0 t Exy).
      cbn in Ef.
      repeat break_match_hyp; try inl_inr; repeat inl_inr_inv; subst;reflexivity.
    -
      specialize (Ef t1 t0 Exy).
      cbn in Ef.
      repeat break_match_hyp; try inl_inr; tauto.
    -
      specialize (Ef t1 t0 Exy).
      cbn in Ef.
      repeat break_match_hyp; try inl_inr; tauto.
    -
      specialize (Ef t2 t1 Exy).
      cbn in Ef.
      repeat break_match_hyp; try inl_inr; repeat inl_inr_inv; subst;auto.
  Qed.

End SimpleError.


#[global] Instance Monad_either_MonadLaws {T:Type}:
  MonadLaws (Monad_either T).
Proof.
  split; intros;  unfold Monad_either, ret, bind;
    repeat break_match;subst; try inl_inr_inv; try reflexivity; try inl_inr.
Qed.
