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

  Lemma list_init_rec_proper_aux :
    forall (A : Type) (Ae : relation A),
      Proper (eq ==> (eq ==> Ae) ==> eqlistA Ae ==> eqlistA Ae) (@list_init_rec A).
  Proof.
    intros A Ae. unfold Proper, respectful.
    intros i i' Hi f g Hfg acc acc' Hacc. subst i'.
    revert acc acc' Hacc.
    induction i as [|i IH]; intros acc acc' Hacc.
    - (* Base case *)
      simpl. assumption.
    - (* Inductive step *)
      simpl. apply IH.
      + constructor; [apply Hfg | assumption].
        reflexivity.
  Qed.

  #[global] Instance list_init_proper
    {A:Type}
    (Ae: relation A)
    :
    Proper (eq ==> (eq ==> (Ae)) ==> eqlistA Ae) list_init.
  Proof.
    intros x y Hxy f g Hfg.
    subst.
    unfold list_init.
    apply list_init_rec_proper_aux.
    - constructor.
    - assumption.
    - constructor.
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

  Definition zmap_forall_keys {A:Type} (pred: Z -> Prop) (m:ZMap.t A) : Prop
    :=
    forall k, ZMap.In k m -> pred k.

  (* A predicate that accepts two ZMaps `map1` and `map2` of
     potentially different value types `A` and `B`, and a relation
     `R`. It ensures that for every key in these ZMaps, `R` holds for
     the corresponding values if the key exists in both maps, or that
     the key does not exist in either map. *)
  Definition zmap_relate_keys {A B : Type} (map1: ZMap.t A) (map2: ZMap.t B)
    (R: ZMap.key -> A -> B -> Prop) : Prop :=
    forall k,
      (exists v1 v2, ZMap.MapsTo k v1 map1 /\ ZMap.MapsTo k v2 map2 /\ R k v1 v2)
      \/ ((~exists v, ZMap.MapsTo k v map1) /\ (~exists v, ZMap.MapsTo k v map2)).

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

  Lemma zmap_in_mapsto {T:Type} (k:ZMap.key) (m:ZMap.t T):
    ZMap.In k m -> (exists v, @ZMap.MapsTo T k v m).
  Proof.
    intros H.
    destruct H.
    exists x.
    unfold ZMap.MapsTo.
    apply H.
  Qed.

  Lemma zmap_in_mapsto' {T:Type} k (m: ZMap.t T):
    ZMap.In k m -> {v | @ZMap.MapsTo T k v m}.
  Proof.
    intros H.
    apply in_find_iff in H.
    destruct (ZMap.find k m) eqn:Hfind.
    - exists t. apply ZMap.find_2. assumption.
    - contradiction.
  Qed.

  Lemma zmap_MapsTo_dec
    {A:Type}
    {Adec: forall x y:A, {x = y} + {x <> y}}
    (k: ZMap.key)
    (v:A)
    (m: ZMap.t A)
    :
    {ZMap.MapsTo (elt:=A) k v m} + {~ ZMap.MapsTo (elt:=A) k v m}.
  Proof.
    destruct (ZMap.find (elt:=A) k m) eqn:H.
    - destruct (Adec v a).
      * left. apply ZMap.find_2 in H. subst. assumption.
      * right. intro Hcontra. apply ZMap.find_1 in Hcontra. congruence.
    - right. intro Hcontra. apply ZMap.find_1 in Hcontra. congruence.
  Qed.

  (* Simple case *)
  #[global] Instance zmap_mapi_Proper_equal
    {A B : Type}
  :
  Proper ((eq ==> eq ==> eq) ==>
      (ZMap.Equal) ==> (ZMap.Equal)) (@ZMap.mapi A B ).
  Proof.
    intros f1 f2 Ef a1 a2 H.
    unfold ZMap.Equal in *.
    intros k.
    specialize (H k).
    rewrite mapi_o.
    rewrite mapi_o.
    -
      unfold option_map.
      repeat break_match;invc H.
      f_equiv.
      apply Ef;reflexivity.
      reflexivity.
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
      simpl.
      apply EM.
    -
      simpl.
      repeat rewrite add_o.
      break_if.
      reflexivity.
      apply IHn.
      assumption.
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

  Lemma zmap_mapsto_in {T:Type} (k:ZMap.key) (m:ZMap.t T) (v:T):
    ZMap.MapsTo k v m -> ZMap.In k m.
  Proof.
    intros H.
    apply ZMap.find_1 in H.
    apply in_find_iff.
    rewrite H.
    congruence.
  Qed.

  Lemma zmap_relate_keys_same_keys {A B:Type} (m1:ZMap.t A) (m2:ZMap.t B) f:
      zmap_relate_keys m1 m2 f ->
      (forall k, ZMap.In k m1 <-> ZMap.In k m2).
  Proof.
    intros H k.
    unfold zmap_relate_keys in H.
    specialize (H k).
    split.
    -
      intros M.
      destruct H.
      +
        destruct H as [v1 [v2 [H1 [H2 H3]]]].
        apply zmap_mapsto_in in H2.
        apply H2.
      +
        destruct H.
        contradict H.
        apply zmap_in_mapsto in M.
        apply M.
    -
      intros M.
      destruct H.
      +
        destruct H as [v1 [v2 [H1 [H2 H3]]]].
        apply zmap_mapsto_in in H1.
        apply H1.
      +
        destruct H.
        contradict H0.
        apply zmap_in_mapsto in M.
        apply M.
  Qed.

  Lemma zmap_maps_to_elements_p
    {A: Type}
    `{Ae: Equivalence A (@eq A)}
    (P: A -> Prop)
    (mv: ZMap.t A)
    :
    (forall k v, ZMap.MapsTo k v mv -> P v) <-> (List.Forall (fun '(k,v) => P v) (ZMap.elements mv)).
  Proof.
    split.
    - intros HMapsTo.
      apply List.Forall_forall.
      intros (k, v) Hin.
      apply In_InA with (eqA:=(ZMap.eq_key_elt (elt:=A))) in Hin.
      apply WZP.elements_mapsto_iff in Hin.
      apply HMapsTo in Hin.
      assumption.
      typeclasses eauto.
    - intros HForall k v HMapsTo.
      apply WZP.elements_mapsto_iff in HMapsTo.
      apply List.Forall_forall with (x := (k, v)) in HForall.
      + apply HForall.
      +
        apply InA_alt in HMapsTo.
        destruct HMapsTo as [(k',v') [ [Ek Ev] HM]].
        cbn in Ek, Ev.
        subst.
        assumption.
  Qed.

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


Definition is_Some {A:Type} (x:option A) : Prop
  := match x with
     | Some _ => True
     | None => False
     end.

Definition is_None {A:Type} (x:option A) : Prop
  := match x with
     | Some _ => False
     | None => True
     end.
