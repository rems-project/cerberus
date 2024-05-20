From Coq.Strings Require Import String Ascii.
Require Import Coq.Arith.PeanoNat.
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

  Import ListNotations.

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

  #[global] Instance list_mapi_aux_Proper:
    forall (A B : Type) (pA: relation A) (pB: relation B),
      Proper (pointwise_relation nat (pA ==> pB) ==> eqlistA pB ==> eq ==> eqlistA pA ==> eqlistA pB) mapi_aux.
  Proof.
    intros A B pA pB f g Hfg acc acc' acc_eq n n' N l1 l2 Heql.
    subst n'.
    revert acc acc' acc_eq n.
    induction Heql as [| x y l1' l2' Hxy Heql' IH];intros.
    - simpl. (* Base case: both lists are empty *)
      apply rev_eqlistA_compat.
      assumption.
    - simpl.
      apply IH.
      constructor.
      + apply Hfg, Hxy.
      + apply acc_eq.
  Qed.

  #[global] Instance list_mapi_Proper
    {A B : Type}
    (pA: relation A)
    (pB: relation B)
    :
    Proper (pointwise_relation _ (pA ==> pB) ==> eqlistA pA ==> eqlistA pB)
      mapi.
  Proof.
    intros f g Hfg l1 l2 Heql.
    unfold mapi.
    eapply list_mapi_aux_Proper;eauto.
  Qed.

  #[global] Instance list_map_Proper
    {A B : Type}
    (pA: relation A)
    (pB: relation B)
    :
    Proper ((pA ==> pB) ==> eqlistA pA ==> eqlistA pB)
      (@List.map A B).
  Proof.
    intros f g Hfg l1 l2 Hl. induction Hl.
    - constructor.
    - simpl. constructor; [apply Hfg | apply IHHl]; assumption.
  Qed.

  #[global] Instance list_init_proper
    {A:Type}
    (Ae: relation A)
    :
    Proper (eq ==> (eq ==> (Ae)) ==> eqlistA Ae) list_init.
  Proof.
    intros n1 n2 Hn f1 f2 Hf.
    subst n2.  (* Since n1 = n2 *)
    unfold list_init.
    apply (list_map_Proper eq Ae).
    - intros x y Hxy. subst y. apply Hf. reflexivity.
    - reflexivity.
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



  Lemma list_init_len {A : Type} (n : nat) (f : nat -> A):
    List.length (list_init n f) = n.
  Proof.
    unfold list_init.
    rewrite map_length.
    apply seq_length.
  Qed.

  Lemma list_split_cons
    {A B: Type}:
    forall ab abss a0 ass b0 bs,
      split (A:=A) (B:=B) (ab::abss) = (a0 :: ass, b0 :: bs) ->
      ab = (a0,b0) /\ split abss = (ass, bs).
  Proof.
    intros ab abss a0 ass b0 bs H.
    simpl in H.
    destruct ab as [a b].
    break_let.
    tuple_inversion.
    split;reflexivity.
  Qed.

  Inductive split_spec {A B: Type}: (list (A * B)) -> (list A) -> (list B) -> Prop
    :=
  | split_nil: split_spec [] [] []
  | split_cons:
    forall a0 b0 lab la lb,
      split_spec lab la lb ->
      split_spec ((a0,b0)::lab) (a0::la) (b0::lb).

  Lemma list_split_spec:
    forall A B ab a b,
      split (A:=A) (B:=B) ab = (a,b) -> split_spec ab a b.
  Proof.
    intros A B ab a b H.

    revert a b H.
    induction ab; intros.
    -
      destruct a, b; cbn in *; repeat break_let; try tuple_inversion.
      constructor.
    -
      destruct a, b; cbn in *; repeat break_let; try tuple_inversion.
      constructor.
      apply IHab.
      reflexivity.
  Qed.


  Lemma split_eq_key_InA
    {A : Type}
    (l : list (Z * A))
    (la : list Z)
    (lb : list A)
    (a0 : Z)
    (b0: A)
    :
    split_spec l la lb -> (In a0 la <-> InA (ZMap.eq_key (elt:=A)) (a0, b0) l).
  Proof.
    intros S.
    split.
    -
      intros N.
      revert S N.
      revert la lb a0.
      dependent induction l;intros.
      +
        invc S.
        inv N.
      +
        invc S.
        invc N.
        *
          constructor.
          reflexivity.
        *
          apply InA_cons_tl.
          eapply IHl;eauto.
    -
      intros N.
      revert S N.
      revert la lb a0 b0.
      dependent induction l;intros.
      +
        invc S.
        inv N.
      +
        invc S.
        invc N.
        *
          constructor.
          invc H0.
          cbn in H.
          auto.
        *
          cbn.
          right.
          eapply IHl;eauto.
  Qed.

  Lemma split_eq_key_elt_InA
    {A : Type}
    (l : list (Z * A))
    (la : list Z)
    (lb : list A)
    (a0 : Z):
    split_spec l la lb -> (In a0 la <-> (exists b0, InA (ZMap.eq_key_elt (elt:=A)) (a0, b0) l)).
  Proof.
    intros S.
    split.
    -
      intros N.
      revert S N.
      revert la lb a0.
      dependent induction l;intros.
      +
        invc S.
        inv N.
      +
        invc S.
        invc N.
        *
          eexists.
          constructor.
          reflexivity.
        *
          specialize (IHl la0 lb0 a0 H3 H).
          destruct IHl as [b1 IHl].
          exists b1.
          apply InA_cons_tl.
          apply IHl.
    -
      intros N.
      destruct N as [b0 N].
      revert S N.
      revert la lb a0 b0.
      dependent induction l;intros.
      +
        invc S.
        inv N.
      +
        invc S.
        invc N.
        *
          constructor.
          invc H0.
          cbn in H.
          auto.
        *
          cbn.
          right.
          eapply IHl;eauto.
  Qed.

  Lemma nth_error_nil
    {A:Type}:
    forall k,
      nth_error (@nil A) k = None.
  Proof.
    intros.
    destruct k;reflexivity.
  Qed.

  (* Could be extended to go both ways *)
  Lemma split_eq_key_elt_nth
    {A : Type}
    (l : list (Z * A))
    (la : list Z)
    (lb : list A)
    (a0 : Z)
    (b0: A)
    (k: nat)
    :
    split_spec l la lb
    -> nth_error la k = Some a0
    -> nth_error lb k = Some b0
    -> nth_error l k = Some (a0, b0).
  Proof.
    intros S NK NV.

    revert S NK NV.
    revert la lb a0 b0 k.
    induction l; intros.
    -
      invc S.
      rewrite nth_error_nil in NK.
      inversion NK.
    -
      invc S.
      destruct k.
      +
        cbn in NK, NV.
        invc NK.
        invc NV.
        reflexivity.
      +
        cbn in NK, NV.
        cbn.
        eapply IHl;eauto.
  Qed.


  (* Strictly speakigg this follows from [split_eq_key_InA] but it was proven earlier *)
  Lemma split_eq_key_not_InA
    {A : Type}
    (l : list (Z * A))
    (la : list Z)
    (b0 : A)
    (lb : list A)
    (a0 : Z):
    split_spec l la lb -> ~ InA (ZMap.eq_key (elt:=A)) (a0, b0) l -> ~ In a0 la.
  Proof.
    intros S N.
    revert S N.
    revert la lb a0 b0.
    dependent induction l;intros.
    -
      invc S.
      auto.
    -
      intros C.
      invc S.
      invc C.
      +
        clear -N.
        contradict N.
        constructor.
        reflexivity.
      +
        eapply IHl;eauto.
  Qed.

  Lemma split_eq_key_NoDup
    {A:Type}
    (l: list (Z*A))
    (lk : list Z)
    (lv: list A):
    split l = (lk, lv) ->
    NoDupA (ZMap.eq_key (elt:=A)) l -> NoDup lk.
  Proof.

    (* unfold ZMap.eq_key, ZMap.Raw.Proofs.PX.eqk. *)
    intros S.
    apply list_split_spec in S.
    revert lk lv S.
    dependent induction l; intros.
    -
      invc S.
      constructor.
    -
      invcs S.
      specialize (IHl la lb H4).
      constructor.
      +
        invc H.
        eapply split_eq_key_not_InA; eauto.
      +
        apply IHl.
        invc H.
        assumption.
  Qed.

  Lemma combine_spec:
    forall A B ab a b,
      length a = length b ->
      combine (A:=A) (B:=B) a b = ab -> split_spec ab a b.
  Proof.
    intros A B ab a b L C.

    revert a b L C.
    induction ab; intros.
    -
      destruct a, b; cbn in *; repeat break_let; try tuple_inversion; try inv L.
      constructor.
      inv C.
    -
      destruct a0, b; cbn in *; repeat break_let; try tuple_inversion;
        try inv C.
      constructor.
      apply IHab.
      auto.
      reflexivity.
  Qed.

  Lemma combine_eq_key_NoDupA
    {A:Type}
    (lk : list ZMap.key)
    (lv : list A):
    NoDup lk -> NoDupA (ZMap.eq_key (elt:=A)) (combine lk lv).
  Proof.
    intros H.
    revert lv.
    induction H; intros.
    -
      cbn.
      constructor.
    -
      cbn.
      destruct lv.
      +
        cbn.
        constructor.
      +
        constructor.
        *
          clear -H.
          intros C.
          unfold ZMap.eq_key, ZMap.Raw.Proofs.PX.eqk in C.
          apply InA_alt in C.
          destruct C as [y [C1 C2]].
          destruct y.
          cbn in C1.
          subst x.
          apply in_combine_l in C2.
          congruence.
        *
          apply IHNoDup.
  Qed.

  Lemma combine_eq_key_elt_NoDupA
    {A:Type}
    (lk : list ZMap.key)
    (lv : list A):
    NoDup lk -> NoDupA (ZMap.eq_key_elt (elt:=A)) (combine lk lv).
  Proof.
    intros H.
    revert lv.
    induction H; intros.
    -
      cbn.
      constructor.
    -
      cbn.
      destruct lv.
      +
        cbn.
        constructor.
      +
        constructor.
        *
          clear -H.
          intros C.
          unfold ZMap.eq_key, ZMap.Raw.Proofs.PX.eqk in C.
          apply InA_alt in C.
          destruct C as [y [C1 C2]].
          destruct y.
          cbv in C1.
          destruct C1.
          subst.
          apply in_combine_l in C2.
          congruence.
        *
          apply IHNoDup.
  Qed.


  (* In standard library [Forall2_nth] is defined only for [Vector]. This is missing version for list *)
  Lemma Forall2_nth_list :
    forall (A B : Type) (R : A -> B -> Prop) (l1 : list A) (l2 : list B) (default1 : A) (default2 : B),
      length l1 = length l2 ->
      (forall i, i < length l1 -> R (nth i l1 default1) (nth i l2 default2))%nat ->
      Forall2 R l1 l2.
  Proof.
    intros A B R l1 l2 default1 default2 Hlen Hnth.
    generalize dependent l2.
    induction l1 as [| x1 l1' IHl1'].
    - intros l2 Hlen. destruct l2 as [| x2 l2'].
      * constructor.
      * inv Hlen.
    - intros l2 Hlen. destruct l2 as [| x2 l2']; try easy.
      simpl in Hlen. injection Hlen as Hlen'.
      constructor.
      + apply (Hnth O). simpl. lia.
      + eapply IHl1'.
        * assumption.
        * intros i.
          specialize (Hnth (S i)).
          intros L.
          apply Hnth.
          cbn.
          lia.
  Qed.

  Lemma skipn_cons_nth_error
    {A:Type}
    (a : A) (l l' : list A)
    (n : nat):
    skipn n l = a :: l' -> nth_error l n = Some a.
  Proof.
    revert l.
    induction n as [|n IH]; intros l H.
    -
      rewrite skipn_O in H.
      rewrite H.
      reflexivity.
    -
      destruct l as [|b l''].
      + simpl in H. discriminate H.
      + simpl in H. apply IH in H. cbn. assumption.
  Qed.

  Lemma list_init_nth {A : Type} (n : nat) (f : nat -> A) :
    forall i, (i<n)%nat -> nth_error (list_init n f) i = Some (f i).
  Proof.
    intros i H.
    unfold list_init.
    apply map_nth_error.
    remember (seq 0 n) as s.
    pose proof (seq_length n 0).
    replace i with (nth i s O) at 2.
    apply nth_error_nth'.
    subst s.
    lia.
    replace i with (0+i)%nat at 2 by lia.
    subst s.
    apply seq_nth.
    assumption.
  Qed.


End ListAux.

Module Import ZP := FMapFacts.WProperties_fun(Z_as_OT)(ZMap).
Module Import WZP := FMapFacts.WFacts_fun(Z_as_OT)(ZMap).

Section ZMapAux.

  Definition zmap_Mem {A:Type} (x:A) (m:ZMap.t A) : Prop
    :=
    forall k, ZMap.MapsTo k x m.

  Definition zmap_forall {A:Type} (pred: A -> Prop) (m:ZMap.t A) : Prop
    :=
    forall k v, ZMap.MapsTo k v m -> pred v.


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

  Lemma zmap_forall_elements_split
    (A : Type)
    (mv : ZMap.t A)
    (P: A -> Prop)
    :
    zmap_forall P mv <-> Forall (fun '(_, v) => P v) (ZMap.elements mv).
  Proof.
    unfold zmap_forall.
    split.
    -
      intros H.
      apply zmap_maps_to_elements_p.
      assumption.
    -
      intros H.
      eapply zmap_maps_to_elements_p.
      assumption.
  Qed.

  Lemma zmap_forall_Forall_elements
    {A : Type}
    (mv : ZMap.t A)
    (P: A -> Prop)
    :
    zmap_forall P mv ->
    forall (lk : list ZMap.key) (lv : list A),
      split (ZMap.elements mv) = (lk, lv) -> Forall P lv.
  Proof.
    intros H lk lv S.
    replace lv with (snd (lk,lv));[|auto].
    rewrite <- S.
    clear S lk.
    apply zmap_forall_elements_split in H.
    generalize dependent (ZMap.elements (elt:=A) mv).
    intros e.
    intros H.
    apply Forall_nth.
    intros k x K.
    pose proof (split_nth e k (Z.of_nat k, x)) as S.
    rewrite Forall_nth in H.
    specialize (H k (Z.of_nat k,x)).
    autospecialize H.
    {
      rewrite split_length_r in K.
      apply K.
    }
    rewrite S in H. clear S.
    cbn in H.
    apply H.
  Qed.

  Lemma InA_eq_key_combine
    {A:Type}
    (lk : list ZMap.key)
    (lv : list A):
    forall k v,
      InA (ZMap.eq_key_elt (elt:=A)) (k, v) (combine lk lv) -> In k lk.
  Proof.
    intros k v H.
    remember (combine lk lv) as e.
    eapply in_combine_l with (l':=lv) (y:=v).
    rewrite <- Heqe.
    apply InA_alt in H.
    destruct H as [kv [H1 H2]].
    unfold ZMap.eq_key_elt, ZMap.Raw.Proofs.PX.eqke in H1.
    destruct kv.
    cbn in H1.
    destruct H1.
    subst k0 a.
    apply H2.
  Qed.

  Lemma In_zmap_elements_split_zmap_in
    {A:Type}
    (m : ZMap.t A) (k : ZMap.key):
    In k (fst (split (ZMap.elements (elt:=A) m))) ->
    ZMap.In (elt:=A) k m.
  Proof.
    intros H.
    remember (ZMap.elements (elt:=A) m) as e.
    remember (split e) as p.
    destruct p as [lk lv].
    cbn in H.
    symmetry in Heqp.
    apply list_split_spec in Heqp.

    apply elements_in_iff.
    apply split_eq_key_elt_InA with (a0:=k) in Heqp.
    apply Heqp in H. clear Heqp.
    destruct H as [v H].
    subst e.
    exists v.
    apply H.
  Qed.

  Lemma elements_to_list
    {A:Type}:
    forall (m:ZMap.t A),
      ZMap.ZP.to_list m = ZMap.elements m.
  Proof.
    intros m.
    reflexivity.
  Qed.

  Lemma zmap_range_init_spec
    {T:Type}
    (a0:Z)
    (n:nat)
    (step:Z)
    (v:T)
    (m:ZMap.t T):
    forall k x,
      ZMap.MapsTo k x (zmap_range_init a0 n step v m)
      ->
        {
          ~(exists i, (i<n)%nat /\ Z.add a0 (Z.mul (Z.of_nat i) step) = k)
          /\ ZMap.MapsTo k x m
        }+
          {
            (exists i, (i<n)%nat /\ Z.add a0 (Z.mul (Z.of_nat i) step) = k)
            /\
              x=v
          }.
  Proof.
    dependent induction n.
    -
      left.
      split.
      +
        intros C.
        destruct C as [i [C _]].
        lia.
      +
        cbn in H.
        assumption.
    -
      simpl. intros k x Hmap.
      destruct (Z.eq_dec (a0 + Z.of_nat n * step) k) as [E|NE].
      + (* Case: k is the newly added key *)
        right. split. exists n. split; lia.
        apply add_mapsto_iff in Hmap.
        destruct Hmap as [[H1 H2] | [H3 H4]];[auto|congruence].
      + (* Case: k is not the newly added key, apply IH *)
        apply add_mapsto_iff in Hmap.
        specialize (IHn step v m k x).
        autospecialize IHn.
        {
          destruct Hmap as [[H1 H2] | [H3 H4]];[congruence|auto].
        }
        destruct IHn as [[Hni Hm]|[Hi Hv]].
        * left. split; auto.
          intro H.
          apply Hni. destruct H as [i [Hlt Heq]].
          exists i. split.
          --
            destruct Hmap.
            ++
              destruct H.
              congruence.
            ++
              destruct H.
              assert(i<>n) by lia.
              lia.
          --
            auto.
        * right. destruct Hi as [i [Hlt Heq]].
          split.
          exists i. split; [lia|]. assumption.
          auto.
  Qed.

  Lemma zmap_update_MapsTo_not_at_k
    {A: Type}
    (old: ZMap.t A)
    (f: option A -> option A)
    (v: A)
    (k k': Z)
    :
    k<>k' ->
    ZMap.MapsTo k v (zmap_update k' f old) <-> ZMap.MapsTo k v old.
  Proof.
    intros K.
    unfold zmap_update.
    split.
    -
      break_match; intros H.
      + apply add_neq_mapsto_iff, remove_neq_mapsto_iff in H; auto.
      + apply remove_neq_mapsto_iff in H; auto.
    -
      break_match; intros H.
      + apply add_neq_mapsto_iff, remove_neq_mapsto_iff;auto.
      + apply remove_neq_mapsto_iff; auto.
  Qed.

  Lemma zmap_update_MapsTo_update_at_k
    {A: Type}
    {m: ZMap.t A}
    {f: option A -> option A}
    {v v': A}
    {k: Z}
    :
    ZMap.MapsTo k v m ->
    ZMap.MapsTo k v' (zmap_update k f m) ->
    f (Some v) = Some v'.
  Proof.
    intros M U.
    unfold zmap_update in U.
    apply ZMap.find_1 in M.
    rewrite M in U.
    clear M.
    destruct (f (Some v)).
    -
      apply F.add_mapsto_iff in U.
      destruct U;destruct H.
      +
        subst.
        reflexivity.
      +
        congruence.
    -
      apply remove_mapsto_iff in U.
      destruct U.
      congruence.
  Qed.

  Lemma zmap_update_MapsTo_update_at_k'
    {A: Type}
    {m: ZMap.t A}
    {f: option A -> option A}
    {v v': A}
    {k: Z}
    :
    ZMap.MapsTo k v m ->
    f (Some v) = Some v' ->
    ZMap.MapsTo k v' (zmap_update k f m).
  Proof.
    intros M U.
    unfold zmap_update.
    apply ZMap.find_1 in M.
    rewrite M.
    clear M.
    destruct (f (Some v)).
    -
      invc U.
      apply ZMap.add_1.
      reflexivity.
    -
      congruence.
  Qed.

  Lemma zmap_update_MapsTo_new_at_k
    {A: Type}
    {m: ZMap.t A}
    {f: option A -> option A}
    {v': A}
    {k: Z}
    :
    ~ ZMap.In k m ->
    ZMap.MapsTo k v' (zmap_update k f m) ->
    f None = Some v'.
  Proof.
    intros M U.
    unfold zmap_update in U.
    apply not_find_in_iff in M.
    rewrite M in U.
    clear M.
    destruct (f None).
    -
      apply F.add_mapsto_iff in U.
      destruct U;destruct H.
      +
        subst.
        reflexivity.
      +
        congruence.
    -
      apply remove_mapsto_iff in U.
      destruct U.
      congruence.
  Qed.

  Lemma zmap_find_first_exists
    {A:Type}
    (f:ZMap.key -> A -> bool)
    (m:ZMap.t A)
    (k:ZMap.key)
    (v:A)
    :
    zmap_find_first f m = Some (k,v)
    ->
      ZMap.find k m = Some v /\ f k v = true.
  Proof.
    unfold zmap_find_first.
    intros H.
    revert H.

    apply fold_rec_weak; intros.
    -
      apply H0 in H1. clear H0.
      symmetry in H.
      destruct H1 as [H2 H3].
      split.
      +
        rewrite H.
        assumption.
      +
        assumption.
    -
      discriminate.
    -
      break_match_hyp.
      +
        apply H0 in H1. clear H0.
        destruct H1 as [H2 H3].
        subst.
        destruct (Z.eq_dec k k0) as [E|NE].
        *
          exfalso.
          subst k0.
          contradict H.
          apply in_find_iff.
          rewrite H2.
          discriminate.
        *
          split.
          rewrite add_neq_o;auto.
          assumption.
      +
        break_match_hyp;[|discriminate].
        clear H0.
        invc H1.
        split.
        *
          rewrite add_eq_o;auto.
        *
          assumption.
  Qed.

  Lemma zmap_find_first_matches
    {A:Type}
    (f:ZMap.key -> A -> bool)
    (m:ZMap.t A)
    (k:ZMap.key)
    (v:A)
    :
    zmap_find_first f m = Some (k,v)
    -> f k v = true.
  Proof.
    unfold zmap_find_first.

    apply fold_rec_weak; intros.
    -
      auto.
    -
      discriminate.
    -
      break_match_hyp.
      +
        auto.
      +
        break_match_hyp;[|discriminate].
        clear H0.
        invc H1.
        auto.
  Qed.

  Lemma zmap_forall_remove {A:Type} (pred: A -> Prop) (m:ZMap.t A) :
    forall k, zmap_forall pred m ->
         zmap_forall pred (ZMap.remove k m).
  Proof.
    intros k' H k v M.
    specialize (H k v).
    destruct (Z.eq_dec k' k) as [E|NE].
    *
      apply zmap_mapsto_in in M.
      apply (ZMap.remove_1 E) in M.
      inversion M.
    *
      apply ZMap.remove_3 in M.
      auto.
  Qed.

  Lemma zmap_forall_keys_remove {A:Type} (pred: Z -> Prop) (m:ZMap.t A):
    forall k, zmap_forall_keys pred m ->
         zmap_forall_keys pred (ZMap.remove k m).
  Proof.
    intros k' H k M.
    specialize (H k).
    destruct (Z.eq_dec k' k) as [E|NE].
    -
      subst k'.
      apply remove_in_iff in M.
      lia.
    -
      rewrite (remove_neq_in_iff _ NE) in M.
      auto.
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

Lemma Z_of_bytes_bytes_of_Z:
  forall (a : ascii) (z : Z), Z_of_bytes false (cons a nil) = inr z -> byte_of_Z z = a.
Proof.
  intros a z H.
  cbn in H.
  break_match_hyp; try discriminate.
  break_match_hyp; invc Heqs; invc H.
  -
    unfold byte_of_Z.
    assert (nat_of_ascii a = O) as H by lia.
    clear Heqz1.
    rewrite <- (ascii_nat_embedding a).
    rewrite <- (ascii_nat_embedding zero).
    auto.
  -
    unfold byte_of_Z.
    assert (nat_of_ascii a = Pos.to_nat p) as H by lia.
    clear Heqz1.
    rewrite <- (ascii_nat_embedding a).
    rewrite H. clear H.
    unfold ascii_of_nat.
    rewrite Znat.positive_nat_N.
    unfold ascii_of_N.
    reflexivity.
  -
    exfalso.
    lia.
Qed.


Section Z_arith.
  Local Open Scope Z_scope.

  Lemma sign_nonneg:
    forall x, (sign x >=? 0) = true -> x>=0.
  Proof.
    intros x H.
    unfold sign in H.
    destruct x;lia.
  Qed.

  Lemma sign_neg:
    forall x, (sign x >=? 0) = false -> x<0.
  Proof.
    intros x H.
    unfold sign in H.
    destruct x;lia.
  Qed.

  Lemma quotrem_pos:
    forall a b,
      0<=a ->
      0<=b ->
      let (q, r) := Z.quotrem a b in
      0<=q /\ 0<=r.
  Proof.
    intros a b H H0.
    break_let.
    rename z into q, z0 into r.
    split.
    -
      unfold Z.quotrem in Heqp.
      destruct a,b; try tuple_inversion; try lia.
      break_let.
      tuple_inversion.
      lia.
    -
      unfold Z.quotrem in Heqp.
      destruct a,b; try tuple_inversion; try lia.
      break_let.
      tuple_inversion.
      lia.
  Qed.

End Z_arith.
