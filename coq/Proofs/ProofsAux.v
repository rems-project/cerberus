Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Program.Equality. (* for dep. destruction *)
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.

Require Import StructTact.StructTactics.


From ExtLib.Data Require Import List.

Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

Require Import Lia.

Require Import Common.SimpleError.
Require Import Common.Utils.
Require Import Common.ZMap.

Require Import Tactics.

Module Import ZP := FMapFacts.WProperties_fun(Z_as_OT)(ZMap).
Module Import WZP := FMapFacts.WFacts_fun(Z_as_OT)(ZMap).

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

(* TODO: move elsewhere *)
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

(* TODO: move elsewhere *)
(* TODO: maybe not needed! *)
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

(* Now we can prove that mapi is Proper with respect to eqlistA. *)
(* TODO: move to Utils.v *)
#[global] Lemma list_mapi_Proper
  {A B : Type}
  (f : nat -> A -> B)
  (pA: relation A)
  (pB: relation B)
  {Hf: Proper (eq ==> pA ==> pB) f}:
  Proper (eqlistA pA ==> eqlistA pB) (mapi f).
Proof.
Admitted.

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

