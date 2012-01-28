(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Constructions of semi-lattices. *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Import Coqlib.
Require Import Maps.
Require Import FSets.
Require Import Metatheory.

(** * Signatures of semi-lattices *)

(** A semi-lattice is a type [t] equipped with an equivalence relation [eq],
  a boolean equivalence test [beq], a partial order [ge], a smallest element 
  [bot], and an upper bound operation [lub].
  Note that we do not demand that [lub] computes the least upper bound. *)

Module Type SEMILATTICE.

  Variable t: Type.
  Variable eq: t -> t -> Prop.
  Hypothesis eq_refl: forall x, eq x x.
  Hypothesis eq_sym: forall x y, eq x y -> eq y x.
  Hypothesis eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Variable beq: t -> t -> bool.
  Hypothesis beq_correct: forall x y, beq x y = true -> eq x y.
  Variable ge: t -> t -> Prop.
  Hypothesis ge_refl: forall x y, eq x y -> ge x y.
  Hypothesis ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Hypothesis ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Variable bot: t.
  Hypothesis ge_bot: forall x, ge x bot.
  Variable lub: t -> t -> t.
  Hypothesis lub_commut: forall x y, eq (lub x y) (lub y x).
  Hypothesis ge_lub_left: forall x y, ge (lub x y) x.

End SEMILATTICE.

(** A semi-lattice ``with top'' is similar, but also has a greatest
  element [top]. *)

Module Type SEMILATTICE_WITH_TOP.

  Include Type SEMILATTICE.
  Variable top: t.
  Hypothesis ge_top: forall x, ge top x.

End SEMILATTICE_WITH_TOP.

(** * Semi-lattice over maps *)

(** Given a semi-lattice with top [L], the following functor implements
  a semi-lattice structure over finite maps from positive numbers to [L.t].
  The default value for these maps is either [L.top] or [L.bot]. *)

Module LPMap(L: SEMILATTICE_WITH_TOP) <: SEMILATTICE_WITH_TOP.

Inductive t_ : Type :=
  | Bot_except: ATree.t L.t -> t_
  | Top_except: ATree.t L.t -> t_.

Definition t: Type := t_.

Definition get (p: atom) (x: t) : L.t :=
  match x with
  | Bot_except m =>
      match m!p with None => L.bot | Some x => x end
  | Top_except m =>
      match m!p with None => L.top | Some x => x end
  end.

Definition set (p: atom) (v: L.t) (x: t) : t :=
  match x with
  | Bot_except m =>
      Bot_except (if L.beq v L.bot then ATree.remove p m else ATree.set p v m)
  | Top_except m =>
      Top_except (if L.beq v L.top then ATree.remove p m else ATree.set p v m)
  end.

Lemma gss:
  forall p v x,
  L.eq (get p (set p v x)) v.
Proof.
  intros. destruct x; simpl. 
  case_eq (L.beq v L.bot); intros.
  rewrite ATree.grs. apply L.eq_sym. apply L.beq_correct; auto. 
  rewrite ATree.gss. apply L.eq_refl.
  case_eq (L.beq v L.top); intros.
  rewrite ATree.grs. apply L.eq_sym. apply L.beq_correct; auto. 
  rewrite ATree.gss. apply L.eq_refl.
Qed.

Lemma gso:
  forall p q v x,
  p <> q -> get p (set q v x) = get p x.
Proof.
  intros. destruct x; simpl.
  destruct (L.beq v L.bot). rewrite ATree.gro; auto. rewrite ATree.gso; auto.
  destruct (L.beq v L.top). rewrite ATree.gro; auto. rewrite ATree.gso; auto.
Qed.

Definition eq (x y: t) : Prop :=
  forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof.
  unfold eq; intros. apply L.eq_refl.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq; intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq; intros. eapply L.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot_except m, Bot_except n => ATree.beq L.beq m n
  | Top_except m, Top_except n => ATree.beq L.beq m n
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  destruct x; destruct y; simpl; intro; try congruence.
  red; intro; simpl.
  generalize (@ATree.beq_correct _ L.eq L.beq L.beq_correct t0 t1 H p).
  destruct (t0!p); destruct (t1!p); intuition. apply L.eq_refl.
  red; intro; simpl.
  generalize (@ATree.beq_correct _ L.eq L.beq L.beq_correct t0 t1 H p).
  destruct (t0!p); destruct (t1!p); intuition. apply L.eq_refl.
Qed.

Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
Proof.
  unfold eq,ge; intros. eapply L.ge_compat; eauto.
Qed.

Definition bot := Bot_except (ATree.empty L.t).

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  unfold bot; intros; simpl. rewrite ATree.gempty. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.

Definition top := Top_except (ATree.empty L.t).

Lemma get_top: forall p, get p top = L.top.
Proof.
  unfold top; intros; simpl. rewrite ATree.gempty. auto.
Qed.

Lemma ge_top: forall x, ge top x.
Proof.
  unfold ge; intros. rewrite get_top. apply L.ge_top.
Qed.

Definition opt_lub (x y: L.t) : option L.t :=
  let z := L.lub x y in
  if L.beq z L.top then None else Some z.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot_except m, Bot_except n =>
      Bot_except
        (ATree.combine 
           (fun a b =>
              match a, b with
              | Some u, Some v => Some (L.lub u v)
              | None, _ => b
              | _, None => a
              end)
           m n)
  | Bot_except m, Top_except n =>
      Top_except
        (ATree.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | None, _ => b
              | _, None => None
              end)
        m n)             
  | Top_except m, Bot_except n =>
      Top_except
        (ATree.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | None, _ => None
              | _, None => a
              end)
        m n)             
  | Top_except m, Top_except n =>
      Top_except
        (ATree.combine 
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | _, _ => None
              end)
           m n)
  end.

Lemma lub_commut:
  forall x y, eq (lub x y) (lub y x).
Proof.
  intros x y p.
  assert (forall u v,
    L.eq (match opt_lub u v with
          | Some x => x
          | None => L.top end)
         (match opt_lub v u with
         | Some x => x
         | None => L.top
         end)).
  intros. unfold opt_lub. 
  case_eq (L.beq (L.lub u v) L.top);
  case_eq (L.beq (L.lub v u) L.top); intros.
  apply L.eq_refl.
  eapply L.eq_trans. apply L.eq_sym. apply L.beq_correct; eauto. apply L.lub_commut.
  eapply L.eq_trans. apply L.lub_commut. apply L.beq_correct; auto.
  apply L.lub_commut.
  destruct x; destruct y; simpl;
  repeat rewrite ATree.gcombine; auto;
  destruct t0!p; destruct t1!p;
  auto; apply L.eq_refl || apply L.lub_commut.
Qed.

Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  assert (forall u v,
    L.ge (match opt_lub u v with Some x => x | None => L.top end) u).
  intros; unfold opt_lub. 
  case_eq (L.beq (L.lub u v) L.top); intros. apply L.ge_top. apply L.ge_lub_left.

  unfold ge, get, lub; intros; destruct x; destruct y.

  rewrite ATree.gcombine; auto.
  destruct t0!p; destruct t1!p.
  apply L.ge_lub_left.
  apply L.ge_refl. apply L.eq_refl. 
  apply L.ge_bot.
  apply L.ge_refl. apply L.eq_refl.

  rewrite ATree.gcombine; auto.
  destruct t0!p; destruct t1!p.
  auto.
  apply L.ge_top.
  apply L.ge_bot.
  apply L.ge_top.

  rewrite ATree.gcombine; auto.
  destruct t0!p; destruct t1!p.
  auto.
  apply L.ge_refl. apply L.eq_refl.
  apply L.ge_top.
  apply L.ge_top.

  rewrite ATree.gcombine; auto.
  destruct t0!p; destruct t1!p.
  auto.
  apply L.ge_top.
  apply L.ge_top.
  apply L.ge_top.
Qed.

End LPMap.

(** * Semi-lattice over a set. *)

(** Given a set [S: FSetInterface.S], the following functor
    implements a semi-lattice over these sets, ordered by inclusion. *)

Module LFSet (S: FSetInterface.S) <: SEMILATTICE.

  Definition t := S.t.

  Definition eq (x y: t) := S.Equal x y.
  Definition eq_refl: forall x, eq x x := S.eq_refl.
  Definition eq_sym: forall x y, eq x y -> eq y x := S.eq_sym.
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := S.eq_trans.
  Definition beq: t -> t -> bool := S.equal.
  Definition beq_correct: forall x y, beq x y = true -> eq x y := S.equal_2.

  Definition ge (x y: t) := S.Subset y x.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge, S.Equal, S.Subset; intros. firstorder. 
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge, S.Subset; intros. eauto.
  Qed.
  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold ge, eq, S.Subset, S.Equal; intros. firstorder.
  Qed.

  Definition  bot: t := S.empty.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot, S.Subset; intros. elim (S.empty_1 H).
  Qed.

  Definition lub: t -> t -> t := S.union.
  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq, S.Equal; intros. split; intro.
    destruct (S.union_1 H). apply S.union_3; auto. apply S.union_2; auto.
    destruct (S.union_1 H). apply S.union_3; auto. apply S.union_2; auto.
  Qed.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub, ge, S.Subset; intros. apply S.union_2; auto. 
  Qed.

End LFSet.

(** * Flat semi-lattice *)

(** Given a type with decidable equality [X], the following functor
  returns a semi-lattice structure over [X.t] complemented with
  a top and a bottom element.  The ordering is the flat ordering
  [Bot < Inj x < Top]. *) 

Module LFlat(X: EQUALITY_TYPE) <: SEMILATTICE_WITH_TOP.

Inductive t_ : Type :=
  | Bot: t_
  | Inj: X.t -> t_
  | Top: t_.

Definition t : Type := t_.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@refl_equal t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot, Bot => true
  | Inj u, Inj v => if X.eq u v then true else false
  | Top, Top => true
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold eq; destruct x; destruct y; simpl; try congruence; intro.
  destruct (X.eq t0 t1); congruence.
Qed.

Definition ge (x y: t) : Prop :=
  match x, y with
  | Top, _ => True
  | _, Bot => True
  | Inj a, Inj b => a = b
  | _, _ => False
  end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold eq, ge; intros; subst y; destruct x; auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; destruct x; destruct y; try destruct z; intuition.
  transitivity t1; auto.
Qed.

Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
Proof.
  unfold eq; intros; congruence.
Qed.

Definition bot: t := Bot.

Lemma ge_bot: forall x, ge x bot.
Proof.
  destruct x; simpl; auto.
Qed.

Definition top: t := Top.

Lemma ge_top: forall x, ge top x.
Proof.
  destruct x; simpl; auto.
Qed.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot, _ => y
  | _, Bot => x
  | Top, _ => Top
  | _, Top => Top
  | Inj a, Inj b => if X.eq a b then Inj a else Top
  end.

Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
Proof.
  unfold eq; destruct x; destruct y; simpl; auto.
  case (X.eq t0 t1); case (X.eq t1 t0); intros; congruence.
Qed.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  destruct x; destruct y; simpl; auto.
  case (X.eq t0 t1); simpl; auto.
Qed.

End LFlat.
  
(** * Boolean semi-lattice *)

(** This semi-lattice has only two elements, [bot] and [top], trivially
  ordered. *)

Module LBoolean <: SEMILATTICE_WITH_TOP.

Definition t := bool.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@refl_equal t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).

Definition beq : t -> t -> bool := eqb.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof eqb_prop.

Definition ge (x y: t) : Prop := x = y \/ x = true.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. unfold ge; tauto. Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. unfold ge; intuition congruence. Qed.

Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
Proof.
  unfold eq; intros; congruence.
Qed.

Definition bot := false.

Lemma ge_bot: forall x, ge x bot.
Proof. destruct x; compute; tauto. Qed.

Definition top := true.

Lemma ge_top: forall x, ge top x.
Proof. unfold ge, top; tauto. Qed.

Definition lub (x y: t) := x || y.

Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
Proof. intros; unfold eq, lub. apply orb_comm. Qed.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. destruct x; destruct y; compute; tauto. Qed.

End LBoolean.

Require Import ListSet.

Module AtomSet.

  Definition set_eq A (l1 l2:list A) := incl l1 l2 /\ incl l2 l1.

  Definition incl_dec_prop (n:nat) :=
    forall (l1 l2:list atom), length l1 = n -> {incl l1 l2} + {~ incl l1 l2}.

  Lemma remove_length : forall A (dec:forall x y : A, {x = y} + {x <> y}) 
      (l1:list A) (a:A),
    (length (List.remove dec a l1) <= length l1)%nat.
  Proof.
    induction l1; intros; simpl; auto.
      assert (J:=@IHl1 a0).
      destruct (dec a0 a); subst; simpl; auto. 
        omega.
  Qed.      

  Lemma remove_In_neq1 : forall A (dec:forall x y : A, {x = y} + {x <> y}) 
      (l1:list A) (a x:A),
    a <> x -> In x l1 -> In x (List.remove dec a l1).
  Proof.
    induction l1; intros; simpl in *; auto.
      destruct H0 as [H0 | H0]; subst.
        destruct (dec a0 x); subst. 
          contradict H; auto.
          simpl; auto.

        destruct (dec a0 a); subst; simpl; auto.
  Qed.          

  Lemma remove_In_neq2 : forall A (dec:forall x y : A, {x = y} + {x <> y}) 
      (l1:list A) (a x:A),
    a <> x -> In x (List.remove dec a l1) -> In x l1.
  Proof.
    induction l1; intros; simpl in *; auto.
      destruct (dec a0 a); subst; eauto.
        simpl in H0.
        destruct H0 as [H0 | H0]; subst; eauto.
  Qed.          

  Lemma incl_dec_aux : forall n, incl_dec_prop n. 
  Proof.
    intro n.  
    apply lt_wf_rec. clear n.
    intros n H.
    unfold incl_dec_prop in *.
    destruct l1; intros l2 Hlength.
      left. intros x J. inversion J.

      simpl in *.
      assert (((length (List.remove eq_atom_dec a l1)) < n)%nat) as LT.
        assert (J:=@remove_length atom eq_atom_dec l1 a).
        omega.  
      destruct (@H (length (List.remove eq_atom_dec a l1)) LT
                  (List.remove eq_atom_dec a l1) l2) as [J1 | J1]; auto.
        destruct(@in_dec _ eq_atom_dec a l2) as [J2 | J2].
          left. intros x J. simpl in J. 
          destruct J as [J | J]; subst; auto.
          destruct (eq_atom_dec x a); subst; auto.            
          apply J1.
          apply remove_In_neq1; auto.
          
          right. intros G. apply J2. apply G; simpl; auto.

        destruct(@in_dec _ eq_atom_dec a l2) as [J2 | J2].
          right. intros G. apply J1. intros x J3. apply G. simpl.
          destruct (eq_atom_dec x a); subst; auto.            
            right. eapply remove_In_neq2; eauto.

          right. intro J. apply J2. apply J. simpl; auto.
  Qed.

  Lemma incl_dec : forall (l1 l2:list atom), {incl l1 l2} + {~ incl l1 l2}.
  Proof.
    intros l1.
    assert (J:=@incl_dec_aux (length l1)).
    unfold incl_dec_prop in J. eauto.
  Qed.              

  Lemma set_eq_dec : forall (l1 l2:set atom), 
    {set_eq _ l1 l2} + {~ set_eq _ l1 l2}.
  Proof.
    intros l1 l2.
    destruct (@incl_dec l1 l2) as [J | J].
      destruct (@incl_dec l2 l1) as [J' | J'].
        left. split; auto.
        right. intro G. destruct G as [G1 G2]. auto.
      destruct (@incl_dec l2 l1) as [J' | J'].
        right. intro G. destruct G as [G1 G2]. auto.
        right. intro G. destruct G as [G1 G2]. auto.
  Qed.

  Lemma set_eq_app : forall x1 x2 y1 y2,
    set_eq atom x1 y1 -> set_eq atom x2 y2 -> set_eq atom (x1++x2) (y1++y2).
  Proof.  
    intros x1 x2 y1 y2 [Hinc11 Hinc12] [Hinc21 Hinc22].
    split.
      apply incl_app.
        apply incl_appl; auto.
        apply incl_appr; auto.
      apply incl_app.
        apply incl_appl; auto.
        apply incl_appr; auto.
  Qed.

  Lemma set_eq_swap : forall x1 x2,
    set_eq atom (x1++x2) (x2++x1).
  Proof.
    intros x1 x2.
    split.
      apply incl_app.
        apply incl_appr; auto using incl_refl.
        apply incl_appl; auto using incl_refl.
      apply incl_app.
        apply incl_appr; auto using incl_refl.
        apply incl_appl; auto using incl_refl.
  Qed.

  Lemma set_eq__rewrite_env : forall x1 x2 x3 y1 y2 y3,
    set_eq atom ((x1 ++ x2) ++ x3) ((y1 ++ y2) ++ y3) ->
    set_eq atom (x1 ++ x2 ++ x3) (y1 ++ y2 ++ y3).
  Proof.
    intros.
    simpl_env in H. auto.
  Qed.

  Lemma set_eq_refl : forall x, set_eq atom x x.  
    split; apply incl_refl.
  Qed.

  Lemma set_eq_sym: forall x y, set_eq atom x y -> set_eq atom y x.
  Proof.
    intros x y J.
    destruct J as [J1 J2]. split; auto.
  Qed.
  
  Lemma set_eq_trans: forall x y z, 
    set_eq atom x y -> set_eq atom y z -> set_eq atom x z.
  Proof.
    intros x y z J1 J2.
    destruct J1 as [J11 J12].
    destruct J2 as [J21 J22].
    split; eapply incl_tran; eauto.
  Qed.

  Lemma incl_empty_inv : forall x, 
    incl x (empty_set _) -> x = empty_set atom.
  Proof.
    destruct x; intro J; auto.
      assert (J1:=J a).
      contradict J1; simpl; auto.
  Qed.

  Lemma set_eq_empty_inv : forall x, 
    set_eq atom x (empty_set _) -> x = empty_set _.
  Proof.
    destruct x; intro J; auto.
      destruct J as [J1 J2].
      assert (J:=J1 a).
      contradict J; simpl; auto.
  Qed.

  Lemma incl_set_eq_left : forall x1 x2 y,
    set_eq atom x1 x2 -> incl x1 y -> incl x2 y.
  Proof.
    intros x1 x2 y [J1 J2] Hincl.
    eapply incl_tran; eauto.
  Qed.

  Lemma set_eq__incl : forall x1 x2, set_eq atom x1 x2 -> incl x1 x2.
  Proof.
    intros x1 x2 J.
    destruct J; auto.
  Qed.

  Lemma incl_set_eq_both : forall x1 x2 y1 y2,
    set_eq atom x1 x2 -> 
    set_eq atom y1 y2 -> 
    incl x1 y1 -> incl x2 y2.
  Proof.
    intros x1 x2 y1 y2 [J1 J2] [J3 J4] J5.
    apply incl_tran with (m:=y1); auto.
    apply incl_tran with (m:=x1); auto.
  Qed.

  Lemma set_eq_empty_inv2 : forall x, 
    set_eq atom (ListSet.empty_set _) x -> x = ListSet.empty_set _.
  Proof.
    intros.
    apply set_eq_sym in H.
    eapply set_eq_empty_inv; eauto.
  Qed.

  Lemma incl_app_invr : forall A (l1 l2 l:list A),
    incl (l1++l2) l -> incl l2 l.
  Proof.
    intros A l1 l2 l H x J.
    apply H. 
    apply (@incl_appr _ l2 l1 l2); auto using incl_refl.
  Qed.

  Lemma incl_app_invl : forall A (l1 l2 l:list A),
    incl (l1++l2) l -> incl l1 l.
  Proof.
    intros A l1 l2 l H x J.
    apply H. 
    apply (@incl_appl _ l1 l2 l1); auto using incl_refl.
  Qed.
  
  Lemma incl_set_eq_right : forall y1 y2 x,
    set_eq atom y1 y2 -> incl x y1 -> incl x y2.
  Proof.
    intros y1 y2 x [J1 J2] Hincl.
    eapply incl_tran; eauto.
  Qed.

  Lemma set_eq_inter : forall l1 l2 l1' l2'
    (H : set_eq atom l1 l1')
    (H0 : set_eq atom l2 l2'),
    set_eq atom (ListSet.set_inter eq_atom_dec l1 l2)
      (ListSet.set_inter eq_atom_dec l1' l2').
  Proof.
    intros.
    destruct H. destruct H0.
    split; intros a J.
      apply ListSet.set_inter_intro.
        apply ListSet.set_inter_elim1 in J; auto.
          apply H; auto.
        apply ListSet.set_inter_elim2 in J; auto.
          apply H0; auto.
      apply ListSet.set_inter_intro.
        apply ListSet.set_inter_elim1 in J; auto.
          apply H1; auto.
        apply ListSet.set_inter_elim2 in J; auto.
          apply H2; auto.
  Qed.

  Lemma set_inter_empty_eq_empty1: forall l1,
     set_eq atom (set_inter eq_atom_dec (empty_set atom) l1) (empty_set atom).
  Proof.
     intros.
      split; intros x J.
        apply set_inter_elim in J.
        destruct J; auto.
        inv J.
  Qed.        

  Lemma set_inter_empty_eq_empty2: forall l1,
     set_eq atom (set_inter eq_atom_dec l1 (empty_set atom)) (empty_set atom).
  Proof.
     intros.
      split; intros x J.
        apply set_inter_elim in J.
        destruct J; auto.
        inv J.
  Qed.        

  Lemma set_inter_incl: forall l1 l2,
    incl l1 l2 -> set_eq atom (set_inter eq_atom_dec l1 l2) l1.
  Proof.
    intros.
    split; intros x J.
      apply set_inter_elim in J.
      destruct J; auto.

      apply set_inter_intro; auto.
        apply H in J; auto.
  Qed.

  Lemma set_inter_refl: forall l1, set_eq _ (set_inter eq_atom_dec l1 l1) l1.
  Proof.
    intro.
    split; intros x J.
      apply set_inter_elim in J.
      destruct J; auto.

      apply set_inter_intro; auto.
  Qed.

  Lemma incl_inter : forall l1 l2 l1' l2'
    (H : incl l1 l1') (H0 : incl l2 l2'),
    incl (ListSet.set_inter eq_atom_dec l1 l2) 
         (ListSet.set_inter eq_atom_dec l1' l2').
  Proof.
    intros.
    intros x J.
    apply set_inter_elim in J. destruct J.
    apply H in H1. apply H0 in H2.
    apply set_inter_intro; auto.
  Qed.

End AtomSet.

(** * Domination analysis *)

(** The type [Dominators] of compile-time approximations of domination. *)

(** We equip this type of approximations with a semi-lattice structure.
  The ordering is inclusion between the sets of values denoted by
  the approximations. *)

Module Dominators.
 
  Export AtomSet.

  Section VarBoundSec.

  Variable bound:set atom.

  Record BoundedSet := mkBoundedSet {
    bs_contents : set atom;
    bs_bound : incl bs_contents bound
  }.

  Definition t := BoundedSet.

  Definition eq (x y: t) :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    set_eq _ cx cy.

  Definition eq_refl: forall x, eq x x. 
  Proof.
    unfold eq. intro x. destruct x.
    apply set_eq_refl.
  Qed.

  Definition eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq. intros x y J. destruct x. destruct y.
    apply set_eq_sym; auto.
  Qed.
 
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq. intros x y z J1 J2. destruct x. destruct y. destruct z.
    eapply set_eq_trans; eauto.
  Qed.

  Lemma eq_dec: forall (x y: t), {eq x y} + {~ eq x y}.
  Proof.
    unfold eq. destruct x. destruct y.
    apply set_eq_dec.
  Qed.

  Definition beq (x y: t) := if eq_dec x y then true else false.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq; intros.  destruct (eq_dec x y). auto. congruence.
  Qed.

  Definition sub (x y: t) :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    incl cx cy.

  Program Definition top : t := mkBoundedSet (empty_set atom) _.
  Next Obligation.
    intros a H. inversion H.
  Qed.

  Program Definition bot : t := mkBoundedSet bound _.
  Next Obligation.
    apply incl_refl.
  Qed.

  Definition ge (x y: t) : Prop := eq x top \/ eq y bot \/ sub x y.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold ge, eq, sub. destruct x, y. simpl.
    intro J. right. right. destruct J; auto.
  Qed.

  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge, eq, sub. destruct x, y, z. simpl.
    intros J1 J2.
    destruct J1 as [J11 | [J12 | J13]]; try auto.
      destruct J2 as [J21 | [J22 | J23]]; try auto.
        assert (set_eq _ bound (empty_set atom)) as EQ.
          eapply set_eq_trans with (y:=bs_contents1); eauto using set_eq_sym.
        left. 
        apply set_eq_empty_inv in EQ; subst.
        apply incl_empty_inv in bs_bound0; subst.
        apply set_eq_refl.

        right. left. 
        eapply incl_set_eq_left in J23; eauto.
        split; auto.

      destruct J2 as [J21 | [J22 | J23]]; try auto.
        left. 
        apply set_eq_empty_inv in J21; subst.
        apply incl_empty_inv in J13; subst.
        apply set_eq_refl.

        right. right. eapply incl_tran; eauto.
  Qed.

  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold ge, eq, sub. destruct x, x', y, y'. simpl in *. 
    intros J1 J2 J3.
    destruct J3 as [J31 | [J32 | J33]].
      left. eapply set_eq_trans with (y:=bs_contents0); eauto using set_eq_sym.
      right. left. 
        eapply set_eq_trans with (y:=bs_contents2); eauto using set_eq_sym.
      right. right. eapply incl_set_eq_both; eauto. 
  Qed.

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, eq, sub. destruct x. simpl. right. left. apply set_eq_refl.
  Qed.

  Lemma ge_top: forall x, ge top x.
  Proof.
    unfold ge, eq, sub. destruct x. simpl. left. apply set_eq_refl.
  Qed.

  Program Definition lub (x y: t) : t :=
    let '(mkBoundedSet cx _) := x in
    let '(mkBoundedSet cy _) := y in
    mkBoundedSet (set_inter eq_atom_dec cx cy) _.
  Next Obligation.
    intros a J.
    apply set_inter_elim in J.
    destruct J as [J1 J2].
    eauto.
  Qed.

  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq. destruct x, y. 
    split.
      intros a J.
      apply set_inter_elim in J. destruct J.
      apply set_inter_intro; auto.

      intros a J.
      apply set_inter_elim in J. destruct J.
      apply set_inter_intro; auto.
  Qed.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub, ge, sub, eq. destruct x, y. simpl.
    right. right.
    intros a J.
    apply set_inter_elim in J. destruct J. auto.
  Qed.

  Lemma ge_lub_right:
    forall x y, ge (lub x y) y.
  Proof.
    intros. 
    apply ge_compat with (x:=lub y x)(y:=y).
      apply lub_commut.
      apply eq_refl.
      apply ge_lub_left.
  Qed.

  Lemma lub_preserves_ge : forall x y, ge x y -> eq (lub x y) x.
  Proof.
    unfold lub, ge, eq. destruct x, y. simpl.
    intros.
    destruct H as [H | [H | H]].
      apply set_eq_empty_inv in H. subst.
      apply set_inter_empty_eq_empty1.

      apply set_inter_incl.
      eapply incl_set_eq_right; eauto using set_eq_sym.

      apply set_inter_incl; auto.

  Qed.

  Lemma lub_compat : forall x y x' y', 
    ge x x' -> ge y y' -> ge (lub x y) (lub x' y').
  Proof.
    unfold lub, ge, eq. destruct x, y, x', y'. simpl.
    intros J1 J2.
    destruct J1 as [J11 | [J12 | J13]].
      apply set_eq_empty_inv in J11. subst.
      left. apply set_inter_empty_eq_empty1.

      destruct J2 as [J21 | [J22 | J23]].
        apply set_eq_empty_inv in J21. subst.
        left. apply set_inter_empty_eq_empty2.

        right. left.
        apply set_eq_trans with (y:=set_inter eq_atom_dec bound bound).
          apply set_eq_inter; auto.
          apply set_inter_refl.

        right. right. apply incl_inter; auto.
        apply incl_set_eq_both with (x1:=bs_contents0)(y1:=bound); auto.
          apply set_eq_refl.
          apply set_eq_sym; auto.

      destruct J2 as [J21 | [J22 | J23]].
        apply set_eq_empty_inv in J21. subst.
        left. apply set_inter_empty_eq_empty2.

        right. right. apply incl_inter; auto.
        apply incl_set_eq_right with (y1:=bound); auto.
        apply set_eq_sym; auto. 

        right. right. apply incl_inter; auto.
  Qed.

  Lemma lub_refl : forall x, eq x (lub x x).
  Proof.
    unfold eq, lub. destruct x. 
    apply set_eq_sym. apply set_inter_refl.
  Qed.

  Lemma ge_top_inv : forall x, ge x top -> eq x top.
  Proof.
    unfold ge, top. destruct x. simpl.
    intros J.
    destruct J as [J1 | [J2 | J3]].
      apply set_eq_empty_inv in J1. subst. apply set_eq_refl.

      apply set_eq_sym in J2. apply set_eq_empty_inv in J2. subst. 
      apply incl_empty_inv in bs_bound0. subst. apply set_eq_refl.

      apply incl_empty_inv in J3. subst. apply set_eq_refl.
  Qed.

  Lemma ge_antisym : forall x y, ge x y -> ge y x -> eq x y.
  Proof. 
    destruct x, y.
    intros J1 J2.
    unfold ge, eq in J1. simpl in J1.
    destruct J1 as [J11 | [J12 | J13]].
      apply set_eq_empty_inv in J11. subst.
      apply ge_top_inv in J2. unfold top in J2.
      unfold eq in *. 
      apply set_eq_empty_inv in J2. subst. apply set_eq_refl.

      unfold ge, eq in *. simpl in *.
      destruct J2 as [J21 | [J22 | J23]].
        apply set_eq_empty_inv in J21. subst.
        apply set_eq_sym in J12. apply set_eq_empty_inv in J12. subst.
        apply incl_empty_inv in bs_bound0. subst. apply set_eq_refl.

        apply set_eq_trans with (y:=bound); auto.
        apply set_eq_sym; auto.

        apply set_eq_trans with (y:=bound); auto.
          split; auto.
            intros x J.
            apply J23. destruct J12 as [_ J12]. apply J12; auto.         
          apply set_eq_sym; auto.

      unfold ge, eq in *. simpl in *.
      destruct J2 as [J21 | [J22 | J23]].
        apply set_eq_empty_inv in J21. subst.
        apply incl_empty_inv in J13. subst. apply set_eq_refl.

        apply set_eq_trans with (y:=bound); auto.
          split; auto.
            intros x J.
            apply J13. destruct J22 as [_ J22]. apply J22; auto.         
          apply set_eq_sym; auto.

        split; auto.
  Qed.

  Lemma lub_compat' : forall x y1 y2, ge x y1 -> ge x y2 -> ge x (lub y1 y2).
  Proof.
    intros. 
    apply ge_trans with (y:=lub x x).
      apply ge_refl. apply lub_refl.
      apply lub_compat; auto.
  Qed.

  Lemma ge_lub_left' : forall a p1 p2, ge p2 p1 -> ge (lub p2 a) p1.
  Proof.
    intros.
    apply ge_trans with (y:=p2); auto. 
    apply ge_lub_left.
  Qed.

  Lemma ge_refl' : forall x, ge x x.
  Proof. 
    intros. apply ge_refl. apply eq_refl.
  Qed.

  Program Definition add (x:t) (a:atom) : t := 
    let '(mkBoundedSet cx _) := x in
    if (In_dec eq_atom_dec a bound) then
      mkBoundedSet (a::cx) _
    else
      x.
  Next Obligation.
    intros a' J.
    simpl in J.
    destruct J; subst; eauto.
  Qed.

  Lemma add_mono: forall a x y, ge x y -> ge (add x a) (add y a).
  Proof.
    unfold ge, add, eq, sub. destruct x, y. simpl. intros.
    destruct (in_dec eq_atom_dec a bound); auto.
      destruct H as [H1 | [H2 | H3]].
        apply set_eq_empty_inv in H1. subst.
        right. right. 
        intros x J. simpl in J. 
        destruct J as [J | J]; subst; try solve [inversion J].
          simpl. auto.

        right. right. 
        intros x J. simpl in J. 
        destruct J as [J | J]; subst; simpl; auto.
        right. destruct H2 as [_ H2]. apply H2. apply bs_bound0; auto.

        right. right. 
        intros x J. simpl in J. 
        destruct J as [J | J]; subst; simpl; auto.
  Qed.

  Definition member (a:atom) (x: t) :=
    let '(mkBoundedSet cx _) := x in In a cx.

  Lemma add_member1: forall a x, 
    In a bound -> member a (add x a).
  Proof.
    unfold member, add. destruct x.
    destruct (in_dec eq_atom_dec a bound); simpl; auto.
      intro J. congruence.
  Qed.

  Lemma add_member2: forall a b x, 
    member a x -> member a (add x b).
  Proof.
    unfold member, add. destruct x.
    destruct (in_dec eq_atom_dec b bound); simpl; auto.
  Qed.

  Lemma member_eq : forall a x1 x2, eq x1 x2 -> member a x2 -> member a x1.
  Proof.
    unfold member, eq. destruct x1, x2.
    intros. destruct H. apply H1; auto.
  Qed.

  Lemma member_lub : forall a x1 x2, 
    member a x2 -> member a x1 -> member a (lub x1 x2).
  Proof.
    unfold member, lub. destruct x1, x2.
    intros. apply set_inter_intro; auto.
  Qed.

  Lemma ge_elim : forall a x y, ge x y -> member a x -> member a y.
  Proof.
    unfold member, ge. destruct x, y. simpl. intros.
    destruct H as [H | [H | H]].
      apply set_eq_empty_inv in H. subst. inv H0.

      destruct H as [J1 J2].
      apply J2. apply bs_bound1; auto.

      apply H; auto.
  Qed.

  Lemma member_dec: forall a x, member a x \/ ~ member a x.
  Proof.
    unfold member. destruct x. 
    destruct (in_dec eq_atom_dec a bs_contents0); auto.
  Qed.

  Lemma lub_compat_eq : forall x y x' y', 
    eq x x' -> eq y y' -> eq (lub x y) (lub x' y').
  Proof.
    unfold lub, eq. destruct x, y, x', y'. simpl.
    intros J1 J2.
    destruct J1. destruct J2.
    split; intros x J.
      apply set_inter_elim in J. destruct J.
      apply set_inter_intro.
        apply H; auto.
        apply H1; auto.

      apply set_inter_elim in J. destruct J.
      apply set_inter_intro.
        apply H0; auto.
        apply H2; auto.
  Qed.

  Lemma add_bot: forall a, eq (add bot a) bot.
  Proof.
    unfold eq, add, bot. intros.
    destruct (in_dec eq_atom_dec a bound).
      split; intros x J.
        simpl in J. destruct J; subst; auto.
        simpl. auto.
      apply set_eq_refl.
  Qed.

  Lemma add_eq: forall a x y, eq x y -> eq (add x a) (add y a).
  Proof.
    unfold eq, add. destruct x, y. intros.
    destruct (in_dec eq_atom_dec a bound); auto.
      destruct H as [H1 H2]. 
      split; intros x J; simpl in *.
        destruct J; subst; auto. 
        destruct J; subst; auto. 
  Qed.

  Lemma lub_intro: forall a x y, member a x -> member a y -> member a (lub x y).
  Proof.
    unfold member, lub. destruct x, y. intros. apply set_inter_intro; auto.
  Qed.

  Definition lubs (pds: list t) : t :=
    fold_left (fun acc => fun p => lub acc p) pds bot.

  Lemma lubs_spec1: forall pds p2 p1,
    ge p2 p1 -> ge (fold_left (fun acc => fun p => lub acc p) pds p2) p1.
  Proof.
    induction pds; simpl; intros; auto.
      apply IHpds. apply ge_lub_left'; auto.
  Qed.

  Lemma lubs_spec2_aux: forall pds p2 p1, In p1 pds -> 
    ge (fold_left (fun acc => fun p => lub acc p) pds p2) p1.
  Proof.
    induction pds; simpl; intros.
      inversion H.
      destruct H as [H | H]; subst.
        apply lubs_spec1.
          apply ge_lub_right; auto.
        apply IHpds; auto.
  Qed.

  Lemma lubs_spec2: forall pds p1, In p1 pds -> 
    ge (lubs pds) p1.
  Proof.
    unfold lubs. intros. apply lubs_spec2_aux; auto.
  Qed.

  Lemma lubs_spec3_aux: forall p0 pds p2,
    ge p0 p2 ->
    (forall p, In p pds -> ge p0 p) ->
    ge p0 (fold_left (fun acc => fun p => lub acc p) pds p2).
  Proof.
    induction pds; simpl; intros; auto.
      apply IHpds; auto.
        apply lub_compat'; auto.
  Qed.

  Lemma lubs_spec3: forall pds p1, 
    (forall p, In p pds -> ge p1 p) -> ge p1 (lubs pds).
  Proof.
    unfold lubs. intros. apply lubs_spec3_aux; auto.
      apply ge_bot.
  Qed.

  End VarBoundSec. 
End Dominators.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)

