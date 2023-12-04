(* Setup of consts and lemmas for lemmas *)

Require Import ZArith Bool.
Require CN_Lemmas.Gen_Spec.
Import CN_Lemmas.Gen_Spec.Types.
Require Import List.
Import ListNotations.
Open Scope Z.
Require Lia.

Fixpoint merge_w (i : nat) (xs ys : list Z) :=
  match (i, xs, ys) with
  | (0%nat, _, _) => []
  | (_, [], _) => ys
  | (_, _, []) => xs
  | (S j, x :: xs, y :: ys) =>
    if x <? y
    then x :: merge_w j xs (y :: ys)
    else y :: merge_w j (x :: xs) ys
  end.

Definition merge (xs ys : list Z) :=
  merge_w (length xs + length ys) xs ys.

Fixpoint walk_a_tree (t : a_tree) : list Z :=
  match t with
  | A_Leaf => []
  | A_Node k l r v => walk_b_tree l ++ k :: walk_b_tree r
  end
  with
  walk_b_tree (t : b_tree) : list Z :=
  match t with
  | B_Leaf => []
  | B_Node even odd => merge
    (List.map (fun i => i * 2) (walk_a_tree even))
    (List.map (fun i => (i * 2) + 1) (walk_a_tree odd))
  end.

Fixpoint to_list (xs : key_list) :=
  match xs with
  | K_Nil => []
  | K_Cons y ys => y :: to_list ys
  end.

Fixpoint from_list (xs : list Z) : key_list :=
  match xs with
  | [] => K_Nil
  | y :: ys => K_Cons y (from_list ys)
  end.

Lemma to_from_list: forall xs,
  to_list (from_list xs) = xs.
Proof.
  intros. induction xs.
  - auto.
  - simpl.
    rewrite IHxs.
    auto.
Qed.

Lemma from_to_list: forall xs,
  from_list (to_list xs) = xs.
Proof.
  intros. induction xs.
  - auto.
  - simpl.
    rewrite IHxs.
    auto.
Qed.

Lemma merge_w_induction:
  forall P,
  (forall xs ys, P (0%nat) xs ys) ->
  (forall i ys, P (S i) [] ys) ->
  (forall i x xs, P (S i) (x :: xs) []) ->
  (forall i x xs y ys, P i xs (y :: ys) -> (x <? y) = true ->
    P (S i) (x :: xs) (y :: ys)) ->
  (forall i x xs y ys, P i (x :: xs) ys -> (x <? y) = false ->
    P (S i) (x :: xs) (y :: ys)) ->
  (forall i xs ys, P i xs ys).
Proof.
  intros until i.
  induction i.
  - auto.
  - intros.
    pose (b := (List.hd 1 xs <? List.hd 1 ys)).
    destruct xs; auto.
    destruct ys; auto.
    simpl in b.
    destruct b eqn: t; auto.
Qed.

Lemma map_merge_w: forall f,
  (forall x y, (f x <? f y) = (x <? y)) ->
  forall i xs ys,
  List.map f (merge_w i xs ys) =
  merge_w i (List.map f xs) (List.map f ys).
Proof.
  intros until i.
  induction i.
  - auto.
  - intros.
    destruct xs as [| x xs2]; destruct ys as [| y ys2];
      simpl; try reflexivity.
    rewrite H.
    destruct (x <? y).
    + simpl.
      rewrite IHi.
      auto.
    + simpl.
      rewrite IHi.
      auto.
Qed.

Lemma map_merge: forall f xs ys,
  (forall x y, (f x <? f y) = (x <? y)) ->
  List.map f (merge xs ys) =
  merge (List.map f xs) (List.map f ys).
Proof.
  intros.
  unfold merge.
  rewrite map_merge_w by auto.
  repeat rewrite List.map_length.
  auto.
Qed.

Lemma merge_w_flip: forall i xs ys,
  (forall x : Z, In x xs -> forall y, In y ys -> x <> y) ->
  merge_w i xs ys = merge_w i ys xs.
Proof.
  intro.
  induction i.
  - auto.
  - intros.
    destruct xs as [| x xs2]; destruct ys as [| y ys2];
      simpl; try reflexivity.
    rewrite Z.ltb_antisym, Z.ltb_compare, Z.leb_compare.
    destruct (y ?= x) eqn: xy; simpl.
    + apply Z.compare_eq in xy.
      assert (x <> y) by auto using H, in_eq.
      Lia.lia.
    + simpl.
      f_equal.
      apply IHi; intros.
      apply H; auto using in_cons.
    + simpl.
      f_equal.
      apply IHi; intros.
      apply H; auto using in_cons.
Qed.

Lemma merge_flip: forall xs ys,
  (forall x, In x xs -> forall y, In y ys -> x <> y) ->
  merge xs ys = merge ys xs.
Proof.
  intros.
  unfold merge.
  rewrite plus_comm.
  apply merge_w_flip.
  auto.
Qed.

