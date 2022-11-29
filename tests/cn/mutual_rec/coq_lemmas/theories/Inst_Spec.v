(* Instantiation of the CN-exported specification
   using results from the prior theories. *)

Require Import ZArith Bool Lia.
Require Import CN_Lemmas.Setup.
Require Import CN_Lemmas.Gen_Spec.
Import CN_Lemmas.Gen_Spec.Types.

Module Inst.

  Definition a_tree_keys (t : a_tree) := from_list (walk_a_tree t).

  Definition b_tree_keys (t : b_tree) := from_list (walk_b_tree t).
  
  Definition inc_list (xs : key_list) :=
    from_list (List.map (fun i => i + (1%Z)) (to_list xs)).
    
  Definition concat (xs ys : key_list) :=
    from_list (to_list xs ++ to_list ys).
    
  Definition merge (xs ys : key_list) :=
    from_list (Setup.merge (to_list xs) (to_list ys)).

  Definition double_list (xs : key_list) :=
    from_list (List.map (fun i => i * (2%Z)) (to_list xs)).

End Inst.

Module Defs := CN_Lemmas.Gen_Spec.Defs (Inst).

Module Proofs.

(* now prove lemmas *)
Import Defs Inst.
Open Scope Z.

Lemma a_tree_keys_leaf_lemma: a_tree_keys_leaf_lemma_type.
Proof.
  unfold a_tree_keys_leaf_lemma_type.
  simpl.
  auto.
Qed.

Lemma b_tree_keys_leaf_lemma: b_tree_keys_leaf_lemma_type.
Proof.
  unfold b_tree_keys_leaf_lemma_type.
  auto.
Qed.

Lemma inc_list_nil_lemma: inc_list_nil_lemma_type.
Proof.
  unfold inc_list_nil_lemma_type.
  auto.
Qed.

Lemma a_tree_keys_node_lemma: a_tree_keys_node_lemma_type.
Proof.
  unfold a_tree_keys_node_lemma_type.
  intros.
  unfold a_tree_keys, b_tree_keys, concat.
  simpl.
  repeat rewrite to_from_list.
  auto.
Qed.

Lemma a_tree_keys_node_concat_inc_lemma: a_tree_keys_node_concat_inc_lemma_type.
Proof.
  unfold a_tree_keys_node_concat_inc_lemma_type.
  intros.
  unfold inc_list, concat.
  repeat rewrite to_from_list.
  rewrite List.map_app.
  auto.
Qed.

Lemma a_tree_keys_node_concat_cons_inc_lemma: a_tree_keys_node_concat_cons_inc_lemma_type.
Proof.
  unfold a_tree_keys_node_concat_cons_inc_lemma_type.
  intros.
  unfold inc_list.
  auto.
Qed.

Lemma b_tree_keys_node_lemma: b_tree_keys_node_lemma_type.
Proof.
  unfold b_tree_keys_node_lemma_type.
  intros.
  unfold merge, b_tree_keys, a_tree_keys, double_list, inc_list.
  simpl.
  repeat rewrite to_from_list.
  rewrite List.map_map.
  auto.
Qed.

Lemma b_tree_keys_node_merge_inc_lemma: b_tree_keys_node_merge_inc_lemma_type.
Proof.
  unfold b_tree_keys_node_merge_inc_lemma_type.
  intros.
  unfold inc_list, merge.
  repeat rewrite to_from_list.
  rewrite map_merge by lia.
  auto.
Qed.

Lemma b_tree_keys_node_merge_flip_lemma: b_tree_keys_node_merge_flip_lemma_type.
Proof.
  unfold b_tree_keys_node_merge_flip_lemma_type.
  intros.
  unfold merge, inc_list, double_list.
  repeat rewrite to_from_list.
  rewrite merge_flip; try reflexivity.
  rewrite<- List.Forall_forall.
  repeat rewrite List.Forall_map.
  rewrite List.Forall_forall.
  intro.
  rewrite<- List.Forall_forall.
  repeat rewrite List.Forall_map.
  rewrite List.Forall_forall.
  intros.
  lia.
Qed.

Lemma b_tree_keys_node_inc_inc_double_lemma: b_tree_keys_node_inc_inc_double_lemma_type.
Proof.
  unfold b_tree_keys_node_inc_inc_double_lemma_type.
  intros.
  unfold inc_list, double_list.
  repeat rewrite to_from_list.
  repeat rewrite List.map_map.
  f_equal.
  apply List.map_ext_in.
  intros.
  lia.
Qed.

End Proofs.

Module InstOK: CN_Lemmas.Gen_Spec.Lemma_Spec(Inst).

  Module D := CN_Lemmas.Gen_Spec.Defs (Inst).

  Include Proofs.

End InstOK.

