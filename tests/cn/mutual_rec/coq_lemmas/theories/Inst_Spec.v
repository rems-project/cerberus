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

Lemma inc_list_lemma: inc_list_lemma_type.
Proof.
  unfold inc_list_lemma_type, inc_list.
  intro.
  destruct xs.
  - auto.
  - intros.
    rewrite CN_Lib.wrapI_idem by lia.
    auto.
Qed.

Lemma a_tree_keys_lemma: a_tree_keys_lemma_type.
Proof.
  unfold a_tree_keys_lemma_type, a_tree_keys, b_tree_keys, concat.
  intros.
  destruct atree.
  - auto.
  - simpl.
    repeat rewrite to_from_list.
    auto.
Qed.

Lemma b_tree_keys_lemma: b_tree_keys_lemma_type.
Proof.
  unfold b_tree_keys_lemma_type, a_tree_keys, b_tree_keys,
    merge, inc_list, double_list.
  intros.
  destruct btree.
  - auto.
  - simpl.
    repeat rewrite to_from_list.
    rewrite List.map_map.
    auto.
Qed.

Lemma inc_concat_lemma: inc_concat_lemma_type.
  unfold inc_concat_lemma_type, inc_list, concat.
  intros.
  repeat rewrite to_from_list.
  rewrite List.map_app.
  auto.
Qed.

Lemma inc_merge_double_lemma: inc_merge_double_lemma_type.
  unfold inc_merge_double_lemma_type, inc_list, merge.
  intros.
  repeat rewrite to_from_list.
  rewrite map_merge by lia.
  auto.
Qed.

Lemma flip_merge_lemma: flip_merge_lemma_type.
  unfold flip_merge_lemma_type, inc_list, merge, double_list.
  intros.
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

Lemma inc_double_lemma: inc_double_lemma_type.
  unfold inc_double_lemma_type, double_list, inc_list.
  intros.
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

