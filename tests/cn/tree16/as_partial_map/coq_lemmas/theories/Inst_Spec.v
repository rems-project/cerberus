(* Instantiation of the CN-exported specification
   using results from the prior theories. *)

Require Import ZArith Bool Lia.
Require Import CN_Lemmas.Setup.
Require Import CN_Lemmas.Gen_Spec.
Import CN_Lemmas.Gen_Spec.Types.

Module Inst.

  Definition empty (a : tree_arc) := Node_None.

  Definition mk_arc := Setup.mk_arc.

  Definition construct := Setup.construct.
  
End Inst.

Module Defs := CN_Lemmas.Gen_Spec.Defs (Inst).

Module Proofs.

(* now prove lemmas *)
Import Defs Inst.
Open Scope Z.

Lemma z_to_nat_eq_0:
  forall (z : Z), z <= 0 -> Z.to_nat z = 0%nat.
Proof.
  lia.
Qed.

Lemma mk_arc_end_lemma : mk_arc_end_lemma_type.
Proof.
  unfold mk_arc_end_lemma_type.
  intros.
  constructor.
  - auto.
  - unfold mk_arc, Setup.mk_arc.
    rewrite z_to_nat_eq_0; auto; lia.
Qed.

Lemma z_to_nat_sub_succ:
  forall i len, i < len ->
  Z.to_nat (len - i) = S (Z.to_nat (len - (i + 1))).
Proof.
  lia.
Qed.

Lemma mk_arc_step_lemma : mk_arc_step_lemma_type.
Proof.
  unfold mk_arc_step_lemma_type.
  intros.
  constructor.
  - auto.
  - unfold mk_arc, Setup.mk_arc.
    rewrite (z_to_nat_sub_succ _ _ H5).
    auto.
Qed.

Lemma empty_lemma : empty_lemma_type.
Proof.
  unfold empty_lemma_type.
  intros.
  auto.
Qed.

Lemma construct_empty_lemma : construct_empty_lemma_type.
Proof.
  unfold construct_empty_lemma_type.
  intros.
  auto.
Qed.

Lemma construct_step_lemma : construct_step_lemma_type.
Proof.
  unfold construct_step_lemma_type.
  intros.
  auto.
Qed.

End Proofs.

Module InstOK: CN_Lemmas.Gen_Spec.Lemma_Spec(Inst).

  Module D := CN_Lemmas.Gen_Spec.Defs (Inst).

  Include Proofs.

End InstOK.

