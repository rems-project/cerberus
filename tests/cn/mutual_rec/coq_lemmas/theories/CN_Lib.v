Require List.
Require Import ZArith Bool.
Require Import Lia.
Require NArith.

Definition wrapI (minInt : Z) (maxInt : Z) x :=
  let delta := ((maxInt - minInt) + 1)%Z in
  let r := Z.modulo x delta in
  (if (r <=? maxInt) then r else r - delta)%Z.

Lemma wrapI_idem:
  forall (minInt maxInt x : Z),
  (minInt <= x <= maxInt)%Z ->
  (minInt <= 0 < maxInt)%Z ->
  wrapI minInt maxInt x = x.
Proof.
  Open Scope Z.
  intros.
  unfold wrapI.
  pose (delta := ((maxInt - minInt) + 1)).
  destruct (0 <=? x) eqn: x_neg.
  - rewrite Z.mod_small by lia.
    rewrite Zle_imp_le_bool by lia.
    reflexivity.
  - rewrite (Znumtheory.Zdivide_mod_minus _ _ (x + delta)).
    + destruct (x + delta <=? maxInt) eqn: leb; lia.
    + lia.
    + exists (-1); lia.
Qed.
