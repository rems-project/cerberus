Require Import Arith.
Require Import FMaps.

Module NatOrdered.
  Definition t := nat.

  Definition eq (a b : t) := a = b.
  Instance eq_equiv : Equivalence eq.
  Proof.
    unfold eq.
    auto.
  Qed.

  Definition eq_refl := @Equivalence_Reflexive _ _ eq_equiv.
  Definition eq_sym := @Equivalence_Symmetric _ _ eq_equiv.
  Definition eq_trans := @Equivalence_Transitive _ _ eq_equiv.

  Definition lt (a b : t) := a < b.

  (*
  Instance lt_strorder : StrictOrder lt.
  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold eq.
    unfold lt.
    split; simpl in *; congruence.
  Qed.
  *)

  Lemma lt_trans: forall  (a b c : t), lt a b -> lt b c -> lt a c.
  Proof.
    unfold lt.
    intros.
    omega.
  Qed.

  Lemma lt_not_eq: forall (x y: t), lt x y -> ~eq x y.
  Proof.
    unfold eq.
    unfold lt.
    intros x y Hlt Heq.
    omega.
  Qed.

  (*
  Definition compare (a b : t) := nat_compare (fst a) (fst b).
  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros.
    unfold eq; unfold lt; unfold compare.
    destruct (nat_compare (fst x) (fst y)) as [ ]_eqn; constructor.
      apply    nat_compare_eq; now auto.
      apply <- nat_compare_lt; now auto.
      apply <- nat_compare_gt; now auto.
  Qed.
  *)

  Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros.
    unfold eq.
    unfold lt.
    destruct (nat_compare x y) as [ ]_eqn.
      constructor 2; apply    nat_compare_eq; now auto.
      constructor 1; apply <- nat_compare_lt; now auto.
      constructor 3; apply <- nat_compare_gt; now auto.
  Qed.

  Definition eq_dec (a b : t) := Peano_dec.eq_nat_dec a b.
End NatOrdered.

Module NatMap.
  Declare Module Map : S with Module E := NatOrdered.
  Module Props := Properties (Map).

  Include Map.
  Definition update : forall elt : Type, t elt -> t elt -> t elt := Props.update.
End NatMap.
