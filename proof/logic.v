Require Import Coq.Program.Equality.

Inductive formula :=
  | KFalse
  | KAnd (f1 f2 : formula)
  | KImp (f1 : formula) (f2 : formula)
  | KGuard (f1 : formula) (f2 : formula).

Inductive no_guard : formula -> Prop :=
  | no_guard_false : no_guard KFalse
  | no_guard_and : forall f1 f2, no_guard f1 -> no_guard f2 -> no_guard (KAnd f1 f2)
  | no_guard_imp : forall f1 f2, no_guard f1 -> no_guard f2 -> no_guard (KImp f1 f2).

Lemma no_guard_and1 : forall f1 f2, no_guard (KAnd f1 f2) -> no_guard f1.
Proof. now inversion 1. Defined.

Lemma no_guard_and2 : forall f1 f2, no_guard (KAnd f1 f2) -> no_guard f2.
Proof. now inversion 1. Defined.

Lemma no_guard_imp1 : forall f1 f2, no_guard (KImp f1 f2) -> no_guard f1.
Proof. now inversion 1. Defined.

Lemma no_guard_imp2 : forall f1 f2, no_guard (KImp f1 f2) -> no_guard f2.
Proof. now inversion 1. Defined.

Inductive wff : formula -> Prop :=
  | wff_false : wff KFalse
  | wff_and   : forall f1 f2,      wff f1 -> wff f2 -> wff (KAnd   f1 f2)
  | wff_imp   : forall f1 f2, no_guard f1 -> wff f2 -> wff (KImp   f1 f2)
  | wff_guard : forall f1 f2, no_guard f1 -> wff f2 -> wff (KGuard f1 f2).

Inductive value : Set :=
  | VTrue
  | VFalse
  | VUndef.

Inductive sem : formula -> value -> Prop :=
  | sem_false : sem KFalse VFalse
  | sem_and_false1 : forall f1 f2, sem f1 VFalse -> sem (KAnd f1 f2) VFalse
  | sem_and_false2 : forall f1 f2, sem f2 VFalse -> sem (KAnd f1 f2) VFalse
  | sem_and_true_true  : forall f1 f2, sem f1 VTrue -> sem f2 VTrue -> sem (KAnd f1 f2) VTrue
  | sem_and_undef_undef : forall f1 f2, sem f1 VUndef -> sem f2 VUndef -> sem (KAnd f1 f2) VUndef
  | sem_and_true_undef : forall f1 f2, sem f1 VTrue -> sem f2 VUndef -> sem (KAnd f1 f2) VUndef
  | sem_and_undef_true : forall f1 f2, sem f1 VUndef -> sem f2 VTrue -> sem (KAnd f1 f2) VUndef
  | sem_imp_true : forall f1 f2 v2, sem f1 VTrue -> sem f2 v2 -> sem (KImp f1 f2) v2
  | sem_imp_false : forall f1 f2, sem f1 VFalse -> sem (KImp f1 f2) VTrue
  | sem_guard_true : forall f1 f2, sem f1 VTrue -> sem (KGuard f1 f2) VUndef
  | sem_guard_false : forall f1 f2 v2, sem f1 VFalse -> sem f2 v2 -> sem (KGuard f1 f2) v2.

Inductive feq : formula -> formula -> Prop :=
  | feq_ext : forall f1 f2 v1 v2, sem f1 v1 -> sem f2 v2 -> (forall v, sem f1 v <-> sem f2 v) -> feq f1 f2.

Lemma sem_and_comm : forall f1 f2 v, sem (KAnd f2 f1) v -> sem (KAnd f1 f2) v.
Proof.
  intros f1 f2 [] Sem;
  dependent destruction Sem;
    try now constructor.
    now apply sem_and_false2.
    now apply sem_and_undef_true.
    now apply sem_and_true_undef.
Qed.

Lemma sem_inj : forall f v1 v2, sem f v1 -> sem f v2 -> v1 = v2.
Proof.
  induction f; intros val1 val2 S1 S2;
    dependent destruction S1;
      try dependent destruction S2;
        try reflexivity;
        try discriminate (IHf1 _ _ S1   S2_1);
        try discriminate (IHf2 _ _ S1   S2_1);
        try discriminate (IHf1 _ _ S1   S2_2);
        try discriminate (IHf2 _ _ S1   S2_2);
        try discriminate (IHf1 _ _ S1_1 S2);
        try discriminate (IHf2 _ _ S1_1 S2);
        try discriminate (IHf1 _ _ S1_2 S2);
        try discriminate (IHf2 _ _ S1_2 S2);
        try discriminate (IHf1 _ _ S1_1 S2_1);
        try discriminate (IHf2 _ _ S1_2 S2_2);
        try (now apply   (IHf1 _ _ S1_1 S2_1));
        try (now apply   (IHf2 _ _ S1_2 S2_2)).
Qed.

Fixpoint no_guard_b f : no_guard f -> bool.
Proof.
  intros p.
  destruct f.
    now apply false.

    set (no_guard_b f1 (no_guard_and1 _ _ p)) as b1.
    set (no_guard_b f2 (no_guard_and2 _ _ p)) as b2.
    now apply (andb b1 b2).

    set (no_guard_b f1 (no_guard_imp1 _ _ p)) as b1.
    set (no_guard_b f2 (no_guard_imp2 _ _ p)) as b2.
    now apply (orb (negb b1) b2).

    revert p. now constructor.
Defined.

Definition value_from_bool (b : bool) : value :=
  match b with
  | true => VTrue
  | false => VFalse
  end. 

Lemma no_guard_sem f (p : no_guard f) : sem f (value_from_bool (no_guard_b f p)).
Proof.
  induction f;
    dependent destruction p; simpl;
      try (now constructor);

      try now (
        set (IHf1 p1) as Sem1;
        set (IHf2 p2) as Sem2;
        case_eq (no_guard_b f1 p1);
        case_eq (no_guard_b f2 p2);
        intros E2 E1;
        rewrite E1 in Sem1;
        rewrite E2 in Sem2;
        simpl in *;
        try (now apply (sem_imp_false));
        try (now apply (sem_and_false2));
        try (now constructor)
      ).
Qed.

Lemma wff_sem : forall f, wff f -> exists v, sem f v.
Proof.
  intros f wff_f.
  dependent induction wff_f;
    try (exists VFalse; now constructor);
    try now (
      (* Destruct KAnd. *)
      try destruct IHwff_f1 as [[] Sem1];
      try destruct IHwff_f2 as [[] Sem2];
      (* Destruct Kimp and KGuard. *)
      try (
        set (no_guard_sem f1 H) as Sem1;
        case_eq (no_guard_b f1 H);
        intros E1;
        rewrite E1 in Sem1;
        simpl in Sem1;
        destruct IHwff_f as [[] Sem2]
      );

      try (exists VTrue;  now constructor);
      try (exists VFalse; now constructor);
      try (exists VUndef; now constructor);

      (* Is there a tactic that checks all unifiable constructors? *)
      try (exists VUndef; now apply sem_and_true_undef);
      try (exists VUndef; now apply sem_and_undef_true);
      try (exists VFalse; now apply sem_and_false2);

      try (exists VTrue; now apply sem_imp_false);
      
      try (exists VUndef; now apply sem_guard_false)
    ).
Qed.

Lemma feq_ext_simpl : forall f1 f2 v, sem f1 v -> sem f2 v -> feq f1 f2.
Proof.
  intros f1 f2 v Sem1 Sem2.
  apply (feq_ext _ _ _ _ Sem1 Sem2).
  intros v'.
  split;
    intros Sem;
    try set (sem_inj _ _ _ Sem1 Sem);
    try set (sem_inj _ _ _ Sem2 Sem);
    congruence.
Qed.

Lemma feq_wff_simpl : forall f1 f2, wff f1 -> wff f2 -> (forall v, sem f1 v <-> sem f2 v) -> feq f1 f2.
Proof.
  intros f1 f2 wff_f1 wff_f2 fequiv.
  destruct (wff_sem f1 wff_f1) as [v1 Sem1].
  destruct (wff_sem f2 wff_f2) as [v2 Sem2].
  apply (feq_ext _ _ _ _ Sem1 Sem2 fequiv).
Qed.

Lemma feq_wff_refl : forall f, wff f -> feq f f.
Proof.
  intros f wff_f.
  destruct (wff_sem f wff_f) as [v Sem].
  apply (feq_ext_simpl _ _ _ Sem Sem).
Qed.

Lemma feq_wff_and_comm : forall f1 f2, wff f1 -> wff f2 -> feq (KAnd f1 f2) (KAnd f2 f1).
Proof.
  intros f1 f2 wff_f1 wff_f2.
  set (wff_and _ _ wff_f1 wff_f2) as wff_f12.
  set (wff_and _ _ wff_f2 wff_f1) as wff_f21.
  destruct (wff_sem (KAnd f1 f2) wff_f12) as [v12 Sem12].
  destruct (wff_sem (KAnd f2 f1) wff_f21) as [v21 Sem21].
  set (sem_and_comm _ _ _ Sem21) as Sem12'.
  rewrite (sem_inj _ _ _ Sem12 Sem12') in Sem12.
  apply (feq_ext_simpl _ _ _ Sem12 Sem21).
Qed.
