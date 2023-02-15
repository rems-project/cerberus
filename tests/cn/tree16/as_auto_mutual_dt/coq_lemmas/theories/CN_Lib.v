Require List.
Require Import ZArith Bool.
Open Scope Z.
Require Import Lia.
Require NArith.

Fixpoint nth_list_enc {A L_A : Type}
    (dest : L_A -> option (A * L_A)) (i : nat) (xs : L_A) (d : A) :=
  match i with
    | 0%nat => match dest xs with
      | None => d
      | Some (y, _) => y
    end
    | S j => match dest xs with
      | None => d
      | Some (_, ys) => nth_list_enc dest j ys d
    end
  end.

Definition nth_list_z {A L_A : Type}
    (dest : L_A -> option (A * L_A)) (i : Z) (xs : L_A) (d : A) :=
  if (i <? 0)%Z then d
  else nth_list_enc dest (Z.to_nat i) xs d.

Lemma nth_list_enc_nil:
  forall {A L_A} (nil_c : L_A) dest ix (d : A),
  (dest nil_c = None) ->
  nth_list_enc dest ix nil_c d = d.
Proof.
  intros.
  destruct ix; simpl; rewrite H; auto.
Qed.

Fixpoint array_to_list_enc {A L_A : Type}
    (nil_c : L_A) (cons_c : A -> L_A -> L_A)
    (arr : Z -> A) (i : Z) (n : nat) : L_A :=
  match n with
  | 0%nat => nil_c
  | S n2 => cons_c (arr i)
    (array_to_list_enc nil_c cons_c arr (i + 1) n2)
  end.

Definition array_to_list {A L_A : Type}
    (nil_c : L_A) (cons_c : A -> L_A -> L_A)
    arr i (n : Z) :=
    if (n <? 0)%Z then nil_c
    else array_to_list_enc nil_c cons_c arr i (Z.to_nat n).

Lemma succ_ltb_mono:
  forall i j,
  (S i <? S j)%nat = (i <? j)%nat.
Proof.
  intros.
  destruct (i <? j)%nat eqn: lt; destruct (S i <? S j)%nat eqn:S_lt.
  - auto.
  - rewrite Nat.ltb_lt in *; rewrite Nat.ltb_ge in *.
    lia.
  - rewrite Nat.ltb_lt in *; rewrite Nat.ltb_ge in *.
    lia.
  - auto.
Qed.

Lemma nth_list_enc_array_to_list_enc:
  forall {A L_A} (arr : Z -> A) nil_c (cons_c : A -> L_A -> L_A) dest,
  (dest nil_c = None) ->
  (forall y ys, dest (cons_c y ys) = Some (y, ys)) ->
  forall (i : Z) n ix d,
  nth_list_enc dest ix (array_to_list_enc nil_c cons_c arr i n) d =
  if (ix <? n)%nat
  then arr (i + Z.of_nat ix)
  else d.
Proof.
  intros until n.
  generalize i.
  induction n.
  - intros.
    auto using nth_list_enc_nil.
  - intros.
    simpl.
    destruct ix; simpl; rewrite H0.
    + f_equal.
      lia.
    + rewrite IHn.
      rewrite succ_ltb_mono.
      destruct (ix <? n)%nat; try reflexivity.
      f_equal.
      lia.
Qed.

Lemma array_to_list_nth_z:
  forall {A L_A} (arr : Z -> A) nil_c (cons_c : A -> L_A -> L_A) dest,
  (dest nil_c = None) ->
  (forall y ys, dest (cons_c y ys) = Some (y, ys)) ->
  forall (i : Z) n ix d,
  nth_list_z dest ix (array_to_list nil_c cons_c arr i n) d =
  if ((0 <=? ix) && (ix <? n))%Z
  then arr (i + ix)
  else d.
Proof.
  intros.
  unfold nth_list_z, array_to_list.
  rewrite Z.leb_antisym.
  destruct (ix <? 0) eqn: ix_lt0;
      destruct (n <? 0) eqn: n_lt0.
  - auto.
  - auto.
  - assert ((ix <? n) = false) as lt by lia.
    rewrite lt.
    auto using nth_list_enc_nil.
  - rewrite nth_list_enc_array_to_list_enc by auto.
    destruct (ix <? n) eqn: ix_lt; simpl.
    + assert ((Z.to_nat ix <? Z.to_nat n)%nat = true) as ix_lt2
        by (rewrite Nat.ltb_lt; lia).
      rewrite ix_lt2.
      f_equal.
      lia.
    + assert ((Z.to_nat ix <? Z.to_nat n)%nat = false) as ix_lt2
        by (rewrite Nat.ltb_ge; lia).
      rewrite ix_lt2.
      auto.
Qed.
