Require List.
Require Import ZArith Bool.
Open Scope Z.
Require Import Lia.
Require NArith.

Fixpoint dec_list {A L_A : Type}
    (dest : L_A -> option (A * L_A)) (xs : L_A) max_len :=
  match max_len with
    | 0%nat => List.nil
    | S i => match dest xs with
      | None => List.nil
      | Some (y, ys) => List.cons y (dec_list dest ys i)
    end
  end.

Fixpoint enc_list {A L_A : Type}
    (nil_c : L_A) (cons_c : A -> L_A -> L_A) xs :=
  match xs with
    | List.nil => nil_c
    | List.cons y ys => cons_c y (enc_list nil_c cons_c ys)
  end.

Definition nth_list_z {A L_A : Type}
    dest (i : Z) (xs : L_A) (d : A) :=
  if (i <? 0)%Z then d
  else List.nth (Z.to_nat i) (dec_list dest xs (S (Z.to_nat i))) d.

Definition array_to_list {A L_A : Type}
    (nil_c : L_A) (cons_c : A -> L_A -> L_A)
    arr i (n : Z) :=
  if (n <? 0)%Z then nil_c
  else enc_list nil_c cons_c (List.map (fun j => arr (i + (Z.of_nat j))) (List.seq 0 (Z.to_nat n))).

Lemma enc_list_dec_list:
  forall {A L_A} nil_c (cons_c : A -> L_A -> L_A) dest,
  (dest nil_c = None) ->
  (forall y ys, dest (cons_c y ys) = Some (y, ys)) ->
  forall xs max_len,
  dec_list dest (enc_list nil_c cons_c xs) max_len = List.firstn max_len xs.
Proof.
  intros until xs.
  induction xs; intros; destruct max_len.
  - auto.
  - simpl.
    rewrite H.
    reflexivity.
  - auto.
  - simpl.
    rewrite H0.
    simpl.
    rewrite IHxs.
    auto.
Qed.

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

Lemma nth_firstn:
  forall {A : Type} i j (xs : list A) d,
  List.nth i (List.firstn j xs) d =
  if (i <? j)%nat then List.nth i xs d else d.
Proof.
  intros until xs.
  generalize i, j.
  induction xs.
  - intros.
    destruct i0; destruct j0; simpl; try reflexivity.
    rewrite Tauto.if_same.
    reflexivity.
  - intros.
    destruct i0; destruct j0; simpl; try reflexivity.
    rewrite IHxs.
    rewrite succ_ltb_mono.
    reflexivity.
Qed.

Lemma nth_map_if_d2:
  forall {A B : Type} (d2 : A) i (f : A -> B) xs d,
  List.nth i (List.map f xs) d =
  if (i <? List.length xs)%nat then f (List.nth i xs d2) else d.
Proof.
  intros until i.
  induction i.
  - intros.
    destruct xs; auto.
  - intros.
    destruct xs; simpl; try reflexivity.
    rewrite IHi.
    rewrite succ_ltb_mono.
    reflexivity.
Qed.

Lemma array_to_list_nth_list:
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
  - simpl.
    rewrite H.
    assert ((ix <? n) = false) by lia.
    rewrite H1.
    assert (forall j, List.nth j nil d = d)
      by (intros; destruct j; auto).
    rewrite H2.
    auto.
  - rewrite enc_list_dec_list by auto.
    rewrite nth_firstn.
    assert (forall j, (j <? S j)%nat = true)
      by (intros; rewrite Nat.ltb_lt; lia).
    rewrite H1.
    rewrite (nth_map_if_d2 0%nat).
    rewrite List.seq_length.
    destruct (ix <? n) eqn: ix_lt_n.
    + assert ((Z.to_nat ix <? Z.to_nat n)%nat = true)
        by (rewrite Nat.ltb_lt; lia).
      rewrite H2.
      simpl.
      f_equal.
      rewrite List.seq_nth by lia.
      lia.
    + assert ((Z.to_nat ix <? Z.to_nat n)%nat = false)
        by (rewrite Nat.ltb_ge; lia).
      rewrite H2.
      auto.
Qed.

Definition wrapI (minInt : Z) (maxInt : Z) x :=
  let delta := (maxInt - minInt)%Z in
  let r := Z.modulo x delta in
  (if (r <=? maxInt) then r else r - delta)%Z.


