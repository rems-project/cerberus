Add LoadPath "../Vellvm/compcert".
Require Import Memory.
Require Import Values.
Require Import Coqlib.
Require Import Integers.
Require Import AST.
Require Import Znumtheory.

Module MoreMem.

Export Mem.

Transparent load alloc.

Definition meminj : Type := block -> option (block * Z).

(** A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection.  Moreover, [Vundef] values
  inject into any other value. *)

Inductive val_inject (mi: meminj): val -> val -> Prop :=
  | val_inject_int:
      forall wz i, val_inject mi (Vint wz i) (Vint wz i)
  | val_inject_float:
      forall f, val_inject mi (Vfloat f) (Vfloat f)
  | val_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta,
      mi b1 = Some (b2, delta) ->
      ofs2 = Int.add 31 ofs1 (Int.repr 31 delta) ->
      val_inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_inttoptr:
      forall i, val_inject mi (Vinttoptr i) (Vinttoptr i)
  | val_inject_undef: val_inject mi Vundef Vundef.

Hint Resolve val_inject_int val_inject_float val_inject_ptr val_inject_inttoptr 
             val_inject_undef.

Inductive val_list_inject (mi: meminj): list val -> list val-> Prop:= 
  | val_nil_inject :
      val_list_inject mi nil nil
  | val_cons_inject : forall v v' vl vl' , 
      val_inject mi v v' -> val_list_inject mi vl vl'->
      val_list_inject mi (v :: vl) (v' :: vl').  

Hint Resolve val_nil_inject val_cons_inject.

Lemma val_load_result_inject:
  forall f chunk v1 v2,
  val_inject f v1 v2 ->
  val_inject f (Val.load_result chunk v1) (Val.load_result chunk v2).
Proof.
  intros. inv H; destruct chunk; simpl; try econstructor; eauto.
    destruct (eq_nat_dec n 31); try econstructor; eauto.
    destruct (eq_nat_dec n 31); try econstructor; eauto.
Qed.

(** Monotone evolution of a memory injection. *)

Definition inject_incr (f1 f2: meminj) : Prop :=
  forall b b' delta, f1 b = Some(b', delta) -> f2 b = Some(b', delta).

Lemma inject_incr_refl :
   forall f , inject_incr f f .
Proof. unfold inject_incr. auto. Qed.

Lemma inject_incr_trans :
  forall f1 f2 f3, 
  inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 .
Proof .
  unfold inject_incr; intros. eauto. 
Qed.

Lemma val_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  val_inject f1 v v' ->
  val_inject f2 v v'.
Proof.
  intros. inv H0; eauto.
Qed.

Lemma val_list_inject_incr:
  forall f1 f2 vl vl' ,
  inject_incr f1 f2 -> val_list_inject f1 vl vl' ->
  val_list_inject f2 vl vl'.
Proof.
  induction vl; intros; inv H0. auto.
  constructor. eapply val_inject_incr; eauto. auto.
Qed.

Hint Resolve inject_incr_refl val_inject_incr val_list_inject_incr.

Inductive memval_inject (f: meminj): memval -> memval -> Prop :=
  | memval_inject_byte:
      forall wz n, memval_inject f (Byte wz n) (Byte wz n)
  | memval_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta n,
      f b1 = Some (b2, delta) ->
      ofs2 = Int.add 31 ofs1 (Int.repr 31 delta) ->
      memval_inject f (Pointer b1 ofs1 n) (Pointer b2 ofs2 n)
  | memval_inject_inttoptr:
      forall i n, memval_inject f (IPointer i n) (IPointer i n)
  | memval_inject_undef: memval_inject f Undef Undef.

Lemma memval_inject_incr: forall f f' v1 v2, 
  memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2.
Proof.
  intros. inv H; econstructor. rewrite (H0 _ _ _ H1). reflexivity. auto.
Qed.

Lemma proj_bytes_inject_some:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n bl,
  proj_bytes n vl = Some bl ->
  proj_bytes n vl' = Some bl.
Proof.
  induction 1; simpl. congruence.
  inv H; try congruence.

  intros.
  destruct (eq_nat_dec wz n0); auto.
  remember (proj_bytes n0 al) as R.
  destruct R.
    inv H. rewrite (IHlist_forall2 n0 l); auto.
    congruence.      
Qed.

Lemma proj_bytes_inject_none:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n,
  proj_bytes n vl = None ->
  proj_bytes n vl' = None.
Proof.
  induction 1; simpl. congruence.
  inv H; try congruence.

  intros.
  destruct (eq_nat_dec wz n0); auto.
  remember (proj_bytes n0 al) as R.
  destruct R.
    inv H. rewrite (IHlist_forall2 n0); auto.
Qed.

Lemma check_pointer_inject_true:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n b ofs b' delta,
  check_pointer n b ofs vl = true ->
  f b = Some(b', delta) ->
  check_pointer n b' (Int.add 31 ofs (Int.repr 31 delta)) vl' = true.
Proof.
  induction 1; intros; destruct n; simpl in *; auto.
  inv H; auto.
  destruct (andb_prop _ _ H1). destruct (andb_prop _ _ H).
  destruct (andb_prop _ _ H5).
  assert (n = n0) by (apply beq_nat_true; auto).
  assert (b = b0) by (eapply proj_sumbool_true; eauto).
  assert (ofs = ofs1) by (eapply proj_sumbool_true; eauto).
  subst. rewrite H3 in H2; inv H2.
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true.
  rewrite <- beq_nat_refl. simpl. eauto.
Qed.

Definition meminj_no_overlap (f: meminj) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2'.

Definition meminj_zero_delta (f: meminj) : Prop :=
  forall b b' delta, f b = Some(b', delta) -> delta = 0.

Lemma check_pointer_inject_false:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  meminj_no_overlap f ->
  meminj_zero_delta f ->
  forall n b ofs b' delta,
  check_pointer n b ofs vl = false ->
  f b = Some(b', delta) ->
  check_pointer n b' (Int.add 31 ofs (Int.repr 31 delta)) vl' = false.
Proof.
  induction 1; intros; destruct n; simpl in *; auto.
  inv H; auto.
  apply andb_false_elim in H3.
  destruct H3 as [H3 | H3].
    apply andb_false_elim in H3.
    destruct H3 as [H3 | H3].
      apply andb_false_elim in H3.
      destruct H3 as [H3 | H3].  
        apply andb_false_intro1.
        apply andb_false_intro1.
        apply andb_false_intro1.
        unfold eq_block in *.
        destruct (zeq b b0); subst; inv H3.
        unfold meminj_no_overlap in H1.
        eapply H1 in n1; eauto.
        destruct (zeq b' b2); subst; try solve [contradict n1; auto | auto].

        apply andb_false_intro1.
        apply andb_false_intro1.
        apply andb_false_intro2.
        apply H2 in H4. apply H2 in H5. subst.
        rewrite Int.add_zero. rewrite Int.add_zero. auto.
      apply andb_false_intro1.
      apply andb_false_intro2; auto.
    eauto using andb_false_intro2.
Qed.

Lemma check_ipointer_inject_true:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n i,
  check_ipointer n i vl = true ->
  check_ipointer n i vl' = true. 
Proof.
  induction 1; intros; destruct n; simpl in *; auto. 
  inv H; auto.

  destruct (andb_prop _ _ H1). destruct (andb_prop _ _ H).
  apply IHlist_forall2 in H2.
  congruence.
Qed.

Lemma check_ipointer_inject_false:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n i,
  check_ipointer n i vl = false ->
  check_ipointer n i vl' = false. 
Proof.
  induction 1; intros; destruct n; simpl in *; auto. 
  inv H; auto.

  apply andb_false_elim in H1.
  destruct H1; auto using andb_false_intro1.
    apply IHlist_forall2 in e.
    auto using andb_false_intro2.
Qed.

Lemma proj_ipointer_inject:
  forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (proj_ipointer vl1) (proj_ipointer vl2).
Proof.
  intros. unfold proj_ipointer.
  inversion H; subst. auto. inversion H0; subst; auto.
  case_eq (check_ipointer (size_chunk_nat Mint32) i 
             (IPointer i n :: al)); intros.
  exploit check_ipointer_inject_true. eexact H. eauto. eauto. 
  intro. rewrite H3. econstructor; eauto. 

  exploit check_ipointer_inject_false. eexact H. eauto. eauto. 
  intro. rewrite H3. econstructor; eauto. 
Qed.

Lemma proj_pointer_inject:
  forall f vl1 vl2,
  meminj_no_overlap f ->
  meminj_zero_delta f ->
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (proj_pointer vl1) (proj_pointer vl2).
Proof.
  intros f v11 v12 J1 J2 H. unfold proj_pointer.
  inversion H; subst. auto. inversion H0; subst; auto.
  case_eq (check_pointer (size_chunk_nat Mint32) b0 ofs1 
             (Pointer b0 ofs1 n :: al)); intros.

  exploit check_pointer_inject_true; eauto.
  intro. rewrite H4. econstructor; eauto. 

  exploit check_pointer_inject_false; eauto. 
  intro. rewrite H4. econstructor; eauto. 
Qed.

Lemma proj_bytes_not_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n,
  proj_bytes n vl = None -> proj_bytes n vl' <> None -> In Undef vl.
Proof.
  induction 1; simpl; intros.
    congruence.
    inv H; try congruence; auto.
    destruct (eq_nat_dec wz n); subst; auto.
      remember (proj_bytes n al) as R.
      remember (proj_bytes n bl) as R'.
      destruct R; destruct R';
        try solve [inversion H1 | inversion H2 | contradict H2; auto].
        right. eapply IHlist_forall2; eauto.
          rewrite <- HeqR'. intro. inversion H.          
      contradict H2; auto.
Qed.

Lemma proj_pointer_undef:
  forall vl, In Undef vl -> proj_pointer vl = Vundef.
Proof.
  intros; unfold proj_pointer.
  destruct vl; auto. destruct m; auto. 
  rewrite check_pointer_undef. auto. auto.
Qed.

Lemma proj_ipointer_undef:
  forall vl, In Undef vl -> proj_ipointer vl = Vundef.
Proof.
  intros; unfold proj_ipointer.
  destruct vl; auto. destruct m; auto. 
  rewrite check_ipointer_undef. auto. auto.
Qed.

Theorem decode_val_inject:
  forall f vl1 vl2 chunk,
  meminj_no_overlap f ->
  meminj_zero_delta f ->
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (decode_val chunk vl1) (decode_val chunk vl2).
Proof.
  intros f vl1 vl2 chunk JJ JJ2 H. unfold decode_val.
  case_eq (proj_bytes (wz_of_chunk chunk) vl1); intros.
    exploit proj_bytes_inject_some; eauto. intros. rewrite H1.
    destruct chunk; constructor.
 
    exploit proj_bytes_inject_none; eauto. intros. rewrite H1.
    destruct chunk; auto.
    destruct (eq_nat_dec n 31); subst; auto.
      assert (H2 := H).
      apply proj_pointer_inject in H2; auto.
      destruct (@proj_pointer_inv vl1) as [J1 | [b1 [ofs1 J1]]]; rewrite J1.
        rewrite J1 in H2. inv H2.
        apply proj_ipointer_inject; auto.

        rewrite J1 in H2. inv H2. eauto.
Qed.

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_access:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      valid_access m1 chunk b1 ofs p ->
      valid_access m2 chunk b2 (ofs + delta) p;
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Nonempty ->
      memval_inject f (m1.(mem_contents) b1 ofs) (m2.(mem_contents) b2 (ofs + delta))
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall f m1 m2 b1 ofs p b2 delta,
  mem_inj f m1 m2 ->
  perm m1 b1 ofs p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) p.
Proof.
  intros. 
  assert (valid_access m1 (Mint 7) b1 ofs p).
    split. red; intros. simpl in H2. rewrite bytesize_chunk_7_eq_1 in H2. replace ofs0 with ofs by omega. auto.
    simpl. apply Zone_divide.
  exploit mi_access; eauto. intros [A B].
  apply A. simpl; rewrite bytesize_chunk_7_eq_1; omega. 
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z_of_nat n) Readable ->
  list_forall2 (memval_inject f) 
               (getN n ofs (m1.(mem_contents) b1))
               (getN n (ofs + delta) (m2.(mem_contents) b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite inj_S in H1. 
  constructor. 
  eapply mi_memval; eauto.
  apply perm_implies with Readable.
  apply H1. omega. constructor. 
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega.
  apply IHn. red; intros; apply H1; omega. 
Qed.

Lemma load_inj:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  meminj_no_overlap f ->
  meminj_zero_delta f ->
  mem_inj f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject f v1 v2.
Proof.
  intros f m1 m2 chunk b1 ofs b2 delta v1 J1 J2 H H0 H1.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents) b2))).
  split. unfold load. apply pred_dec_true.  
  eapply mi_access; eauto with mem. 
  exploit load_result; eauto. intro. rewrite H2. 
  apply decode_val_inject; auto. apply getN_inj; auto. 
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. 
  intros [A B]. auto.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (c1 q) (c2 (q + delta))) ->
  (forall q, access q -> memval_inject f ((setN vl1 p c1) q) 
                                         ((setN vl2 (p + delta) c2) (q + delta))).
Proof.
  induction 1; intros; simpl. 
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by omega.
  apply IHlist_forall2; auto. 
  intros. unfold update at 1. destruct (zeq q0 p). subst q0.
  rewrite update_s. auto.
  rewrite update_o. auto. omega.
Qed.

Lemma inj_bytes_inject:
  forall f wz bl, 
    list_forall2 (memval_inject f) (inj_bytes wz bl) (inj_bytes wz bl).
Proof.
  induction bl; constructor; auto. constructor.
Qed.

Lemma repeat_Undef_inject_self:
  forall f n,
  list_forall2 (memval_inject f) (list_repeat n Undef) (list_repeat n Undef).
Proof.
  induction n; simpl; constructor; auto. constructor.
Qed.  

Theorem encode_val_inject:
  forall f v1 v2 chunk,
  val_inject f v1 v2 ->
  list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2).
Proof.
  intros. inv H; simpl.
    apply inj_bytes_inject.
    apply inj_bytes_inject.

    destruct chunk; try apply repeat_Undef_inject_self.
    destruct (eq_nat_dec n 31); subst; try apply repeat_Undef_inject_self.
      simpl; repeat econstructor; auto.

    destruct chunk; try apply repeat_Undef_inject_self.
    destruct (eq_nat_dec n 31); subst; try apply repeat_Undef_inject_self.
      unfold inj_ipointer; simpl; repeat econstructor; auto.

    destruct chunk; try apply repeat_Undef_inject_self.
Qed.

Lemma store_mapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  meminj_no_overlap f ->
  f b1 = Some (b2, delta) ->
  val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H. 
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply mi_access0; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE]. 
  exists n2; split. eauto.
  constructor.
(* access *)
  intros.
  eapply store_valid_access_1; [apply STORE |].
  eapply mi_access0; eauto.
  eapply store_valid_access_2; [apply H0 |]. auto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Nonempty). eapply perm_store_2; eauto. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  unfold update. 
  destruct (zeq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite zeq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Nonempty).
  apply encode_val_inject; auto. auto. auto. 
  destruct (zeq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros. 
  assert (b2 <> b2).
    eapply H1; eauto. 
  congruence.
  (* block <> b1, block <> b2 *)
  eauto.
Qed.

Lemma store_unmapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite update_o. eauto with mem. 
  congruence.
Qed.

Lemma store_outside_inj:
  forall f m1 m2 chunk b ofs v m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Nonempty ->
    ofs' + delta < ofs \/ ofs' + delta >= ofs + size_chunk chunk) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  unfold update. destruct (zeq b2 b). subst b2.
  rewrite setN_outside. auto. 
  rewrite encode_val_length. rewrite <- size_chunk_conv. 
  eapply H0; eauto. 
  eauto with mem.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* access *)
  intros. eauto with mem. 
(* mem_contents *)
  intros.
  assert (valid_access m2 (Mint 7) b0 (ofs + delta) Nonempty).
    eapply mi_access0; eauto.
    split. simpl. red; intros. rewrite bytesize_chunk_7_eq_1 in H3. assert (ofs0 = ofs) by omega. congruence.
    simpl. apply Zone_divide. 
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. rewrite update_o. eauto with mem.
  rewrite NEXT. apply sym_not_equal. eauto with mem. 
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Lemma free_right_inj:
  forall f m1 m2 b lo hi m2',
  mem_inj f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs p ->
    lo <= ofs + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* access *)
  intros. exploit mi_access0; eauto. intros [RG AL]. split; auto.
  red; intros. eapply perm_free_1; eauto. 
  destruct (zeq b2 b); auto. subst b. right.
  destruct (zlt ofs0 lo); auto. destruct (zle hi ofs0); auto.
  elimtype False. eapply H1 with (ofs := ofs0 - delta). eauto. 
  apply H3. omega. omega.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  specialize (mi_memval0 _ _ _ _ H2 H3).
  assert (b=b2 /\ lo <= ofs+delta < hi \/ (b<>b2 \/ ofs+delta<lo \/ hi <= ofs+delta)) by (unfold block; omega).
  destruct H4. destruct H4. subst b2.
  specialize (H1 _ _ _ _ H2 H3). elimtype False; auto.
  rewrite (clearN_out _ _ _ _ _ _ H4); auto.
Qed.

Lemma meminj_no_overlap_spec : forall f b1 b d1 b2 d2,
  meminj_no_overlap f -> f b1 = Some (b, d1) -> f b2 = Some (b, d2) ->
  b1 = b2 /\ d1 = d2.
Proof.
  intros.
  destruct (zeq b1 b2); subst.
    rewrite H1 in H0.
    inv H0. split; auto.

    elimtype False. unfold meminj_no_overlap in H.
    eapply H in n; eauto.
Qed.

Lemma free_inj:
  forall f m1 m2 b1 b2 delta lo hi m1' m2',
  meminj_no_overlap f ->
  meminj_zero_delta f ->
  mem_inj f m1 m2 ->
  free m1 b1 lo hi = Some m1' ->
  free m2 b2 (lo+delta) (hi+delta) = Some m2' ->
  f b1 = Some (b2, delta) ->
  mem_inj f m1' m2'.
Proof.
  intros f m1 m2 b1 b2 delta lo hi m1' m2' J J' H H0 H1 H2.
  exploit free_result; eauto. 
  intro FREE. inversion H. constructor.
(* access *)
  intros. exploit mi_access0; eauto with mem. 
  intros [RG AL]. split; auto.
  red; intros. eapply perm_free_1; eauto. 
  destruct (zeq b3 b2); auto. 
    subst b2. right.
    destruct (zlt ofs0 (lo + delta)); auto. 
    destruct (zle (hi + delta) ofs0); auto.
    destruct (@meminj_no_overlap_spec f b0 b3 delta0 b1 delta J H3 H2)
      as [G1 G2]; subst.
    assert (lo <= ofs0 - delta < hi) as J1.
      clear - z z0. auto with zarith.
    assert (ofs <= ofs0 - delta < ofs + size_chunk chunk) as J2.
      clear - H5. auto with zarith.
    destruct H4 as [H41 H42].
    apply H41 in J2.
    eapply perm_free_2 with (p:=p) in J1; eauto.
    congruence.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  assert (FREE':=H0). apply free_result in FREE'.
  rewrite FREE'; simpl.   
  assert (b0=b1 /\ lo <= ofs < hi \/ (b1<>b0 \/ ofs<lo \/ hi <= ofs)) as J1
    by (unfold block; omega).
  assert (b2=b3 /\ lo+delta <= ofs+delta < hi+delta \/ 
    (b2<>b3 \/ ofs+delta<lo+delta \/ hi+delta <= ofs+delta)) 
    as J2 by (unfold block; omega).
  destruct J1 as [J1 | J1].
    destruct J1 as [J11 J12]; subst.
    eapply perm_free_2 with (p:=Nonempty) in H0; eauto.
    congruence.

    rewrite (clearN_out _ _ _ _ _ _ J1).
    destruct J2 as [J2 | J2].
      destruct J2 as [J21 J22]; subst.
      destruct (@meminj_no_overlap_spec f b0 b3 delta0 b1 delta J H3 H2)
        as [G1 G2]; subst.
      assert (lo <= ofs < hi) as EQ.
        clear - J22. auto with zarith.
      clear - J1 EQ.
      destruct J1 as [J1 | J1]; try solve [congruence].
      contradict EQ; auto with zarith.

      assert (W1:=H2). apply J' in W1. subst.
      assert (W2:=H3). apply J' in W2. subst.
      rewrite (clearN_out _ _ _ _ _ _ J2).
      eapply perm_free_3 in H4; eauto.
Qed.

Global Opaque load alloc.

End MoreMem.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
