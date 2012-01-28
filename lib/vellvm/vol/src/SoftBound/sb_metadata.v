Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import vellvm.
Require Import genericvalues.
Require Import sb_def.

Ltac zauto := auto with zarith.

Tactic Notation "bdestruct" ident(H) "as" ident(J1) ident(J2) :=
     apply andb_true_iff in H; destruct H as [J1 J2].

Tactic Notation "bdestruct3" ident(H) "as" ident(J1) ident(J2) ident(J3) :=
     bdestruct H as H J3;
     bdestruct H as J1 J2.

Tactic Notation "bdestruct4" ident(H) "as" ident(J1) ident(J2) ident(J3) ident(J4) :=
     bdestruct3 H as H J3 J4;
     bdestruct H as J1 J2.

Tactic Notation "bdestruct5" ident(H) "as" ident(J1) ident(J2) ident(J3) ident(J4) ident(J5) :=
     bdestruct4 H as H J3 J4 J5;
     bdestruct H as J1 J2.

Ltac bdestructn H Js :=
  match Js with
  | nil => idtac
  | ?J::nil => rename H into J
  | ?J::?Js' => apply andb_true_iff in H; destruct H as [H J]; bdestructn H Js
  end.

Ltac bsplit :=
  eapply andb_true_iff; split.

Ltac repeat_bsplit :=
  repeat (bsplit; auto using eq_sumbool2bool_true).

Ltac zeauto := eauto with zarith.

Module SBspecMetadata. 

Export SBspec.

Section SBspecMetadata.

Context {GVsSig : GenericValues}.

(*****************************************)
(* misc *)

Lemma updateValuesForNewBlock_spec4 : forall rvs lc x rm lc' rm' md,
  lookupAL _ rm x = None ->
  (lc', rm') = @updateValuesForNewBlock GVsSig rvs lc rm ->
  lookupAL _ rm' x = Some md ->
  exists gv, In (x, gv, Some md) rvs.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' gv Hlk Hupdate Hlk'.
    inv Hupdate. rewrite Hlk in Hlk'. inversion Hlk'.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk'; auto.
        inv Hlk'. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [gv' HeqR]. 
        eauto.

      eapply IHrvs in HeqR; eauto.
      destruct HeqR as [gv' HeqR]. 
      eauto.
Qed.

Lemma updateValuesForNewBlock_spec6 : forall rvs lc x rm lc' rm' md,
  (lc', rm') = @updateValuesForNewBlock GVsSig rvs lc rm ->
  lookupAL _ rm' x = Some md ->
  lookupAL _ rm x = Some md \/
  exists id1, exists gv1, In (id1,gv1,Some md) rvs.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' md Hupdate Hlk.
    inv Hupdate. auto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md1 ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk. 
        inv Hlk. right. exists x. exists g. auto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [J1 | [id1 [gv1 HeqR]]]; auto.
          right. exists id1. exists gv1. auto.

     eapply IHrvs in HeqR; eauto.
     destruct HeqR as [J1 | [id1 [gv1 HeqR]]]; auto.
       right. exists id1. exists gv1. auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec : forall ps TD b gl lc id1
    rm re gv1 opmd1,
  Some re = @getIncomingValuesForBlockFromPHINodes GVsSig TD ps b gl lc rm ->
  In (id1, gv1, opmd1) re ->
  In id1 (getPhiNodesIDs ps).
Proof.    
  induction ps; intros; simpl in *.
    inv H. inversion H0.

    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); try solve [inversion H].   
    destruct (getOperandValue TD v lc gl); try solve [inversion H].   
    remember (getIncomingValuesForBlockFromPHINodes TD ps b gl lc rm) as R.
    destruct R; try solve [inv H].
    simpl.
    destruct (isPointerTypB t); inv H.
      destruct (get_reg_metadata TD gl rm v) as [[md mt]|]; inv H2.      
      simpl in H0.
      destruct H0 as [H0 | H0]; eauto.  
        inv H0; auto.

      simpl in H0.
      destruct H0 as [H0 | H0]; eauto.  
        inv H0; auto.
Qed.

Lemma updateValuesForNewBlock_spec1 : forall rvs lc x rm lc' rm' gv,
  lookupAL _ lc x = None ->
  (lc', rm') = @updateValuesForNewBlock GVsSig rvs lc rm ->
  lookupAL _ lc' x = Some gv ->
  exists omd, In (x, gv, omd) rvs.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' gv Hlk Hupdate Hlk'.
    inv Hupdate. rewrite Hlk in Hlk'. inversion Hlk'.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk'; auto.
        inv Hlk'. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [omd HeqR]. eauto.

      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk'; auto.
        inv Hlk'. eauto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
        eapply IHrvs in HeqR; eauto.
        destruct HeqR as [omd HeqR]. eauto.
Qed.

Lemma updateValuesForNewBlock_spec5 : forall rvs lc x rm lc' rm' md,
  lookupAL _ rm x = Some md ->
  (lc', rm') = @updateValuesForNewBlock GVsSig rvs lc rm ->
  exists md, lookupAL _ rm' x = Some md.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' md Hlk Hupdate.
    inv Hupdate; eauto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md1 ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq.
        eauto.

        rewrite <- lookupAL_updateAddAL_neq; auto.
        eapply IHrvs in HeqR; eauto.

      eapply IHrvs in HeqR; eauto.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall rvs lc x rm lc' rm' gvx md,
  In (x, gvx, Some md) rvs ->
  (lc', rm') = @updateValuesForNewBlock GVsSig rvs lc rm ->
  exists md, lookupAL _ rm' x = Some md.
Proof.
  induction rvs; simpl; intros lc x rm lc' rm' gvx md Hin Hupdate.
    inversion Hin.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs lc rm) as R.
    destruct R as [lc1 rm1].
    destruct o as [[md1 ?]|]; inv Hupdate.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq. eauto.

        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct Hin as [Hin | Hin].
          inv Hin. contradict n; auto.
          eapply IHrvs in HeqR; eauto.

      destruct Hin as [Hin | Hin].
        inv Hin. 
        eapply IHrvs in HeqR; eauto.
Qed.

Lemma initializeFrameValues_spec1 : forall TD la lc1 rm1 x md lc2 rm2,
  lookupAL _ rm1 x = Some md ->
  Some (lc2, rm2) = @_initializeFrameValues GVsSig TD la nil lc1 rm1 ->
  exists md, lookupAL _ rm2 x = Some md.
Proof.
  induction la; simpl; intros lc1 rm1 x md lc2 rm2 Hlk Hinit.  
    inv Hinit. eauto.

    destruct a. destruct p.
    remember (_initializeFrameValues TD la nil lc1 rm1) as R.
    destruct R as [[lc1' rm1']|]; tinv Hinit.
    destruct (gundef TD t); tinv Hinit.
    destruct (isPointerTypB t); inv Hinit; eauto.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq; eauto.
        rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma initializeFrameValues_spec3 : forall TD la lc x rm lc' rm' md,
  Some (lc', rm') = @_initializeFrameValues GVsSig TD la nil lc rm ->
  lookupAL _ rm' x = Some md ->
  lookupAL _ rm x = Some md \/
  md = null_md.
Proof.
  induction la; simpl; intros.
    inv H. auto.

    destruct a. destruct p.
    remember (_initializeFrameValues TD la nil lc rm) as R.
    destruct R as [[lc1 rm1]|]; tinv H.
    destruct (gundef TD t); tinv H.
    destruct (isPointerTypB t); inv H.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in H0. 
        inv H0. auto.
      
        rewrite <- lookupAL_updateAddAL_neq in H0; auto.
        eapply IHla in HeqR; eauto. 
      eapply IHla in HeqR; eauto. 
Qed.

Lemma initializeFrameValues_spec2 : forall TD la ogvs lc x rm lc' rm' md,
  Some (lc', rm') = @_initializeFrameValues GVsSig TD la ogvs lc rm ->
  lookupAL _ rm' x = Some md ->
  lookupAL _ rm x = Some md \/
  md = null_md \/
  exists gv1, In (gv1,Some md) ogvs.
Proof.
  induction la; simpl; intros ogvs lc x rm lc' rm' md Hinit Hlk.
    inv Hinit. auto.

    destruct a. destruct p.
    destruct ogvs.
      remember (_initializeFrameValues TD la nil lc rm) as R.
      destruct R as [[lc1 rm1]|]; tinv Hinit.
      destruct (gundef TD t); tinv Hinit.
      destruct (isPointerTypB t); inv Hinit.
        destruct (eq_atom_dec i0 x); subst.
          rewrite lookupAL_updateAddAL_eq in Hlk. 
          inv Hlk. auto.

          rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
          eapply initializeFrameValues_spec3 in HeqR; eauto.
          destruct HeqR; auto.
        eapply initializeFrameValues_spec3 in HeqR; eauto.
        destruct HeqR; auto.

      destruct p.
      remember (_initializeFrameValues TD la ogvs lc rm) as R.
      destruct R as [[lc1 rm1]|]; tinv Hinit.
      destruct (lift_op1 GVsSig (fit_gv TD t) g t); tinv Hinit.
      destruct (isPointerTypB t); inv Hinit.
        destruct o as [[md1 ?]|]; inv H0.
          destruct (eq_atom_dec i0 x); subst.
            rewrite lookupAL_updateAddAL_eq in Hlk. 
            inv Hlk. right. right. exists g. simpl. auto.

            rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
            eapply IHla in HeqR; eauto.
            destruct HeqR as [HeqR | [HeqR | [gv1 HeqR]]]; auto.
              right. right. exists gv1. simpl. auto.

          destruct (eq_atom_dec i0 x); subst.
            rewrite lookupAL_updateAddAL_eq in Hlk. 
            inv Hlk. auto.

            rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
            eapply IHla in HeqR; eauto.
            destruct HeqR as [HeqR | [HeqR | [gv1 HeqR]]]; auto.
              right. right. exists gv1. simpl. auto.

        eapply IHla in HeqR; eauto.
        destruct HeqR as [HeqR | [HeqR | [gv1 HeqR]]]; auto.
          right. right. exists gv1. simpl. auto.
Qed.

Notation "$ gv # t $" := (GVsSig.(gv2gvs) gv t) (at level 41).

Lemma initLocals_spec : forall TD la gvs id1 lc rm,
  In id1 (getArgsIDs la) ->
  @initLocals GVsSig TD la gvs = Some (lc, rm) ->
  exists gv, lookupAL _ lc id1 = Some gv.
Proof.
  unfold initLocals.
  induction la; intros; simpl in *.
    inversion H.

    destruct a as [[t c] id0].  
    simpl in H.
    destruct H as [H | H]; subst; simpl.
      destruct gvs. 
        remember (@_initializeFrameValues GVsSig TD la nil nil nil) as R1.
        destruct R1 as [[lc' rm']|]; tinv H0.
        remember (gundef TD t) as R2.
        destruct R2; inv H0.
        destruct (isPointerTypB t); inv H1;
          exists ($ g # t $); apply lookupAL_updateAddAL_eq; auto.      

        destruct p.
        remember (_initializeFrameValues TD la gvs nil nil) as R1.
        destruct R1 as [[lc' rm']|]; tinv H0.
        remember (lift_op1 GVsSig (fit_gv TD t) g t) as R2.
        destruct R2 as [g0|]; inv H0.
        assert (lc = updateAddAL _ lc' id1 g0) as EQ.
          destruct (isPointerTypB t); inv H1; auto.
          destruct o; inv H0; auto.
        subst. exists g0. apply lookupAL_updateAddAL_eq; auto. 

      destruct (eq_atom_dec id0 id1); subst.
        destruct gvs.
          remember (@_initializeFrameValues GVsSig TD la nil nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          destruct (isPointerTypB t); inv H2;
            exists ($ g # t $); apply lookupAL_updateAddAL_eq; auto.      

          destruct p.
          remember (_initializeFrameValues TD la gvs nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          remember (lift_op1 GVsSig (fit_gv TD t) g t) as R2.
          destruct R2 as [g0|]; inv H0.
          assert (lc = updateAddAL _ lc' id1 g0) as EQ.
            destruct (isPointerTypB t); inv H2; auto.
            destruct o; inv H1; auto.
          subst. exists g0. apply lookupAL_updateAddAL_eq; auto. 

        destruct gvs.
          remember (@_initializeFrameValues GVsSig TD la nil nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          destruct (isPointerTypB t); inv H2;
            exists gv; rewrite <- lookupAL_updateAddAL_neq; auto.

          destruct p.
          remember (_initializeFrameValues TD la gvs nil nil) as R1.
          destruct R1 as [[lc' rm']|]; tinv H0.
          remember (lift_op1 GVsSig (fit_gv TD t) g t) as R2.
          destruct R2 as [g0|]; inv H0.
          assert (lc = updateAddAL _ lc' id0 g0) as EQ.
            destruct (isPointerTypB t); inv H2; auto.
            destruct o; inv H1; auto.
          subst.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          exists gv. rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

(*****************************************)
(* wf_data *)

Definition blk_temporal_safe M b : Prop :=
let (lo, _) := Mem.bounds M b in
Mem.perm M b lo Nonempty.

Definition wf_data (TD:TargetData) (M:mem) blk bofs eofs : Prop :=
  blk < Mem.nextblock M /\
  (blk_temporal_safe M blk ->
   Mem.range_perm M blk (Int.signed 31 bofs) (Int.signed 31 eofs) Writable).

Definition wf_rmetadata (TD:TargetData) (M:mem) (rm:rmetadata) : Prop :=
  forall (i:id) blk bofs eofs,
    lookupAL _ rm i = Some (mkMD blk bofs eofs) -> wf_data TD M blk bofs eofs.

Definition wf_mmetadata (TD:TargetData) (M:mem) (MM:mmetadata) : Prop :=
  forall (b:Values.block) (ofs:int32) blk bofs eofs,
    MM b ofs = Some (mkMD blk bofs eofs) -> wf_data TD M blk bofs eofs.

Definition wf_metadata (TD:TargetData) (M:mem) (rm:rmetadata) (MM:mmetadata) 
    : Prop :=
  wf_rmetadata TD M rm /\ wf_mmetadata TD M MM.

Definition wf_global_ptr S TD Mem0 gl : Prop :=
  forall id0 gv0 typ0, lookupAL GenericValue gl id0 = Some gv0 ->
  wf_const S TD (const_gid typ0 id0) (typ_pointer typ0) ->
  exists b, exists sz,
    gv0 = (Vptr b (Int.zero 31), AST.Mint 31)::nil /\
    getTypeAllocSize TD typ0 = Some sz /\
    Mem.bounds Mem0 b = (0, Z_of_nat sz) /\
    b < Mem.nextblock Mem0 /\
    (blk_temporal_safe Mem0 b -> Mem.range_perm Mem0 b 0 (Z_of_nat sz) Writable).

(***********************************************)
(* axiom *)

Axiom callExternalFunction_mem_bounds : forall Mem0 fid gvs oresult Mem' b,
  callExternalFunction Mem0 fid gvs = Some (oresult, Mem') ->
  Mem.bounds Mem0 b = Mem.bounds Mem' b.

Axiom callExternalFunction_temporal_prop : forall Mem0 fid gvs oresult Mem' base
    bound b,
  callExternalFunction Mem0 fid gvs = Some (oresult, Mem') ->
  b < Mem.nextblock Mem0 /\
  (blk_temporal_safe Mem0 b -> Mem.range_perm Mem0 b base bound Writable) ->
  b < Mem.nextblock Mem' /\
  (blk_temporal_safe Mem' b -> Mem.range_perm Mem' b base bound Writable).

(***********************************************)
(* dec *)

Lemma assert_mptr_dec : forall TD t ptr md,
  assert_mptr TD t ptr md \/ ~ assert_mptr TD t ptr md.
Proof.
  intros.
  unfold is_true. 
  destruct (assert_mptr TD t ptr md); auto.
Qed.

Lemma blk_temporal_safe_dec : forall M b,
  {blk_temporal_safe M b} + {~ blk_temporal_safe M b}.
Proof.
  intros M b.
  unfold blk_temporal_safe.
  destruct (Mem.bounds M b).
  apply Mem.perm_dec.
Qed.

Lemma valid_block_dec : forall M b,
  {Mem.valid_block M b} + { ~ Mem.valid_block M b}.
Proof.
  intros M b.
  unfold Mem.valid_block.
  apply Z_lt_dec; auto.
Qed.  

(***********************************************)
(* temoporal_prop *)

Lemma blk_temporal_safe_store_1 : forall m Mem0 b ofs0 v0 Mem' b0,
  Mem.store m Mem0 b ofs0 v0 = Some Mem' ->
  blk_temporal_safe Mem0 b0 ->
  blk_temporal_safe Mem' b0.
Proof.
  intros m Mem0 b ofs0 v0 Mem' b0 Hstore H.
  unfold blk_temporal_safe in *.
  assert (J:=Hstore).
  apply Mem.bounds_store with (b':=b0) in J.
  rewrite J.
  destruct (Mem.bounds Mem0 b0).
  eapply Mem.perm_store_1 in H; eauto.  
Qed.

Lemma blk_temporal_safe_store_2 : forall m Mem0 b ofs0 v0 Mem' b0,
  Mem.store m Mem0 b ofs0 v0 = Some Mem' ->
  blk_temporal_safe Mem' b0 ->
  blk_temporal_safe Mem0 b0. 
Proof.
  intros m Mem0 b ofs0 v0 Mem' b0 Hstore H.
  unfold blk_temporal_safe in *.
  assert (J:=Hstore).
  apply Mem.bounds_store with (b':=b0) in J.
  rewrite <- J.
  destruct (Mem.bounds Mem' b0).
  eapply Mem.perm_store_2 in H; eauto.  
Qed.

Lemma store_preserves_temoporal_prop : forall m Mem0 b b1 ofs0 v0 Mem' i0 i1
  (H1 : Mem.store m Mem0 b ofs0 v0 = Some Mem')
  (J : b1 < Mem.nextblock Mem0 /\
      (blk_temporal_safe Mem0 b1 ->
       Mem.range_perm Mem0 b1 i0 i1 Writable)),
  b1 < Mem.nextblock Mem' /\
   (blk_temporal_safe Mem' b1 ->
    Mem.range_perm Mem' b1 i0 i1 Writable).
Proof.
  intros.
    destruct J as [J1 J2].
    split.
      apply Mem.nextblock_store in H1.
      rewrite H1. auto.

      intro H.
      eapply blk_temporal_safe_store_2 in H; eauto.
      apply J2 in H.
      eauto using Mem.store_range_perm_1.
Qed.

Lemma store_aux_preserves_temoporal_prop : forall b1 i0 i1 b gv ofs Mem0 Mem' 
  (H1 : mstore_aux Mem0 gv b ofs = ret Mem')
  (J : b1 < Mem.nextblock Mem0 /\
      (blk_temporal_safe Mem0 b1 ->
       Mem.range_perm Mem0 b1 i0 i1 Writable)),
  b1 < Mem.nextblock Mem' /\
   (blk_temporal_safe Mem' b1 ->
    Mem.range_perm Mem' b1 i0 i1 Writable).
Proof.
  induction gv; simpl; intros.
    inv H1; auto.

    destruct a.
    remember (Mem.store m Mem0 b ofs v) as R.
    destruct R as [M' | ]; tinv H1.  
    apply IHgv with (Mem0:=M')(ofs:=ofs + size_chunk m); auto.
    eapply store_preserves_temoporal_prop; eauto.
Qed.

Lemma free_preserves_temporal_prop : forall (Mem0 Mem' : mem) (b : Values.block)
  (z z0 : Z) (HeqR : (z, z0) = Mem.bounds Mem0 b)
  (H0 : Mem.free Mem0 b z z0 = ret Mem')
  (i0 : Z) (b1 : Values.block) (i1 : Z)
  (J2 : b1 < Mem.nextblock Mem0 /\ 
        (blk_temporal_safe Mem0 b1 -> Mem.range_perm Mem0 b1 i0 i1 Writable)),
  b1 < Mem.nextblock Mem' /\
  (blk_temporal_safe Mem' b1 -> Mem.range_perm Mem' b1 i0 i1 Writable).
Proof.
  intros. 
  destruct J2 as [J2 J3].
  split.
      apply Mem.nextblock_free in H0.
      rewrite H0. auto.

      intro Hwfb.
      unfold blk_temporal_safe in *.
      erewrite Mem.bounds_free in Hwfb; eauto.
      assert (Hfree:=H0).
      destruct (Values.eq_block b b1); subst.
        rewrite <- HeqR in Hwfb.
        destruct (Z_lt_dec z z0).
          apply Mem.perm_free_2 with (ofs:=z)(p:=Nonempty) in H0; 
            zeauto.
          contradict Hwfb; auto.

          rewrite <- HeqR in J3.   
          eapply Mem.perm_free_3 in Hwfb; eauto.
          apply J3 in Hwfb. clear J3.
          unfold Mem.range_perm in *.
          intros ofs J. apply Hwfb in J.
          apply Mem.perm_free_1 with (b:=b1)(ofs:=ofs)(p:=Writable) in H0; auto.
            clear - n.
            destruct (Z_lt_dec ofs z); auto.
            destruct (Z_le_dec z0 ofs); auto.
            assert (False) as H. zeauto. 
            inversion H.

       destruct (Mem.bounds Mem0 b1).
       eapply Mem.perm_free_3 in Hwfb; eauto.
       apply J3 in Hwfb. clear J3.
       unfold Mem.range_perm in *.
       intros ofs J. apply Hwfb in J.
        apply Mem.perm_free_1 with (b:=b1)(ofs:=ofs)(p:=Writable) in H0;
          zeauto.
Qed.     

Lemma blk_temporal_alloc_inv : forall Mem0 lo hi Mem' mb b0,
  Mem.alloc Mem0 lo hi = (Mem', mb) ->
  blk_temporal_safe Mem' b0 ->
  (if Values.eq_block b0 mb then 
    Mem.bounds Mem' b0 = (lo, hi)
  else blk_temporal_safe Mem0 b0).
Proof.
  intros.
  unfold blk_temporal_safe in *.
  assert (Halloc := H).  
  apply Mem.bounds_alloc with (b':=b0) in H.
  destruct (Values.eq_block b0 mb); subst; auto.
    rewrite <- H.
    destruct (Mem.bounds Mem' b0).
    apply Mem.perm_alloc_inv with (b':=b0)(ofs:=z)(p:=Nonempty) in Halloc; auto.
    destruct (zeq b0 mb); auto.
      subst. contradict n; auto.
Qed.

Lemma alloc_preserves_temporal_prop : forall Mem0 sz Mem' mb
  (H4 : Mem.alloc Mem0 0 sz = (Mem', mb))
  (i0 : Z) (b0 : Values.block) (i1 : Z)
  (J' : b0 < Mem.nextblock Mem0 /\ 
        (blk_temporal_safe Mem0 b0 -> Mem.range_perm Mem0 b0 i0 i1 Writable)),
  b0 < Mem.nextblock Mem' /\
  (blk_temporal_safe Mem' b0 -> Mem.range_perm Mem' b0 i0 i1 Writable).
Proof.
  intros.
  destruct J' as [J1' J2'].
  split.
    apply Mem.nextblock_alloc in H4.
    rewrite H4. zauto.

    intro Hwfb.
    assert (Halloc := H4).
    eapply blk_temporal_alloc_inv in H4; eauto.         
    destruct (Values.eq_block b0 mb); subst.
      apply Mem.alloc_result in Halloc.    
      rewrite <- Halloc in J1'.
      contradict J1'; zauto.
      
      apply J2' in H4.
      eauto using Mem.range_perm_alloc_other.
Qed.

(***********************************************)
(* wf_data *)

Lemma wf_mmetadata__wf_data : forall Mem0 TD MM b0 ofs blk bofs eofs,
  wf_mmetadata TD Mem0 MM ->
  MM b0 ofs = Some (mkMD blk bofs eofs) ->
  wf_data TD Mem0 blk bofs eofs.
Proof.
  intros Mem0 TD MM b0 ofs blk bofs eofs Hwfm J.
  apply Hwfm in J; auto.
Qed.

Lemma wf_data__store__wf_data : forall m Mem0 b ofs0 v0 Mem' TD blk bofs eofs,
  Mem.store m Mem0 b ofs0 v0 = Some Mem' ->
  wf_data TD Mem0 blk bofs eofs ->
  wf_data TD Mem' blk bofs eofs.
Proof.
  intros m Mem0 b ofs0 v0 Mem' TD blk bofs eofs H1 J.
  unfold wf_data in *.
  eapply store_preserves_temoporal_prop; eauto.
Qed.

Lemma wf_data__store_aux__wf_data : forall TD blk bofs eofs b gv ofs Mem0 Mem',
  mstore_aux Mem0 gv b ofs = ret Mem' ->
  wf_data TD Mem0 blk bofs eofs ->
  wf_data TD Mem' blk bofs eofs.
Proof.
  intros TD blk bofs eofs b gv ofs Mem0 Mem' H1 J.
  unfold wf_data in *.
  eapply store_aux_preserves_temoporal_prop; eauto.
Qed.

Lemma wf_mmetadata__store__wf_data : forall m Mem0 b ofs0 v0 Mem' TD MM b0 ofs 
     blk bofs eofs,
  Mem.store m Mem0 b ofs0 v0 = Some Mem' ->
  wf_mmetadata TD Mem0 MM ->
  MM b0 ofs = Some (mkMD blk bofs eofs) ->
  wf_data TD Mem' blk bofs eofs.
Proof.
  intros m Mem0 b ofs0 v0 Mem' TD MM b0 ofs blk bofs eofs H1 Hwfm J.
  apply wf_mmetadata__wf_data with (Mem0:=Mem0)(TD:=TD) in J; eauto.
  eapply wf_data__store__wf_data; eauto.
Qed.

Lemma wf_mmetadata__store_aux__wf_data : forall Mem0 b ofs0 gv Mem' TD MM b0 
    ofs blk bofs eofs,
  mstore_aux Mem0 gv b ofs = ret Mem' ->
  wf_mmetadata TD Mem0 MM ->
  MM b0 ofs0 = Some (mkMD blk bofs eofs) ->
  wf_data TD Mem' blk bofs eofs.
Proof.
  intros Mem0 b ofs0 gv Mem' TD MM b0 ofs blk bofs eofs H1 Hwfm J.
  apply wf_mmetadata__wf_data with (Mem0:=Mem0)(TD:=TD) in J; eauto.
  eapply wf_data__store_aux__wf_data; eauto.
Qed.

Lemma GV2ptr__cgv2gv : forall TD sz g b ofs t, 
  GV2ptr TD sz g = ret (Vptr b ofs) -> g = ? g # typ_pointer t ?.
Proof.
  intros TD sz g b ofs t J1.
  unfold GV2ptr in J1.    
  destruct g as [|[[] ?][|]]; inv J1.
  simpl. auto.
Qed.

Lemma get_const_metadata_gid__wf_data : forall S TD Mem0 gl t i0 bblk bofs eofs 
    bm em,
  wf_global_ptr S TD Mem0 gl ->
  wf_const S TD (const_gid t i0) (typ_pointer t) ->
  LLVMgv.const2GV TD gl (const_castop castop_bitcast (const_gid t i0) p8) = 
    ret ((Vptr bblk bofs, bm)::nil) ->
  LLVMgv.const2GV TD gl 
       (const_castop castop_bitcast
         (const_gep false (const_gid t i0)
            (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const)) p8)
    = ret ((Vptr bblk eofs, em)::nil) ->
  wf_data TD Mem0 bblk bofs eofs.
Proof.
  intros S TD Mem0 gl t i0 bblk bofs eofs bm em Hwfg Hwfc H2 H3.
  unfold LLVMgv.const2GV in H3.
  remember (_const2GV TD gl 
    (const_castop castop_bitcast
      (const_gep false (const_gid t i0)
        (Cons_list_const (const_int Size.ThirtyTwo 1) Nil_list_const)) p8))
    as R0.
  simpl in HeqR0.
  destruct R0 as [[gv ?]|]; inv H3.
  unfold LLVMgv.const2GV in H2.
  remember (_const2GV TD gl (const_castop castop_bitcast (const_gid t i0) p8)) 
    as R1.
  destruct R1 as [[gv' ?]|]; inv H2.
  unfold _const2GV in *.
  unfold mcast, mbitcast, p8 in *.
  remember (lookupAL GenericValue gl i0) as R'.
  destruct R'; try solve [inversion HeqR0].
  inv HeqR1.
  assert (exists b, exists sz,
    g = (Values.Vptr b (Int.zero 31), AST.Mint 31)::nil /\
    getTypeAllocSize TD t = Some sz /\
    Mem.bounds Mem0 b = (0, Z_of_nat sz) /\
    b < Mem.nextblock Mem0 /\
    (blk_temporal_safe Mem0 b -> Mem.range_perm Mem0 b 0 (Z_of_nat sz) Writable))
    as J.
    eapply Hwfg; eauto.
  destruct J as [b [sz [J1 [J2 [J3 [J4 J5]]]]]]; subst.
  simpl in HeqR0.
  unfold mgetoffset in HeqR0.
  destruct TD. simpl in HeqR0.
(*
  assert (exists ut2, Constant.typ2utyp l1 (typ_array 0%nat t) = 
    Some (typ_array 0%nat ut2) /\
    getTypeAllocSize (l0, l1) ut2 = getTypeAllocSize (l0, l1) t) as J.
    clear - Hwfc. inv Hwfc. 
    unfold Constant.unifiable_typ in H5.
    destruct H5 as [ut [H5 H6]].
    unfold Constant.typ2utyp in *.
    simpl. rewrite H5. simpl. rewrite <- H6. eauto.
  destruct J as [ut2 [J6 J7]].
  rewrite J6 in HeqR0. simpl in HeqR0.
  rewrite J7 in HeqR0. rewrite J2 in HeqR0. simpl in HeqR0.
*)
  rewrite J2 in HeqR0. simpl in HeqR0.
  inv HeqR0. unfold ptr2GV, val2GV in H0. simpl in H0. inv H0.
  inv H1.
  unfold wf_data.
  split; auto.  
    intro Htmp.
    apply J5 in Htmp.
    rewrite (Int.add_commut 31).
    rewrite (Int.add_zero 31).
    unfold INTEGER.to_Z. 
    assert (Z_of_nat sz * 1 = Z_of_nat sz) as EQ. zauto.
    rewrite EQ.
    intros z Hz.
    apply Htmp.
    assert (J:=@Int.signed_repr_ge_0 31 (Z_of_nat sz) (Z_of_nat_ge_0 sz)).
    rewrite (Int.signed_zero 31) in Hz.
    zauto.
Qed.

Lemma eq_gv_is_wf_data : forall TD Mem bb bofs,
  bb < Mem.nextblock Mem ->
  wf_data TD Mem bb bofs bofs.
Proof.
  intros TD Mem bb bofs H0.
  unfold wf_data.
  split; auto.
    intros Hwfb ofs J.
    contradict J; zauto.
Qed.

Lemma nullptr_lt_nextblock : forall Mem0,
  Mem.nullptr < Mem.nextblock Mem0.
Proof.
  intros.
  assert (J:=@Mem.nextblock_pos Mem0).
  unfold Mem.nullptr.
  zauto.
Qed.

Lemma null_is_wf_data : forall TD Mem blk bofs efs,
  null_md = mkMD blk bofs efs ->
  wf_data TD Mem blk bofs efs.
Proof.
  intros TD Mem blk bofs efs H.
  inv H.
  eapply eq_gv_is_wf_data with (bb:=Mem.nullptr).
    apply nullptr_lt_nextblock.
Qed.

Lemma wf_rmetadata__get_const_metadata : forall S TD gl Mem0 rm c blk bofs eofs 
    c0 c1 ct' bm em,
  wf_global_ptr S TD Mem0 gl ->
  wf_const S TD c ct' ->
  wf_rmetadata TD Mem0 rm ->
  get_const_metadata c = Some (c0,c1) ->
  LLVMgv.const2GV TD gl c0 = Some ((Vptr blk bofs, bm)::nil) ->
  LLVMgv.const2GV TD gl c1 = Some ((Vptr blk eofs, em)::nil) ->
  wf_data TD Mem0 blk bofs eofs.
Proof.
  induction c; intros blk bofs eofs cc0 cc1 ct' bm em Hwfg Hwfc Hwfr H1 H2 H3; 
    try solve [inversion H1].

  inv Hwfc.
  destruct t; inv H1; 
    try solve [ 
      eapply get_const_metadata_gid__wf_data; eauto using wf_const_gid
    ].

    unfold LLVMgv.const2GV in H2, H3.
    remember (_const2GV TD gl (const_castop castop_bitcast (const_gid 
      (typ_function t l0 v) i0) p8)) as R.
    destruct R; try solve [inversion H2 | inversion H3].
    destruct p. inv H2. inv H3.
    unfold GV2ptr.
    unfold _const2GV in HeqR.
    remember (lookupAL GenericValue gl i0) as R1.
    destruct R1; inv HeqR.
    assert (exists b, exists sz,
      g0 = (Values.Vptr b (Int.zero 31), AST.Mint 31)::nil /\
      getTypeAllocSize TD (typ_function t l0 v) = Some sz /\
      Mem.bounds Mem0 b = (0, Z_of_nat sz) /\
      b < Mem.nextblock Mem0 /\
      (blk_temporal_safe Mem0 b -> Mem.range_perm Mem0 b 0 (Z_of_nat sz) Writable))
      as J.
      eapply Hwfg; eauto using wf_const_gid.
    destruct J as [b [sz [J1 [J2 [J3 [J4 J5]]]]]]; subst.
    unfold p8 in *.
    rewrite H0 in H1. inv H1. inv H0.
    eapply eq_gv_is_wf_data; eauto.

  simpl in H1.
  destruct c; try solve [inversion H1].
  destruct t; try solve [inversion H1].
  inv Hwfc.
  eapply IHc; eauto.
     
  inv Hwfc.
  simpl in H1; eauto.
Qed.

Lemma get_reg_metadata_const_inv : forall TD gl rm c blk bofs eofs,
  get_reg_metadata TD gl rm (value_const c) =
      ret {| md_blk := blk; md_bofs := bofs; md_eofs := eofs |} ->
  (get_const_metadata c = None /\
   {| md_blk := blk; md_bofs := bofs; md_eofs := eofs |} = null_md) \/
  exists bc, exists ec,
    get_const_metadata c = Some (bc, ec) /\
    LLVMgv.const2GV TD gl bc = Some ((Vptr blk bofs, AST.Mint 31)::nil) /\
    LLVMgv.const2GV TD gl ec = Some ((Vptr blk eofs, AST.Mint 31)::nil).
Proof.
  intros TD gl rm c blk bofs eofs J. 
  unfold get_reg_metadata in J.
  remember (get_const_metadata c) as R.
  destruct R as [[bc ec] |]; try solve [inversion J; subst; auto].
  remember (LLVMgv.const2GV TD gl bc) as R0.
  remember (LLVMgv.const2GV TD gl ec) as R1.
  destruct R0; try solve [inversion J]. 
  destruct g as [|[]]; tinv J.
  destruct v; tinv J.
  destruct m; tinv J.
  destruct g as [|[]]; tinv J.
  destruct R1; tinv J. 
  destruct g as [|[]]; tinv J.
  destruct v; tinv J.
  destruct m; tinv J.
  destruct g as [|[]]; tinv J.
  destruct (zeq b b0); tinv J.
  destruct (eq_nat_dec n 31); tinv J.
  destruct (eq_nat_dec n0 31); inv J.
  subst. right. exists bc. exists ec. eauto.
Qed.

Lemma wf_rmetadata__get_reg_metadata : forall S los nts Ps Mem0 rm gl vp blk bofs
    eofs f tp,
  wf_global_ptr S (los, nts) Mem0 gl ->
  wf_rmetadata (los, nts) Mem0 rm ->
  wf_value S (module_intro los nts Ps) f vp tp ->
  get_reg_metadata (los, nts) gl rm vp = Some (mkMD blk bofs eofs) ->
  wf_data (los, nts) Mem0 blk bofs eofs.
Proof.
  intros S los nts Ps Mem0 rm gl vp blk bofs eofs t tp Hwfg Hwfr Hwfv J.
  destruct vp.
    unfold get_reg_metadata in J.
    remember (lookupAL metadata rm i0) as R.
    destruct R; inv J.
    symmetry in HeqR.
    apply Hwfr in HeqR; auto.

    apply get_reg_metadata_const_inv in J.
    destruct J as [[J1 J2] | [bc [ec [J1 [J2 J3]]]]]; auto using null_is_wf_data.
      inv Hwfv.
      eapply wf_rmetadata__get_const_metadata; eauto.
Qed.

Lemma wf_mmetadata__get_mem_metadata : forall TD Mem0 MM gvp blk bofs eofs,
  wf_mmetadata TD Mem0 MM ->
  get_mem_metadata TD MM gvp = mkMD blk bofs eofs ->
  wf_data TD Mem0 blk bofs eofs.
Proof.
  intros TD Mem0 MM gvp blk bofs eofs Hwfm H4.
  unfold get_mem_metadata in H4.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion H4; subst; auto using null_is_wf_data].
  destruct v; try solve [inversion H4; subst; auto using null_is_wf_data].
  remember (MM b i0) as R'.
  destruct R'; inv H4; auto using null_is_wf_data.
  symmetry in HeqR'.     
  apply Hwfm in HeqR'; auto.
Qed.

Lemma free_preserves_wf_data : forall TD (Mem0 Mem' : mem) (b : Values.block)
  (z z0 : Z) (HeqR : (z, z0) = Mem.bounds Mem0 b)
  (H0 : Mem.free Mem0 b z z0 = ret Mem') blk bofs eofs
  (J : wf_data TD Mem0 blk bofs eofs),
  wf_data TD Mem' blk bofs eofs.
Proof.
  intros.
  unfold wf_data in *.
  destruct J as [J1 J2].
  split.
    apply Mem.nextblock_free in H0.
    rewrite H0. auto.

    eapply free_preserves_temporal_prop; eauto.
Qed.

Lemma alloc_preserves_wf_data : forall TD Mem0 sz Mem' mb
  (H4 : Mem.alloc Mem0 0 sz = (Mem', mb)) blk bofs eofs
  (J' : wf_data TD Mem0 blk bofs eofs),
  wf_data TD Mem' blk bofs eofs.
Proof.
  intros.
  unfold wf_data in *.
  eapply alloc_preserves_temporal_prop; eauto.
Qed.

(****************************************)
(* wf_global_ptr *)

Lemma free_preserves_wf_global_ptr : forall S TD Mem0 gl gv Mem',
  free TD Mem0 gv = ret Mem' ->
  wf_global_ptr S TD Mem0 gl ->
  wf_global_ptr S TD Mem' gl.
Proof.
  intros S TD Mem0 gl gv Mem' Hfree Hwfg.
  apply free_inv in Hfree. 
  destruct Hfree as [blk [ofs [hi [lo [J1 [J2 [J3 J4]]]]]]].
  intros x gv0 typ0 Hlk Hwfc.
  eapply Hwfg in Hwfc; eauto.
  destruct Hwfc as [b [sz0 [J5 [J6 [J7 J8]]]]].
  eapply free_preserves_temporal_prop in J8; eauto.
  exists b. exists sz0. repeat (split; auto).
    erewrite Mem.bounds_free; eauto.
Qed.

Lemma free_allocas_preserves_wf_global_ptr : forall S TD gl als Mem0 Mem',
  free_allocas TD Mem0 als = ret Mem' ->
  wf_global_ptr S TD Mem0 gl ->
  wf_global_ptr S TD Mem' gl.
Proof.  
  induction als; simpl; intros Mem0 Mem' Hfree Hwfr.
    inv Hfree. auto.

    remember (free TD Mem0 (blk2GV TD a)) as R.
    destruct R; inv Hfree.
    eapply IHals; eauto.
    eapply free_preserves_wf_global_ptr in Hwfr; eauto.
Qed.

Lemma malloc_preserves_wf_global_ptr : forall S TD Mem0 gl tsz gn align0 Mem' mb,
  malloc TD Mem0 tsz gn align0 = ret (Mem', mb) ->
  wf_global_ptr S TD Mem0 gl ->
  wf_global_ptr S TD Mem' gl.
Proof.
  intros.
  apply malloc_inv in H.
  destruct H as [n [J1 [J0 J2]]].
  intros x gv0 typ0 Hlk Hwfc.
  eapply H0 in Hwfc; eauto.
  destruct Hwfc as [b [sz0 [J5 [J6 [J3 J4]]]]].
  exists b. exists sz0.
  assert (G:=J4). destruct G as [G _].
  eapply alloc_preserves_temporal_prop in J4; eauto.
  repeat (split; auto).
    assert (J:=J2).
    apply Mem.bounds_alloc with (b':=b) in J; auto.
    destruct (eq_block b mb); subst.
      destruct J4 as [J4 _].
      assert (J':=J2).
      apply Mem.nextblock_alloc in J2; subst.
      apply Mem.alloc_result in J'; subst.
      contradict G; zauto.

      rewrite J. auto.
Qed.

Lemma store_aux_preserves_wf_global_ptr : forall S TD gl b gv ofs Mem0 Mem',
  mstore_aux Mem0 gv b ofs = ret Mem' ->
  wf_global_ptr S TD Mem0 gl ->
  wf_global_ptr S TD Mem' gl.
Proof.
  induction gv; simpl; intros ofs Mem0 Mem' Hstore Hgptr.
    inv Hstore. auto.

    destruct a.
    remember (Mem.store m Mem0 b ofs v) as R.
    destruct R as [M' | ]; tinv Hstore.  
    symmetry in HeqR.
    apply IHgv with (Mem0:=M')(ofs:=ofs + size_chunk m); auto.
    intros x gv0 typ0 Hlk Hwfc.
    eapply Hgptr in Hwfc; eauto.
    destruct Hwfc as [b' [sz0 [J5 [J6 [J7 J8]]]]].
    eapply store_preserves_temoporal_prop in J8; eauto.
    exists b'. exists sz0.
    repeat (split; auto).
      erewrite Mem.bounds_store; eauto.
Qed.

Lemma store_preserves_wf_global_ptr : forall S TD Mem0 gl gvp t gv align Mem',
  mstore TD Mem0 gvp t gv align = Some Mem' ->
  wf_global_ptr S TD Mem0 gl ->
  wf_global_ptr S TD Mem' gl.
Proof.
  intros.
  apply store_inv in H.
  destruct H as [b [ofs [J1 J2]]].
  eapply store_aux_preserves_wf_global_ptr in J2; eauto.
Qed.

Lemma callExternalFunction_preserves_wf_global_ptr : forall Mem0 fid gvs oresult
    Mem' S TD gl,
  callExternalFunction Mem0 fid gvs = Some (oresult, Mem') ->
  wf_global_ptr S TD Mem0 gl ->
  wf_global_ptr S TD Mem' gl.
Proof.
  intros.
  intros x gv0 typ0 Hlk Hwfc.
  eapply H0 in Hwfc; eauto.
  destruct Hwfc as [b [sz0 [J5 [J6 [J7 J8]]]]].
  exists b. exists sz0. 
  repeat (split; eauto using callExternalFunction_temporal_prop).
    erewrite <- callExternalFunction_mem_bounds; eauto.
Qed.

(********************************************)
(* wf_rmetadata *)

Lemma free_preserves_wf_rmetadata : forall TD (Mem0 Mem' : mem) gv 
  (H0 : free TD Mem0 gv = ret Mem') rm (Hwfr : wf_rmetadata TD Mem0 rm),
  wf_rmetadata TD Mem' rm.
Proof.
  intros. 
  apply free_inv in H0. 
  destruct H0 as [blk [ofs [hi [lo [J1 [J2 [J3 J4]]]]]]].
  intros i1 bblk bofs eofs J.
  apply Hwfr in J.   
  eapply free_preserves_wf_data; eauto.
Qed.

Lemma free_allocas_preserves_wf_rmetadata : forall als TD M M' rm,
  free_allocas TD M als = Some M' ->
  wf_rmetadata TD M rm ->
  wf_rmetadata TD M' rm.
Proof.
  induction als; simpl; intros TD M M' rm Hfree Hwfr.
    inv Hfree. auto.

    remember (free TD M (blk2GV TD a)) as R.
    destruct R; inv Hfree.
    eapply IHals; eauto.
    eapply free_preserves_wf_rmetadata in Hwfr; eauto.
Qed.

Lemma malloc_preserves_wf_rmetadata : forall (TD : TargetData) rm gn align0
  (Mem0 Mem' : mem) (tsz : sz) (mb : mblock)
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (Hwfr : wf_rmetadata TD Mem0 rm),
  wf_rmetadata TD Mem' rm.
Proof.
  intros. 
  apply malloc_inv in H1. 
  destruct H1 as [n [J1 [J2 J3]]].
  intros i1 blk bofs eofs J.
  apply Hwfr in J.   
  eapply alloc_preserves_wf_data; eauto.
Qed.
  
Lemma malloc_extends_wf_rmetadata : forall
  (TD : TargetData)
  (rm : AssocList metadata)
  (id0 : atom)
  (gn : GenericValue)
  (align0 : align)
  (Mem0 : mem)
  (Mem' : mem)
  (tsz : sz)
  (mb : mblock)
  (rm' : rmetadata)
  (n : Z)
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : updateAddAL _ rm id0 (bound2MD mb tsz n) = rm')
  (Hwfr : wf_rmetadata TD Mem0 rm),
  wf_rmetadata TD Mem' rm'.
Proof.
  intros.
  subst.
  unfold malloc in H1.
  rewrite H2 in H1.
  destruct (zle 0 (Size.to_Z tsz * n)); try solve [inversion H1].
  remember (Mem.alloc Mem0 0 (Size.to_Z tsz * n)) as R.
  inversion H1. clear H1. subst.
  clear H2.
  intros i0 blk bofs eofs J.
  destruct (@id_dec id0 i0); subst.
  SCase "id0=i0".
      rewrite lookupAL_updateAddAL_eq in J.
      inversion J; subst. clear J.
      unfold wf_data.
      split.
        assert (H4':=H0).
        apply Mem.alloc_result in H0.
        apply Mem.nextblock_alloc in H4'.
        rewrite H0. rewrite H4'. zauto.

        intros Hwfb ofs J1. 
        apply Mem.valid_access_alloc_same with (ofs:=ofs)(chunk:=AST.Mint 7) 
          in H0.
          destruct H0 as [J2 J3].
          unfold Mem.range_perm in J2.
          apply Mem.perm_implies with (p1:=Freeable); auto with mem.
          apply J2.
          simpl. clear.
          assert (J:=@bytesize_chunk_pos 7).
          zauto.

          rewrite Int.signed_zero in J1; zauto. 
(*
          rewrite Int.signed_repr in J1; zauto. clear.
          assert (J1:=@Int.min_signed_neg 31).          
          assert (J2:=@Int.max_signed_pos 31).          
          zauto.
*)
          simpl. rewrite bytesize_chunk_7_eq_1. 
          destruct J1 as [_ J1].
          unfold Int.signed in J1.
          unfold Int.unsigned in J1.
          simpl in J1.
          clear - J1 z.
          assert (J:=@Int.modulus_pos 31).
          assert ((Size.to_Z tsz * n) mod Int.modulus 31 <= (Size.to_Z tsz * n)) 
            as LE.
            apply Zmod_le; zauto.
          destruct (zlt ((Size.to_Z tsz * n) mod Int.modulus 31) 
            (Int.half_modulus 31)); zeauto.

          simpl. rewrite bytesize_chunk_7_eq_1. zauto.

  SCase "id0<>i0".
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      assert (J':=@Hwfr i0 blk bofs eofs J). clear Hwfr.    
      eapply alloc_preserves_wf_data; eauto.
Qed.

Lemma returnUpdateLocals__wf_rmetadata : forall los nts Result lc rm gl c' lc' 
    rm' Mem0 Mem' als lc'' rm'' S Ps f rt
  (Hwfg : wf_global_ptr S (los, nts) Mem0 gl)
  (Hwfv : wf_value S (module_intro los nts Ps) f Result rt)
  (H0 : free_allocas (los, nts) Mem0 als = ret Mem')
  (H1 : @returnUpdateLocals GVsSig (los, nts) c' rt Result lc lc' rm rm' gl =
       ret (lc'', rm''))
  (Hwfm1' : wf_rmetadata (los, nts) Mem0 rm)
  (Hwfm2' : wf_rmetadata (los, nts) Mem0 rm'),
  wf_rmetadata (los, nts) Mem' rm''.
Proof.
  intros.
  unfold returnUpdateLocals, returnResult in H1.
  assert (wf_rmetadata (los, nts) Mem' rm') as Hwfm.
    eauto using free_allocas_preserves_wf_rmetadata.
  remember (getOperandValue (los, nts) Result lc gl) as R1.
  destruct R1; try solve [inv H1; auto].
  destruct (isPointerTypB rt).
    remember (get_reg_metadata (los, nts) gl rm Result) as R3.
    destruct R3 as [[md ?]|]; try solve [inv H1; auto].
    destruct c'; try solve [inv H1; auto].
    destruct n; try solve [inv H1; auto].
    unfold isPointerTypB in H1.
    destruct t; try solve [inv H1; auto].
    destruct (lift_op1 GVsSig (fit_gv (los, nts) t) g t); tinv H1.
    destruct t; inv H1; auto.
      intros x blk bofs eofs Hlk.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk.
        inv Hlk. symmetry in HeqR3.
        eapply wf_rmetadata__get_reg_metadata with (rm:=rm); eauto.
          eapply free_allocas_preserves_wf_global_ptr in H0; eauto.
          eapply free_allocas_preserves_wf_rmetadata in H0; eauto.
 
        rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.

    destruct c'; try solve [inv H1; auto].
    destruct n; try solve [inv H1; auto].
    unfold isPointerTypB in H1.
    destruct t; try solve [inv H1; auto].
    destruct (lift_op1 GVsSig (fit_gv (los, nts) t) g t); tinv H1.
    destruct t; inv H1; auto.
      intros x blk bofs eofs Hlk.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk.
        inv Hlk. apply null_is_wf_data; auto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes__wf_rmetadata : forall los nts M f b
  ps gl lc rm S PNs re id1 gv1 blk1 bofs1 eofs1 b' ifs
  (Hwfg : wf_global_ptr S (los, nts) M gl)
  (Hwfps : wf_phinodes ifs S (module_intro los nts ps) f b' PNs),
  NoDup (getPhiNodesIDs PNs) ->
  wf_rmetadata (los, nts) M rm ->
  @getIncomingValuesForBlockFromPHINodes GVsSig (los, nts) PNs b gl lc rm 
    = Some re ->
  In (id1,gv1,Some (mkMD blk1 bofs1 eofs1)) re ->
  wf_data (los, nts) M blk1 bofs1 eofs1.
Proof.
  induction PNs; simpl; intros re id1 gv1 blk1 bofs1 eofs1 b' ifs Hwfg Hwfps 
    Huniq Hwfr Hget Hin.
    inv Hget. inversion Hin.

    inv Huniq. inv Hwfps.
    destruct a.
    remember (getValueViaBlockFromValuels l0 b) as R0.
    destruct R0; try solve [inv Hget].
    destruct (getOperandValue (los,nts) v lc gl); try solve [inv Hget].
    remember (getIncomingValuesForBlockFromPHINodes (los,nts) PNs b gl lc rm) 
      as R.
    destruct R; try solve [inv Hget].
    destruct (isPointerTypB t); inv Hget.
      remember (get_reg_metadata (los,nts) gl rm v) as R1.
      destruct R1 as [[bv ev]|]; inv H0.
      simpl in Hin.
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin. 
        symmetry in HeqR1.
        inv H8.
        destruct b. simpl in HeqR0.
        eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H4; eauto.
        eapply wf_rmetadata__get_reg_metadata in HeqR1; eauto.

      simpl in Hin.
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin.
Qed.

Lemma updateValuesForNewBlock__wf_rmetadata_aux : forall TD M rvs rm lc,
  (forall id1 gv1 blk1 bofs1 eofs1, 
    In (id1,gv1,Some (mkMD blk1 bofs1 eofs1)) rvs ->
    wf_data TD M blk1 bofs1 eofs1) ->
  forall rvs2 rvs1 lc1 rm1 lc2 rm2,
  rvs = rvs1 ++ rvs2 ->
  @updateValuesForNewBlock GVsSig rvs1 lc rm = (lc1, rm1) ->
  wf_rmetadata TD M rm1 ->
  updateValuesForNewBlock rvs2 lc1 rm1 = (lc2, rm2) ->
  wf_rmetadata TD M rm2.
Proof.
  intros TD M rvs rm lc Hprop.
  induction rvs2; simpl; intros rvs1 lc1 rm1 lc2 rm2 Heq Hupdate1 Hrmap1
    Hupdate2; subst.
    inv Hupdate2. auto.

    destruct a. destruct p.
    remember (updateValuesForNewBlock rvs2 lc1 rm1) as R. 
    destruct R as [lc2' rm2'].
    destruct o as [[blk bofs eofs]|]; inv Hupdate2.
      intros x blk2 bofs2 eofs2 Hlk.
      destruct (eq_atom_dec i0 x); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk.
        apply Hprop with (id1:=x)(gv1:=g); eauto.
          apply in_or_app. simpl. auto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
        eapply updateValuesForNewBlock_spec6 in Hlk; eauto.
        destruct Hlk as [Hlk | [id1 [gv1 Hin]]]; eauto.
          eapply Hprop; eauto.
            apply in_or_app. simpl. eauto.
                       
      intros x blk bofs eofs Hlk.
      eapply updateValuesForNewBlock_spec6 in Hlk; eauto.
      destruct Hlk as [Hlk | [id1 [gv1 Hin]]]; eauto.
        eapply Hprop; eauto.
          apply in_or_app. simpl. eauto.
Qed.

Lemma updateValuesForNewBlock__wf_rmetadata : forall rvs TD M lc rm lc' rm',
  (forall id1 gv1 blk1 bofs1 eofs1, 
    In (id1,gv1,Some (mkMD blk1 bofs1 eofs1)) rvs ->
    wf_data TD M blk1 bofs1 eofs1) ->
  wf_rmetadata TD M rm ->
  @updateValuesForNewBlock GVsSig rvs lc rm = (lc', rm') ->
  wf_rmetadata TD M rm'.
Proof.
  intros.
  eapply updateValuesForNewBlock__wf_rmetadata_aux with (rvs1:=nil)(lc1:=lc)
    (rm1:=rm)(rvs2:=rvs); simpl; eauto.
Qed.

Lemma switchToNewBasicBlock__wf_rmetadata : forall S M b1 b2 gl lc rm lc' rm' 
    F ifs los nts Ps,
  wf_global_ptr S (los, nts) M gl ->
  wf_fdef ifs S (module_intro los nts Ps) F ->
  uniqFdef F ->
  blockInFdefB b1 F ->
  wf_rmetadata (los, nts) M rm ->
  @switchToNewBasicBlock GVsSig (los, nts) b1 b2 gl lc rm = Some (lc', rm') ->
  wf_rmetadata (los, nts) M rm'.
Proof.
  intros S M b1 b2 gl lc rm lc' rm' F ifs los nts m Hwfg HwfF Huniq HBinF Hwfr 
    Hswitch.
  unfold switchToNewBasicBlock in Hswitch.
  remember (getIncomingValuesForBlockFromPHINodes (los, nts)  
             (getPHINodesFromBlock b1) b2 gl lc rm) as R.
  destruct R; inv Hswitch.
  eapply updateValuesForNewBlock__wf_rmetadata; eauto.
  intros. 
  inv HwfF.
  apply wf_blocks__wf_block with (b:=b1) in H15; auto.
  destruct b1. inv H15.
  eapply getIncomingValuesForBlockFromPHINodes__wf_rmetadata; eauto.

    apply uniqFdef__uniqBlockLocs in HBinF; auto.
    apply NoDup_inv in HBinF. destruct HBinF; auto.
Qed.

Lemma get_mem_metadata__wf_rmetadata : forall los nts Mem0 rm gvp id0 MM,
  wf_mmetadata (los, nts) Mem0 MM ->
  wf_rmetadata (los, nts) Mem0 rm ->
  wf_rmetadata (los, nts) Mem0 
    (updateAddAL metadata rm id0 (get_mem_metadata (los, nts) MM gvp)).
Proof.
  intros.
  intros i0 blk bofs eofs J.
  destruct (@id_dec id0 i0); subst.
    rewrite lookupAL_updateAddAL_eq in J.
    inversion J; subst.
    eapply wf_mmetadata__get_mem_metadata in H2; eauto.

    rewrite <- lookupAL_updateAddAL_neq in J; auto. eauto.
Qed.

Lemma store_aux_preserves_wf_rmetadata : forall TD b rm gv ofs Mem0 Mem',
  mstore_aux Mem0 gv b ofs = ret Mem' ->
  wf_rmetadata TD Mem0 rm -> 
  wf_rmetadata TD Mem' rm.
Proof.
  induction gv; simpl; intros ofs Mem0 Mem' Hstore Hwfr.
    inv Hstore. auto.

    destruct a.
    remember (Mem.store m Mem0 b ofs v) as R.
    destruct R as [M' | ]; tinv Hstore.  
    symmetry in HeqR.
    apply IHgv with (Mem0:=M')(ofs:=ofs + size_chunk m); auto.
    intros i1 blk bofs eofs J.
    apply Hwfr in J. clear Hwfr.
    eapply wf_data__store__wf_data; eauto.
Qed.

Lemma store_preserves_wf_rmetadata : forall TD Mem0 gvp t gv align0 Mem' rm, 
  mstore TD Mem0 gvp t gv align0 = ret Mem' ->
  wf_rmetadata TD Mem0 rm -> 
  wf_rmetadata TD Mem' rm.
Proof. 
  intros TD Mem0 gvp t gv align0 Mem' rm H3 Hwfr.
  apply store_inv in H3.
  destruct H3 as [b [ofs [J1 J2]]].
  eapply store_aux_preserves_wf_rmetadata in J2; eauto.
Qed.

Lemma prop_metadata_preserves_wf_rmetadata : forall los nts Mem0 rm md gl S Ps
    f t id0 vp
  (H : get_reg_metadata (los, nts) gl rm vp = ret md)
  (Hwfg' : wf_global_ptr S (los, nts) Mem0 gl)
  (Hwfv : wf_value S (module_intro los nts Ps) f vp t)
  (Hwfr : wf_rmetadata (los, nts) Mem0 rm),
  wf_rmetadata (los, nts) Mem0 (updateAddAL metadata rm id0 md).
Proof.
  intros.
  intros i0 blk bofs eofs J0.
  destruct (@id_dec id0 i0); subst.
    rewrite lookupAL_updateAddAL_eq in J0.
    inversion J0; subst. clear J0.
    eapply wf_rmetadata__get_reg_metadata in H; eauto.

    rewrite <- lookupAL_updateAddAL_neq in J0; auto.
    apply Hwfr in J0; auto.
Qed.

Lemma adding_null_preserves_wf_rmetadata : forall TD Mem0 rm id0,
  wf_rmetadata TD Mem0 rm ->
  wf_rmetadata TD Mem0 (updateAddAL metadata rm id0 null_md).
Proof.
  intros TD Mem0 rm id0 Hwfr.
  intros i0 blk bofs eofs J.
  destruct (@id_dec id0 i0); subst.
    rewrite lookupAL_updateAddAL_eq in J.
    inversion J; subst. clear J.
    unfold wf_data.
    simpl.
    split.
      apply nullptr_lt_nextblock.
  
      intros Htmp ofs J.
      contradict J; zauto.
  
    rewrite <- lookupAL_updateAddAL_neq in J; auto.
    apply Hwfr in J; auto.
Qed.

Lemma params2GVs__wf_rmetadata : forall S los nts Ps f M rm lc gl ps ogvs
  (Hwfvs : forall t1 a1 v1, In (t1,a1,v1) ps -> 
    wf_value S (module_intro los nts Ps) f v1 t1)
  (Hwfg : wf_global_ptr S (los, nts) M gl),
  wf_rmetadata (los,nts) M rm ->
  @params2GVs GVsSig (los,nts) ps lc gl rm = Some ogvs ->
  forall gv1 blk1 bofs1 eofs1,
    In (gv1, Some (mkMD blk1 bofs1 eofs1)) ogvs ->
    wf_data (los,nts) M blk1 bofs1 eofs1.
Proof.
  induction ps; simpl; intros ogvs Hwfvs Hwfg Hwfr Hp2ogvs gv1 blk1 bofs1 eofs1 
    Hin.
    inv Hp2ogvs. inv Hin.

    destruct a as [[t attr] v].
    destruct (getOperandValue (los,nts) v lc gl); 
      try solve [inv Hp2ogvs].
    remember (params2GVs (los,nts) ps lc gl rm) as R.
    destruct R; try solve [inv Hp2ogvs].
    destruct (isPointerTypB t); inv Hp2ogvs.
      simpl in Hin. 
      destruct Hin as [Hin | Hin]; eauto. 
        inv Hin.
        eapply wf_rmetadata__get_reg_metadata in H1; eauto.
        
      simpl in Hin. 
      destruct Hin as [Hin | Hin]; eauto. 
        inv Hin.
Qed.

Lemma initializeFrameValues__wf_rmetadata : forall TD M la ogvs lc rm
  (Hprop: forall gv1 blk1 bofs1 eofs1, 
    In (gv1,Some (mkMD blk1 bofs1 eofs1)) ogvs ->
    wf_data TD M blk1 bofs1 eofs1),
  forall la2 la1 ogvs1 ogvs2 lc1 rm1 lc2 rm2,
  la = la1 ++ la2 ->
  ogvs = ogvs1 ++ ogvs2 ->
  @_initializeFrameValues GVsSig TD la1 ogvs1 lc rm = Some (lc1, rm1) ->
  wf_rmetadata TD M rm1 ->
  _initializeFrameValues TD la2 ogvs2 lc1 rm1 = Some (lc2, rm2) ->
  wf_rmetadata TD M rm2.
Proof.
  intros TD M la ogvs lc rm Hprop.
  induction la2; simpl; intros la1 ogvs1 ogvs2 lc1 rm1 lc2 rm2 Heqla heqogvs 
    Hinit1 Hwfr1 Hinit2; subst.
    inv Hinit2. auto.

    destruct a. destruct p.
    destruct ogvs2.
      remember (_initializeFrameValues TD la2 nil lc1 rm1) as R.
      destruct R as [[lc' rm']|]; tinv Hinit2.
      destruct (gundef TD t); tinv Hinit2.
      destruct (isPointerTypB t); inv Hinit2.
        apply adding_null_preserves_wf_rmetadata.
        intros x blk bofs eofs Hlk.
        eapply initializeFrameValues_spec2 in Hlk; eauto.
        destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
          inv Hlk. apply null_is_wf_data; auto.
          inv Hlk.

        intros x blk bofs eofs Hlk.
        eapply initializeFrameValues_spec2 in Hlk; eauto.
        destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
          inv Hlk. apply null_is_wf_data; auto.
          inv Hlk.

    destruct p.
    remember (_initializeFrameValues TD la2 ogvs2 lc1 rm1) as R.
    destruct R as [[lc' rm']|]; tinv Hinit2.
    destruct (lift_op1 GVsSig (fit_gv TD t) g t); tinv Hinit2.
    destruct (isPointerTypB t); inv Hinit2.
      destruct o as [[md1 ?]|]; inv H0.
        intros x blk bofs eofs Hlk.
        destruct (eq_atom_dec i0 x); subst.
          rewrite lookupAL_updateAddAL_eq in Hlk. 
          inv Hlk. 
          eapply Hprop; eauto. 
            apply in_or_app. simpl. auto.

          rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
          eapply initializeFrameValues_spec2 in Hlk; eauto.
          destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
            inv Hlk. apply null_is_wf_data; auto.
            eapply Hprop; eauto. 
              apply in_or_app. simpl. eauto.

        apply adding_null_preserves_wf_rmetadata.
        intros x blk bofs eofs Hlk.
        eapply initializeFrameValues_spec2 in Hlk; eauto.
        destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
          inv Hlk. apply null_is_wf_data; auto.
          eapply Hprop; eauto. 
            apply in_or_app. simpl. eauto.
      intros x blk bofs eofs Hlk.
      eapply initializeFrameValues_spec2 in Hlk; eauto.
      destruct Hlk as [Hlk | [Hlk | [gv1 Hlk]]]; eauto.
        inv Hlk. apply null_is_wf_data; auto.
        eapply Hprop; eauto. 
          apply in_or_app. simpl. eauto.
Qed.

Lemma initLocals__wf_rmetadata : forall ogvs (rm : rmetadata) lc'
  M rm' los nts ps la gl lc f Ps S
  (Hwfvs : forall t1 a1 v1, In (t1,a1,v1) ps -> 
    wf_value S (module_intro los nts Ps) f v1 t1)
  (Hwfg : wf_global_ptr S (los, nts) M gl),
  wf_rmetadata (los,nts) M rm ->
  @params2GVs GVsSig (los,nts) ps lc gl rm = Some ogvs ->
  initLocals (los,nts) la ogvs = Some (lc', rm') ->
  wf_rmetadata (los,nts) M rm'.
Proof.
  intros.
  unfold initLocals in H1.
  rewrite_env (nil++la) in H1.
  rewrite_env (nil++ogvs) in H1.
  eapply initializeFrameValues__wf_rmetadata with (lc1:=nil)(rm1:=nil)(lc:=nil)
    (rm:=nil)(ogvs1:=nil)(la1:=nil) in H1; eauto.
    eapply params2GVs__wf_rmetadata; eauto.
    intros x blk bofs eofs J. inv J.
Qed.

Lemma callExternalFunction_preserves_wf_rmetadata : forall Mem0 fid gvs oresult
    Mem' rm TD,
  callExternalFunction Mem0 fid gvs = Some (oresult, Mem') ->
  wf_rmetadata TD Mem0 rm ->
  wf_rmetadata TD Mem' rm.
Proof.
  intros Mem0 fid gvs oresult Mem' rm TD Hcall Hwfr.
  intros x blk bofs eofs Hlk.
  apply Hwfr in Hlk.
  unfold wf_data in *.
  eauto using callExternalFunction_temporal_prop.
Qed.

(********************************************)
(* wf_mmetadata *)

Lemma free_preserves_wf_mmetadata : forall TD (Mem0 Mem' : mem) gv
  (H0 : free TD Mem0 gv = ret Mem') MM (Hwfm : wf_mmetadata TD Mem0 MM),
  wf_mmetadata TD Mem' MM.
Proof.
  intros. 
  apply free_inv in H0. 
  destruct H0 as [blk [ofs [hi [lo [J1 [J2 [J3 J4]]]]]]].
  intros b1 ofs' bblk bofs eofs J.
  assert (J':=@Hwfm b1 ofs' bblk bofs eofs J).
  eapply free_preserves_wf_data; eauto.
Qed.

Lemma free_allocas_preserves_wf_mmetadata : forall als TD M M' MM,
  free_allocas TD M als = Some M' ->
  wf_mmetadata TD M MM ->
  wf_mmetadata TD M' MM.
Proof.
  induction als; simpl; intros TD M M' MM Hfree Hwfr.
    inv Hfree. auto.

    remember (free TD M (blk2GV TD a)) as R.
    destruct R; inv Hfree.
    eapply IHals; eauto.
    eapply free_preserves_wf_mmetadata in Hwfr; eauto.
Qed.

Lemma malloc_preserves_wf_mmetadata : forall (TD : TargetData) MM gn align0
  (Mem0 Mem' : mem) (tsz : sz) (mb : mblock)
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (Hwfm : wf_mmetadata TD Mem0 MM),
  wf_mmetadata TD Mem' MM.
Proof.
  intros. 
  apply malloc_inv in H1. 
  destruct H1 as [n [J1 [J2 J3]]].
  intros b ofs blk bofs eofs J.
  assert (J':=@Hwfm b ofs blk bofs eofs J).
  eapply alloc_preserves_wf_data; eauto.
Qed.

Lemma malloc_extends_wf_mmetadata : forall
  (TD : TargetData)
  (lc : GVsMap)
  (id0 : atom)
  (gn : GenericValue)
  (align0 : align)
  (Mem0 : mem)
  (MM : mmetadata)
  (Mem' : mem)
  (tsz : sz)
  (mb : mblock)
  (lc' : GVsMap)
  (rm' : rmetadata)
  (n : Z) rm t
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : prop_reg_metadata lc rm id0 ($ (blk2GV TD mb) # typ_pointer t $)
         (bound2MD mb tsz n) = (lc', rm'))
  (Hwfm : wf_mmetadata TD Mem0 MM),
  wf_mmetadata TD Mem' MM.
Proof.
  intros.
  invert_prop_reg_metadata. clear H3.
  unfold malloc in H1.
  rewrite H2 in H1.
  destruct (zle 0 (Size.to_Z tsz * n)); try solve [inversion H1].
  remember (Mem.alloc Mem0 0 (Size.to_Z tsz * n)) as R.
  inversion H1. clear H1. subst.
  intros b ofs blk bofs eofs J.
  assert (J':=@Hwfm b ofs blk bofs eofs J). clear Hwfm.
  eapply alloc_preserves_wf_data; eauto.
Qed.

Lemma store_aux_preserves_wf_mmetadata : forall TD b MM gv ofs Mem0 Mem',
  mstore_aux Mem0 gv b ofs = ret Mem' ->
  wf_mmetadata TD Mem0 MM -> 
  wf_mmetadata TD Mem' MM.
Proof.
  induction gv; simpl; intros ofs Mem0 Mem' Hstore Hwfm.
    inv Hstore. auto.

    destruct a.
    remember (Mem.store m Mem0 b ofs v) as R.
    destruct R as [M' | ]; tinv Hstore.  
    symmetry in HeqR.
    apply IHgv with (Mem0:=M')(ofs:=ofs + size_chunk m); auto.
    intros b0 ofs' blk bofs eofs J.
    apply Hwfm in J. clear Hwfm.
    eapply wf_data__store__wf_data; eauto.
Qed.

Lemma store_nptr_preserves_wf_mmetadata : forall TD Mem0 gvp t gv align0 Mem' MM,
  mstore TD Mem0 gvp t gv align0 = ret Mem' ->
  wf_mmetadata TD Mem0 MM -> 
  wf_mmetadata TD Mem' MM.
Proof. 
  intros TD Mem0 gvp t gv align0 Mem' rm H3 Hwfm.
  apply store_inv in H3.
  destruct H3 as [b [ofs [J1 J2]]].
  eapply store_aux_preserves_wf_mmetadata in J2; eauto.
Qed.

Lemma store_ptr_preserves_wf_mmetadata : forall los nts Mem0 rm MM md' gl S
    gvp gv align0 Mem' Ps f v t
  (Hwfg' : wf_global_ptr S (los, nts) Mem0 gl)
  (Hwfm1' : wf_rmetadata (los, nts) Mem0 rm)
  (H3 : mstore (los, nts) Mem0 gvp t gv align0 = ret Mem')
  (H5 : get_reg_metadata (los, nts) gl rm v = ret md')
  (Hwfv : wf_value S (module_intro los nts Ps) f v t)
  (Hwfm : wf_mmetadata (los, nts) Mem0 MM),
  wf_mmetadata (los, nts) Mem' (set_mem_metadata (los, nts) MM gvp md').
Proof.
  intros.
  apply store_inv in H3.
  destruct H3 as [b [ofs [J1 J2]]].
  intros b0 ofs' blk bofs eofs J. 
    subst.
    unfold set_mem_metadata in J.
    rewrite J1 in J.
    destruct (zeq b0 b); subst; 
       simpl in J; eauto using wf_mmetadata__store_aux__wf_data.
    destruct (Int.eq_dec 31 ofs ofs'); subst; 
       simpl in J; eauto using wf_mmetadata__store_aux__wf_data.
  
       inversion J; subst. clear J.
       eapply wf_rmetadata__get_reg_metadata with (Mem0:=Mem0) in H5; eauto.
         eapply wf_data__store_aux__wf_data; eauto.
Qed.

Lemma callExternalFunction_preserves_wf_mmetadata : forall Mem0 fid gvs oresult
    Mem' TD MM,
  callExternalFunction Mem0 fid gvs = Some (oresult, Mem') ->
  wf_mmetadata TD Mem0 MM ->
  wf_mmetadata TD Mem' MM.
Proof.
  intros Mem0 fid gvs oresult Mem' TD MM Hcall Hwfm.
  intros b ofs blk bofs eofs Hlk.
  apply Hwfm in Hlk.
  unfold wf_data in *.
  eauto using callExternalFunction_temporal_prop.
Qed.

(********************************************)
(* assert_mptr *)

Lemma typ2memory_chunk__le__getTypeAllocSize : forall sys t c s TD,
  wf_typ sys t ->
  (forall a b o, 
    getTypeSizeInBits_and_Alignment TD o t = Some (a,b) ->
    (b > 0)%nat) ->
  typ2memory_chunk t = Some c ->
  Some s = getTypeAllocSize TD t ->
  size_chunk c <= Size.to_Z s.
Proof.
  intros sys t c s TD Hwft Hwfa H1 H2.
  unfold getTypeAllocSize, getTypeStoreSize, getTypeSizeInBits, 
         getTypeSizeInBits_and_Alignment in H2.
  assert (Z_of_nat 0 = 0) as EQ0. simpl. auto.
  destruct TD.
  destruct t; inv H1; inv H2;
    simpl; unfold bytesize_chunk, Size.to_nat, RoundUpAlignment, Size.to_Z.
    assert (ZRdiv (Z_of_nat s0) 8 >= 0) as J.
      apply ZRdiv_prop2; zauto.
    assert (Z_of_nat 0 = 0) as EQ. simpl. auto.
    assert (Z_of_nat (getIntAlignmentInfo l0 s0 true) > 0) as GT.
      rewrite <- EQ0.
      apply inj_gt.
      eapply Hwfa; simpl; eauto.
    assert (ZRdiv (Z_of_nat (S (s0 - 1))) 8 <= ZRdiv (Z_of_nat s0) 8) as J2.  
      unfold ZRdiv.
      apply Coqlib.ZRdiv_prop7.
        apply inj_le.
          inv Hwft. unfold Size.gt in H1. omega.
        apply Z_of_S_gt_O.
    assert (J':=@roundup_is_correct (ZRdiv (Z_of_nat s0) 8)
      (Z_of_nat (getIntAlignmentInfo l0 s0 true)) GT). 
    rewrite nat_of_Z_eq.
      rewrite nat_of_Z_eq; auto.
        zauto.
      rewrite nat_of_Z_eq; auto.
        zauto.

    destruct f; inv H0; inv H1; simpl; unfold RoundUpAlignment.
      assert (Z_of_nat (getFloatAlignmentInfo l0 32 true) > 0) as GT.
        rewrite <- EQ0.
        apply inj_gt.
        eapply Hwfa; simpl; eauto.
      rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
      assert (J:=@roundup_is_correct 4 (Z_of_nat 
        (getFloatAlignmentInfo l0 32 true)) GT).
      rewrite nat_of_Z_eq; zauto. 

      assert (Z_of_nat (getFloatAlignmentInfo l0 64 true) > 0) as GT.
        rewrite <- EQ0.
        apply inj_gt.
        eapply Hwfa; simpl; eauto.
      rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
      assert (J:=@roundup_is_correct 8 (Z_of_nat 
        (getFloatAlignmentInfo l0 64 true)) GT).
      rewrite nat_of_Z_eq; zauto. 

    assert (Z_of_nat (getPointerAlignmentInfo l0 true) > 0) as GT.
      rewrite <- EQ0.
      apply inj_gt.
      eapply Hwfa; simpl; eauto.
    rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
    assert (J:=@roundup_is_correct 4 (Z_of_nat 
      (getPointerAlignmentInfo l0 true)) GT).
    assert (ZRdiv (Z_of_nat 32) 8 = 4) as EQ.
      unfold ZRdiv. simpl. zauto.
    rewrite EQ. clear EQ.
    rewrite nat_of_Z_max.
    rewrite Zmax_left; zauto.
Qed.

Lemma assert_mptr__valid_access' : forall S md los nts Ps Mem gl rm MM t g b ofs
    c f v tv,
  wf_metadata (los, nts) Mem rm MM ->
  wf_global_ptr S (los, nts) Mem gl ->
  wf_value S (module_intro los nts Ps) f v tv ->
  Some md = get_reg_metadata (los, nts) gl rm v ->
  wf_typ S t ->
  (forall a b o, 
    getTypeSizeInBits_and_Alignment (los, nts) o t = Some (a,b) ->
    (b > 0)%nat) ->
  assert_mptr (los, nts) t g md ->
  GV2ptr (los, nts) (getPointerSize (los, nts)) g = ret Values.Vptr b ofs ->
  typ2memory_chunk t = ret c ->
  (align_chunk c | Int.signed 31 ofs) ->
  blk_temporal_safe Mem b ->
  Mem.valid_access Mem c b (Int.signed 31 ofs) Writable.
Proof.
  intros S md los nts Ps Mem gl rm MM t g b ofs c f v tv Hwf Hwfg Hwfv Heqmd
    Hwft Hwfa J R3 R4 R5 Htmp.
  unfold Mem.valid_access.
  split; auto.
    unfold assert_mptr in J.
    rewrite R3 in J.
    symmetry in Heqmd.  
    destruct md.
    destruct Hwf as [Hwfr Hwfm].
    eapply wf_rmetadata__get_reg_metadata in Heqmd; eauto.
    unfold wf_data in Heqmd.
    unfold layouts, namedts in J.
    remember (getTypeAllocSize (@pair (list layout) (list namedt) los nts) t)
      as R6.
    destruct R6; try solve [inversion J].
    simpl in J.
    intros z Jz.
    bdestruct3 J as J1 J2 J3.
    destruct (zeq b md_blk0); subst; try solve [inversion J1].
    apply Heqmd; auto.
    clear - J2 J3 Jz HeqR6 R4 Hwfa Hwft.
    assert (size_chunk c <= Size.to_Z s) as J4.
      eapply typ2memory_chunk__le__getTypeAllocSize; eauto.
    destruct (zle (Int.signed 31 md_bofs0) (Int.signed 31 ofs)); 
      simpl in J2; inversion J2.
    destruct (zle (Int.signed 31 ofs + Size.to_Z s) (Int.signed 31 md_eofs0)); 
      simpl in J3; inversion J3.
    zeauto.
Qed.

Lemma assert_mptr_inv : forall TD t ptr bb bofs eofs,
  assert_mptr TD t ptr (mkMD bb bofs eofs) -> 
  exists pb, exists pofs, exists tsz,
    GV2ptr TD (getPointerSize TD) ptr = Some (Vptr pb pofs) /\
    getTypeAllocSize TD t = Some tsz /\
    zeq pb bb &&
    zle (Integers.Int.signed 31 bofs) (Integers.Int.signed 31 pofs) &&
    zle (Integers.Int.signed 31 pofs + Size.to_Z tsz) 
        (Integers.Int.signed 31 eofs).
Proof.
  intros.
  simpl in H.
  destruct (GV2ptr TD (getPointerSize TD) ptr) as [[]|]; tinv H.
  destruct (getTypeAllocSize TD t); tinv H.
  exists b. exists i0. exists s.
  split; auto.
Qed.

Lemma assert_mptr__valid_access : forall blk bofs eofs TD Mem t g b ofs c delta 
    tsz,
  wf_data TD Mem blk bofs eofs ->
  assert_mptr TD t g (mkMD blk bofs eofs) ->
  GV2ptr TD (getPointerSize TD) g = ret Values.Vptr b ofs ->
  getTypeAllocSize TD t = Some tsz ->
  delta >= 0 ->
  delta + size_chunk c <= Size.to_Z tsz ->
  (align_chunk c | Int.signed 31 ofs + delta) ->
  blk_temporal_safe Mem b ->
  Mem.valid_access Mem c b ((Int.signed 31 ofs) + delta) Writable.
Proof.
  intros blk bofs eofs TD Mem t g b ofs c delta tsz Hwfd Hast Hptr Heq Hnp Hle 
    Halign Htmp.
  unfold Mem.valid_access.
  split; auto.
    apply assert_mptr_inv in Hast.
    destruct Hast as [pb [pofs [tsz' [J1' [J4' J5]]]]].
    rewrite Hptr in J1'. inv J1'.
    rewrite Heq in J4'. inv J4'.
    unfold wf_data in Hwfd.
    intros z Jz.
    bdestruct3 J5 as J1 J2 J3.
    destruct (zeq pb blk); subst; tinv J1.
    apply Hwfd; auto.
    clear Halign Heq Hwfd Htmp Hptr J1.
    unfold zle in *. 
    destruct (Z_le_gt_dec (Int.signed 31 bofs) (Int.signed 31 pofs)); tinv J2.
    destruct (Z_le_gt_dec (Int.signed 31 pofs + Size.to_Z tsz') 
                          (Int.signed 31 eofs)); tinv J3.
    clear J2 J3.
    zeauto.
Qed.

End SBspecMetadata. End SBspecMetadata. 

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-impredicative-set") ***
*** End: ***
 *)
