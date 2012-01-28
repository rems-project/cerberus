Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import Values.
Require Import vellvm.
Require Import genericvalues.
Require Import trace.
Require Import Memory.
Require Import alist.
Require Import Integers.
Require Import Coqlib.
Require Import Lattice.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import opsem.
Require Import dopsem.
Require Import sb_def.
Require Import sb_ds_trans.
Require Import sb_metadata.
Import SB_ds_pass.
Require Import sb_msim.
Require Import sb_ds_sim.
Require Import sb_ds_gv_inject.
Require Import sb_ds_trans_axioms.

Ltac zauto := auto with zarith.
Ltac zeauto := eauto with zarith.

(***************************)

Lemma in_codom_of_rmap : forall rm2 pid bid eid,
  lookupAL (id * id) rm2 pid = ret (bid, eid) ->
  bid `in` codom rm2 /\ eid `in` codom rm2.
Proof.
  induction rm2; intros pid bid eid J.
    inversion J.  

    simpl in J.
    destruct a.
    destruct (pid == a); subst.
      inv J.
      simpl. auto.

      apply IHrm2 in J.
      destruct J as [J1 J2].
      simpl. destruct p.
      auto.
Qed.

Lemma inject_incr__preserves__reg_simulation : forall mi TD fl F rm1 rm2 lc1 lc2
    mi',
  reg_simulation mi TD fl F rm1 rm2 lc1 lc2 ->
  inject_incr mi mi' ->
  reg_simulation mi' TD fl F rm1 rm2 lc1 lc2.
Proof.
  intros mi TD fl F rm1 rm2 lc1 lc2 mi' Hrsim Hinc.
  destruct Hrsim as [J1 [J2 J3]].
  split.
    intros. apply J1 in H. destruct H as [gv2 [H1 H2]].
    exists gv2. split; eauto using gv_inject_incr.
  split; auto.
    intros. apply J2 in H. 
    destruct H as [bv2 [ev2 [bgv2 [egv2 [H1 [H2 [H3 [H4 H5]]]]]]]].
    exists bv2. exists ev2. exists bgv2. exists egv2.
    repeat (split; eauto using gv_inject_incr).
Qed.

Lemma gv_inject__same_size : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 ->
  sizeGenericValue gv1 = sizeGenericValue gv2.
Proof.
  intros mi gv1 gv2 Hinj.
  induction Hinj; simpl; auto.
Qed.

Lemma simulation__fit_gv : forall maxb mi TD t Mem Mem2 gv1 gv1' gv2,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gv1 gv2 ->
  fit_gv TD t gv1 = ret gv1' ->
  exists gv2', 
    fit_gv TD t gv2 = ret gv2' /\ gv_inject mi gv1' gv2'.
Proof.
  intros maxb mi TD t Mem Mem2 gv1 gv1' gv2 Hwfmi Hinj Hfit.
  unfold fit_gv in *.
  destruct (getTypeSizeInBits TD t); tinv Hfit.
  erewrite <- gv_inject__same_size; eauto.
  destruct (sizeGenericValue gv1 =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)); 
    inv Hfit; eauto using gv_inject_gundef.
Qed.

Lemma simulation___cundef_gv : forall maxb mi t Mem Mem2 gv,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gv gv ->
  gv_inject mi (cundef_gv gv t) (cundef_gv gv t).
Proof.
  intros.
  destruct t; simpl; eauto.
    destruct f; simpl; eauto.
    inv H. unfold null. eauto.
Qed.

Lemma simulation___cgv2gv : forall maxb mi t Mem Mem2 gv1 gv2,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gv1 gv2 ->
  gv_inject mi (? gv1 # t ?) (? gv2 # t ?).
Proof.
  intros maxb mi t Mem Mem2 gv1 gv2 Hwfmi Hinj.
  induction Hinj; auto.
    inv H; simpl; eauto.
    destruct gv1; inv Hinj; eauto.
      eapply simulation___cundef_gv; eauto.
Qed.

Lemma simulation__getOperandValue : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 
    gl F v gv,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  getOperandValue TD v lc gl = ret gv ->
  exists gv', 
    getOperandValue TD v lc2 gl = ret gv' /\
    gv_inject mi gv gv'.
Proof.
  intros maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F v gv Hwfg H0 H1 H2.
  unfold getOperandValue in *.
  destruct H1 as [H1 _].
  destruct v.
    apply H1 in H2. auto.

    exists gv. split; auto. eapply sb_mem_inj__const2GV; eauto.
Qed.

Lemma simulation__BOP : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F bop0 sz0 
    v1 v2 gv3,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  BOP TD lc gl bop0 sz0 v1 v2 = ret gv3 ->
  exists gv3',
    BOP TD lc2 gl bop0 sz0 v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F bop0 sz0 v1 v2 gv3 Hwfg H0 
    H1 H3.
  unfold BOP in *.
  remember (getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv H3.
  remember (getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv H2.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2.
  eapply simulation__getOperandValue in HeqR2; eauto.
  destruct HeqR2 as [g0' [J3 J4]].
  rewrite J3.
  eapply simulation__mbop in H3; eauto.
Qed.

Lemma simulation__FBOP : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F fop0 fp 
    v1 v2 gv3,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  FBOP TD lc gl fop0 fp v1 v2 = ret gv3 ->
  exists gv3',
    FBOP TD lc2 gl fop0 fp v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof.  
  intros maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F fop0 fp v1 v2 gv3 Hwfg H0 
    H1 H3.
  unfold FBOP in *.
  remember (getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv H3.
  remember (getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv H2.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2.
  eapply simulation__getOperandValue in HeqR2; eauto.
  destruct HeqR2 as [g0' [J3 J4]].
  rewrite J3.
  eapply simulation__mfbop in H3; eauto.
Qed.

Lemma simulation__GEP : forall maxb mi TD Mem Mem2 inbounds0 vidxs vidxs' gvp1 
    gvp gvp' t,
  wf_sb_mi maxb mi Mem Mem2 ->
  gv_inject mi gvp gvp' ->
  gvs_inject mi vidxs vidxs' ->
  GEP TD t gvp vidxs inbounds0 = ret gvp1 ->
  exists gvp2,
    GEP TD t gvp' vidxs' inbounds0 = ret gvp2 /\
    gv_inject mi gvp1 gvp2.
Proof.
  intros maxb mi TD Mem Mem2 inbounds0 vidxs vidxs' gvp1 gvp gvp' t H H0 H1 H2.
  unfold GEP in *.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; inv H2.
    symmetry in HeqR.
    eapply simulation__GV2ptr in HeqR; eauto.
    destruct HeqR as [v' [J1 J2]].
    rewrite J1. 
    assert (GVs2Nats TD vidxs = GVs2Nats TD vidxs') as EQ.
      eapply simulation__GVs2Nats; eauto.
    rewrite <- EQ.
    destruct (GVs2Nats TD vidxs).
      remember (mgep TD t v l0) as R1.
      destruct R1; inv H4.
        symmetry in HeqR1.
        eapply simulation__mgep in HeqR1; eauto.
        destruct HeqR1 as [v0' [J11 J12]].
        rewrite J11. exists (ptr2GV TD v0').
        unfold ptr2GV, val2GV.
        simpl. eauto.

        symmetry in HeqR1.
        eapply simulation__mgep' in HeqR1; eauto.
        rewrite HeqR1. rewrite H3.
        eauto using gv_inject_gundef.

      rewrite H4. eauto using gv_inject_gundef.

    erewrite simulation__GV2ptr'; eauto.
    rewrite H4. eauto using gv_inject_gundef.
Qed.

Lemma simulation__values2GVs : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 
    gl F idxs gvs,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  values2GVs TD idxs lc gl = ret gvs ->
  exists gvs', 
    values2GVs TD idxs lc2 gl = ret gvs' /\
    gvs_inject mi gvs gvs'.
Proof.
  induction idxs; simpl; intros.
    inv H2.
    exists nil. simpl. split; auto.

    remember (getOperandValue TD v lc gl) as R.
    destruct R; tinv H2.
    remember (values2GVs TD idxs lc gl) as R1.
    destruct R1; inv H2.
    symmetry in HeqR, HeqR1.
    eapply simulation__getOperandValue in HeqR; eauto.
    destruct HeqR as [gv' [J1 J2]].
    rewrite J1.
    eapply IHidxs in H1; eauto.
    destruct H1 as [gvs' [J3 J4]].
    rewrite J3.
    exists (gv' :: gvs').
    split; auto.    
      simpl. split; auto.
Qed.

Lemma simulation__TRUNC : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F t1 
    v1 gv3 op t2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  TRUNC TD lc gl op t1 v1 t2 = ret gv3 ->
  exists gv3',
    TRUNC TD lc2 gl op t1 v1 t2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof. intros.
  unfold TRUNC in *.
  remember (getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv H2.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  eapply simulation__mtrunc in H4; eauto.
Qed.

Lemma simulation__EXT : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F t1 
    v1 gv3 op t2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  EXT TD lc gl op t1 v1 t2 = ret gv3 ->
  exists gv3',
    EXT TD lc2 gl op t1 v1 t2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof. intros.
  unfold EXT in *.
  remember (getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv H2.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  eapply simulation__mext in H4; eauto.
Qed.

Lemma simulation__CAST : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F t1 
    v1 gv3 op t2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  CAST TD lc gl op t1 v1 t2 = ret gv3 ->
  exists gv3',
    CAST TD lc2 gl op t1 v1 t2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof. intros.
  unfold CAST in *.
  remember (getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv H2.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  eapply simulation__mcast in H4; eauto.
Qed.

Lemma simulation__ICMP : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F t1 
    v1 gv3 cond0 v2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  ICMP TD lc gl cond0 t1 v1 v2 = ret gv3 ->
  exists gv3',
    ICMP TD lc2 gl cond0 t1 v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof. intros.
  unfold ICMP in *.
  remember (getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv H2.
  remember (getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv H4.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2.
  eapply simulation__getOperandValue in HeqR2; eauto.
  destruct HeqR2 as [g0' [J3 J4]].
  rewrite J3.
  eapply simulation__micmp in H3; eauto.
Qed.

Lemma simulation__FCMP : forall maxb mi rm rm2 lc lc2 TD Mem Mem2 gl F fp 
    v1 gv3 fcond0 v2,
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation mi TD gl F rm rm2 lc lc2 ->
  FCMP TD lc gl fcond0 fp v1 v2 = ret gv3 ->
  exists gv3',
    FCMP TD lc2 gl fcond0 fp v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof. intros.
  unfold FCMP in *.
  remember (getOperandValue TD v1 lc gl) as R1.
  destruct R1; inv H2.
  remember (getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv H4.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2.
  eapply simulation__getOperandValue in HeqR2; eauto.
  destruct HeqR2 as [g0' [J3 J4]].
  rewrite J3.
  eapply simulation__mfcmp in H3; eauto.
Qed.

Lemma lookupAL_wf_globals : forall mgb gl g ofs b i0 TD,
  wf_globals mgb gl ->
  0 <= mgb ->
  GV2val TD g = ret Vptr b ofs ->
  ret g = lookupAL GenericValue gl i0 ->
  b <= mgb.
Proof.
  induction gl; intros.
    inversion H2.

    destruct a. simpl in *.
    destruct H as [J1 J2].
    destruct (i0 == i2); subst; eauto.
      inv H2.
      unfold GV2val in H1.
      destruct g0; inv H1.
      destruct p.
      destruct g0; inv H2.
      simpl in J1.
      destruct J1; auto.
Qed.      

Lemma trans_cmds_inv : forall ex_ids1 rm2 c cs ex_ids2 cs',
  trans_cmds ex_ids1 rm2 (c :: cs) = ret (ex_ids2, cs') ->
  exists ex_ids3, exists cs1', exists cs2',
  trans_cmd ex_ids1 rm2 c = ret (ex_ids3, cs1') /\
  trans_cmds ex_ids3 rm2 cs = ret (ex_ids2, cs2') /\  
  cs1' ++ cs2' = cs'.
Proof.
  intros. simpl in H.
  destruct (trans_cmd ex_ids1 rm2 c) as [[ex_ids3 cs1]|]; 
    try solve [inversion H].
  remember (trans_cmds ex_ids3 rm2 cs) as R.
  destruct R as [[ex_ids4 cs2]|]; inv H.
  exists ex_ids3. exists cs1. exists cs2. eauto.
Qed.


Lemma mem_simulation__malloc : forall mi TD MM Mem Mem2 tsz gn align0 Mem' mb 
    mgb,
  wf_sb_mi mgb mi Mem Mem2 ->
  mem_simulation mi TD mgb MM Mem Mem2 ->
  malloc TD Mem tsz gn align0 = ret (Mem', mb) ->
  exists mi', exists Mem2', exists mb',
    malloc TD Mem2 tsz gn align0 = ret (Mem2', mb') /\
    wf_sb_mi mgb mi' Mem' Mem2' /\
    mem_simulation mi' TD mgb MM Mem' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb = Some (mb', 0) /\
    (forall b, b <> mb -> mi b = mi' b).
Proof.
  intros mi TD MM Mem Mem2 tsz gn align0 Mem' mb mgb Hwfmi Hmsim Halloc.
  destruct Hmsim as [H1 [Hmgb [Hzeroout H2]]].
  unfold malloc in *.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; try solve [inversion Halloc].
  remember (Mem.alloc Mem 0 (Size.to_Z tsz * z)) as R1.
  destruct R1 as [Mem1 mb1].
  destruct (zle 0 (Size.to_Z tsz * z)); inv Halloc.
  remember (Mem.alloc Mem2 0 (Size.to_Z tsz * z)) as R2.
  destruct R2 as [Mem2' mb2].
  exists (fun b => if zeq b mb then Some (mb2,0%Z) else mi b).
  exists Mem2'. exists mb2.
  split; auto.
  assert (inject_incr mi (fun b : Z => if zeq b mb then ret (mb2, 0) else mi b))
    as Hinject_incr.
    unfold inject_incr.
    intros b b' d H.
    destruct (zeq b mb); subst; auto.
      clear - Hwfmi H HeqR1.
      symmetry in HeqR1.
      apply Mem.alloc_result in HeqR1. subst.
      destruct Hwfmi as [_ _ Hmap1 _].
      assert (mi (Mem.nextblock Mem) = None) as J.
        apply Hmap1; auto with zarith.
      rewrite H in J. inversion J.

  split; auto.
  Case "wfmi".
    clear - Hwfmi Hmgb HeqR2 HeqR1.
    destruct Hwfmi as [Hno_overlap Hnull Hmap1 Hmap2 mi_freeblocks 
      mi_mappedblocks mi_range_block mi_bounds mi_globals].
    symmetry in HeqR2, HeqR1. 
    assert (J:=HeqR2).
    apply Mem.nextblock_alloc in HeqR2.
    split.
    SCase "no_overlap".
      clear - Hno_overlap J Hmap2.
      unfold MoreMem.meminj_no_overlap in *.
      intros.      
      destruct (zeq b1 mb); subst.
        destruct (zeq b2 mb); subst.
          contradict H; auto.

          inv H0.
          apply Hmap2 in H1.
          apply Mem.alloc_result in J.
          subst. clear - H1. intro J. subst. contradict H1; zauto.
        destruct (zeq b2 mb); subst; eauto.
          inv H1.
          apply Hmap2 in H0.
          apply Mem.alloc_result in J.
          subst. clear - H0. intro J. subst. contradict H0; zauto.
    SCase "null".
      destruct (zeq Mem.nullptr mb); subst; auto.
        apply Mem.alloc_result in HeqR1.
        assert(J':=@Mem.nextblock_pos Mem).
        rewrite <- HeqR1 in J'.
        unfold Mem.nullptr in J'.
        contradict J'; zauto.
    SCase "map1".
      intros b H2.
      assert (J':=HeqR1).
      apply Mem.alloc_result in J'.
      apply Mem.nextblock_alloc in HeqR1.
      rewrite HeqR1 in H2.
      destruct (zeq b mb); subst; zeauto.
        contradict H2; zauto.
    SCase "map2".
      intros b1 b delta2 J'.
      rewrite HeqR2.
      destruct (zeq b1 mb); subst; zeauto.
        inv J'.
        apply Mem.alloc_result in J.
        subst.
        auto with zarith.
    SCase "freeblocks".
      intros b J'.
      destruct (zeq b mb); subst.
        apply Mem.valid_new_block in HeqR1.
        contradict HeqR1; auto.

        apply mi_freeblocks.
          intro J1. apply J'.
          eapply Mem.valid_block_alloc; eauto.
    SCase "mappedblocks".
      intros b b' delta J'.
      destruct (zeq b mb); subst.
        inv J'.            
        apply Mem.valid_new_block in J; auto.
        eapply Mem.valid_block_alloc; eauto.
    SCase "range_block".
      intros b b' delta J'.
      destruct (zeq b mb); inv J'; subst; eauto.
    SCase "bounds".
      intros b b' delta J'.
      erewrite Mem.bounds_alloc; eauto.
      erewrite Mem.bounds_alloc with (m2:=Mem2'); eauto.
      unfold eq_block.
      destruct (zeq b mb); subst.
        inv J'.
        destruct (zeq b' b'); subst; auto.
          contradict n; auto.      

        destruct (zeq b' mb2); subst; eauto.
          apply Hmap2 in J'.
          apply Mem.alloc_result in J.
          rewrite J in J'. contradict J'; zauto.
    SCase "globals".
      intros b J'.
      destruct (zeq b mb); subst; eauto.
        assert (J'':=J').
        apply mi_globals in J'.
        destruct (SBspecMetadata.valid_block_dec Mem mb).
          apply Mem.fresh_block_alloc in HeqR1.
          contradict HeqR1; auto.
     
          apply mi_freeblocks in n.        
          rewrite n in J'. inversion J'.
 
  split; auto.
  Case "msim".
    split.    
    SCase "msim1".
      clear H2.
      destruct H1.
      apply MoreMem.mk_mem_inj.
      SSCase "mi_access".
        intros b1 b2 d c ofs p J1 J2.
        destruct (zeq b1 mb); subst; inv J1.
        SSSCase "b1=mb".
          symmetry in HeqR1.
          symmetry in HeqR2.
          destruct J2 as [J21 J22].
          assert (0 <= ofs /\ ofs + size_chunk c <= Size.to_Z tsz * z) as EQ.
            destruct (Z_le_dec 0 ofs).
              destruct (Z_le_dec (ofs + size_chunk c) (Size.to_Z tsz * z)); auto.
                apply Mem.perm_alloc_3 with (ofs:=ofs+size_chunk c-1) (p:=p) in 
                  HeqR1; auto with zarith.
                unfold Mem.range_perm in J21.
                assert (ofs <= ofs + size_chunk c - 1 < ofs + size_chunk c) as J.
                  assert (J':=@Memdata.size_chunk_pos c).
                  auto with zarith.
                apply J21 in J.           
                contradict J; auto. 
              apply Mem.perm_alloc_3 with (ofs:=ofs) (p:=p) in HeqR1; 
                auto with zarith.
              unfold Mem.range_perm in J21.
              assert (ofs <= ofs < ofs + size_chunk c) as J.
                assert (J':=@Memdata.size_chunk_pos c).
                auto with zarith.
              apply J21 in J.           
              contradict J; auto. 

          apply Mem.valid_access_alloc_same with (chunk:=c)(ofs:=ofs+0) in HeqR2;
            auto with zarith.
            eapply Mem.valid_access_implies; eauto using perm_F_any.

        SSSCase "b1<>mb".
          eapply Mem.valid_access_alloc_other; eauto.
          eapply Mem.valid_access_alloc_inv with (b:=mb)(lo:=0)
            (hi:=Size.to_Z tsz * z)(p:=p) in J2; eauto.
          destruct (eq_block); subst; try solve [eauto | contradict n; auto].

      SSCase "mi_memval".
Transparent Mem.alloc.
        intros b1 ofs b2 d J1 J2.
        injection HeqR1. intros NEXT MEM.
        injection HeqR2. intros NEXT2 MEM2.
        destruct Mem2. destruct Mem2'. destruct Mem. destruct Mem'. 
        inv MEM.
        inv MEM2. clear HeqR1 HeqR2.
        simpl in *.
        unfold Mem.perm in *. simpl in *.
        clear maxaddress_pos0 conversion_props0 maxaddress_pos2 
              conversion_props2.
        unfold update.     
        destruct (zeq b1 nextblock1); subst; inv J1.
        SSSCase "b1=nextblock1".
          destruct (zeq b2 b2) as [e | n]; 
            try solve [contradict n; auto].
          apply MoreMem.memval_inject_undef.

        SSSCase "b1<>mb".
          destruct (zeq b2 nextblock); subst.
            clear - H0 Hwfmi.
            destruct Hwfmi. simpl in *.
            apply Hmap2 in H0.
            contradict H0; auto with zarith.

            apply MoreMem.memval_inject_incr with (f:=mi); auto.
              apply mi_memval; auto.
                clear - J2 n.
                unfold update in J2.
                destruct (zeq b1 nextblock1); subst; 
                  try solve [auto | contradict n; auto].

Global Opaque Mem.alloc.

    split.
    SCase "mgb".
      clear - Hmgb HeqR2.
      symmetry in HeqR2.
      apply Mem.nextblock_alloc in HeqR2.
      rewrite HeqR2.
      auto with zarith.

    split.
    SCase "zeroout".
      clear - Hzeroout HeqR1.
      symmetry in HeqR1.
      apply Mem.nextblock_alloc in HeqR1. intros.
      rewrite HeqR1 in H. 
      apply Hzeroout; auto with zarith.

    SCase "msim2".
      clear H1.
      intros lc2 gl b ofs blk bofs eofs als bid0 eid0 pgv' fs F B cs tmn S Ps EC 
        v cm Hwfg J1 J2 J3.
        apply gv_inject_ptr_inv in J2.
        destruct J2 as [b' [ofs' [J5 J6]]].
        inv J6.
        destruct (zeq b mb); subst; inv H3.
          clear H2.
          exists null. exists null.
          unfold get_mem_metadata, ptr2GV, val2GV, GV2ptr in J1.
          assert (mb >= Mem.nextblock Mem) as GE.
            symmetry in HeqR1.
            apply Mem.alloc_result in HeqR1.
            subst. omega.
          rewrite Hzeroout in J1; auto. inv J1.
          assert (gv_inject (fun b : Z => if zeq b mb then ret (b', 0) else mi b)
            null null) as Hinject_null.
              unfold null.
              apply gv_inject_cons; auto.
                inv Hwfmi.
                apply MoreMem.val_inject_ptr with (delta:=0).
                  destruct (zeq Mem.nullptr mb); subst; auto.
                    symmetry in HeqR1.
                    apply Mem.alloc_result in HeqR1.
                    assert(J':=@Mem.nextblock_pos Mem).
                    rewrite <- HeqR1 in J'.
                    unfold Mem.nullptr in J'.
                    contradict J'; zauto.
                  rewrite Int.add_zero; auto.
          split; auto.
            eapply get_mmetadata_fn__alloc__zeroout; 
              unfold ptr2GV, val2GV; eauto.

          assert (gv_inject mi ((Vptr b ofs,cm)::nil) 
            ((Vptr b' (Int.add 31 ofs (Int.repr 31 delta)),cm) :: nil)) as W.
            clear - Hwfg J3 HeqR2 Hmgb n H0.
            unfold ptr2GV, val2GV. simpl.
              apply gv_inject_cons; auto.
              apply MoreMem.val_inject_ptr with (delta:=delta); auto.
          eapply H2 with (lc2:=lc2)(gl:=gl)(als:=als)(bid0:=bid0)(eid0:=eid0)
            (v:=v)(fs:=fs)(F:=F)(B:=B)(cs:=cs)(tmn:=tmn)(S0:=S)
            (Ps:=Ps)(EC:=EC)in J1; eauto.
          destruct J1 as [bgv' [egv' [J37 [J33 J34]]]].
          clear H2.
          exists bgv'. exists egv'. 
          split.
            eapply get_mmetadata_fn__alloc__preserve; eauto.
            split; eauto using gv_inject_incr.

  split; auto.
  split.
    destruct (zeq mb mb); auto.
      contradict n; auto.
    intros.
    destruct (zeq b mb); subst; auto.
      contradict H; auto.
Qed.

Ltac invert_prop_reg_metadata :=
  match goal with
  | [H : SBspec.prop_reg_metadata _ _ _ _ _ = (_, _) |- _ ] =>
      inv H; subst; eauto
  end.

Lemma notin_codom__neq : forall rm d id0 id1 bid eid,
  AtomSetImpl.inter d (codom rm) [<=] {} ->
  id0 `in` d ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  id0 <> bid /\ id0 <> eid.
Proof.
  induction rm; intros d id0 id1 bid eid J1 J2 J3.
    inversion J3.

    destruct a. destruct p. simpl in *.
    destruct (id1 == i0); subst.
      inv J3. clear IHrm. fsetdec.
      eapply IHrm in J3; eauto.
        clear - J1. fsetdec.
Qed.

Lemma ids2atoms_dom : forall x d,
  In x d <-> x `in` ids2atoms d.
Proof.
  induction d.
    split; intro J.
      inversion J.
      contradict J; fsetdec.
    split; simpl; intro J.
      destruct J as [J | J]; subst; auto.
        apply IHd in J. auto.

      assert (x `in` (singleton a) \/ x `in` (ids2atoms d)) as H.
        fsetdec.
      destruct H as [H | H]; try fsetdec.
        apply IHd in H. auto.
Qed.

Lemma tmp_is_fresh : forall i0 d ex_ids tmp ex_ids',
  i0 `in` d ->
  d [<=] ids2atoms ex_ids ->
  (tmp, ex_ids') = mk_tmp ex_ids ->
  i0 <> tmp.
Proof.
  intros. unfold mk_tmp in H1.
  destruct (atom_fresh_for_list ex_ids).
  inv H1.
  assert (x `notin` ids2atoms ex_ids) as J.
    intro H1. apply n.
    apply ids2atoms_dom; auto.              
  fsetdec.
Qed.

Lemma rmap_lookupAL : forall rm bid eid id1,
  ret (bid, eid) = lookupAL (id * id) rm id1 ->
  bid `in` codom rm /\ eid `in` codom rm /\ id1 `in` dom rm.
Proof.
  induction rm; intros.
    inversion H.
    destruct a. destruct p. simpl in *.
    destruct (id1 == a); subst.
      inv H. fsetdec.
      apply IHrm in H. fsetdec.
Qed.

Lemma rm_codom_disjoint_spec : forall rm pid bid eid,
  rm_codom_disjoint rm ->
  Some (bid, eid) = lookupAL _ rm pid ->
  bid <> eid /\ bid <> pid /\ eid <> pid.
Proof.
  induction rm; intros. 
    inversion H0.
    destruct a. destruct p. simpl in *.
    destruct (pid == i0); subst.
      inv H0. destruct H as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
      repeat split; auto.

      destruct H as [_ [_ [_ [_ [_ [_ H]]]]]].
      eapply IHrm in H; eauto.
Qed.

Lemma rm_codom_disjoint_spec' : forall rm bid1 eid1 id1 bid2 eid2 id2,
  rm_codom_disjoint rm ->
  ret (bid1, eid1) = lookupAL (id * id) rm id1 ->
  ret (bid2, eid2) = lookupAL (id * id) rm id2 ->
  id1 <> id2 ->
  bid1 <> bid2 /\ bid1 <> eid2 /\ bid1 <> id2 /\ bid1 <> id1 /\
  eid1 <> bid2 /\ eid1 <> eid2 /\ eid1 <> id1 /\ eid1 <> id2 /\
  bid2 <> id1 /\ eid2 <> id1.
Proof.
  induction rm; intros.
    inversion H0.
    destruct a. destruct p. simpl in *.
    destruct H as [H8 [H9 [H3 [H4 [H5 [H6 H7]]]]]].
    destruct (id1 == i0); subst.
      destruct (id2 == i0); subst.
        contradict H2; auto.

        inv H0.
        eapply rm_codom_disjoint_spec in H7; eauto.
        apply rmap_lookupAL in H1.
        destruct H1 as [H11 [H12 H13]].
        destruct H7 as [H0 [H1 H10]].
        repeat (split; auto). 
          clear - H5 H11. fsetdec.
          clear - H5 H12. fsetdec.
          clear - H5 H13. fsetdec.
          clear - H6 H11. fsetdec.
          clear - H6 H12. fsetdec.
          clear - H6 H13. fsetdec.
          clear - H11 H4. fsetdec.
          clear - H12 H4. fsetdec.
      destruct (id2 == i0); subst; eauto.
        inv H1.
        eapply rm_codom_disjoint_spec in H7; eauto.
        destruct H7 as [H1 [H7 H10]].
        apply rmap_lookupAL in H0.
        destruct H0 as [H11 [H12 H13]].
        repeat (split; auto). 
          clear - H5 H11. fsetdec.
          clear - H6 H11. fsetdec.
          clear - H4 H11. fsetdec.
          clear - H5 H12. fsetdec.
          clear - H6 H12. fsetdec.
          clear - H4 H12. fsetdec.
          clear - H5 H13. fsetdec.
          clear - H6 H13. fsetdec.
Qed.

Lemma tmp_is_fresh' : forall id1 ex_ids tmp ex_ids' bid eid rm,
  codom rm [<=] ids2atoms ex_ids ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  (tmp, ex_ids') = mk_tmp ex_ids ->
  bid <> tmp /\ eid <> tmp.
Proof.
  intros. unfold mk_tmp in H1.
  destruct (atom_fresh_for_list ex_ids).
  inv H1.
  assert (x `notin` ids2atoms ex_ids) as J.
    intro H1. apply n.
    apply ids2atoms_dom; auto.              
  apply rmap_lookupAL in H0.
  fsetdec.
Qed.

Lemma mk_tmp_inc : forall ex_ids ex_ids3 ex_ids5 tmp,
  incl ex_ids ex_ids3 ->
  (tmp, ex_ids5) = mk_tmp ex_ids3 ->
  incl ex_ids ex_ids5.
Proof.
  intros. intros x J. unfold mk_tmp in H0.
  remember (atom_fresh_for_list ex_ids3) as R.
  destruct R. inv H0.
  simpl. auto.
Qed.

Lemma reg_simulation_spec : forall mi nts los gl f1 rm1 rm2 lc1 lc2 gv1 i0,
  reg_simulation mi (los,nts) gl f1 rm1 rm2 lc1 lc2 ->
  lookupAL GenericValue lc1 i0 = ret gv1 ->
  i0 `in` (ids2atoms (getFdefLocs f1)).
Proof.
  intros.
  destruct H as [_ [_ H]].
  apply H in H0.
  apply ids2atoms_dom; auto.
Qed.

Lemma in_singleton : forall a d, singleton a [<=] d <-> a `in` d.
Proof.
  intros.
  unfold AtomSetImpl.Subset.
  split; intros; eauto.
    assert (a0 = a) as EQ. fsetdec.
    subst. auto.
Qed.      

Lemma ids2atoms__in : forall a d, In a d <-> singleton a [<=] (ids2atoms d).
Proof. 
  induction d; simpl.
    split; intros. 
      inv H.

      apply in_singleton in H. 
      fsetdec.
    destruct IHd as [J1 J2].
    split; intros. 
      destruct H as [H | H]; subst. 
        fsetdec.        
        apply J1 in H. fsetdec.
        assert (a = a0 \/ a `in` (ids2atoms d)) as J.
          fsetdec.
        destruct J as [J | J]; subst; auto.
          apply in_singleton in J. eauto.
Qed.

Lemma ids2atoms__notin : forall a d, ~ In a d <-> a `notin` (ids2atoms d).
Proof. 
  split; intros.  
    destruct (AtomSetProperties.In_dec a (ids2atoms d)); auto.
      apply in_singleton in i0.
      apply ids2atoms__in in i0. congruence.
    destruct (in_dec eq_atom_dec a d); auto.
      apply ids2atoms__in in i0.
      apply in_singleton in i0. congruence.
Qed.

Lemma incl_nil : forall A (d:list A), incl nil d.
Proof. intros. intros x J. inv J. Qed.

Lemma ids2atoms__inc : forall d1 d2,
  incl d1 d2 <-> ids2atoms d1 [<=] ids2atoms d2.
Proof.
  intros.
  split; intros.
    induction d1; simpl.
      fsetdec.
      simpl_env in H.
      assert (H':=H).
      apply AtomSet.incl_app_invr in H.
      apply AtomSet.incl_app_invl in H'.
      apply IHd1 in H.      
      assert (In a [a]) as Hin. simpl. auto.
      apply H' in Hin.
      apply ids2atoms__in in Hin.
      fsetdec.
    induction d1; simpl in *; auto using incl_nil.
      intros x J.
      simpl in J.
      destruct J as [J | J]; subst.
      apply ids2atoms__in. fsetdec.

      revert J. revert x. 
      apply IHd1. fsetdec.
Qed.

Lemma gen_metadata_id_spec : forall (ex_ids1 ex_ids0 : ids) i0 rm1
  (Hin : i0 `in` ids2atoms ex_ids0)
  (H1 : ids2atoms ex_ids0[<=]ids2atoms ex_ids1)
  (H2 : AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm1)[<=]empty)
  (H3 : codom rm1[<=]ids2atoms ex_ids1)
  (H4 : rm_codom_disjoint rm1)
  (H6 : dom rm1[<=]ids2atoms ex_ids0)
  (ex_ids5 : ids) (rm5 : rmap) 
  (b : id) (e : id)
  (Hgenid : gen_metadata_id ex_ids1 rm1 i0 = (b, e, ex_ids5, rm5)),
   ids2atoms ex_ids1[<=]ids2atoms ex_ids5 /\
   AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm5)[<=]empty /\
   codom rm5[<=]ids2atoms ex_ids5 /\
   rm_codom_disjoint rm5 /\ dom rm5[<=]ids2atoms ex_ids0.
Proof.
  intros.
      unfold gen_metadata_id in Hgenid.      
      remember (atom_fresh_for_list ex_ids1) as R1.
      destruct R1.
      remember (atom_fresh_for_list (x::ex_ids1)) as R2.
      destruct R2.
      inv Hgenid.
      assert (b `notin` ids2atoms ex_ids1) as Hnotinb.
        apply ids2atoms__notin; auto.
      assert (e `notin` ids2atoms (b::ex_ids1)) as Hnotine.
        apply ids2atoms__notin; auto.
      simpl in Hnotine.
      destruct_notin.
      simpl.
      split. fsetdec.
      split.
        clear - H2 H1 NotInTac Hnotinb.
        fsetdec.
      split. clear - H3. fsetdec.
      split.
        clear HeqR1 HeqR2 n n0 Hnotine.
        split. clear - Hin H1 Hnotinb. fsetdec.
        split. clear - Hin H1 NotInTac. fsetdec.
        split; auto.
        split. clear - Hin H2. fsetdec.
        split. clear - H3 H6 Hnotinb H1. fsetdec.
        split; auto. 
          clear - H3 H6 NotInTac H1. fsetdec.
 
        simpl. clear - H6 Hin.
        intros x J. 
        assert (x = i0 \/ x `in` (dom rm1)) as H.
          fsetdec.
        destruct H as [H | H]; subst; auto.
Qed.      
  
Lemma gen_metadata_args_spec : forall ex_ids0 la rm1 rm2 ex_ids1 ex_ids2, 
  incl (getArgsIDs la) ex_ids0 ->
  ids2atoms ex_ids0 [<=] ids2atoms ex_ids1 ->
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm1) [<=] {} ->
  codom rm1 [<=] ids2atoms ex_ids1 ->
  rm_codom_disjoint rm1 ->
  dom rm1 [<=] ids2atoms ex_ids0 ->
  gen_metadata_args ex_ids1 rm1 la = (ex_ids2,rm2) ->
  ids2atoms ex_ids1 [<=] ids2atoms ex_ids2 /\
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm2) [<=] {} /\
  codom rm2 [<=] ids2atoms ex_ids2 /\
  rm_codom_disjoint rm2 /\
  dom rm2 [<=] ids2atoms ex_ids0.
Proof.
  induction la; simpl; intros rm1 rm2 ex_ids1 ex_ids2 Hinc H1 H2 H3 H4 H6 H5.
    inv H5. split; auto. fsetdec.

    destruct a. destruct p.
    assert (i0 `in` ids2atoms ex_ids0) as Hin.
      apply ids2atoms__inc in Hinc.
      simpl in Hinc. fsetdec.
    simpl_env in Hinc. apply AtomSet.incl_app_invr in Hinc.
    destruct (isPointerTypB t).
      case_eq (gen_metadata_id ex_ids1 rm1 i0).
      intros [[b e] ex_ids5] rm5 Hgenid.
      rewrite Hgenid in H5.
      eapply gen_metadata_id_spec in Hgenid; eauto.
      destruct Hgenid as [J8 [J9 [J10 [J11 J12]]]].
      assert (ids2atoms ex_ids0[<=]ids2atoms ex_ids5) as Hinc'.
        clear - H1 J8. fsetdec.
      apply IHla in H5; auto.
      destruct H5 as [J1 [J2 [J3 J4]]].
      split; auto. 
         clear - J8 J1. fsetdec.

      apply IHla in H5; auto.
Qed.

Lemma gen_metadata_phinodes_spec : forall ex_ids0 ps rm1 rm2 ex_ids1 ex_ids2,
  incl (getPhiNodesIDs ps) ex_ids0 ->
  ids2atoms ex_ids0 [<=] ids2atoms ex_ids1 ->
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm1) [<=] {} ->
  codom rm1 [<=] ids2atoms ex_ids1 ->
  rm_codom_disjoint rm1 ->
  dom rm1 [<=] ids2atoms ex_ids0 ->
  gen_metadata_phinodes ex_ids1 rm1 ps = (ex_ids2,rm2) ->
  ids2atoms ex_ids1 [<=] ids2atoms ex_ids2 /\
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm2) [<=] {} /\
  codom rm2 [<=] ids2atoms ex_ids2 /\
  rm_codom_disjoint rm2 /\
  dom rm2 [<=] ids2atoms ex_ids0.
Proof.
  induction ps; simpl; intros rm1 rm2 ex_ids1 ex_ids2 Hinc H1 H2 H3 H4 H6 H5.
    inv H5. split; auto. fsetdec.

    destruct a. simpl in *.
    assert (i0 `in` ids2atoms ex_ids0) as Hin.
      apply ids2atoms__inc in Hinc.
      simpl in Hinc. fsetdec.
    simpl_env in Hinc. apply AtomSet.incl_app_invr in Hinc.
    destruct (isPointerTypB t).
      case_eq (gen_metadata_id ex_ids1 rm1 i0).
      intros [[b e] ex_ids5] rm5 Hgenid.
      rewrite Hgenid in H5.
      eapply gen_metadata_id_spec in Hgenid; eauto.
      destruct Hgenid as [J8 [J9 [J10 [J11 J12]]]].
      assert (ids2atoms ex_ids0[<=]ids2atoms ex_ids5) as Hinc'.
        clear - H1 J8. fsetdec.
      apply IHps in H5; auto.
      destruct H5 as [J1 [J2 [J3 J4]]].
      split; auto. 
         clear - J8 J1. fsetdec.

      apply IHps in H5; auto.
Qed.

Lemma gen_metadata_cmds_spec : forall nts ex_ids0 cs rm1 rm2 ex_ids1 ex_ids2, 
  incl (getCmdsLocs cs) ex_ids0 ->
  ids2atoms ex_ids0 [<=] ids2atoms ex_ids1 ->
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm1) [<=] {} ->
  codom rm1 [<=] ids2atoms ex_ids1 ->
  rm_codom_disjoint rm1 ->
  dom rm1 [<=] ids2atoms ex_ids0 ->
  gen_metadata_cmds nts ex_ids1 rm1 cs = Some (ex_ids2,rm2) ->
  ids2atoms ex_ids1 [<=] ids2atoms ex_ids2 /\
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm2) [<=] {} /\
  codom rm2 [<=] ids2atoms ex_ids2 /\
  rm_codom_disjoint rm2 /\
  dom rm2 [<=] ids2atoms ex_ids0.
Proof.
  induction cs; simpl; intros rm1 rm2 ex_ids1 ex_ids2 Hinc H1 H2 H3 H4 H6 H5.
    inv H5. split; auto. fsetdec.

    destruct (getCmdTyp nts a); tinv H5. simpl in H5.
    assert ((getCmdLoc a) `in` ids2atoms ex_ids0) as Hin.
      apply ids2atoms__inc in Hinc.
      simpl in Hinc. fsetdec.
    simpl_env in Hinc. apply AtomSet.incl_app_invr in Hinc.
    destruct (isPointerTypB t).
      case_eq (gen_metadata_id ex_ids1 rm1 (getCmdLoc a)).
      intros [[b e] ex_ids5] rm5 Hgenid.
      rewrite Hgenid in H5.
      eapply gen_metadata_id_spec in Hgenid; eauto.
      destruct Hgenid as [J8 [J9 [J10 [J11 J12]]]].
      assert (ids2atoms ex_ids0[<=]ids2atoms ex_ids5) as Hinc'.
        clear - H1 J8. fsetdec.
      apply IHcs in H5; auto.
      destruct H5 as [J1 [J2 [J3 J4]]].
      split; auto. 
         clear - J8 J1. fsetdec.

      apply IHcs in H5; auto.
Qed.

Lemma gen_metadata_block_spec : forall nts ex_ids0 b rm1 rm2 ex_ids1 ex_ids2, 
  incl (getBlockLocs b) ex_ids0 ->
  ids2atoms ex_ids0 [<=] ids2atoms ex_ids1 ->
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm1) [<=] {} ->
  codom rm1 [<=] ids2atoms ex_ids1 ->
  rm_codom_disjoint rm1 ->
  dom rm1 [<=] ids2atoms ex_ids0 ->
  gen_metadata_block nts ex_ids1 rm1 b = Some (ex_ids2,rm2) ->
  ids2atoms ex_ids1 [<=] ids2atoms ex_ids2 /\
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm2) [<=] {} /\
  codom rm2 [<=] ids2atoms ex_ids2 /\
  rm_codom_disjoint rm2 /\
  dom rm2 [<=] ids2atoms ex_ids0.
Proof.
  intros nts ex_ids0 b rm1 rm2 ex_ids1 ex_ids2 Hinc H1 H2 H3 H4 H6 H5.
  destruct b.
  simpl in H5.
  case_eq (gen_metadata_phinodes ex_ids1 rm1 p).
  intros ex_ids5 rm5 Hgenps. rewrite Hgenps in H5.
  simpl in Hinc.
  assert (Hinc':=Hinc). 
  apply AtomSet.incl_app_invl in Hinc'.
  apply AtomSet.incl_app_invr in Hinc.
  apply AtomSet.incl_app_invl in Hinc.
  eapply gen_metadata_phinodes_spec in Hgenps; eauto.
  destruct Hgenps as [J8 [J9 [J10 [J11 J12]]]].
  assert (ids2atoms ex_ids0[<=]ids2atoms ex_ids5) as Hinc''.
    clear - H1 J8. fsetdec.
  eapply gen_metadata_cmds_spec in H5; eauto.
  destruct H5 as [J1 [J2 [J3 [J4 J5]]]].
  split; auto.
    clear - J8 J1. fsetdec.
Qed.

Lemma gen_metadata_blocks_spec : forall nts ex_ids0 bs rm1 rm2 ex_ids1 ex_ids2, 
  incl (getBlocksLocs bs) ex_ids0 ->
  ids2atoms ex_ids0 [<=] ids2atoms ex_ids1 ->
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm1) [<=] {} ->
  codom rm1 [<=] ids2atoms ex_ids1 ->
  rm_codom_disjoint rm1 ->
  dom rm1 [<=] ids2atoms ex_ids0 ->
  gen_metadata_blocks nts ex_ids1 rm1 bs = Some (ex_ids2,rm2) ->
  ids2atoms ex_ids1 [<=] ids2atoms ex_ids2 /\
  AtomSetImpl.inter (ids2atoms ex_ids0) (codom rm2) [<=] {} /\
  codom rm2 [<=] ids2atoms ex_ids2 /\
  rm_codom_disjoint rm2 /\
  dom rm2 [<=] ids2atoms ex_ids0.
Proof.
  induction bs; simpl; intros rm1 rm2 ex_ids1 ex_ids2 Hinc H1 H2 H3 H4 H6 H5.
    inv H5. split; auto. fsetdec.

    assert (Hinc':=Hinc). 
    apply AtomSet.incl_app_invl in Hinc'.
    apply AtomSet.incl_app_invr in Hinc.
    remember (gen_metadata_block nts ex_ids1 rm1 a) as R.
    destruct R as [[ex_ids5 rm5]|]; tinv H5.
    symmetry in HeqR.
    eapply gen_metadata_block_spec in HeqR; eauto.
    destruct HeqR as [J8 [J9 [J10 [J11 J12]]]].
    assert (ids2atoms ex_ids0[<=]ids2atoms ex_ids5) as Hinc''.
      clear - H1 J8. fsetdec.
    apply IHbs in H5; auto.
    destruct H5 as [J1 [J2 [J3 J4]]].
    split; auto. 
       clear - J8 J1. fsetdec.
Qed.
    
Lemma gen_metadata_fdef_spec : forall nts f1 rm2 ex_ids2,
  gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids2,rm2) ->
  ids2atoms (getFdefLocs f1) [<=] ids2atoms ex_ids2 /\
  AtomSetImpl.inter (ids2atoms (getFdefLocs f1)) (codom rm2) [<=] {} /\
  codom rm2 [<=] ids2atoms ex_ids2 /\
  rm_codom_disjoint rm2.
Proof.
  intros nts f1 rm2 ex_ids2 Hgenf.
  destruct f1. destruct f. simpl in *.
  case_eq (gen_metadata_args (getArgsIDs a ++ getBlocksLocs b) nil a).
  intros ex_ids3 rm3 Hgenargs.
  rewrite Hgenargs in Hgenf.
  assert (incl (getArgsIDs a) (getArgsIDs a ++ getBlocksLocs b)) as Hinc1.
    apply incl_appl; auto using incl_refl.
  assert (incl (getBlocksLocs b) (getArgsIDs a ++ getBlocksLocs b)) as Hinc2.
    apply incl_appr; auto using incl_refl.
  apply gen_metadata_args_spec with (ex_ids0:=getArgsIDs a ++ getBlocksLocs b) 
    in Hgenargs; simpl; auto; try fsetdec.
  destruct Hgenargs as [J1 [J2 [J3 [J4 J5]]]].
  apply gen_metadata_blocks_spec with (ex_ids0:=getArgsIDs a ++ getBlocksLocs b) 
    in Hgenf; auto.
  destruct Hgenf as [J6 [J7 [J78 [J9 J10]]]].
  split; auto.
    fsetdec.
Qed.

Lemma reg_simulation__updateAddAL_lc : forall mi los nts gl f1 rm1 rm2 lc1 lc2 i0
    gv gv' ex_ids3,
  reg_simulation mi (los, nts) gl f1 rm1 rm2 lc1 lc2 ->
  gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids3,rm2) ->
  In i0 (getFdefLocs f1) ->
  gv_inject mi gv gv' ->
  reg_simulation mi (los, nts) gl f1 rm1 rm2 (updateAddAL GenericValue lc1 i0 gv)
    (updateAddAL GenericValue lc2 i0 gv').
Proof.
  intros mi los nts gl f1 rm1 rm2 lc1 lc2 i0 gv gv' ex_ids3 Hsim Hgenmd Hin Hinj.

  assert (Hspec := Hgenmd).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].
  clear Hinc1 Hinc3.
  eapply ids2atoms_dom in Hin.
  assert (i0 `notin` codom rm2) as Hnotin.
    clear - Hin Hdisj1. fsetdec.

  destruct Hsim as [J1 [J2 J3]].    
  split.
    intros i1 gv1 J.
    destruct (id_dec i0 i1); subst.
      rewrite lookupAL_updateAddAL_eq in *; auto.
      inv J. exists gv'. auto.
    
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.

  split.
    intros vp blk1 bofs1 eofs1 J.
    apply J2 in J. 
    destruct J as [bv2 [ev2 [bgv2 [egv2 [J11 [J12 [J13 [J14 J15]]]]]]]].
    exists bv2. exists ev2. exists bgv2. exists egv2.
    split; auto.
    destruct vp as [pid |]; simpl in J11.
      case_eq (lookupAL (id * id) rm2 pid).
        intros [bid eid] J.
        rewrite J in J11.    
        inv J11.
        simpl.
        assert (J':=J).
        apply in_codom_of_rmap in J'.    
        destruct J' as [J16 J17].      
        rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
        rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
        repeat (split; auto).

        intro J.
        rewrite J in J11. inversion J11.

      case_eq (get_const_metadata c).
        intros [bc ec] J.
        rewrite J in J11.
        inv J11.
        simpl in *.
        repeat (split; auto).

        intro J.  rewrite J in J11.
        inv J11. simpl in *.
        repeat (split; auto).

    intros i1 gv1 Hlk.
    destruct (id_dec i0 i1); subst.
      rewrite lookupAL_updateAddAL_eq in Hlk; auto.
      inv Hlk. apply ids2atoms_dom in Hin; auto.
    
      rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma reg_simulation__updateAddAL_md : forall mi los nts gl f1 rm1 rm2 lc1 lc2 
    id0 blk1 bofs1 eofs1 bgv2 egv2 bid eid mgb M1 M2 ex_ids
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids,rm2) ->
  reg_simulation mi (los,nts) gl f1 rm1 rm2 lc1 lc2 ->
  ret (bid, eid) = lookupAL (id * id) rm2 id0 ->
  gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 ->
  gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2 ->
  reg_simulation mi (los,nts) gl f1 
    (updateAddAL _ rm1 id0 (mkMD blk1 bofs1 eofs1)) rm2 lc1
    (updateAddAL _ (updateAddAL _ lc2 bid bgv2) eid egv2).
Proof.
  intros mi los nts gl f1 rm1 rm2 lc1 lc2 id0 blk1 bofs1 eofs1 bgv2 egv2 bid eid 
    mgb M1 M2 ex_ids Hwfmi Hwfg Hgenmd Hrsim HeqR1 Hbinj Heinj.
  assert (Hspec := Hgenmd).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].
  clear Hinc1 Hinc3.
  split.
  SSCase "rsim1".
      intros i0 gv1 J.
      assert (Hin:=Hrsim).
      eapply reg_simulation_spec in Hin; eauto.
      
      destruct Hrsim as [J1 _].
      apply J1 in J.
      destruct J as [gv2 [J2 J3]].
      exists gv2.
        split; auto.
        apply notin_codom__neq with (id0:=i0)(id1:=id0)(bid:=bid)(eid:=eid)
          (rm:=rm2)(d:=ids2atoms (getFdefLocs f1)) in Hdisj1; auto.
        destruct Hdisj1 as [Heq1 Heq2].
        rewrite <- lookupAL_updateAddAL_neq; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.

  split.
  SSCase "rsim2".
      intros vp blk0 bofs0 eofs0 J.
      destruct vp as [pid | ]; simpl.
      SSSCase "vp = pid".
        unfold SBspecAux.get_reg_metadata in J.
        destruct (id_dec id0 pid); subst.
        SSSSCase "id0 = pid".
          rewrite <- HeqR1.
          rewrite lookupAL_updateAddAL_eq in J.
          inv J.
          exists (value_id bid). exists (value_id eid).
          exists bgv2. exists egv2.
          split; auto.
          split.
            simpl in *.
            rewrite <- lookupAL_updateAddAL_neq.
              rewrite lookupAL_updateAddAL_eq; auto.
              eapply rm_codom_disjoint_spec in HeqR1; eauto. 

          split. simpl. rewrite lookupAL_updateAddAL_eq; auto.
          split; auto.

        SSSSCase "id0 <> pid".
          rewrite <- lookupAL_updateAddAL_neq in J; auto.
          destruct Hrsim as [_ [Hrsim _]].
          destruct (@Hrsim (value_id pid) blk0 bofs0 eofs0) as 
            [bv2 [ev2 [bgv2' [egv2' [J1 [J2 [J3 [J4 J5]]]]]]]]; auto.
          exists bv2. exists ev2. exists bgv2'. exists egv2'.
          simpl in J1.
          split; auto.
          remember (lookupAL (id * id) rm2 pid) as R.
          destruct R; inv J1. destruct p; inv H0.
          simpl.
          eapply rm_codom_disjoint_spec' with (id1:=id0)(id2:=pid) in Hdisj2; 
            eauto.
          destruct Hdisj2 as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 G10]]]]]]]]]. 
          simpl.
          split.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.

      SSSCase "vp = c".
        apply SBspecMetadata.get_reg_metadata_const_inv in J.
        destruct J as [[J1 J2] | [c1 [c2 [J1 [J2 J3]]]]].
          inv J2.
          exists vnullp8. exists vnullp8. exists null. exists null.
          simpl. unfold const2GV. simpl. unfold null. 
          unfold val2GV.
          inv Hwfmi. rewrite J1.
          repeat (split; eauto).

          exists (value_const c1). exists (value_const c2). simpl.
          rewrite J1.
          exists ((Vptr blk0 bofs0, AST.Mint 31) :: nil). 
          exists ((Vptr blk0 eofs0, AST.Mint 31) :: nil). 
          repeat (split; eauto using sb_mem_inj__const2GV).

  SSCase "rsim3".
    destruct Hrsim as [_ [_ Hrsim]]; auto.
Qed.

Lemma tmp_is_fresh2 : forall i0 d tmp ex_ids' ex_ids1 ex_ids2,
  In i0 d ->
  ids2atoms d [<=] ids2atoms ex_ids1 ->
  incl ex_ids1 ex_ids2 ->
  (tmp, ex_ids') = mk_tmp ex_ids2 ->
  i0 <> tmp.
Proof.
  intros.
  apply ids2atoms__inc in H1.
  apply ids2atoms__in in H.
  eapply tmp_is_fresh with (ex_ids:=ex_ids2); eauto.
    fsetdec.
Qed. 

Lemma tmp_is_fresh3 : forall ex_ids1 ex_ids2 tmp ex_ids' bid eid rm id1,
  codom rm [<=] ids2atoms ex_ids1 ->
  Some (bid, eid) = lookupAL _ rm id1 ->
  incl ex_ids1 ex_ids2 ->
  (tmp, ex_ids') = mk_tmp ex_ids2 ->
  bid <> tmp /\ eid <> tmp.
Proof.
  intros.
  apply ids2atoms__inc in H1.
  eapply tmp_is_fresh' with (ex_ids:=ex_ids2); eauto.
    fsetdec.
Qed. 

Lemma get_reg_metadata_fresh'' : forall
  (rm2 : rmap)
  (ex_ids : ids)
  (id0 : id) f1 nts
  (Hgenmd : gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids,rm2))
  (Hin : In id0 (getFdefLocs f1))
  (vp0 : value)
  (bv0 : value)
  (ev0 : value)
  (J11 : get_reg_metadata rm2 vp0 = ret (bv0, ev0)),
  id_fresh_in_value bv0 id0 /\ id_fresh_in_value ev0 id0.
Proof.
  intros.
  apply gen_metadata_fdef_spec in Hgenmd; auto.
  destruct Hgenmd as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].
  clear Hinc1 Hinc3 Hdisj2.
  destruct vp0; simpl in J11.
    remember (lookupAL (id * id) rm2 i0) as R.
    destruct R as [[bid eid]|]; inv J11.
    simpl.
    apply rmap_lookupAL in HeqR.
    destruct HeqR as [J1 [J2 _]].
    apply ids2atoms__in in Hin.
    clear - Hdisj1 Hin J1 J2.
    fsetdec.
  
    destruct (SBspecAux.get_const_metadata c) as [[be ec]|]; inv J11; simpl;auto.
Qed.

Lemma get_reg_metadata_fresh3 : forall nts f1 ex_ids3 rm2 vp bv2 ev2 id0 bid0
    eid0,
  gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids3,rm2) ->
  get_reg_metadata rm2 vp = ret (bv2, ev2) ->
  lookupAL (id * id) rm2 id0 = ret (bid0, eid0) ->
  id_fresh_in_value ev2 bid0 /\ id_fresh_in_value bv2 eid0.
Proof.
  intros nts f1 ex_ids3 rm2 vp bv2 ev2 id0 bid0 eid0 Hgenmd Hgetr Hlk.
  apply gen_metadata_fdef_spec in Hgenmd; auto.
  destruct Hgenmd as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].
  clear Hinc1 Hinc3 Hdisj1.
  destruct vp; simpl in Hgetr.
    remember (lookupAL (id * id) rm2 i0) as R.
    destruct R as [[bid eid]|]; inv Hgetr.
    simpl. symmetry in Hlk. 
    destruct (i0==id0); subst.
      rewrite <- Hlk in HeqR. inv HeqR.
      apply rm_codom_disjoint_spec in Hlk; auto.
      destruct Hlk as [J1 [J2 _]]. auto.

      apply rm_codom_disjoint_spec' with (id1:=id0)(bid1:=bid0)(eid1:=eid0) 
        in HeqR; auto.
      destruct HeqR as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 [G9 G10]]]]]]]]]. 
      auto.
  
    destruct (SBspecAux.get_const_metadata c) as [[be ec]|]; 
      inv Hgetr; simpl; auto.
Qed.        

Lemma reg_simulation__updateAddAL_tmp : forall mi los nts gl f1 rm1 rm2 lc1 lc2 
   tmp tgv ex_ids3 ex_ids3' ex_ids5 mgb M1 M2
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  reg_simulation mi (los, nts) gl f1 rm1 rm2 lc1 lc2 ->
  gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids3,rm2) ->
  incl ex_ids3 ex_ids3' ->
  (tmp, ex_ids5) = mk_tmp ex_ids3' ->
  reg_simulation mi (los, nts) gl f1 rm1 rm2 lc1 (updateAddAL _ lc2 tmp tgv).
Proof.
  intros mi los nts gl f1 rm1 rm2 lc1 lc2 tmp tgv ex_ids3 ex_ids3' ex_ids5 mgb M1
    M2 Hwfmi Hwfg Hrsim Hgenmd Htmp HeqR2.
  assert (Hspec := Hgenmd).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].
  clear Hdisj1.
    split.
    SSCase "rsim1".
      intros i0 gv1 J.
      assert (Hin:=Hrsim).
      eapply reg_simulation_spec in Hin; eauto.
      destruct Hrsim as [J1 _].
      apply J1 in J.
      destruct J as [gv2 [J J2]].
      exists gv2.
      split; auto.
        eapply tmp_is_fresh2 in Hinc1; eauto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
          apply ids2atoms__in. apply in_singleton; auto.

    split.
    SSCase "rsim2".
      intros vp blk1 bofs1 eofs1 J.
      destruct vp as [pid | ]; simpl.
      SSSCase "vp = pid".
          unfold SBspecAux.get_reg_metadata in J.
          destruct Hrsim as [_ [Hrsim _]].
          destruct (@Hrsim (value_id pid) blk1 bofs1 eofs1) as 
            [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]]; auto.
          exists bv2. exists ev2. exists bgv2. exists egv2.
          simpl in J1.
          split; auto.
          remember (lookupAL (id * id) rm2 pid) as R.
          destruct R; inv J1. destruct p; inv H0.
          eapply tmp_is_fresh3 in HeqR; eauto.
          destruct HeqR as [Hneq1 Hneq2]. 
          simpl.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.

      SSSCase "vp = c".
        apply SBspecMetadata.get_reg_metadata_const_inv in J.
        destruct J as [[J1 J2] | [c1 [c2 [J1 [J2 J3]]]]].
          inv J2.
          exists vnullp8. exists vnullp8. exists null. exists null.
          simpl. unfold const2GV. simpl. unfold null. 
          unfold val2GV.
          inv Hwfmi. rewrite J1.
          repeat (split; eauto).

          exists (value_const c1). exists (value_const c2). simpl.
          rewrite J1.
          exists ((Vptr blk1 bofs1, AST.Mint 31) :: nil). 
          exists ((Vptr blk1 eofs1, AST.Mint 31) :: nil). 
          repeat (split; eauto using sb_mem_inj__const2GV).

    SSCase "rsim3". destruct Hrsim as [_ [_ Hrsim]]; auto.
Qed.

Lemma mem_simulation__free : forall mi TD MM Mem0 M2 Mem' mgb hi lo
  (b2 : Values.block) (delta : Z) blk,
  wf_sb_mi mgb mi Mem0 M2 ->
  mem_simulation mi TD mgb MM Mem0 M2 ->
  Mem.free Mem0 blk lo hi = ret Mem' ->
  (lo, hi) = Mem.bounds Mem0 blk ->
  mi blk = ret (b2, delta) ->
  exists Mem2',
    Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2' /\
    wf_sb_mi mgb mi Mem' Mem2' /\
    mem_simulation mi TD mgb MM Mem' Mem2'.
Proof.
  intros mi TD MM Mem0 M2 Mem' mgb hi lo b2 delta blk Hwfmi HsimM H0
    HeqR2 H4.

  destruct HsimM as [Hmsim1 [Hmgb [Hzeroout Hmsim2]]].  
  assert ({ Mem2':Mem.mem | Mem.free M2 b2 (lo+delta) (hi+delta) = ret Mem2'}) 
    as J.
    apply Mem.range_perm_free.
    apply Mem.free_range_perm in H0.
    clear - H0 Hmsim1 H4.
    unfold Mem.range_perm in *.
    intros ofs J.
    assert (lo <= ofs - delta < hi) as J'.
      auto with zarith.
    apply H0 in J'.
    eapply MoreMem.perm_inj in J'; eauto.
    assert (ofs - delta + delta = ofs) as EQ. auto with zarith.
    rewrite EQ in J'. auto.
  destruct J as [Mem2' J].
  exists Mem2'. split; auto.
  split.
  SCase "wfmi".
    clear - Hwfmi H0 J H4.
    inversion_clear Hwfmi.
    split; eauto with mem.
    SSCase "Hmap3".
      intros. erewrite Mem.nextblock_free in H; eauto.
    SSCase "Hmap4".
      intros. erewrite Mem.nextblock_free; eauto.
    SSCase "bounds".
      intros. apply mi_bounds in H. 
      erewrite Mem.bounds_free; eauto.
      erewrite Mem.bounds_free with (m2:=Mem2'); eauto.

  SCase "msim".
    split.
      clear - Hmsim1 Hwfmi H0 J H4.
      inv Hwfmi.
      eapply MoreMem.free_inj; eauto.

    split.
      clear - Hmgb J.
      apply Mem.nextblock_free in J.
      rewrite J. auto.
  
    split.
      clear - Hzeroout H0. intros.
      apply Mem.nextblock_free in H0.
      apply Hzeroout.
      rewrite <- H0. auto.

      clear Hmsim1 Hmgb.
      intros lc0 gl0 b0 ofs blk0 bofs0 eofs0 als0 bid0 eid0 pgv' fs F B0 cs0 tmn 
        S0 Ps0 EC0 v1 cm Hwfg0 G1 G2 G3.
      assert (G3':=G3).
      eapply Hmsim2 with (blk:=blk0)(bofs:=bofs0)(eofs:=eofs0)(als:=als0)
        (bid0:=bid0)(eid0:=eid0)(b:=b0)(ofs:=ofs) in G3'; eauto.
      destruct G3' as [bgv' [egv' [G4 [G5 G6]]]].
      exists bgv'. exists egv'.
      split; auto.
        eapply free_doesnt_change_gmmd; eauto.
Qed.

Lemma free_allocas_sim : forall TD mi mgb als1 M1 als2 M2 M1' MM,
  free_allocas TD M1 als1 = Some M1' ->
  mem_simulation mi TD mgb MM M1 M2 ->
  wf_sb_mi mgb mi M1 M2 ->
  als_simulation mi als1 als2 ->
  exists M2', free_allocas TD M2 als2 = Some M2' /\ 
    mem_simulation mi TD mgb MM M1' M2' /\
    wf_sb_mi mgb mi M1' M2'.
Proof.
  induction als1; simpl; intros.
    destruct als2; simpl; inv H2.
      inv H. eauto.

    destruct als2; simpl; inv H2.
    remember (free TD M1 (blk2GV TD a)) as R.
    destruct R as [Mem'|]; try solve [inv H].
    symmetry in HeqR.
    apply free_inv in HeqR.
    destruct HeqR as [blk [ofs [hi [lo [J1 [J2 [J3 J4]]]]]]].
    unfold blk2GV, free, GV2ptr, ptr2GV, val2GV in J1.
    inv J1.   
    eapply mem_simulation__free with (b2:=m)(delta:=0) in J4; eauto.
    destruct J4 as [Mem2' [J4 [J5 J6]]].
    unfold blk2GV, free, GV2ptr, ptr2GV, val2GV.
    simpl. 
    inv H1.
    erewrite <- mi_bounds; eauto.
    rewrite <- J3. 
    assert (lo+0=lo) as Eq1. zauto.
    assert (hi+0=hi) as Eq2. zauto. 
    rewrite <- Eq1. rewrite <- Eq2.
    rewrite J4. eauto.
Qed.

Lemma getOperandValue_eq_fresh_id : forall tmp TD v lc2 gl gvp2,
  id_fresh_in_value v tmp ->
  getOperandValue TD v lc2 gl = 
    getOperandValue TD v (updateAddAL GenericValue lc2 tmp gvp2) gl.
Proof.
  intros.
  destruct v; simpl; auto.
    rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma inject_incr__preserves__als_simulation : forall mi mi' als1 als2,
  als_simulation mi als1 als2 ->
  inject_incr mi mi' ->
  als_simulation mi' als1 als2.
Proof.
  induction als1; destruct als2; simpl; intros; auto.
    destruct H.
    split; eauto.
Qed.

Lemma inject_incr__preserves__sbEC_simulate_EC_tail : forall mi mi' TD gl Ps
    EC1 EC2,
  inject_incr mi mi' ->
  sbEC_simulates_EC_tail TD Ps gl mi EC1 EC2 ->
  sbEC_simulates_EC_tail TD Ps gl mi' EC1 EC2.
Proof.
  intros.
  destruct EC1 as [f1 b1 cs1 tmn1 lc1 rm1 als1].
  destruct EC2 as [f2 b2 cs2 tmn2 lc2 rm2 als2].
  destruct TD as [los nts]. destruct f1. destruct f2.
  destruct b1; try solve [inv H0].
  destruct cs1; try solve [inv H0].
  destruct c0; try solve [inv H0].
  destruct H0 as [J0 [J1 [J2 [Htfdef [Heq0 [Hasim [Hnth [Heqb1 [Heqb2 [ex_ids 
    [rm2' [ex_ids3 [ex_ids4 [cs22 [cs23 [cs24 [Hgenmeta [Hrsim [Hinc [Hcall 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]]]; subst.
  eapply inject_incr__preserves__als_simulation in Hasim; eauto.
  eapply inject_incr__preserves__reg_simulation in Hrsim; eauto.
  repeat (split; auto).
  exists ex_ids. exists rm2'. exists ex_ids3. exists ex_ids4. exists cs22.
  exists cs23. exists cs24.
  repeat (split; auto).
Qed.

Lemma inject_incr__preserves__sbECs_simulate_ECs_tail : forall mi mi' TD gl Ps
    ECs1 ECs2,
  inject_incr mi mi' ->
  sbECs_simulate_ECs_tail TD Ps gl mi ECs1 ECs2 ->
  sbECs_simulate_ECs_tail TD Ps gl mi' ECs1 ECs2.
Proof.
  induction ECs1; destruct ECs2; simpl; intros; auto.
    destruct H0.
    split; eauto using inject_incr__preserves__sbEC_simulate_EC_tail.
Qed.

Lemma cmds_at_block_tail_next : forall B c cs tmn2,
  (exists l1, exists ps1, exists cs11, B = 
    block_intro l1 ps1 (cs11 ++ c :: cs) tmn2) ->
  exists l1, exists ps1, exists cs11, B = block_intro l1 ps1 (cs11 ++ cs) tmn2.
Proof.
  intros.
  destruct H as [l1 [ps1 [cs11 H]]]; subst.
  exists l1. exists ps1. exists (cs11 ++ [c]). simpl_env. auto.
Qed.

Lemma cmds_at_block_tails_next : forall B cs1 cs2 cs3 tmn,
  (exists l0 : l,
    exists ps0 : phinodes,
      exists cs0 : list cmd, B = 
        block_intro l0 ps0 (cs0 ++ (cs1 ++ cs2) ++ cs3) tmn) ->
  exists l0 : l,
    exists ps0 : phinodes,
      exists cs0 : list cmd, B = block_intro l0 ps0 (cs0 ++ cs2 ++ cs3) tmn.
Proof.
  intros.
  destruct H as [l2 [ps2 [cs21 Heqb2]]]; subst;
  exists l2; exists ps2; exists (cs21 ++ cs1); simpl_env; auto.
Qed.

Lemma reg_simulation__updateAddAL_prop : forall mi los nts gl f1 rm1 rm2 lc1 lc2 
    blk1 bofs1 eofs1 bgv2 egv2 bid eid ex_ids3 mgb M1 M2 id0 gv1 gv2
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids3,rm2) ->
  reg_simulation mi (los,nts) gl f1 rm1 rm2 lc1 lc2 ->
  ret (bid, eid) = lookupAL (id * id) rm2 id0 ->
  In id0 (getFdefLocs f1) ->
  gv_inject mi gv1 gv2 ->
  gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 ->
  gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2 ->
  reg_simulation mi (los,nts) gl f1 
    (updateAddAL _ rm1 id0 (mkMD blk1 bofs1 eofs1)) rm2 
    (updateAddAL GenericValue lc1 id0 gv1)
    (updateAddAL _ (updateAddAL _ 
      (updateAddAL GenericValue lc2 id0 gv2) bid bgv2) eid egv2).
Proof.
  intros.
  eapply reg_simulation__updateAddAL_md; eauto.
  eapply reg_simulation__updateAddAL_lc; eauto.
Qed.

Lemma simulation_mload_aux : forall Mem0 Mem2 b b2 delta mi mgb
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : MoreMem.mem_inj mi Mem0 Mem2)
  (H1 : mi b = ret (b2, delta)) mcs ofs gv
  (Hmloads : mload_aux Mem0 mcs b ofs = ret gv),
   exists gv2 : GenericValue,
     mload_aux Mem2 mcs b2 (ofs + delta) = ret gv2 /\ gv_inject mi gv gv2.
Proof.
  induction mcs; simpl; intros.
    inv Hmloads. eauto.

    remember (Mem.load a Mem0 b ofs) as R.
    destruct R as [v|]; tinv Hmloads.
    symmetry in HeqR.
    inv Hwfmi.
    eapply MoreMem.load_inj in HeqR; eauto.
    destruct HeqR as [v2 [Hmload Hinj]].
    rewrite Hmload.
    remember (mload_aux Mem0 mcs b (ofs + size_chunk a)) as R1.
    destruct R1; inv Hmloads.
    symmetry in HeqR1.
    apply IHmcs in HeqR1; auto.
    destruct HeqR1 as [gv2 [Hmloads Hinjs]].
    assert (ofs + delta + size_chunk a = ofs + size_chunk a + delta) as EQ. ring.
    rewrite EQ.
    rewrite Hmloads. eauto.
Qed.

Lemma simulation__mload : forall mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 mgb,
  wf_sb_mi mgb mi Mem0 Mem2 ->
  mem_simulation mi TD mgb MM Mem0 Mem2 ->
  mload TD Mem0 gvp t align0 = ret gv ->
  gv_inject mi gvp gvp2 ->
  exists gv2, mload TD Mem2 gvp2 t align0 = ret gv2 /\ gv_inject mi gv gv2.
Proof.
  intros mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 mgb Hwfmi Hmsim Hmload Hginject.
  apply mload_inv in Hmload.
  destruct Hmload as [b [ofs [m [mc [Heq [Hflat Hmload]]]]]]; subst.
  inv Hginject. inv H4. inv H3.
  unfold mload. simpl. rewrite Hflat.
  destruct Hmsim as [Hmsim _].
  eapply simulation_mload_aux in Hmload; eauto.
  destruct Hmload as [gv2 [Hmload Hinj]].
  inv Hwfmi.
  apply mi_range_block in H1. subst.
  rewrite Int.add_zero.
  assert (Int.signed 31 ofs + 0 = Int.signed 31 ofs) as EQ. zauto.
  rewrite EQ in Hmload. eauto.
Qed.

Lemma get_reg_metadata__fresh : forall
  (rm2 : rmap) (ex_ids ex_ids1 ex_ids3: ids) (bv2 ev2 : value) (ptmp : id) f1 nts
  (Hgenmd : gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids3,rm2))
  (Hinc : incl ex_ids3 ex_ids) vp
  (HeqR1 : (ptmp, ex_ids1) = mk_tmp ex_ids)
  (J1 : SB_ds_pass.get_reg_metadata rm2 vp = ret (bv2, ev2)),
  id_fresh_in_value bv2 ptmp /\ id_fresh_in_value ev2 ptmp.
Proof.
  intros.
  apply gen_metadata_fdef_spec in Hgenmd; auto.
  destruct Hgenmd as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].
  clear Hinc1 Hdisj2.
  destruct vp; simpl in *.
  remember (lookupAL (id * id) rm2 i0) as R.
  destruct R; inv J1.
  destruct p; inv H0; simpl.
  apply ids2atoms__inc in Hinc.
  eapply tmp_is_fresh' with (tmp:=ptmp)(ex_ids:=ex_ids) in HeqR; eauto. 
    fsetdec.
  destruct (SBspecAux.get_const_metadata c) as [[bc ec]|]; inv J1; simpl; auto.
Qed.            

Lemma get_reg_metadata_fresh' : forall nts vp rm2 ex_ids3 f1
  (Hgenmd : gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids3,rm2))
  (Hnotin : (getValueID vp) [<=] ids2atoms ((getFdefLocs f1)))
  (ptmp : id)
  (ex_ids1 ex_ids: ids)
  (Hinc : incl ex_ids3 ex_ids)
  (HeqR1 : (ptmp, ex_ids1) = mk_tmp ex_ids),
  id_fresh_in_value vp ptmp.
Proof.
  intros.
  apply gen_metadata_fdef_spec in Hgenmd; auto.
  destruct Hgenmd as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].
  clear Hdisj2.
  destruct vp; simpl in *; auto.
    apply tmp_is_fresh with (i0:=i0)(d:=singleton i0) in HeqR1; auto.
      apply ids2atoms__inc in Hinc.
      fsetdec.
Qed.
(*
Lemma wf_fresh__mk_tmp' : forall ex_ids vp rm2 ptmp ex_ids1,
 union (getValueID vp) (codom rm2)[<=] ids2atoms ex_ids ->
 (ptmp, ex_ids1) = mk_tmp ex_ids ->
 union (getValueID vp) (codom rm2)[<=] ids2atoms ex_ids1.
Proof.
  intros.
    unfold mk_tmp in H0.
    destruct (atom_fresh_for_list ex_ids).
    inv H0.
    simpl.
    assert (x `notin` ids2atoms ex_ids) as J.
      intro H1. apply n.
      apply ids2atoms_dom; auto.              
    fsetdec.
Qed.
Lemma get_reg_metadata_fresh'' : forall
  (rm2 : rmap)
  (ex_ids : ids)
  (id0 : id)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnotin : wf_fresh ex_ids (insn_load id0 t vp align0) rm2)
  (vp0 : value)
  (t0 : typ)
  (bv0 : value)
  (ev0 : value)
  (J11 : get_reg_metadata rm2 vp0 = ret (bv0, ev0)),
  id_fresh_in_value bv0 id0 /\ id_fresh_in_value ev0 id0.
Proof.
  intros.
  destruct Hnotin as [Hnotin _].          
  destruct vp0; simpl in J11.
    remember (lookupAL (id * id) rm2 i0) as R.
    destruct R as [[bid eid]|]; inv J11.
    simpl.
    apply rmap_lookupAL in HeqR.
    destruct HeqR as [J1 [J2 _]].
    unfold getCmdIDs in Hnotin. simpl in Hnotin.
    clear - Hnotin J2 J1. fsetdec.
  
    destruct (SBopsem.get_const_metadata c) as [[be ec]|].
      inv J11; simpl; auto.
      destruct (Constant.getTyp c); inv J11; simpl; auto.
Qed.
*)

Lemma mstore_inversion : forall Mem2 t align0 TD gvp2 Mem2'
  (gv2 : GenericValue)
  (H21 : mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2'),
  exists b, exists ofs, exists cm, 
    gvp2 = (Vptr b ofs,cm)::nil /\ 
    mstore_aux Mem2 gv2 b (Int.signed 31 ofs) = ret Mem2'.
Proof.
  intros.
  unfold mstore in H21.
  remember (GV2ptr TD (getPointerSize TD) gvp2) as R.
  destruct R; try solve [inversion H21].
  destruct v; try solve [inversion H21].
  unfold GV2ptr in HeqR.
  destruct gvp2; try solve [inversion HeqR].
  destruct p.
  destruct v; try solve [inversion HeqR].
  destruct gvp2; inv HeqR.
  exists b0. exists i2. exists m. eauto.
Qed.

Lemma simulation_mstore_aux : forall b b2 delta mi mgb MM TD
  (H1 : mi b = ret (b2, delta)) gv ofs gv2 Mem0 Mem2 Mem0'
  (Hwfmi : wf_sb_mi mgb mi Mem0 Mem2)
  (Hmsim : mem_simulation mi TD mgb MM Mem0 Mem2)
  (Hinj : gv_inject mi gv gv2)
  (Hmstores : mstore_aux Mem0 gv b ofs = ret Mem0'),
   exists Mem2',
     mstore_aux Mem2 gv2 b2 (ofs + delta) = ret Mem2' /\ 
     wf_sb_mi mgb mi Mem0' Mem2' /\ 
     mem_simulation mi TD mgb MM Mem0' Mem2'.
Proof.
  induction gv; simpl; intros.
    inv Hmstores. inv Hinj. simpl. eauto.

    destruct a. inv Hinj.
    remember (Mem.store m Mem0 b ofs v) as R1.
    destruct R1 as [M|]; tinv Hmstores.
    symmetry in HeqR1.
    destruct Hmsim as [Hmsim1 [Hmgb [Hzero Hmsim2]]].
    inv Hwfmi.
    assert (Hmstore0 := HeqR1).
    eapply MoreMem.store_mapped_inj with (f:=mi)(m2:=Mem2) in HeqR1; 
      try solve [eauto | inversion Hwfmi; eauto].
    destruct HeqR1 as [Mem2' [Hmstore Hminj]].
    simpl. rewrite Hmstore.
    assert (ofs + delta + size_chunk m = ofs + size_chunk m + delta) as EQ. ring.
    rewrite EQ.
    apply IHgv with (Mem0:=M); auto.
    Case "wf_sb_mi".
      split; auto.
      SCase "Hnext1".
        erewrite <- Mem.nextblock_store with (m1:=Mem0) in Hmap1; eauto.
      SCase "Hnext2".
        intros b1 b0 delta2 J.
        apply Hmap2 in J.
        apply Mem.nextblock_store in Hmstore.
        rewrite Hmstore. auto.
      SCase "mi_freeblocks0".
        intros b0 J. apply mi_freeblocks. intro J'. apply J.
        eapply Mem.store_valid_block_1; eauto.
      SCase "mi_mappedblocks0".
        intros b0 b' delta0 J.
        eapply Mem.store_valid_block_1; eauto.
      SCase "mi_bounds".
        intros b0 b' delta0 J.
        apply mi_bounds in J.
        apply Mem.bounds_store with (b':=b0) in Hmstore0; auto.
        rewrite Hmstore0. rewrite J.
        erewrite Mem.bounds_store with (m2:=Mem2'); eauto.
    
    Case "msim".
      split; auto.
      split.
        apply Mem.nextblock_store in Hmstore.
        rewrite Hmstore. auto.
      split; auto.
        clear - Hzero Hmstore0.
        apply Mem.nextblock_store in Hmstore0. intros.
        apply Hzero. rewrite <- Hmstore0. auto.
    
        clear Hmsim1.
        intros lc2 gl b0 ofs0 blk0 bofs0 efs0 als bid0 eid0 pgv' fs F B cs tmn S 
          Ps EC v1 cm Hwfg G1 G2 G3.
        assert (G3':=G3).
        eapply Hmsim2 with (blk:=blk0)(bofs:=bofs0)(eofs:=efs0)(als:=als)
          (bid0:=bid0)(eid0:=eid0)(b:=b0)(ofs:=ofs0) in G3'; eauto.
        destruct G3' as [bgv' [egv' [G4 [G5 G6]]]].
        exists bgv'. exists egv'.
        eapply store_doesnt_change_gmmd in G4; eauto.
Qed.

Lemma simulation__mstore : forall mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 gv2
                                  Mem0' mgb,
  wf_sb_mi mgb mi Mem0 Mem2 ->
  mem_simulation mi TD mgb MM Mem0 Mem2 ->
  mstore TD Mem0 gvp t gv align0 = ret Mem0' ->
  gv_inject mi gvp gvp2 ->
  gv_inject mi gv gv2 ->
  exists Mem2', 
    mstore TD Mem2 gvp2 t gv2 align0 = ret Mem2' /\ 
    wf_sb_mi mgb mi Mem0' Mem2' /\
    mem_simulation mi TD mgb MM Mem0' Mem2'.
Proof.
  intros mi TD MM Mem0 Mem2 gvp align0 gv t gvp2 gv2 Mem0' mgb Hwfmi Hmsim 
    Hmstore Hginject1 Hginject2.
  apply mstore_inversion in Hmstore.
  destruct Hmstore as [b [ofs [cm [Heq Hmstore]]]]; subst.
  inv Hginject1. inv H4. inv H3.

  unfold mstore. simpl.
  eapply simulation_mstore_aux in Hmstore; eauto.
  destruct Hmstore as [Mem2' [Hmstore [Hwfmi' Hmsim']]].
  inv Hwfmi.
  apply mi_range_block in H1. subst.
  rewrite Int.add_zero.
  assert (Int.signed 31 ofs + 0 = Int.signed 31 ofs) as EQ. zauto.
  rewrite EQ in Hmstore. eauto.
Qed.

Lemma memval_inject_trans : forall mi mv1 mv2 mv3,
  memval_inject mi mv1 mv2 ->
  memval_inject inject_id mv2 mv3 ->
  memval_inject mi mv1 mv3.
Proof.
  unfold inject_id.
  intros mi mv1 mv2 mv3 H1 H2.
  inv H1; inv H2; try solve [apply memval_inject_undef; auto].
    apply memval_inject_byte.

    inv H5.
    eapply memval_inject_ptr; eauto.
      rewrite Int.add_zero. auto.

    apply memval_inject_inttoptr; auto.
Qed.

Lemma prop_metadata_inv : forall ex_ids3 rm2 c vp id0 ex_ids5 cs1',
  prop_metadata ex_ids3 rm2 c vp id0 = ret (ex_ids5, cs1') ->
  exists bv, exists ev, exists bid0, exists eid0,
     get_reg_metadata rm2 vp = Some (bv, ev) /\
     lookupAL _ rm2 id0 = Some (bid0, eid0) /\
     ex_ids5 = ex_ids3 /\ 
     cs1' = c :: insn_cast bid0 castop_bitcast p8 bv p8
              :: insn_cast eid0 castop_bitcast p8 ev p8 :: nil.
Proof.
  intros.
  unfold prop_metadata in H.
  destruct (get_reg_metadata rm2 vp) as [[bv ev]|]; try solve [inversion H].
  destruct (lookupAL _ rm2 id0) as [[bid0 eid0]|]; inv H.
  exists bv. exists ev. exists bid0. exists eid0. split; auto.
Qed.

Lemma prop_metadata_mono : forall ex_ids1 rm c v i0 ex_ids2 cs2,
  prop_metadata ex_ids1 rm c v i0 =  ret (ex_ids2, cs2) ->
  incl ex_ids1 ex_ids2.
Proof.
  intros.
  unfold prop_metadata in *.
  destruct (get_reg_metadata rm v) as [[? ?]|]; try solve [inv H].
  remember (mk_tmp ex_ids1) as R.
  destruct R; inv H.
  unfold mk_tmp in HeqR.
  destruct (atom_fresh_for_list ex_ids1); inv HeqR.
  destruct (lookupAL (id * id) rm i0) as [[? ?]|]; inv H1.
  auto using incl_refl.
Qed.

Lemma trans_cmd_fresh_mono : forall rm c ex_ids1 ex_ids2 cs2,
  trans_cmd ex_ids1 rm c = Some (ex_ids2, cs2) ->
  incl ex_ids1 ex_ids2.
Proof.
  intros.
  destruct c; simpl in H; try solve [inv H; auto using incl_refl].
  
    destruct (lookupAL (id * id) rm i0) as [[bid eid]|]; inv H.
    remember (mk_tmp ex_ids1) as R.
    destruct R; tinv H1.
    remember (mk_tmp i3) as R.
    destruct R; inv H1.
    unfold mk_tmp in *.
    destruct (atom_fresh_for_list ex_ids1); inv HeqR.
    destruct (atom_fresh_for_list (x::ex_ids1)); inv HeqR0.
    simpl_env.
    apply incl_appr. apply incl_appr. apply incl_refl.

    destruct (lookupAL (id * id) rm i0) as [[bid eid]|]; inv H.
    remember (mk_tmp ex_ids1) as R.
    destruct R; tinv H1.
    remember (mk_tmp i3) as R.
    destruct R; inv H1.
    unfold mk_tmp in *.
    destruct (atom_fresh_for_list ex_ids1); inv HeqR.
    destruct (atom_fresh_for_list (x::ex_ids1)); inv HeqR0.
    simpl_env.
    apply incl_appr. apply incl_appr. apply incl_refl.

    destruct (get_reg_metadata rm v) as [[? ?]|]; try solve [inv H].
    remember (mk_tmp ex_ids1) as R.
    destruct R; inv H.
    unfold mk_tmp in HeqR.
    destruct (atom_fresh_for_list ex_ids1); inv HeqR.
    destruct (isPointerTypB t).
      destruct (lookupAL (id * id) rm i0) as [[? ?]|]; inv H1.
      auto using incl_cons.
      inv H1. auto using incl_cons. 

    destruct (get_reg_metadata rm v0) as [[? ?]|]; try solve [inv H].
    remember (mk_tmp ex_ids1) as R.
    destruct R; inv H.
    unfold mk_tmp in HeqR.
    destruct (atom_fresh_for_list ex_ids1); inv HeqR.
    destruct (isPointerTypB t).
      destruct (get_reg_metadata rm v) as [[? ?]|]; inv H1.
      auto using incl_cons.
      inv H1. auto using incl_cons. 

    eapply prop_metadata_mono; eauto.
    
    destruct c; inv H; auto using incl_refl.
      destruct (lookupAL (id * id) rm i0) as [[? ?]|]; inv H1.
      auto using incl_refl.

      destruct (isPointerTypB t).
        eapply prop_metadata_mono; eauto.
        inv H1. auto using incl_refl.

    destruct (isPointerTypB t).
      destruct (get_reg_metadata rm v0) as [[? ?]|]; inv H.
      destruct (get_reg_metadata rm v1) as [[? ?]|]; inv H1.
      destruct (lookupAL (id * id) rm i0) as [[? ?]|]; inv H0.
      unfold mk_tmp in H1.
      destruct (atom_fresh_for_list ex_ids1); inv H1.
      auto using incl_cons.

      inv H. auto using incl_refl.

    destruct (trans_params rm p 1) as [?|]; inv H.
    destruct (call_suffix i0 n c t v p rm); inv H1.
    auto using incl_refl.
Qed.
    
Lemma trans_cmds_cons_inv : forall ex_ids1 rm c cs ex_ids2 cs2,
  trans_cmds ex_ids1 rm (c :: cs) = ret (ex_ids2, cs2) ->
  exists ex_ids3, exists cs21, exists cs22,
    trans_cmd ex_ids1 rm c = ret (ex_ids3, cs21) /\
    trans_cmds ex_ids3 rm cs = ret (ex_ids2, cs22) /\
    cs21 ++ cs22 = cs2.
Proof.
  intros. 
  simpl in H.
  remember (trans_cmd ex_ids1 rm c) as R.
  destruct R as [[ex_ids1' cs21]|]; inv H.
  remember (trans_cmds ex_ids1' rm cs) as R1.
  destruct R1 as [[ex_ids2' cs22]|]; inv H1.
  exists ex_ids1'. exists cs21. exists cs22.
  split; eauto.
Qed.    

Lemma trans_cmds_fresh_mono : forall rm cs ex_ids1 ex_ids2 cs2,
  trans_cmds ex_ids1 rm cs = Some (ex_ids2, cs2) ->
  incl ex_ids1 ex_ids2.
Proof.
  induction cs; intros.
    inv H; auto using incl_refl.

    apply trans_cmds_cons_inv in H.
    destruct H as [ex_ids3 [cs21 [cs22 [J1 [J2 eq]]]]]; subst.
    apply trans_cmd_fresh_mono in J1.
    apply IHcs in J2.
    eapply incl_tran; eauto. 
Qed.


Lemma trans_blocks_cons_inv : forall ex_ids1 rm b bs ex_ids2 bs2,
  trans_blocks ex_ids1 rm (b :: bs) = ret (ex_ids2, bs2) ->
  exists ex_ids3, exists b2, exists bs2',
    trans_block ex_ids1 rm b = ret (ex_ids3, b2) /\
    trans_blocks ex_ids3 rm bs = ret (ex_ids2, bs2') /\
    b2::bs2' = bs2.
Proof.
  intros. 
  simpl in H.
  remember (trans_block ex_ids1 rm b) as R.
  destruct R as [[ex_ids1' b1]|]; inv H.
  remember (trans_blocks ex_ids1' rm bs) as R1.
  destruct R1 as [[ex_ids2' bs']|]; inv H1.
  exists ex_ids1'. exists b1. exists bs'.
  split; eauto.
Qed.    

Lemma trans_block_inv : forall ex_ids rm l1 p c t ex_ids3 b2,
  trans_block ex_ids rm (block_intro l1 p c t) = ret (ex_ids3, b2) ->
  exists p', exists c', exists cs,
    trans_phinodes rm p = Some p' /\
    trans_cmds ex_ids rm c = Some (ex_ids3, c') /\
    trans_terminator rm t = Some cs /\
    b2 = block_intro l1 p' (c'++cs) t.
Proof.
  intros. simpl in *.
    remember (trans_phinodes rm p) as R2.
    destruct R2 as [ps2|]; try solve [inv H].
    remember (trans_cmds ex_ids rm c) as R3.
    destruct R3 as [[ex_ids2 cs2]|]; try solve [inv H].
    remember (trans_terminator rm t) as R4.
    destruct R4 as [cs2'|]; inv H.
    exists ps2. exists cs2. exists cs2'. split; auto.
Qed.

Lemma trans_fdef_inv : forall nts fa t fid la va bs f',
  trans_fdef nts (fdef_intro (fheader_intro fa t fid la va) bs) = Some f' ->
  if isCallLib fid then 
    f' = (fdef_intro (fheader_intro fa t fid la va) bs)
  else
    exists ex_ids, exists rm, exists cs', exists ex_ids',
    exists bs', exists l1, exists ps1, exists cs1, exists tmn1,
      gen_metadata_fdef nts 
        (getFdefLocs (fdef_intro (fheader_intro fa t fid la va) bs)) nil 
        (fdef_intro (fheader_intro fa t fid la va) bs) = Some (ex_ids,rm) /\
      trans_args rm la 1%Z = Some cs' /\
      trans_blocks ex_ids rm bs = 
        Some (ex_ids', (block_intro l1 ps1 cs1 tmn1)::bs') /\
      f' = (fdef_intro 
                     (fheader_intro fa t (wrapper_fid fid) la va) 
                     ((block_intro l1 ps1 (cs'++cs1) tmn1)::bs')). 
Proof.
  intros. simpl in *.
  destruct (isCallLib fid).
    inv H; auto.

    destruct (gen_metadata_args (getArgsIDs la ++ getBlocksLocs bs) nil la).
    destruct (gen_metadata_blocks nts i0 r bs) as [[ex_ids rm]|]; inv H.
    exists ex_ids. exists rm.
    destruct (trans_args rm la 1) as [cs'|]; inv H1.
    exists cs'.
    destruct (trans_blocks ex_ids rm bs); inv H0.
    destruct p.
    destruct b; inv H1.
    destruct b; inv H0. 
    exists i2. exists b0. exists l0. exists p. exists c. exists t0.
    eauto.
Qed.

Lemma trans_blocks_inv : forall ex_ids1 rm2 bs1 ex_ids2 b2 bs2',
  trans_blocks ex_ids1 rm2 bs1 = Some (ex_ids2, b2::bs2') ->
  exists b1, exists bs1', exists ex_ids3, 
    trans_block ex_ids1 rm2 b1 = Some (ex_ids3, b2) /\
    trans_blocks ex_ids3 rm2 bs1' = Some (ex_ids2, bs2') /\
    bs1 = b1::bs1'.
Proof.
  intros.
  destruct bs1.
    inv H.
    apply trans_blocks_cons_inv in H; auto.
    destruct H as [e1 [b1 [bs3' [J1 [J2 J3]]]]].
    inv J3.
    exists b. exists bs1. exists e1. split; auto.
Qed.

Lemma lookup_trans_blocks__trans_block : forall ex_ids0 l0 rm b1 bs1 bs2 ex_ids 
    ex_ids',
  incl ex_ids0 ex_ids ->
  trans_blocks ex_ids rm bs1 = Some (ex_ids', bs2) ->
  lookupBlockViaLabelFromBlocks bs1 l0 = Some b1 ->
  exists ex_ids1, exists ex_ids2, exists b2,
    lookupBlockViaLabelFromBlocks bs2 l0 = Some b2 /\
    trans_block ex_ids1 rm b1 = Some (ex_ids2, b2) /\
    incl ex_ids0 ex_ids1.
Proof.
  induction bs1; intros bs2 ex_ids ex_ids' Hinc Htrans Hlk.
    inv Hlk.

    apply trans_blocks_cons_inv in Htrans.
    destruct Htrans as [ex_ids3 [b2 [bs2' [J1 [J2 eq]]]]]; subst.
    
    destruct a.
    apply trans_block_inv in J1.
    destruct J1 as [ps2 [cs2 [cs2' [J1 [J3 [J4 eq]]]]]]; subst.
    unfold lookupBlockViaLabelFromBlocks in *. simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); subst.
    exists ex_ids. exists ex_ids3. exists (block_intro l1 ps2 (cs2 ++ cs2') t). 
    inv Hlk. simpl. rewrite J1. rewrite J3. rewrite J4.
    split; auto.

    eapply IHbs1 with (ex_ids':=ex_ids')(ex_ids:=ex_ids3) ; eauto.
      apply trans_cmds_fresh_mono in J3.
      eapply incl_tran; eauto.
Qed.

Lemma wrapper_is_identical : forall fv, wrap_call fv = fv.
Proof. 
  unfold wrap_call. 
  destruct fv; auto.
  destruct c; auto. 
    rewrite wrapper_fid_is_identical. auto.
Qed.

Lemma trans_products__trans_fdef : forall nts Ps1 Ps2 fid f1,
  trans_products nts Ps1 = Some Ps2 ->
  lookupFdefViaIDFromProducts Ps1 fid = ret f1 ->
  exists f2, 
    lookupFdefViaIDFromProducts Ps2 fid = ret f2 /\
    trans_fdef nts f1 = ret f2.
Proof.
  induction Ps1; simpl; intros Ps2 fid f1 J1 J2.
    inv J2.

    remember (trans_product nts a) as R.     
    destruct R; try solve [inv J1].
    remember (trans_products nts Ps1) as R1.
    destruct R1; inv J1.
    destruct a; simpl in *.
      inv HeqR. simpl. eauto.
      inv HeqR. simpl. eauto.

      remember (trans_fdef nts f) as R1.
      destruct R1; inv HeqR. 
      simpl.
      destruct f. destruct f.
      symmetry in HeqR0. assert (Hf:=HeqR0).
      apply trans_fdef_inv in HeqR0.
      remember (isCallLib i0) as R.
      destruct R; subst.      
        simpl. simpl in J2.
        destruct (i0==fid); subst.
          destruct (fid==fid); subst.
            inv J2.
            exists (fdef_intro (fheader_intro f t fid a v) b).
            split; auto.
            contradict n; auto.
          eauto.

        destruct HeqR0 as [e1 [rm [cs [e2 [bs [l1 [ps1 [cs1 [tmn1 [J1 [J5 [J3 J4]
          ]]]]]]]]]]]; subst.
        simpl. simpl in J2.
        rewrite wrapper_fid_is_identical.
        rewrite wrapper_fid_is_identical in Hf.
        destruct (i0==fid); subst.
          destruct (fid==fid); subst.
            inv J2. 
            exists (fdef_intro (fheader_intro f t fid a v)
              (block_intro l1 ps1 (cs ++ cs1) tmn1 :: bs)).
            split; auto.

            contradict n; auto.
          eauto.
Qed.

Lemma lookupFdefViaPtr__simulation : forall mi los nts gl2 F rm rm2 lc lc2 f1
    fv Ps1 Ps2 fs1 fs2 M1 M2 mgb fptr1,
  wf_globals mgb  gl2 ->
  wf_sb_mi mgb mi M1 M2 ->
  reg_simulation mi (los,nts) gl2 F rm rm2 lc lc2 ->
  ftable_simulation mi fs1 fs2 ->
  getOperandValue (los, nts) fv lc gl2 = Some fptr1 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs1 fptr1 = Some f1 ->
  trans_products nts Ps1 = Some Ps2 ->
  exists fptr2, exists f2,
    getOperandValue (los, nts) (wrap_call fv) lc2 gl2 = Some fptr2 /\
    gv_inject mi fptr1 fptr2 /\
    OpsemAux.lookupFdefViaPtr Ps2 fs2 fptr2 = Some f2 /\
    trans_fdef nts f1 = Some f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R2.
  destruct R2 as [fid|]; inv H4.
  eapply simulation__getOperandValue in H3; eauto.
  destruct H3 as [fptr2 [J1 J2]].
  rewrite wrapper_is_identical.
  rewrite J1. simpl. 
  exists fptr2.
  erewrite <- H2; eauto.
  rewrite <- HeqR2. simpl.
  eapply trans_products__trans_fdef in H7; eauto.
  destruct H7 as [f2 [J3 J4]].
  eauto.
Qed.
  
Lemma trans_params_simulation : forall mi TD gl F rm2 lp n rm1 lc1 lc2 ogvs cs,
  reg_simulation mi TD gl F rm1 rm2 lc1 lc2 ->
  SBspec.params2GVs TD lp lc1 gl rm1 = Some ogvs ->
  trans_params rm2 lp n = Some cs ->
  params_simulation TD gl mi lc2 ogvs n cs.
Proof.
  induction lp; simpl; intros n rm1 lc1 lc2 ogvs cs Hrsim Hp2gv Htpa.
    inv Hp2gv. inv Htpa. simpl. auto.

    destruct a as [[t attr] v].
    remember (Opsem.getOperandValue TD v lc1 gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    remember (SBspec.params2GVs TD lp lc1 gl rm1) as R.
    destruct R; try solve [inv Hp2gv].
    remember (trans_params rm2 lp (n + 1)) as R1.
    destruct R1; try solve [inv Htpa].
    destruct (isPointerTypB t); inv Hp2gv.
      remember (get_reg_metadata rm2 v) as R2.
      destruct R2 as [[bv2 ev2]|]; inv Htpa.
      unfold call_set_shadowstack.
      simpl.
      remember (SBspecAux.get_reg_metadata TD gl rm1 v) as R3.
      destruct R3 as [[bgv1 egv1]|].
        symmetry in HeqR3.
        assert (J:=Hrsim).
        destruct J as [_ Hrsim2].        
        apply Hrsim2 in HeqR3.
        destruct HeqR3 as [bv2' [ev2' [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
        rewrite <- HeqR2 in J1. inv J1.
        exists bv2'. exists ev2'. exists bgv2. exists egv2.
        repeat (split; eauto).

        eauto.
     inv Htpa. 
     simpl. eauto.
Qed.

Lemma trans_products__trans_fdec : forall nts Ps1 Ps2 fid f1,
  trans_products nts Ps1 = Some Ps2 ->
  lookupFdecViaIDFromProducts Ps1 fid = ret f1 ->
  exists f2, 
    lookupFdecViaIDFromProducts Ps2 fid = ret f2 /\
    trans_fdec f1 = f2.
Proof.
  induction Ps1; simpl; intros Ps2 fid f1 J1 J2.
    inv J2.

    remember (trans_product nts a) as R.     
    destruct R; try solve [inv J1].
    remember (trans_products nts Ps1) as R1.
    destruct R1; inv J1.
    destruct a; simpl in *.
      inv HeqR. simpl. eauto.

      destruct f. destruct f. simpl in HeqR.
      inv HeqR. simpl. 
      simpl in J2.
      rewrite wrapper_fid_is_identical.
      destruct (i0==fid); subst; eauto.
        inv J2. simpl. 
        rewrite wrapper_fid_is_identical.
        eauto.

      remember (trans_fdef nts f) as R.
      destruct R; inv HeqR.
      simpl. eauto.
Qed.

Lemma trans_products__none : forall nts Ps1 Ps2 fid,
  trans_products nts Ps1 = Some Ps2 ->
  lookupFdefViaIDFromProducts Ps1 fid = None ->
  lookupFdefViaIDFromProducts Ps2 fid = None.
Proof.
  induction Ps1; simpl; intros Ps2 fid J1 J2.
    inv J1. simpl. auto.

    remember (trans_product nts a) as R.     
    destruct R; try solve [inv J1].
    remember (trans_products nts Ps1) as R1.
    destruct R1; inv J1.
    destruct a; simpl in *.
      inv HeqR. simpl. eauto.
      inv HeqR. simpl. eauto.

      remember (trans_fdef nts f) as R1.
      destruct R1; inv HeqR. 
      simpl.
      destruct f. destruct f.
      symmetry in HeqR0. assert (Hf:=HeqR0).
      apply trans_fdef_inv in HeqR0.
      remember (isCallLib i0) as R.
      destruct R; subst.      
        simpl. simpl in J2.
        destruct (i0==fid); subst.
          inv J2. eauto.

        destruct HeqR0 as [e1 [rm [cs [e2 [bs [l1 [ps1 [cs1 [tmn1 [J1 [J5 [J3 J4]
          ]]]]]]]]]]]; subst.
        simpl. simpl in J2.
        rewrite wrapper_fid_is_identical.
        rewrite wrapper_fid_is_identical in Hf.
        destruct (i0==fid); subst.
          inv J2. eauto.
Qed.

Lemma lookupExFdecViaGV__simulation : forall mi los nts gl2 F rm rm2 lc lc2 f1
    fv Ps1 Ps2 fs1 fs2 M1 M2 mgb fptr1,
  wf_globals mgb gl2 ->
  wf_sb_mi mgb mi M1 M2 ->
  reg_simulation mi (los,nts) gl2 F rm rm2 lc lc2 ->
  ftable_simulation mi fs1 fs2 ->
  getOperandValue (los,nts) fv lc gl2 = Some fptr1 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs1 fptr1 = Some f1 ->
  trans_products nts Ps1 = Some Ps2 ->
  exists fptr2, exists f2,
    getOperandValue (los,nts) (wrap_call fv) lc2 gl2 = Some fptr2 /\
    OpsemAux.lookupExFdecViaPtr Ps2 fs2 fptr2 = Some f2 /\
    gv_inject mi fptr1 fptr2 /\
    trans_fdec f1 = f2.
Proof.
  intros.
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs1 fptr1) as R2.
  destruct R2 as [fid|]; inv H4.
  eapply simulation__getOperandValue in H3; eauto.
  destruct H3 as [fptr2 [J1 J2]].
  rewrite wrapper_is_identical. 
  exists fptr2.
  erewrite <- H2; eauto.
  rewrite <- HeqR2. simpl.
  remember (lookupFdefViaIDFromProducts Ps1 fid) as R.
  destruct R; inv H7.
  erewrite trans_products__none; eauto.
  eapply trans_products__trans_fdec in H4; eauto.
  destruct H4 as [f2 [H4 H6]].
  eauto.
Qed.

Lemma getValueViaBlockFromValuels__eql : forall B1 B2 vls,
  label_of_block B1 = label_of_block B2 ->
  getValueViaBlockFromValuels vls B1 = getValueViaBlockFromValuels vls B2.
Proof.
  intros.  
  destruct B1. destruct B2. simpl in H. subst. simpl. auto.
Qed.

Lemma get_metadata_from_list_value_l_spec : forall mi TD gl F rm1 rm2 lc1 lc2 B1 
  B2 blk1 bofs1 eofs1
  (Hrsim : reg_simulation mi TD gl F rm1 rm2 lc1 lc2)
  (Heq : label_of_block B1 = label_of_block B2)
  vls v
  (HeqR1 : ret v = getValueViaBlockFromValuels vls B1)
  (HeqR4 : ret (mkMD blk1 bofs1 eofs1) =
          SBspecAux.get_reg_metadata TD gl rm1 v)
  (bvls0 : list_value_l) (evls0 : list_value_l)
  (HeqR5 : ret (bvls0, evls0) =
          get_metadata_from_list_value_l rm2 vls),
  exists bv2, exists ev2, exists bgv2, exists egv2,
    getValueViaBlockFromValuels bvls0 B2 = Some bv2 /\
    getValueViaBlockFromValuels evls0 B2 = Some ev2 /\
    Opsem.getOperandValue TD bv2 lc2 gl = Some bgv2 /\
    Opsem.getOperandValue TD ev2 lc2 gl = Some egv2 /\
    gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 /\
    gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2.
Proof.
  intros mi TD gl F rm1 rm2 lc1 lc2.
  destruct B1. destruct B2. simpl.
  induction vls; simpl; intros; subst.
    inv HeqR1.

    remember (get_reg_metadata rm2 v) as R.
    destruct R as [[bv ev]|]; try solve [inv HeqR5].
    remember (get_metadata_from_list_value_l rm2 vls) as R'.
    destruct R' as [[baccum eaccum]|]; inv HeqR5.
    simpl.
    destruct (l2==l1); subst.
      inv HeqR1.
      exists bv. exists ev.
      destruct Hrsim as [Hrsim1 Hrsim2].
      symmetry in HeqR4.
      apply Hrsim2 in HeqR4.
      destruct HeqR4 as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
      rewrite <- HeqR in J1. inv J1.
      exists bgv2. exists egv2. split; auto.

      eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes__reg_simulation : forall M1 M2 TD gl 
  mi F B1 B2 rm2 mgb
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl)
  ps1 lc1 rm1 re1 lc2 ps2,
  reg_simulation mi TD gl F rm1 rm2 lc1 lc2 ->
  SBspec.getIncomingValuesForBlockFromPHINodes TD ps1 B1 gl lc1 rm1 
    = Some re1 ->
  label_of_block B1 = label_of_block B2 ->
  trans_phinodes rm2 ps1 = Some ps2 ->
  exists re2, 
    Opsem.getIncomingValuesForBlockFromPHINodes TD ps2 B2 gl lc2 = Some re2 
      /\ incomingValues_simulation mi re1 rm2 re2.
Proof.
  induction ps1; simpl; intros lc1 rm1 re1 lc2 ps2 Hrsim Hget Heq Htrans; auto.
    inv Hget. inv Htrans. simpl. exists nil. auto.

    destruct a as [id0 t vls].
    remember (trans_phinodes rm2 ps1) as R.
    destruct R as [ps2'|]; try solve [inv Htrans].
    remember (getValueViaBlockFromValuels vls B1) as R1.
    destruct R1 as [v|]; try solve [inv Hget].
    remember (Opsem.getOperandValue TD v lc1 gl) as R2.
    destruct R2 as [gv1|]; try solve [inv Hget].
    remember (SBspec.getIncomingValuesForBlockFromPHINodes TD ps1 B1 gl lc1 
      rm1) as R3.
    destruct R3 as [idgvs|]; try solve [inv Hget].
    destruct (isPointerTypB t).
      remember (SBspecAux.get_reg_metadata TD gl rm1 v) as R4.
      destruct R4 as [[bgv1 egv1]|]; inv Hget.
      remember (get_metadata_from_list_value_l rm2 vls) as R5.
      destruct R5 as [[bvls0 evls0]|]; try solve [inv Htrans].
      remember (lookupAL (id * id) rm2 id0) as R6.
      destruct R6 as [[bid0 eid0]|]; inv Htrans.
      simpl.
      eapply get_metadata_from_list_value_l_spec in HeqR5; eauto.
      destruct HeqR5 as [bv2 [ev2 [bgv2 [egv2 [Hvb [Hve [Hgetb [Hgete
        [Hinjb Hinje]]]]]]]]].
      rewrite Hvb. rewrite Hve. 
      rewrite Hgetb. rewrite Hgete.
      erewrite <- getValueViaBlockFromValuels__eql; eauto.
      rewrite <- HeqR1.
      symmetry in HeqR2.
      eapply simulation__getOperandValue in HeqR2; eauto.
      destruct HeqR2 as [gv2 [HeqR2 Hinj2]].
      replace (@Opsem.getOperandValue DGVs) with getOperandValue; auto.
      rewrite HeqR2.
      symmetry in HeqR3.
      eapply IHps1 in HeqR3; eauto.
      destruct HeqR3 as [re2 [Hgeti Hisim]].
      rewrite Hgeti.  
      exists ((eid0, egv2) :: (bid0, bgv2) :: (id0,gv2) :: re2).
      repeat (split; auto). 
      
      inv Hget. inv Htrans.
      simpl. 
      erewrite <- getValueViaBlockFromValuels__eql; eauto.
      rewrite <- HeqR1.
      symmetry in HeqR2.
      eapply simulation__getOperandValue in HeqR2; eauto.
      destruct HeqR2 as [gv2 [HeqR2 Hinj2]].
      replace (@Opsem.getOperandValue DGVs) with getOperandValue; auto.
      rewrite HeqR2.
      symmetry in HeqR3.
      eapply IHps1 in HeqR3; eauto.
      destruct HeqR3 as [re2 [Hgeti Hisim]].
      rewrite Hgeti.  
      exists ((id0, gv2) :: re2).
      repeat (split; auto). 
Qed.

Fixpoint incomingValues_in_dom (re1:list (id * GenericValue * monad metadata)) 
  (d:ids) : Prop :=
match re1 with
| nil => True
| (id1,_,_)::re1' => In id1 d /\ incomingValues_in_dom re1' d 
end.

Lemma updateValuesForNewBlock__reg_simulation : forall mi los gl f1 rm2 re1 
    rm1 lc1 lc2 re2 lc1' rm1' lc2' M1 M2 mgb ex_ids nts
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),
  incomingValues_in_dom re1 (getFdefLocs f1) ->
  gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids,rm2) ->
  reg_simulation mi (los,nts) gl f1 rm1 rm2 lc1 lc2 ->
  incomingValues_simulation mi re1 rm2 re2 ->
  @SBspec.updateValuesForNewBlock DGVs re1 lc1 rm1 = (lc1', rm1') ->
  @Opsem.updateValuesForNewBlock DGVs re2 lc2 = lc2' ->
  reg_simulation mi (los,nts) gl f1 rm1' rm2 lc1' lc2'.
Proof.
  induction re1; simpl; intros rm1 lc1 lc2 re2 lc1' rm1' lc2' M1 M2 mgb ex_ids
    nts Hwfmi Hwfg Hindom Hgetmd Hrsim Hisim Hupdate Hupdate'.
    inv Hupdate. 
    destruct re2; inv Hisim; eauto.

    destruct a as [[i1 gv1] [[bgv1 bgv2]|]].
      destruct re2; try solve [inv Hisim].
      destruct p as [eid2 egv2'].
      destruct re2; try solve [inv Hisim].
      destruct p as [bid2 bgv2'].
      destruct re2; try solve [inv Hisim].
      destruct p as [i2 gv2].
      destruct Hisim as [Heq [Hginj [Hlk [Hbinj [Heinj Hisim]]]]]; subst.
      remember (@SBspec.updateValuesForNewBlock DGVs re1 lc1 rm1) as R.      
      destruct R as [lc' rm']. inv Hupdate.
      simpl.
      destruct Hindom as [Hin Hindom].
      eapply reg_simulation__updateAddAL_prop; eauto.

      destruct re2; try solve [inv Hisim].
      destruct p as [i2 gv2].
      destruct Hisim as [Heq [Hginj Hisim]]; subst.
      remember (@SBspec.updateValuesForNewBlock DGVs re1 lc1 rm1) as R.      
      destruct R as [lc' rm']. inv Hupdate.
      simpl.
      destruct Hindom as [Hin Hindom].
      eapply reg_simulation__updateAddAL_lc; eauto.
Qed.

Lemma getPhiNodeID_in_getFdefLocs : forall f1 l0 ps p cs tmn,
  blockInFdefB (block_intro l0 ps cs tmn) f1 = true ->
  In p ps ->
  In (getPhiNodeID p) (getFdefLocs f1).
Proof.
  intros.
  destruct f1. destruct f. simpl.
  apply in_or_app. right.
  eapply in_getBlockLocs__in_getBlocksLocs in H; eauto.
  simpl. 
  apply in_or_app. left.
  apply in_getPhiNodeID__in_getPhiNodesIDs; auto.
Qed.  

Lemma getIncomingValues_in_dom_aux : forall l0 cs1 tmn f1 TD B1 gl ps2 ps1 lc1 
    rm1 re1,
  blockInFdefB (block_intro l0 (ps1++ps2) cs1 tmn) f1 = true ->
  @SBspec.getIncomingValuesForBlockFromPHINodes DGVs TD ps2 B1 gl lc1 rm1 
    = ret re1 ->
  incomingValues_in_dom re1 (getFdefLocs f1).
Proof.
  induction ps2; simpl; intros ps1 lc1 rm1 re1 HBinF Hget. 
    inv Hget. simpl. auto.

    destruct a.
    destruct (getValueViaBlockFromValuels l1 B1); tinv Hget.
    destruct (Opsem.getOperandValue TD v lc1 gl); tinv Hget.
    remember (SBspec.getIncomingValuesForBlockFromPHINodes TD ps2 B1 gl lc1 rm1) as R.
    destruct R; tinv Hget.
    destruct (isPointerTypB t).
      destruct (SBspecAux.get_reg_metadata TD gl rm1 v); inv Hget.
      simpl. symmetry in HeqR.
      rewrite_env ((ps1 ++ [insn_phi i0 t l1]) ++ ps2) in HBinF.
      apply IHps2 with (ps1:=ps1 ++ [insn_phi i0 t l1]) in HeqR; simpl; auto.
      split; auto.
        eapply getPhiNodeID_in_getFdefLocs with (p:=insn_phi i0 t l1); eauto.
          simpl. apply in_or_app. left. apply in_or_app. simpl. auto.
      
      inv Hget. simpl.
      simpl. symmetry in HeqR.
      rewrite_env ((ps1 ++ [insn_phi i0 t l1]) ++ ps2) in HBinF.
      apply IHps2 with (ps1:=ps1 ++ [insn_phi i0 t l1]) in HeqR; simpl; auto.
      split; auto.
        eapply getPhiNodeID_in_getFdefLocs with (p:=insn_phi i0 t l1); eauto.
          simpl. apply in_or_app. left. apply in_or_app. simpl. auto.
Qed.

Lemma getIncomingValues_in_dom : forall l0 cs1 tmn f1 TD B1 gl ps1 lc1 rm1 re1,
  blockInFdefB (block_intro l0 ps1 cs1 tmn) f1 = true ->
  @SBspec.getIncomingValuesForBlockFromPHINodes DGVs TD ps1 B1 gl lc1 rm1 
    = ret re1 ->
  incomingValues_in_dom re1 (getFdefLocs f1).
Proof.
  intros.
  eapply getIncomingValues_in_dom_aux with (ps1:=nil); eauto.
Qed.

Lemma switchToNewBasicBlock__reg_simulation : forall mi nts los gl f1 rm1 rm2 lc1
  lc2 B1 B2 l0 ps1 cs1 tmn ps2 cs2 lc1' rm1' M1 M2 mgb ex_ids
  (Hwfmi : wf_sb_mi mgb mi M1 M2)
  (Hwfg : wf_globals mgb gl),  
  blockInFdefB (block_intro l0 ps1 cs1 tmn) f1 = true ->
  gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids,rm2) ->
  reg_simulation mi (los,nts) gl f1 rm1 rm2 lc1 lc2 ->
  SBspec.switchToNewBasicBlock (los,nts) (block_intro l0 ps1 cs1 tmn) B1 gl 
    lc1 rm1 = ret (lc1', rm1') ->
  label_of_block B1 = label_of_block B2 ->
  trans_phinodes rm2 ps1 = Some ps2 ->
  exists lc2', Opsem.switchToNewBasicBlock (los,nts)
    (block_intro l0 ps2 cs2 tmn) B2 gl lc2 = Some lc2' /\
    reg_simulation mi (los,nts) gl f1 rm1' rm2 lc1' lc2'.
Proof.
  intros mi nts los gl f1 rm1 rm2 lc1 lc2 B1 B2 l0 ps1 cs1 tmn ps2 cs2 lc1' rm1' 
    M1 M2 mgb ex_ids Hwfmi Hwfg HBinF Hgenmd Hrsim Hswitch Hleq Htphis.
  unfold SBspec.switchToNewBasicBlock in Hswitch.
  unfold Opsem.switchToNewBasicBlock. simpl in *.
  remember (SBspec.getIncomingValuesForBlockFromPHINodes (los,nts) ps1 B1 gl 
    lc1 rm1) as R.
  destruct R; try solve [inv Hswitch].  
    symmetry in HeqR.
    assert (Hindom := HeqR).
    eapply getIncomingValues_in_dom in Hindom; eauto.
    eapply getIncomingValuesForBlockFromPHINodes__reg_simulation in HeqR; eauto.
    destruct HeqR as [re2 [Hget Hisim]].
    rewrite Hget. inv Hswitch.
    eapply updateValuesForNewBlock__reg_simulation in H0; eauto.
Qed.

Lemma getCmdID_in_getFdefLocs : forall B f1 c cs tmn2 id0
  (HBinF : blockInFdefB B f1 = true)
  (Heqb1 : exists l1, exists ps1, exists cs11, 
                B = block_intro l1 ps1 (cs11 ++ c :: cs) tmn2)
  (Hget : getCmdID c = Some id0),
  In id0 (getFdefLocs f1).
Proof.
  intros.
  destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
  destruct f1. destruct f. simpl.
  destruct (split a).
  apply in_or_app. right.
  eapply in_getBlockLocs__in_getBlocksLocs in HBinF; eauto.
  simpl. 
  apply in_or_app. right.
  apply in_or_app. left.
  apply getCmdID_in_getCmdsLocs with (c:=c); auto.
  apply in_or_app. simpl. auto.
Qed.  

Lemma ids2atoms_app : forall d1 d2,
  ids2atoms (d1++d2) [=] ids2atoms d1 `union` ids2atoms d2.
Proof.
  induction d1; intros; simpl.
    fsetdec.
    rewrite IHd1. fsetdec.
Qed.

Lemma wf_value_id__in_getFdefLocs : forall S m f v t,
  wf_value S m f v t -> SB_ds_pass.getValueID v[<=]ids2atoms (getFdefLocs f).
Proof.
  intros.
  inv H; simpl.
    clear. fsetdec.

    destruct f. destruct f. simpl in *.
    remember (lookupTypViaIDFromArgs a id5) as R.
    apply ids2atoms__in.
    destruct R; inv H2.
      symmetry in HeqR.
      destruct (In_dec eq_atom_dec id5 (getArgsIDs a)) as [Hin | Hnotin].
        apply in_or_app. auto.

        apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
        rewrite HeqR in Hnotin. inv Hnotin.
      destruct (In_dec eq_atom_dec id5 (getBlocksLocs b)) as [Hin | Hnotin].
        apply in_or_app. auto.
        
        apply notInBlocks__lookupTypViaIDFromBlocks in Hnotin.
        rewrite H3 in Hnotin. inv Hnotin.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-impredicative-set") ***
*** End: ***
 *)

