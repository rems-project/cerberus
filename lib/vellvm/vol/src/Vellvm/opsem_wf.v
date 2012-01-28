Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "./GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import Ensembles.
Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Require Import analysis.
Require Import typings.
Require Import typings_props.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Lattice.
Require Import Floats.
Require Import AST.
Require Import Maps.
Require Import opsem.
Require Import opsem_props.

(************** Opsem PP *********************************************** ***)

Module OpsemPP. Section OpsemPP.

Context `{GVsSig : GenericValues}.

Export Opsem.
Export OpsemProps.
Import AtomSet.

Notation GVs := GVsSig.(GVsT).
Notation "gv @ gvs" := 
  (GVsSig.(instantiate_gvs) gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (GVsSig.(gv2gvs) gv t) (at level 41).
Notation "vidxs @@ vidxss" := (in_list_gvs vidxs vidxss) 
  (at level 43, right associativity).

Inductive wf_GVs : TargetData -> GVs -> typ -> Prop :=
| wf_GVs_intro : forall TD gvs t sz, 
    getTypeSizeInBits TD t = Some sz ->
    (forall gv, gv @ gvs ->
      sizeGenericValue gv = Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8)) ->
    GVsSig.(inhabited) gvs -> 
    wf_GVs TD gvs t.

Hint Constructors wf_GVs.

Inductive wf_defs TD (f:fdef) (lc:GVsMap) : list atom -> Prop :=
| wf_defs_nil : wf_defs TD f lc nil
| wf_defs_cons : forall id1 t1 gvs1 defs',
    lookupTypViaIDFromFdef f id1 = Some t1 ->
    lookupAL _ lc id1 = Some gvs1 -> 
    wf_GVs TD gvs1 t1 ->
    wf_defs TD f lc defs' ->
    wf_defs TD f lc (id1::defs').

Lemma wf_defs_elim : forall TD ids1 F lc,
  wf_defs TD F lc ids1 ->
  forall id1, List.In id1 ids1 ->
  exists t1, exists gvs1,
    lookupTypViaIDFromFdef F id1 = Some t1 /\
    lookupAL _ lc id1 = Some gvs1 /\
    wf_GVs TD gvs1 t1.
Proof.
  induction ids1; intros; simpl in H0; inv H0.  
    inv H.
    exists t1. exists gvs1. split; auto.

    inv H.
    eapply IHids1 in H6; eauto.
Qed.    

Lemma wf_defs_intro : forall TD ids1 F lc,
  (forall id1, List.In id1 ids1 ->
   exists t1, exists gvs1,
     lookupTypViaIDFromFdef F id1 = Some t1 /\
     lookupAL _ lc id1 = Some gvs1 /\
     wf_GVs TD gvs1 t1) ->
  wf_defs TD F lc ids1.
Proof.
  induction ids1; intros.
    apply wf_defs_nil.  

    destruct (@H a) as [t1 [gvs1 [J1 [J2 J3]]]]; simpl; auto.
    eapply wf_defs_cons; eauto.
      apply IHids1.
      intros id1 J.
      apply H. simpl. auto.
Qed.

Lemma wf_defs_eq : forall TD ids2 ids1 F' lc',
  set_eq _ ids1 ids2 ->
  wf_defs TD F' lc' ids1 ->
  wf_defs TD F' lc' ids2.
Proof.
  intros.
  apply wf_defs_intro.
  intros id1 Hin.
  destruct H as [J1 J2].
  eapply wf_defs_elim in H0; eauto.
Qed.

Lemma wf_defs_updateAddAL : forall TD g F' lc' ids1 ids2 i1 t1,
  wf_defs TD F' lc' ids1 ->
  set_eq _ (i1::ids1) ids2 ->
  lookupTypViaIDFromFdef F' i1 = ret t1 ->
  wf_GVs TD g t1 ->
  wf_defs TD F' (updateAddAL _ lc' i1 g) ids2.
Proof.
  intros TD g F' lc' ids1 ids2 i1 t1 HwfDefs Heq Hlkup Hwfgvs.  
  apply wf_defs_intro.  
  intros id1 Hin.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  destruct (eq_dec i1 id1); subst.
    exists t1. exists g. 
    split; auto.
    split; auto. 
      apply lookupAL_updateAddAL_eq; auto.      

    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    eapply wf_defs_elim in HwfDefs; eauto.
    destruct HwfDefs as [t2 [gv2 [J1 [J2 J3]]]].
    exists t2. exists gv2.
    split; auto.
    split; auto. 
      rewrite <- lookupAL_updateAddAL_neq; auto.      
Qed.

Definition wf_lc TD (f:fdef) (lc:GVsMap) : Prop := forall i0 gvs0 t0, 
  lookupTypViaIDFromFdef f i0 = Some t0 ->
  lookupAL _ lc i0 = Some gvs0 -> 
  wf_GVs TD gvs0 t0.

Lemma const2GV__inhabited : forall TD gl c gvs,
  const2GV TD gl c = Some gvs -> GVsSig.(inhabited) gvs.
Proof.
  intros TD gl c gvs H.
  unfold const2GV in H.
  destruct (_const2GV TD gl c) as [[gv ?]|]; inv H.
    eauto using GVsSig.(cgv2gvs__inhabited).
Qed.

Lemma const2GV__getTypeSizeInBits : forall S TD c t gl gvs gv,
  wf_typ S t ->
  wf_const S TD c t ->
  feasible_typ TD t ->
  const2GV TD gl c = Some gvs ->
  gv @ gvs ->
  wf_global TD S gl ->
  exists sz, 
    getTypeSizeInBits TD t = Some sz /\
    Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv.
Proof.
  intros.
  unfold const2GV in H2.
  remember (_const2GV TD gl c) as R.
  destruct R as [[]|]; inv H2.
  symmetry in HeqR.
  destruct TD.
  unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment.
  eapply const2GV__getTypeSizeInBits_aux in HeqR; eauto.
  destruct HeqR as [Heq [sz [al [J1 J2]]]]; subst.
  exists sz. 
  rewrite J1.
  split; auto.
    eapply GVsSig.(cgv2gvs__getTypeSizeInBits); eauto.
Qed.

Lemma getOperandValue__inhabited : forall los nts s ps f v t lc gl gvs,
  wf_lc (los, nts) f lc ->
  wf_value s (module_intro los nts ps) f v t ->
  getOperandValue (los, nts) v lc gl = Some gvs ->
  GVsSig.(inhabited) gvs.
Proof.
  intros los nts s ps f v t lc gl gvs Hwflc Hwfv Hget.
  inv Hwfv; simpl in Hget; eauto using const2GV__inhabited.
    unfold wf_lc in Hwflc.
    eapply Hwflc in H8; eauto.
    inv H8; auto.
Qed.
    
Lemma getOperandValue__wf_gvs : forall los nts s ps f v t lc gl gvs,
  wf_global (los,nts) s gl ->
  wf_lc (los,nts) f lc ->
  wf_value s (module_intro los nts ps) f v t ->
  getOperandValue (los,nts) v lc gl = Some gvs ->
  wf_GVs (los,nts) gvs t.
Proof.
  intros los nts s ps f v t lc gl gvs Hwfg Hwflc Hwfv Hget.
  assert (J:=Hget).
  eapply getOperandValue__inhabited in J; eauto.
  inv Hwfv;  simpl in Hget.
    assert (H7':=H7).
    eapply feasible_typ_inv in H7; eauto.
    destruct H7 as [sz [al [J1 J2]]].
    eapply wf_GVs_intro with (sz:=sz); 
      eauto using GVsSig.(cgv2gvs__getTypeSizeInBits).
      unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment, 
             getTypeSizeInBits_and_Alignment_for_namedts in *.
      rewrite J1. auto.

      intros.  
      eapply const2GV__getTypeSizeInBits in Hget; eauto.
      destruct Hget as [sz0 [J3 J4]].
      unfold getTypeSizeInBits in J3.
      rewrite J1 in J3. inv J3. auto.

    unfold wf_lc in Hwflc.
    eapply Hwflc in H8; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec1_aux : forall ifs s Ps los nts f
    b gl lc id1 t l3 cs tmn ps2 ps1 lc' ,
  wf_lc (los,nts) f lc ->
  Some lc' = getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc ->
  List.In id1 (getPhiNodesIDs ps2) ->
  uniqFdef f ->
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_global (los, nts) s gl ->
  wf_phinodes ifs s (module_intro los nts Ps) f 
    (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  lookupTypViaIDFromFdef f id1 = ret t ->
  exists gvs, lookupAL _ lc' id1 = Some gvs /\ wf_GVs (los,nts) gvs t.
Proof.    
  intros ifs s Ps los nts f b gl lc id1 t l3 cs tmn ps2 ps1 lc' Hwflc H H0 Huniq 
    Hbinf Hwfg Hwfps Hlk.
  assert (Huniq':=Hbinf).
  apply uniqFdef__uniqBlockLocs in Huniq'; auto.
  simpl in Huniq'. 
  apply NoDup_split in Huniq'.
  destruct Huniq' as [Huniq' _].
  assert (In id1 (getPhiNodesIDs (ps1++ps2))) as Hin.
    rewrite getPhiNodesIDs_app.
    apply in_app_iff; auto.
  generalize dependent lc'.
  generalize dependent ps1.
  induction ps2; simpl in *; intros.
    inversion H0.

    assert (J:=Hbinf).
    eapply lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes in J; eauto.
    destruct a.
    simpl in H0. simpl in J.
    inv Hwfps. inv H8.
    destruct H0 as [H0 | H0]; subst.
      rewrite NoDup_lookupTypViaIDFromPhiNodes in J; auto.
      inv J.
      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].
        eapply wf_value_list__getValueViaBlockFromValuels__wf_value in H4; eauto.
        remember (getOperandValue (los,nts) v lc gl) as R.
        destruct R as [g|]; tinv H.
        symmetry in HeqR. eapply getOperandValue__wf_gvs in HeqR; eauto.
        destruct (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc); 
          inv H.
        exists g. simpl. 
        destruct (id1 == id1) as [e' | n]; try solve [contradict n; auto].
          split; auto.

      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].   
        remember (getOperandValue (los,nts) v lc gl) as R.
        destruct R; tinv H. 
        remember (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc) 
          as R.
        destruct R; inversion H; subst.         
        simpl.
        destruct (id1==i0); subst.
          clear - Huniq' H0.
          rewrite getPhiNodesIDs_app in Huniq'.
          apply NoDup_split in Huniq'.
          destruct Huniq' as [_ Huniq'].
          inv Huniq'. congruence.
      
          eapply IHps2 with (ps1:=ps1 ++ [insn_phi i0 t0 l0]); simpl_env; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall ifs s Ps los nts f b 
    gl lc id1 t l3 cs tmn ps lc' ,
  wf_lc (los,nts) f lc ->
  Some lc' = getIncomingValuesForBlockFromPHINodes (los,nts) ps b gl lc ->
  In id1 (getPhiNodesIDs ps) ->
  uniqFdef f ->
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_global (los, nts) s gl ->
  wf_fdef ifs s (module_intro los nts Ps) f ->
  lookupTypViaIDFromFdef f id1 = ret t ->
  exists gvs, lookupAL _ lc' id1 = Some gvs /\ wf_GVs (los,nts) gvs t.
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H3.
    apply lookupBlockViaLabelFromFdef_inv in H3; auto.
    destruct H3; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec1_aux with (ps1:=nil); 
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2_aux : forall ifs s los nts Ps f
  b gl lc l3 cs tmn (Hwflc: wf_lc (los, nts) f lc) 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps2 ps1 rs,
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_phinodes ifs s (module_intro los nts Ps) f 
    (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps2 b gl lc ->
  (forall id0 gvs t0, In (id0,gvs) rs -> 
     lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs (los, nts) gvs t0).
Proof.    
  intros ifs s los nts Ps f b gl lc l3 cs tmn Hwflc Hwfg Huniq ps2 ps1 rs Hbinf.
  assert (Huniq':=Hbinf).
  apply uniqFdef__uniqBlockLocs in Huniq'; auto.
  simpl in Huniq'. 
  apply NoDup_split in Huniq'.
  destruct Huniq' as [Huniq' _].
  generalize dependent rs.
  generalize dependent ps1.
  induction ps2; intros ps1 Hbinf Hnup rs Hwfps H id0 gv t0 Hin Hlkup; 
    simpl in *.
    inv H. inv Hin.

    destruct a.
    remember (getValueViaBlockFromValuels l0 b) as R1.
    destruct R1; try solve [inversion H].   
      remember (getOperandValue (los,nts) v lc gl) as R.
      destruct R; tinv H.
      destruct (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc); 
        inv H.
      inv Hwfps.
      simpl in Hin. 
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin.
        inv H6.
        assert (J:=Hbinf).
        eapply lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes in J; eauto.
          eapply wf_value_list__getValueViaBlockFromValuels__wf_value in H2; 
            eauto.
          simpl in J.
          rewrite NoDup_lookupTypViaIDFromPhiNodes in J; auto.
          inv J.
          symmetry in HeqR. eapply getOperandValue__wf_gvs in HeqR; eauto.

          simpl. rewrite getPhiNodesIDs_app.
          apply in_app_iff; simpl; auto.

        rewrite_env ((ps1 ++ [insn_phi i0 t l0]) ++ ps2) in H7.
        eapply IHps2 in H7; simpl_env; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2 : forall ifs s los nts Ps f b 
  gl lc l3 cs tmn (Hwflc: wf_lc (los, nts) f lc) 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps rs,
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_global (los, nts) s gl ->
  wf_fdef ifs s (module_intro los nts Ps) f ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps b gl lc ->
  (forall id0 gvs t0, In (id0,gvs) rs -> 
     lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs (los, nts) gvs t0).
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H.
    apply lookupBlockViaLabelFromFdef_inv in H; auto.
    destruct H; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec2_aux with (ps1:=nil); 
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma updateValuesForNewBlock_spec2 : forall TD f lc id1 gv t,
  lookupAL _ lc id1 = Some gv ->
  lookupTypViaIDFromFdef f id1 = Some t ->
  wf_lc TD f lc ->
  forall rs, 
  (forall id0 gv t0, 
     In (id0,gv) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs TD gv t0) ->
  exists t', exists gv', 
    lookupTypViaIDFromFdef f id1 = Some t' /\
    lookupAL _ (updateValuesForNewBlock rs lc) id1 = Some gv' /\
    wf_GVs TD gv' t'.
Proof.
  induction rs; intros; simpl in *.   
    exists t. exists gv. eauto.

    destruct a. 
    destruct (id1==i0); subst.
      exists t. exists g. rewrite lookupAL_updateAddAL_eq; eauto.
      rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall TD f lc,
  wf_lc TD f lc ->
  forall rs, 
  (forall id0 gv t0, 
     In (id0,gv) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_GVs TD gv t0) ->
  wf_lc TD f (updateValuesForNewBlock rs lc).
Proof.  
  induction rs; intros; simpl in *; auto.
    destruct a.
    intros x gvx tx Htyp Hlk.
    destruct (i0==x); subst.
      rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk. eauto.

      rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
      eapply IHrs in Hlk; eauto.
Qed.

Lemma wf_lc_br_aux : forall ifs s los nts Ps f b1 b2 gl lc lc' l3 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f)
  (Hswitch : switchToNewBasicBlock (los, nts) b1 b2 gl lc = ret lc')
  (Hlkup : Some b1 = lookupBlockViaLabelFromFdef f l3)
  (Hwfg : wf_global (los, nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts Ps) f)
  (Hwflc : wf_lc (los, nts) f lc),
  wf_lc (los, nts) f lc'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  remember (getIncomingValuesForBlockFromPHINodes (los, nts)
              (getPHINodesFromBlock b1) b2 gl lc) as R1.
  destruct R1; inv Hswitch.
  apply updateValuesForNewBlock_spec3; auto.
    destruct b1.
    eapply getIncomingValuesForBlockFromPHINodes_spec2; 
      eauto using lookupBlockViaLabelFromFdef_prop.
Qed.

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' gl los nts Ps ifs s
  (l3 : l)
  (ps : phinodes)
  (cs : list cmd) tmn
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
         (block_intro l3 ps cs tmn) gl lc = ret lc')
  (t : list atom)
  (Hwfdfs : wf_defs (los,nts) F lc t)
  (ids0' : list atom)
  (Hwflc : wf_lc (los,nts) F lc)
  (Hwfg : wf_global (los, nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts Ps) F)
  (Huniq : uniqFdef F)
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  apply wf_defs_intro.
  intros id1 Hid1.
  remember (getIncomingValuesForBlockFromPHINodes (los,nts) ps'
                (block_intro l3 ps cs tmn) gl lc) as R1.
  destruct R1; inv Hswitch.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    assert (J:=Hlkup).
    eapply InPhiNodes_lookupTypViaIDFromFdef in Hlkup; eauto.
    destruct Hlkup as [t1 Hlkup].
    eapply getIncomingValuesForBlockFromPHINodes_spec1 in HeqR1; eauto.
    destruct HeqR1 as [gv [HeqR1 Hwfgv]].
    eapply updateValuesForNewBlock_spec4 in HeqR1; eauto.

    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin.
    apply wf_defs_elim with (id1:=id1) in Hwfdfs; auto.
    destruct Hwfdfs as [t1 [gv1 [J1 [J2 J3]]]].
    eapply updateValuesForNewBlock_spec2 with (rs:=l0) in J2; eauto.
      eapply getIncomingValuesForBlockFromPHINodes_spec2; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 ifs
  s los nts Ps lc lc' gl,
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef ifs s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 ifs s los nts Ps lc lc' gl Hwfg
    Hwflc HwfF Huniq HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd, inscope_of_id.
  destruct F as [[? ? ? la va] bs].
  remember (dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms Huniq HwfF.
    simpl in Huniq. destruct Huniq.
    eapply dom_successors; eauto.

  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound').
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil ++ getArgsIDs la)(fh:=fheader_intro f t i0 la va)(bs:=bs)
      (l0:=l') in J1.
    destruct J1 as [r J1].
    exists r. split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
      apply fold_left__spec in J1.
      symmetry in Hinscope.
      apply fold_left__spec in Hinscope.
      destruct J1 as [J1 [J2 J3]].
      destruct Hinscope as [J4 [J5 J6]].
      intros id1 J.
      assert (J':=J).
      apply ListSet.set_diff_elim1 in J.
      apply ListSet.set_diff_elim2 in J'.
      apply J3 in J.
      destruct J as [J | J].
      SCase "id1 in init and the current block".
        simpl in J.
        apply in_app_or in J.
        destruct J as [J | J]; try solve [contradict J; auto].
        apply J4.
        apply in_or_app. right.
        apply in_or_app; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. destruct Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs la).
            apply in_or_app; auto.
      
            apply J5 in J9; auto.
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      eapply wf_defs_br_aux; eauto.
        
  Case "cs'<>nil".
    assert (J1:=inbound').
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n]; 
      try solve [contradict n; auto].
    simpl_env.
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getArgsIDs la)(fh:=fheader_intro f t i0 la va)(bs:=bs)(l0:=l') in J1.
    destruct J1 as [r J1].
    exists r. split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
      apply fold_left__spec in J1.
      symmetry in Hinscope.
      apply fold_left__spec in Hinscope.
      destruct J1 as [J1 [J2 J3]].
      destruct Hinscope as [J4 [J5 J6]].
      intros id1 J.
      assert (J':=J).
      apply ListSet.set_diff_elim1 in J.
      apply ListSet.set_diff_elim2 in J'.
      apply J3 in J.
      destruct J as [J | J].
      SCase "id1 in init and the current block".
        simpl in J.
        apply in_app_or in J.
        destruct J as [J | J]; try solve [contradict J; auto].
        apply J4.
        apply in_or_app. right.
        apply in_or_app; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. destruct Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs la).
            apply in_or_app; auto.
      
            apply J5 in J9; auto. 
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      eapply wf_defs_br_aux; eauto.
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs ids0 l' ps' cs' tmn' l0 
  ifs s los nts Ps lc lc' gl bid,
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef ifs s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c los nts Ps gl lc ifs s lc',
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef ifs s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero (los,nts) c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  remember (isGVZero (los,nts) c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Fixpoint wf_params TD (gvs:list GVs) (lp:params) : Prop :=
match (gvs, lp) with
| (nil, nil) => True
| (gv::gvs', ((t, _), _)::lp') => wf_GVs TD gv t /\ wf_params TD gvs' lp'
| _ => False
end.

Lemma params2GVs_wf_gvs : forall los nts Ps F gl lc (Hwfc : wf_lc (los,nts) F lc)
  S (Hwfg : wf_global (los, nts) S gl) tvs lp gvs,
  wf_value_list
          (make_list_system_module_fdef_value_typ
             (map_list_typ_attributes_value
                (fun (typ_' : typ) attr (value_'' : value) =>
                 (S, (module_intro los nts Ps), F, value_'', typ_'))
                tvs)) ->
  lp = map_list_typ_attributes_value
        (fun (typ_' : typ) attr (value_'' : value) => (typ_', attr, value_''))
        tvs ->
  params2GVs (los,nts) lp lc gl = Some gvs -> wf_params (los,nts) gvs lp.
Proof.
  induction tvs; intros lp gvs Hwfvs Heq Hp2gv; subst; simpl in *.
    inv Hp2gv. simpl. auto.

    remember (getOperandValue (los,nts) v lc gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    remember (params2GVs (los,nts) (map_list_typ_attributes_value
                (fun (typ_' : typ) (attr : attributes) (value_'' : value) 
                   => (typ_', attr, value_''))
                tvs) lc gl) as R.
    destruct R; inv Hp2gv.
    inv Hwfvs.
    split; eauto.
      eapply getOperandValue__wf_gvs; eauto.
Qed.

Lemma wf_lc_updateAddAL : forall TD f lc gv i0 t,
  wf_lc TD f lc -> 
  lookupTypViaIDFromFdef f i0 = ret t ->
  wf_GVs TD gv t -> 
  wf_lc TD f (updateAddAL _ lc i0 gv).
Proof.
  intros.
  intros x gvx tx Htyp Hlk.
  destruct (eq_atom_dec i0 x); subst.
    rewrite lookupAL_updateAddAL_eq in Hlk.
    inv Hlk. rewrite H0 in Htyp. inv Htyp. auto.

    rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma gundef_cgv2gvs__wf_gvs : forall los nts gv s t
  (Hwft : wf_typ s t)
  (H0 : feasible_typ (los, nts) t)
  (HeqR : ret gv = gundef (los, nts) t),
  wf_GVs (los, nts) ($ gv # t $) t.
Proof.
  intros.
  eapply gundef__getTypeSizeInBits in HeqR; eauto.
  destruct HeqR as [sz1 [al1 [J1 J2]]].
  apply wf_GVs_intro with (sz:=sz1); auto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts.
    rewrite J1. auto.
    eapply GVsSig.(gv2gvs__getTypeSizeInBits); eauto.
    eapply GVsSig.(gv2gvs__inhabited); eauto.
Qed.

Lemma fit_gv_gv2gvs__wf_gvs_aux : forall los nts gv s t gv0
  (Hwft : wf_typ s t)
  (H0 : feasible_typ (los, nts) t)
  (HeqR : ret gv = fit_gv (los, nts) t gv0),
  wf_GVs (los, nts) ($ gv # t $) t.
Proof.
  intros.
  eapply fit_gv__getTypeSizeInBits in HeqR; eauto.
  destruct HeqR as [sz [J1 J2]].
  apply wf_GVs_intro with (sz:=sz); auto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts in J1.
    remember (_getTypeSizeInBits_and_Alignment los
           (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
           true t) as R.
    destruct R as [[]|]; inv J1.
    eapply GVsSig.(gv2gvs__getTypeSizeInBits); eauto.

    eapply GVsSig.(gv2gvs__inhabited); eauto.
Qed.

Lemma lift_fit_gv__wf_gvs : forall los nts g s t t0 gv
  (Hwft : wf_typ s t) (Hwfg : wf_GVs (los, nts) g t0)
  (H0 : feasible_typ (los, nts) t)
  (HeqR : GVsSig.(lift_op1) (fit_gv (los, nts) t) g t = Some gv),
  wf_GVs (los, nts) gv t.
Proof.
  intros.
  assert (J:=H0).
  eapply feasible_typ_inv in H0; eauto.
  destruct H0 as [sz [al [J1 [J2 J3]]]].
  apply wf_GVs_intro with (sz:=sz); auto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts in *.
    rewrite J1. auto.

    eapply GVsSig.(lift_op1__getTypeSizeInBits); eauto.
    intros. symmetry in H0.
    eapply fit_gv__getTypeSizeInBits in H0; eauto.
    destruct H0 as [sz0 [H1 H2]].
    unfold getTypeSizeInBits in H1.
    rewrite J1 in H1. inv H1. auto.

    inv Hwfg.
    eapply GVsSig.(lift_op1__inhabited) in HeqR; eauto.
    intro x. apply fit_gv__total; auto.
Qed.

Lemma initializeFrameValues__wf_lc_aux : forall los nts Ps s ifs fattr ft fid va 
  bs2 la2 la1 lc1 
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  (Hwflc: wf_lc (los,nts) 
     (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) lc1) 
  lc2 gvs2 lp2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 = Some lc2 -> 
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) 
    lc2.
Proof.
  induction la2; simpl; intros la1 lc1 Huniq HwfF Hwflc lc2 gvs2 lp2 Hin Hpar.
    inv Hin. auto.

    destruct a. destruct p.
    destruct gvs2; simpl in *; subst.
      remember (_initializeFrameValues (los,nts) la2 nil lc1) as R1.
      destruct R1 as [lc'|]; tinv Hin.
      remember (gundef (los,nts) t) as R2.
      destruct R2; inv Hin.
        apply wf_lc_updateAddAL with (t:=t); eauto.
          rewrite_env ((la1++[(t,a,i0)])++la2).
          eapply IHla2; simpl_env; eauto.

          inv HwfF.
          simpl. 
          destruct Huniq as [Huniq1 Huniq2].
          apply NoDup_split in Huniq2.
          destruct Huniq2 as [Huniq2 _].
          rewrite NoDup_lookupTypViaIDFromArgs; auto.

          inv HwfF.
          assert (In (t, a, i0)
            (map_list_typ_attributes_id
              (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
              (typ_, attributes_, id_)) typ_attributes_id_list)) as J.
            rewrite <- H11.
            apply in_or_app; simpl; auto.
          apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
            auto.
          apply feasible_typ_list__in_args__feasible_typ 
            with (t:=t)(a:=a)(i0:=i0) in H13; auto.
          inv H13.
          eapply gundef_cgv2gvs__wf_gvs; eauto.

      remember (_initializeFrameValues (los,nts) la2 gvs2 lc1) as R1.
      destruct R1 as [lc'|]; tinv Hin.
      remember (GVsSig.(lift_op1) (fit_gv (los, nts) t) g t) as R2.
      destruct R2 as [gv|]; inv Hin.
      destruct lp2 as [|[[]]]; tinv Hpar.
      destruct Hpar as [Hwfg Hpar].
      apply wf_lc_updateAddAL with (t:=t); eauto.
        rewrite_env ((la1++[(t,a,i0)])++la2).
        eapply IHla2; simpl_env; eauto.
        
        inv HwfF.
        simpl. 
        destruct Huniq as [Huniq1 Huniq2].
        apply NoDup_split in Huniq2.
        destruct Huniq2 as [Huniq2 _].
        rewrite NoDup_lookupTypViaIDFromArgs; auto.
        
        inv HwfF.
        assert (In (t, a, i0)
          (map_list_typ_attributes_id
            (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
            (typ_, attributes_, id_)) typ_attributes_id_list)) as J.
          rewrite <- H11.
          apply in_or_app; simpl; auto.
        apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
          auto.
        apply feasible_typ_list__in_args__feasible_typ 
          with (t:=t)(a:=a)(i0:=i0) in H13; auto.
        inv H13.
        eapply lift_fit_gv__wf_gvs; eauto.
Qed.

Lemma initializeFrameValues__wf_lc : forall ifs s los nts Ps fattr ft fid la2 va 
  bs2 lc1 
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (Hwflc:wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) 
    lc1) 
  lc2 gvs2 lp2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 = Some lc2 -> 
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) lc2.
Proof.
  intros.  
  rewrite_env (nil++la2) in HwfF.
  rewrite_env (nil++la2) in Hwflc.
  rewrite_env (nil++la2).
  eapply initializeFrameValues__wf_lc_aux; eauto.
Qed.

Lemma initLocals__wf_lc : forall ifs s los nts Ps fattr ft fid la2 va 
  bs2
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  lc gvs2 lp2,
  initLocals (los,nts) la2 gvs2 = Some lc -> 
  wf_params (los,nts) gvs2 lp2 ->
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) lc.
Proof.
  intros. unfold initLocals in H. 
  eapply initializeFrameValues__wf_lc; eauto.
    intros x gvx tx J1 J2. inv J2.
Qed.

Lemma initLocals_spec' : forall fid fa rt la va lb gvs los nts ifs s lc Ps id1 t 
  lp
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hlk: lookupTypViaIDFromFdef (fdef_intro (fheader_intro fa rt fid la va) lb)
         id1 = ret t)
  (Hinit: initLocals (los,nts) la gvs = Some lc)
  (Hwfp : wf_params (los,nts) gvs lp)
  (Hin: In id1 (getArgsIDs la)),
  exists gv, lookupAL _ lc id1 = Some gv /\ wf_GVs (los, nts) gv t.
Proof.
  intros.
  assert (J:=Hinit).
  eapply initLocals_spec in J; eauto.
  destruct J as [gv J].
  eapply initLocals__wf_lc in Hinit; eauto.
Qed.

Lemma returnUpdateLocals__wf_lc : forall ifs los nts S F F' c Result lc lc' gl 
  lc'' Ps l1 ps1 cs1 tmn1 t B'
  (Hwfg: wf_global (los,nts) S gl) 
  (Hwfv: wf_value S (module_intro los nts Ps) F Result t),
  wf_lc (los,nts) F lc -> wf_lc (los,nts) F' lc' ->
  returnUpdateLocals (los,nts) c Result lc lc' gl = 
    ret lc'' ->
  uniqFdef F' ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F' = true -> 
  In c cs1 ->
  wf_insn ifs S (module_intro los nts Ps) F' B' (insn_cmd c) ->
  wf_lc (los,nts) F' lc''.
Proof.
  intros.
  unfold returnUpdateLocals in H1.
  remember (getOperandValue (los,nts) Result lc gl) as R.
  destruct R; tinv H1.
  destruct c; inv H1; auto.
  destruct n; inv H7; auto.
  destruct t0; tinv H6.
  remember (GVsSig.(lift_op1) (fit_gv (los, nts) t0) g t0) as R.
  destruct R; inv H6.
    eapply wf_lc_updateAddAL with (t:=t0); eauto.
      eapply uniqF__lookupTypViaIDFromFdef; eauto.

      symmetry in HeqR.
      eapply getOperandValue__wf_gvs in HeqR; eauto.
      inv H5. inv H20. inv H11. inv H22.
      eapply lift_fit_gv__wf_gvs; eauto.
Qed.

Lemma BOP__wf_gvs : forall S F los nts ps lc gl bop0 sz0 v1 v2 gvs3,
  wf_lc (los,nts) F lc ->
  wf_value S (module_intro los nts ps) F v1 (typ_int sz0) ->
  wf_value S (module_intro los nts ps) F v2 (typ_int sz0) ->
  BOP (los,nts) lc gl bop0 sz0 v1 v2 = ret gvs3 ->
  wf_GVs (los,nts) gvs3 (typ_int sz0).
Proof.
  intros S F los nts ps lc gl bop0 sz0 v1 v2 gvs3 Hwflc Hwfv1 Hwfv2 
    Hbop.
  assert (J:=Hwfv1). apply wf_value__wf_typ in J. destruct J as [Hwft Hft].
  unfold BOP in Hbop.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv Hbop.
  remember(getOperandValue (los,nts) v2 lc gl) as R2.
  destruct R2; inv Hbop.
  eapply wf_GVs_intro; eauto.
    unfold getTypeSizeInBits. simpl. eauto.

    intros gv Hin. 
    eapply GVsSig.(lift_op2__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      simpl. eauto.
      intros. erewrite mbop_typsize; eauto.

    eapply GVsSig.(lift_op2__inhabited) in H0; 
      eauto using getOperandValue__inhabited.
    eapply mbop_is_total; eauto.
Qed.

Lemma FBOP__wf_gvs : forall S F los nts ps lc gl fbop0 fp v1 v2 gvs3,
  wf_lc (los,nts) F lc ->
  wf_value S (module_intro los nts ps) F v1 (typ_floatpoint fp) ->
  wf_value S (module_intro los nts ps) F v2 (typ_floatpoint fp) ->
  FBOP (los,nts) lc gl fbop0 fp v1 v2 = ret gvs3 ->
  wf_GVs (los,nts) gvs3 (typ_floatpoint fp).
Proof.
  intros S F los nts ps lc gl fbop0 fp v1 v2 gvs3 Hwflc Hwfv1 Hwfv2 Hfbop.
  unfold FBOP in Hfbop.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv Hfbop.
  remember(getOperandValue (los,nts) v2 lc gl) as R2.
  destruct R2; inv Hfbop.
  assert (J:=Hwfv1). apply wf_value__wf_typ in J. destruct J as [Hwft Hft].
  assert (Hft':=Hft).
  eapply feasible_typ_inv in Hft; eauto.
  destruct Hft as [sz [al [H1 H2]]].
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits. rewrite H1. auto.

    intros gv Hin. 
    eapply GVsSig.(lift_op2__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      simpl. eauto.

      intros x y z ? ? J3. 
      eapply mfbop_typsize in J3; eauto.
      destruct J3 as [sz1 [al1 [J5 J6]]].
      unfold getTypeSizeInBits_and_Alignment in H1.
      unfold getTypeSizeInBits_and_Alignment_for_namedts in *.
      rewrite H1 in J5. inv J5. auto.

    eapply GVsSig.(lift_op2__inhabited) in H0; 
      eauto using getOperandValue__inhabited.
    eapply mfbop_is_total; eauto.
Qed.

Lemma ICMP__wf_gvs : forall S los nts ps F lc gl c t v1 v2 gvs3,
  wf_lc (los,nts) F lc ->
  Typ.isIntOrIntVector t \/ isPointerTyp t ->
  wf_value S (module_intro los nts ps) F v1 t ->
  wf_value S (module_intro los nts ps) F v2 t ->
  ICMP (los,nts) lc gl c t v1 v2 = ret gvs3 ->
  wf_GVs (los,nts) gvs3 (typ_int Size.One).
Proof.
  intros S los nts ps F lc gl c t v1 v2 gvs3 Hwflc Hwft Hwfv1 Hwfv2 Hiop.
  unfold ICMP in Hiop.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv Hiop.
  remember(getOperandValue (los,nts) v2 lc gl) as R2.
  destruct R2; inv Hiop.
  eapply wf_GVs_intro with (sz:=Size.to_nat Size.One); eauto.
    intros gv Hin. 
    eapply GVsSig.(lift_op2__getTypeSizeInBits) with (los:=los)(nts:=nts)(S:=S); 
      eauto.
      apply wf_typ_int. unfold Size.gt. auto.
      simpl. eauto.
      intros. unfold Size.to_nat. erewrite micmp_typsize; eauto.

    apply GVsSig.(lift_op2__inhabited) in H0; 
      eauto using getOperandValue__inhabited.
    eapply micmp_is_total; eauto.
Qed.

Lemma FCMP__wf_gvs : forall S los nts ps F lc gl c fp v1 v2 gvs3,
  wf_lc (los,nts) F lc ->
  wf_fcond c = true  ->
  wf_value S (module_intro los nts ps) F v1 (typ_floatpoint fp) ->
  wf_value S (module_intro los nts ps) F v2 (typ_floatpoint fp) ->
  FCMP (los,nts) lc gl c fp v1 v2 = ret gvs3 ->
  wf_GVs (los,nts) gvs3 (typ_int Size.One).
Proof.
  intros S los nts ps F lc gl c fp v1 v2 gvs3 Hwflc Hc Hwfv1 Hwfv2 Hiop.
  unfold FCMP in Hiop.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv Hiop.
  remember(getOperandValue (los,nts) v2 lc gl) as R2.
  destruct R2; inv Hiop.
  eapply wf_GVs_intro with (sz:=Size.to_nat Size.One); eauto.
    intros gv Hin. 
    eapply GVsSig.(lift_op2__getTypeSizeInBits) with (los:=los)(nts:=nts)(S:=S); 
      eauto.
      apply wf_typ_int. unfold Size.gt. auto.
      simpl. eauto.
      intros. unfold Size.to_nat. erewrite mfcmp_typsize; eauto.

    apply GVsSig.(lift_op2__inhabited) in H0; 
      eauto using getOperandValue__inhabited.
    apply wf_value__wf_typ in Hwfv1. destruct Hwfv1.
    eapply mfcmp_is_total; eauto.
Qed.

Lemma wf_params_spec : forall TD gvs lp, 
  wf_params TD gvs lp -> forall gv, In gv gvs -> GVsSig.(inhabited) gv.
Proof.
  induction gvs; simpl; intros.
    inv H0.

    destruct lp as [|[[]]]; tinv H.
    destruct H as [J1 J2].
    destruct H0 as [H0 | H0]; subst; eauto.
      inv J1; auto.
Qed.

Lemma values2GVs__inhabited : forall S los nts f lc (Hwflc: wf_lc (los,nts) f lc)
  gl Ps idxs vidxs,
  wf_value_list
          (make_list_system_module_fdef_value_typ
             (map_list_sz_value
                (fun (sz_:sz) (value_ : value) =>
                 (S, module_intro los nts Ps, f, value_,
                 typ_int Size.ThirtyTwo)) idxs)) ->
  values2GVs (los,nts) idxs lc gl = Some vidxs ->
  exists vidxs0, vidxs0 @@ vidxs.
Proof.
  induction idxs; simpl; intros vidxs Hwfvs Hv2gvs.
    inv Hv2gvs. exists nil. simpl. auto. 

    remember (getOperandValue (los,nts) v lc gl) as R.
    destruct R; tinv Hv2gvs.
    remember (values2GVs (los,nts) idxs lc gl) as R1.
    destruct R1; inv Hv2gvs.
    symmetry in HeqR1. symmetry in HeqR.
    inv Hwfvs.
    destruct (@IHidxs l0) as [vidxs0 J]; auto.
    eapply getOperandValue__inhabited in HeqR; eauto.
    apply GVsSig.(inhabited_inv) in HeqR.
    destruct HeqR as [gv HeqR].
    exists (gv::vidxs0). simpl. simpl; auto.
Qed.

Lemma GEP__wf_gvs : forall S TD t mp vidxs inbounds0 mp' vidxs0 t' gl lc idxs,
  @values2GVs GVsSig TD idxs lc gl = Some vidxs ->
  wf_GVs TD mp (typ_pointer t) -> vidxs0 @@ vidxs ->
  wf_typ S t' -> feasible_typ TD t' ->
  getGEPTyp idxs t = ret t' ->
  GEP TD t mp vidxs0 inbounds0 = ret mp' ->
  wf_GVs TD mp' t'.
Proof.
  intros S TD t mp vidxs inbounds0 mp' vidxs0 t' gl lc idxs Hvg2 Hwfgv Hin Hwft 
    Hft Hgt' Hget.
  unfold GEP in Hget. inv Hget.
  unfold getGEPTyp in Hgt'.
  destruct idxs; tinv Hgt'.  
  remember (getSubTypFromValueIdxs idxs t) as R4.
  destruct R4; inv Hgt'.
  destruct TD as [los nts].
  apply wf_GVs_intro with (sz:=32%nat); auto.
    intros gv Hin'.
    eapply GVsSig.(lift_op1__getTypeSizeInBits) with (los:=los)(nts:=nts)
      (f:=gep (los, nts) t vidxs0 inbounds0) (g:=mp)
      (t:=typ_pointer (typ_int Size.One))(S:=S); eauto.
      apply wf_typ_pointer; auto.
        apply wf_typ_int. unfold Size.gt. auto.
        unfold isValidElementTyp, isValidElementTypB. auto.
      simpl. eauto.

      intros x y ? J3.
      unfold gep, LLVMgv.GEP in J3.
      assert(gundef (los, nts) (typ_pointer t0) = ret y ->
             sizeGenericValue y = nat_of_Z (ZRdiv (Z_of_nat 32) 8)) as G.
        intro W .
        eapply GVsSig.(gv2gvs__getTypeSizeInBits) with (los:=los)(nts:=nts)
          (gv:=y); eauto.
          simpl. eauto.

          symmetry in W. inv Hft. 
          eapply gundef__getTypeSizeInBits in W; eauto.
          destruct W as [sz1 [al1 [J1' J2']]].
          simpl in J1'. inv J1'. simpl in J2'. auto.

          apply GVsSig.(instantiate_gv__gv2gvs).

      destruct (GV2ptr (los, nts) (getPointerSize (los, nts)) x); eauto.
      destruct (GVs2Nats (los, nts) vidxs0); eauto.
      destruct (mgep (los, nts) t v0 l0); eauto.
        inv J3.
        unfold ptr2GV, val2GV. simpl. auto.

    inv Hwfgv.
    eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
    unfold gep. intro. apply GEP_is_total; auto.
Qed.

Lemma CAST__wf_gvs : forall ifs s f b los nts ps lc gl cop0 t1 v1 t2 gvs2 id5
  (Hwfg : wf_global (los, nts) s gl),
  wf_lc (los,nts) f lc ->
  wf_cast ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_cast id5 cop0 t1 v1 t2)) ->
  CAST (los,nts) lc gl cop0 t1 v1 t2 = ret gvs2 ->
  wf_GVs (los,nts) gvs2 t2.
Proof.
  intros ifs s f b los nts ps lc gl cop0 t1 v1 t2 gvs2 id5 Hwfg Hwflc Hwfc Hcast.
  unfold CAST in Hcast.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; inv Hcast.
  symmetry in HeqR1.
  inv Hwfc.
    inv H14.
    eapply getOperandValue__wf_gvs in HeqR1; eauto.
    eapply wf_GVs_intro with (sz:=sz5); eauto.
      intros gv Hin.
      eapply GVsSig.(lift_op1__getTypeSizeInBits)with (los:=los)(nts:=nts);eauto.
        simpl. eauto.
        
        intros x y ? J2.
        symmetry in J2.
        eapply gundef__getTypeSizeInBits in J2; eauto.
        destruct J2 as [sz1 [al1 [J4 J5]]].
        simpl in J4. inv J4. auto.

      inv HeqR1.
      eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
        intro. apply gundef__total; auto.

    inv H14.
    eapply getOperandValue__wf_gvs in HeqR1; eauto.
    eapply wf_GVs_intro with (sz:=32%nat); eauto.
      intros gv Hin.
      eapply GVsSig.(lift_op1__getTypeSizeInBits)with (los:=los)(nts:=nts);eauto.
        simpl. eauto.
        
        intros x y ? J2.
        symmetry in J2.
        eapply gundef__getTypeSizeInBits in J2; eauto.
        destruct J2 as [sz1 [al1 [J4 J5]]].
        simpl in J4. inv J4. auto.

      inv HeqR1.
      eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
        intro. apply gundef__total; auto.
       
    eapply getOperandValue__wf_gvs in HeqR1; eauto.
    eapply wf_GVs_intro with (sz:=32%nat); eauto.
      intros gv Hin. 
      eapply GVsSig.(lift_op1__getTypeSizeInBits)with(los:=los)(nts:=nts) in Hin;
        eauto.
        simpl. eauto.
        intros x y Hin' Heq. inv Heq.
        inv HeqR1.
        unfold getTypeSizeInBits in H. inv H. simpl in *. eauto.

      inv HeqR1.
      eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
        unfold mcast, mbitcast. eauto.
Qed.

Lemma TRUNC__wf_gvs : forall  ifs s f b los nts ps lc gl top0 t1 v1 t2 gvs2 id5
  (Hwfg : wf_global (los, nts) s gl),
  wf_lc (los,nts) f lc ->
  wf_trunc ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_trunc id5 top0 t1 v1 t2)) ->
  TRUNC (los,nts) lc gl top0 t1 v1 t2 = ret gvs2 ->
  wf_GVs (los,nts) gvs2 t2.
Proof.
  intros ifs s f b los nts ps lc gl top0 t1 v1 t2 gvs2 id5 Hwfg Hwflc Hwfc 
    Htrunc.
  unfold TRUNC in Htrunc.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; inv Htrunc.
  assert (J:=Hwfc).
  apply wf_trunc__wf_typ in J.
  destruct J as [J1 J2]. inv J2.
  assert (H':=H).
  apply feasible_typ_inv' in H.
  destruct H as [sz [al [J2 J3]]].
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits.
    rewrite J2. auto.

    intros gv Hin. 
    eapply GVsSig.(lift_op1__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      intros x y Hin' J2'.   
      eapply mtrunc_typsize in J2'; eauto.
      destruct J2' as [sz' [al' [J2' J4']]].
      unfold getTypeSizeInBits_and_Alignment in J2.
      unfold layouts, namedts in J2.
      rewrite J2 in J2'. inv J2'. auto.

    eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
      eapply mtrunc_is_total; eauto.

      symmetry in HeqR1.
      eapply getOperandValue__wf_gvs in HeqR1; eauto using wf_trunc__wf_value.
      inv HeqR1; auto.    
Qed.

Lemma EXT__wf_gvs : forall  ifs s f b los nts ps lc gl eop0 t1 v1 t2 gvs2 id5
  (Hwfg : wf_global (los, nts) s gl),
  wf_lc (los,nts) f lc ->
  wf_ext ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_ext id5 eop0 t1 v1 t2)) ->
  EXT (los,nts) lc gl eop0 t1 v1 t2 = ret gvs2 ->
  wf_GVs (los,nts) gvs2 t2.
Proof.
  intros ifs s f b los nts ps lc gl eop0 t1 v1 t2 gvs2 id5 Hwfg Hwflc Hwfc Hext.
  unfold EXT in Hext.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; inv Hext.
  assert (J:=Hwfc).
  apply wf_ext__wf_typ in J.
  destruct J as [J1 J2]. inv J2.
  assert (H':=H).
  apply feasible_typ_inv' in H.
  destruct H as [sz [al [J2 J3]]].
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits.
    rewrite J2. auto.

    intros gv Hin. 
    eapply GVsSig.(lift_op1__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      intros x y Hin' J2'.   
      eapply mext_typsize in J2'; eauto.
      destruct J2' as [sz' [al' [J2' J4']]].
      unfold getTypeSizeInBits_and_Alignment in J2.
      unfold layouts, namedts in J2.
      rewrite J2 in J2'. inv J2'. auto.

    eapply GVsSig.(lift_op1__inhabited) in H0; eauto.
      eapply mext_is_total; eauto.

      symmetry in HeqR1.
      eapply getOperandValue__wf_gvs in HeqR1; eauto using wf_ext__wf_value.
      inv HeqR1; auto.    
Qed.

Lemma insertGenericValue__wf_gvs : forall S los nts t1 t2 gvs1 gvs2 cidxs gvs',
  wf_GVs (los, nts) gvs1 t1 ->
  wf_GVs (los, nts) gvs2 t2 ->
  insertGenericValue (los, nts) t1 gvs1 cidxs t2 gvs2 = ret gvs' ->
  getSubTypFromConstIdxs cidxs t1 = ret t2 ->
  feasible_typ (los, nts) t1 ->
  wf_typ S t1 ->
  feasible_typ (los, nts) t2 ->
  wf_typ S t2 ->
  wf_GVs (los, nts) gvs' t1.
Proof.  
  intros S los nts t1 t2 gvs1 gvs2 cidxs gvs' Hwfgv1 Hwfgv2 Hinsert e0 Hft Hwft 
    Hft2 Hwft2.
  inv Hwfgv1. inv Hwfgv2. 
  assert (H0':=Hft).
  inv H0'. 
  assert (H5':=H5).
  apply feasible_typ_inv' in H5.
  destruct H5 as [sz [al [J2 J3]]].

  assert (H2':=Hft2).
  inv H2'. 
  assert (H6':=H5).
  apply feasible_typ_inv' in H5.
  destruct H5 as [sz' [al' [J2' J3']]].
  unfold insertGenericValue in Hinsert.
  remember (intConsts2Nats (los, nts) cidxs) as R1.
  destruct R1; tinv Hinsert.
  remember (mgetoffset (los, nts) t1 l0) as R2.
  destruct R2 as [[]|]; inv Hinsert.
  eapply getSubTypFromConstIdxs__mgetoffset in e0; eauto.
  subst.
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits.
    rewrite J2. auto.

    unfold getTypeSizeInBits_and_Alignment, 
           getTypeSizeInBits_and_Alignment_for_namedts in J2, J2'.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment, 
           getTypeSizeInBits_and_Alignment_for_namedts in H, H2.
    rewrite J2 in H. inv H. 
    rewrite J2' in H2. inv H2. 
    intros gv0 Hin.
    eapply GVsSig.(lift_op2__getTypeSizeInBits)with (los:=los)(nts:=nts)(t:=t1); 
      eauto.
      intros x y z0 J4 J5 J6.
      apply H0 in J4. apply H3 in J5.
      unfold mset' in J6.
      remember (mset (los, nts) x z t2 y) as R4.
      destruct R4 as [gv'|]; inv J6.
        eapply mset_typsize in HeqR4; eauto.
        rewrite <- HeqR4. auto.

        symmetry in H2.
        eapply gundef__getTypeSizeInBits in H2; eauto.
        destruct H2 as [sz2 [al2 [J7' J8']]].
        unfold layouts, namedts in J2.
        rewrite J2 in J7'. inv J7'. auto.

    eapply GVsSig.(lift_op2__inhabited) in H6; eauto.
      eapply mset'_is_total; eauto.
Qed.

Lemma extractGenericValue__wf_gvs : forall S los nts t1 gv1 const_list gv typ'
  (Hwfg : wf_GVs (los, nts) gv1 t1)
  (HeqR3 : extractGenericValue (los, nts) t1 gv1 const_list = ret gv)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ')
  (H0 : feasible_typ (los, nts) typ')
  (w1 : wf_typ S typ'),
  wf_GVs (los, nts) gv typ'.
Proof.  
  intros.
  inv Hwfg. assert (H0':=H0).
  inv H0. assert (H3':=H3).
  apply feasible_typ_inv' in H3.
  destruct H3 as [sz [al [J2 J3]]].
  unfold extractGenericValue in HeqR3.
  remember (intConsts2Nats (los, nts) const_list) as R1.
  destruct R1; tinv HeqR3.
  remember (mgetoffset (los, nts) t1 l0) as R2.
  destruct R2 as [[]|]; inv HeqR3.
  eapply getSubTypFromConstIdxs__mgetoffset in e0; eauto.
  subst.
  eapply wf_GVs_intro with (sz:=sz); eauto.
    unfold getTypeSizeInBits.
    rewrite J2. auto.

    intros gv0 Hin.
    eapply GVsSig.(lift_op1__getTypeSizeInBits) with (los:=los)(nts:=nts); eauto.
      intros x y J4 J5.
      unfold mget' in J5.
      unfold getTypeSizeInBits_and_Alignment, 
             getTypeSizeInBits_and_Alignment_for_namedts in J2.
      remember (mget (los, nts) x z typ') as R4.
      destruct R4 as [gv'|]; inv J5.
        eapply mget_typsize in HeqR4; eauto.
          destruct HeqR4 as [sz1 [al1 [J7 J8]]].
          unfold layouts, namedts in J2.
          rewrite J2 in J7. inv J7. auto.

        symmetry in H4.
        eapply gundef__getTypeSizeInBits in H4; eauto.
        destruct H4 as [sz1 [al1 [J7 J8]]].
        rewrite J2 in J7. inv J7. auto.

    eapply GVsSig.(lift_op1__inhabited) in H3; eauto.
      eapply mget'_is_total; eauto.
Qed.
 
(*********************************************)
(** * Preservation *)

Lemma preservation_dbCall_case : forall fid l' fa rt la va lb gvs los
  nts ifs s lc Ps lp
  (Hinhs : forall gv, In gv gvs -> GVsSig.(inhabited) gv)
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hwfp : wf_params (los, nts) gvs lp)
  (Hinit : initLocals (los,nts) la gvs = Some lc),
   match
     fold_left
       (inscope_of_block (fdef_intro (fheader_intro fa rt fid la va) lb) l')
       nil (ret getArgsIDs la)
   with
   | ret ids0 =>
       wf_defs (los,nts) (fdef_intro (fheader_intro fa rt fid la va) lb) lc ids0
   | merror => False
   end.
Proof.
  intros.
  assert (incl nil (bound_blocks lb)) as J.
    intros x J. inv J.    
  apply fold_left__bound_blocks with (fh:=fheader_intro fa rt fid la va)(l0:=l')
    (init:=getArgsIDs la) in J.
  destruct J as [r J]. unfold l in *.
  rewrite J.       
  apply fold_left__spec in J.
  destruct J as [_ [_ J]].
  apply wf_defs_intro.
  intros id1 Hin.
  apply J in Hin.
  destruct Hin as [Hin | Hin].    
    assert (J1:=Hin).
    apply InArgsIDs_lookupTypViaIDFromFdef with (t0:=rt)(id0:=fid)(la0:=la)
      (va0:=va)(bs:=lb)(fa:=fa) in J1.
    destruct J1 as [t J1].
    exists t. rewrite J1.
    eapply initLocals_spec' with (gvs:=gvs) in Hin; eauto.
    destruct Hin as [gv [Hin Hinh]].
    exists gv. split; auto.
  
    destruct Hin as [b1 [l1 [Hin _]]].
    apply ListSet.set_diff_elim1 in Hin. inv Hin.
Qed.

Definition wf_ExecutionContext TD (ps:list product) (ec:ExecutionContext) : Prop 
  :=
let '(mkEC f b cs tmn lc als) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
InProductsB (product_fdef f) ps = true /\
wf_lc TD f lc /\
match cs with
| nil => 
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs TD f lc ids
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs TD f lc ids
    | None => False
    end
end /\
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Definition wf_call (ec:@ExecutionContext GVsSig) (ecs:@ECStack GVsSig) : Prop :=
let '(mkEC f _ _ _ _ _) := ec in
forall b, blockInFdefB b f ->
let '(block_intro _ _ _ tmn) := b in
match tmn with
| insn_return _ _ _ | insn_return_void _ =>
    match ecs with
    | nil => True
    | mkEC f' b' (insn_call _ _ _ _ _ _ ::_) tmn' lc' als'::ecs' 
        => True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack TD (ps:list product) (ecs:ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' => 
    wf_ExecutionContext TD ps ec /\ wf_ECStack TD ps ecs' /\ wf_call ec ecs'
end.

Definition wf_State (cfg:Config) (S:State) : Prop :=
let '(mkCfg s (los, nts) ps gl _ ) := cfg in
let '(mkState ecs _) := S in
wf_global (los,nts) s gl /\
wf_system nil s /\
moduleInSystemB (module_intro los nts ps) s = true /\
ecs <> nil /\
wf_ECStack (los,nts) ps ecs.

Lemma wf_State__inv : forall S los nts Ps F B c cs tmn lc als EC gl fs Mem0,
  wf_State (mkCfg S (los,nts) Ps gl fs) 
    (mkState ((mkEC F B (c::cs) tmn lc als)::EC) Mem0) ->
  wf_global (los, nts) S gl /\
  wf_lc (los,nts) F lc /\ 
  wf_insn nil S (module_intro los nts Ps) F B (insn_cmd c).
Proof.
  intros.
  destruct H as 
    [Hwfg [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
     [HwfEC HwfCall]]]]]
    ]; subst.
  split; auto. 
  split; auto. 
    eapply wf_system__wf_cmd; eauto using in_middle.
Qed.  

Lemma preservation_cmd_updated_case : forall
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (lc : GVsMap)
  (gl : GVMap)
  (fs : GVMap)
  (gv3 : GVs)
  (EC : list ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  t0
  (Htyp : Some t0 = getCmdTyp c0)
  (Hwfgv : wf_GVs (los,nts) gv3 t0)
  (HwfS1 : wf_State {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |}
            {|
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Mem := Mem0 |}),
   wf_State {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     Globals := gl;
     FunTable := fs |}
     {|
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := updateAddAL GVs lc id0 gv3;
            Allocas := als |} :: EC;
     Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]]
    ]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  assert (uniqFdef F) as HuniqF.
    eapply wf_system__uniqFdef; eauto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      intros; congruence.
      Case "wflc".
      eapply wf_lc_updateAddAL; eauto.
        eapply uniqF__lookupTypViaIDFromFdef; eauto using in_middle.

      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
       subst.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs3')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.
        
      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma preservation_cmd_non_updated_case : forall
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (lc : GVsMap)
  (gl : GVMap)
  (fs : GVMap)
  (EC : list ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None)
  (HwfS1 : wf_State {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |}
            {|
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Mem := Mem0 |}),
   wf_State {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     Globals := gl;
     FunTable := fs |}
     {|
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := lc;
            Allocas := als |} :: EC;
     Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]]
    ]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      Case "0".
      intros. congruence.
      Case "1".
      destruct cs; simpl_env in *.
      SCase "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs3')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq; eauto.
        
      SCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq ; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Tactic Notation "sInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "sReturn" | c "sReturnVoid" | c "sBranch" | c "sBranch_uncond" |
    c "sBop" | c "sFBop" | c "sExtractValue" | c "sInsertValue" |
    c "sMalloc" | c "sFree" |
    c "sAlloca" | c "sLoad" | c "sStore" | c "sGEP" |
    c "sTrunc" | c "sExt" | 
    c "sCast" | 
    c "sIcmp" | c "sFcmp" | c "sSelect" |  
    c "sCall" | c "sExCall" ].

Lemma preservation : forall cfg S1 S2 tr,
  sInsn cfg S1 S2 tr -> wf_State cfg S1 -> wf_State cfg S2.
Proof.
  intros cfg S1 S2 tr HsInsn HwfS1.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts].
Focus.
Case "sReturn".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split. intros; congruence.
    split; auto. 
    split; auto.
    split; auto.
    split; auto. 

    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
    assert (In (insn_call i0 n c t v p) 
      (cs2'++[insn_call i0 n c t v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c t v p) in Hwfc; eauto.
    assert (uniqFdef F') as HuniqF.
      eapply wf_system__uniqFdef; eauto.

    split.
      eapply wf_system__wf_tmn in HBinF1; eauto.
      inv HBinF1.
      eapply returnUpdateLocals__wf_lc with (Result:=Result)(lc:=lc); eauto.
    split.
    SSCase "1.1".
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc (insn_call i0 n c t v p)) (getCmdsLocs cs2')) 
          as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          destruct t; tinv H1.
          remember (GVsSig.(lift_op1) (fit_gv (los, nts) t) g t) as R2.
          destruct R2; inv H1.
          inv Hwfc. inv H16. inv H7. inv H18.
          eapply wf_defs_updateAddAL with (t1:=typ1);
            eauto using getOperandValue__inhabited.
            eapply uniqF__lookupTypViaIDFromFdef; eauto.
            eapply lift_fit_gv__wf_gvs; eauto.
              eapply wf_system__wf_tmn in HBinF1; eauto.
              inv HBinF1.
              eapply getOperandValue__wf_gvs with (f:=F)(v:=Result); eauto.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [insn_call i0 n c t v p] ++ [c0] ++ 
          cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          destruct t; tinv H1.
          remember (GVsSig.(lift_op1) (fit_gv (los, nts) t) g t) as R2.
          destruct R2; inv H1.
          inv Hwfc. inv H16. inv H7. inv H18.
          eapply wf_defs_updateAddAL with (t1:=typ1); 
            eauto using getOperandValue__inhabited.
            eapply uniqF__lookupTypViaIDFromFdef; eauto.
            eapply lift_fit_gv__wf_gvs; eauto.
              eapply wf_system__wf_tmn in HBinF1; eauto.
              inv HBinF1.
              eapply getOperandValue__wf_gvs with (f:=F)(v:=Result); eauto.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto. 
    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[insn_call i0 n c t v p]).   
      simpl_env. auto.
Unfocus.

Focus.
Case "sReturnVoid".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split. intros; congruence.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.   
    SSCase "1.1".
      apply HwfCall' in HBinF1. simpl in HBinF1.
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [c'] ++ [c] ++ cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnodup H1.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 

    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "sBranch".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  split. intros; congruence.
  split; auto.         
  SCase "1".
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    split.
      clear - Hreach1 H1 HBinF1 HFinPs1 HmInS HwfSystem HuniqF HwfF.
      unfold isReachableFromEntry in *.
      destruct (isGVZero (los, nts) c).
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; eauto.
        destruct H1 as [H1 _].
        eapply reachable_successors; eauto.
          simpl. auto.
      
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; eauto.
        destruct H1 as [H1 _].
        eapply reachable_successors; eauto.
          simpl. auto.
    split. 
      clear - H1 HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      destruct (isGVZero (los, nts) c).
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; auto.
          destruct H1; auto.
        symmetry in H1.
        apply lookupBlockViaLabelFromFdef_inv in H1; auto.
          destruct H1; auto.
    split; auto.
    split.
      destruct (isGVZero (los, nts) c);
        eapply wf_lc_br_aux in H1; eauto.
    split.
      clear - H0 HeqR1 H1 Hinscope1 H2 HwfSystem HBinF1 HwfF HuniqF Hwflc1 Hwfg.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "sBranch_uncond".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
     [HwfEC HwfCall]]]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  split. intros; congruence.
  SCase "1".
    split; auto.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    split.
      clear - Hreach1 H HBinF1 HFinPs1 HmInS HwfSystem HuniqF HwfF.
      unfold isReachableFromEntry in *.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
      destruct H as [H _].
      eapply reachable_successors; eauto.
        simpl. auto.
    split.
      clear - H HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
        destruct H; auto.
    split; auto.
    split. eapply wf_lc_br_aux in H0; eauto.
    split.
      clear - H0 HeqR1 Hinscope1 H HwfSystem HBinF1 HwfF HuniqF Hwfg Hwflc1.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "sBop". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply BOP__wf_gvs with (v1:=v1); eauto.

Case "sFBop". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply FBOP__wf_gvs with (v1:=v1); eauto.

Case "sExtractValue".
  assert (J':=HwfS1).
  destruct J' as 
      [Hwfg [HwfSystem [HmInS [Hnonempty [
        [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
        [HwfEC HwfCall]]]]]
      ]; subst.
  eapply wf_system__wf_cmd with (c:=insn_extractvalue id0 t v idxs) in HBinF1; 
    eauto using in_middle.
  inv HBinF1.
  assert (exists t0, getSubTypFromConstIdxs idxs t = Some t0) as J.
    destruct H15 as [idxs0 [o [J1 J2]]].
    symmetry in J2.
    eapply mgetoffset__getSubTypFromConstIdxs in J2; eauto.
  destruct J as [t0 J].
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    destruct H15 as [idxs0 [o [J3 J4]]].
    symmetry in J4.
    eapply mgetoffset__getSubTypFromConstIdxs in J4; eauto.
    rewrite J in J4. inv J4.
    eapply getOperandValue__wf_gvs in H; eauto.
    eapply extractGenericValue__wf_gvs; eauto. 

Case "sInsertValue". 
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    destruct H19 as [idxs0 [o [J3 J4]]].
    symmetry in J4.
    eapply mgetoffset__getSubTypFromConstIdxs in J4; eauto.
    eapply getOperandValue__wf_gvs in H; eauto.
    eapply getOperandValue__wf_gvs in H0; eauto.
    assert (J1:=H13). apply wf_value__wf_typ in H13. destruct H13.
    assert (J2:=H16). apply wf_value__wf_typ in H16. destruct H16.
    eapply insertGenericValue__wf_gvs in H1; eauto.

Case "sMalloc". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  unfold blk2GV, ptr2GV, val2GV. simpl.
  eapply wf_GVs_intro; eauto.  
    unfold getTypeSizeInBits. simpl. eauto.
    intros gv Hin. 
    apply GVsSig.(none_undef2gvs_inv) in Hin; subst; auto.
      intros mc. congruence.
    apply GVsSig.(gv2gvs__inhabited). 

Case "sFree". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "sAlloca". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  destruct HwfS1 as 
      [Hwfg [HwfSystem [HmInS [Hnonempty [
        [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
        [HwfEC HwfCall]]]]]
      ]; subst.
  repeat (split; try solve [intros; congruence | eauto]). 

  unfold blk2GV, ptr2GV, val2GV. simpl.
  eapply wf_GVs_intro; eauto.  
    unfold getTypeSizeInBits. simpl. eauto.
    intros gv Hin. 
    apply GVsSig.(none_undef2gvs_inv) in Hin; subst; auto.
      intros mc. congruence.
    apply GVsSig.(gv2gvs__inhabited). 

Case "sLoad".  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  apply wf_value__wf_typ in H11. destruct H11.
  inv H2. inv H3. inv H14.
  eapply mload__getTypeSizeInBits in H1; eauto.
    destruct H1 as [sz [J1 J2]]. 
    eapply wf_GVs_intro; eauto.  
      unfold getTypeSizeInBits in J1.
      remember (getTypeSizeInBits_and_Alignment (los, nts) true t) as R.
      destruct R as [[]|]; inv J1.
      unfold getTypeSizeInBits_and_Alignment in HeqR.
      eapply GVsSig.(gv2gvs__getTypeSizeInBits); eauto.

      apply GVsSig.(gv2gvs__inhabited).

Case "sStore". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "sGEP". 
  assert (J:=HwfS1).
  destruct J as 
    [Hwfg [HwfSystem [HmInS [Hnonempty [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
         [HwfEC HwfCall]]]]]
    ]; subst.
  eapply wf_system__wf_cmd with (c:=insn_gep id0 inbounds0 t v idxs) in HBinF1;
    eauto using in_middle.
  inv HBinF1; eauto.
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    eapply getOperandValue__wf_gvs in H; eauto.
    assert (H0':=H0).
    eapply values2GVs__inhabited in H0; eauto.
    destruct H0 as [vidxs0 H0].
    eapply GEP__wf_gvs in H1; eauto. 

Case "sTrunc". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply TRUNC__wf_gvs; eauto.

Case "sExt". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply EXT__wf_gvs; eauto.

Case "sCast". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply CAST__wf_gvs; eauto.

Case "sIcmp". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply ICMP__wf_gvs with (v1:=v1); eauto.

Case "sFcmp". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  eapply FCMP__wf_gvs with (v1:=v1); eauto.

Case "sSelect".
  assert (J:=HwfS1).
  apply wf_State__inv in J.
  destruct J as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  eapply getOperandValue__wf_gvs in H0; eauto.
  eapply getOperandValue__wf_gvs in H1; eauto.
  destruct (isGVZero (los, nts) c); 
    eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.

Focus.
Case "sCall".
  destruct HwfS1 as [Hwfg [HwfSys [HmInS [Hnonempty [
    [Hreach [HBinF [HFinPs [Hwflc [Hinscope [l1 [ps [cs'' Heq]]]]]]]]
    [HwfECs HwfCall]]]]]]; subst.
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  split; auto.
  split; auto.
  split; auto.
  split. intros; congruence.
  split; auto.
  SCase "1".     
    assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) 
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    assert (wf_params (los,nts) gvs lp) as JJ.
      eapply wf_system__wf_cmd in HBinF; eauto using in_middle.
      inv HBinF.
      eapply params2GVs_wf_gvs; eauto.

    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
     apply entryBlockInFdef in H2; auto.
    split; auto.
    split.
     eapply initLocals__wf_lc; eauto.
    split.
     assert (ps'=nil) as EQ.
       eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
     subst.
     apply dom_entrypoint in H2. 
     destruct cs'.
       unfold inscope_of_tmn.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R. simpl in H2. subst.
       eapply preservation_dbCall_case; eauto using wf_params_spec.

       unfold inscope_of_cmd, inscope_of_id.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R. simpl. simpl in H2. subst.
       destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
         try solve [contradict n; auto]. 
       eapply preservation_dbCall_case; eauto using wf_params_spec.

    exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    repeat (split; auto). eauto.
  SCase "3".
    simpl. intros b HbInBs. destruct b.
    destruct t; auto.

Unfocus.

Case "sExCall". 
  unfold exCallUpdateLocals in H2.
  destruct noret0.
    inv H5.
    eapply preservation_cmd_non_updated_case in HwfS1; eauto.

    assert (exists t0, getCmdTyp (insn_call rid false ca ft fv lp) = Some t0)
      as J.
      destruct HwfS1 as 
       [Hwfg [HwfSystem [HmInS [Hnonempty [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
         [HwfEC HwfCall]]]]]
       ]; subst.
      eapply wf_system__wf_cmd with (c:=insn_call rid false ca ft fv lp) 
        in HBinF1; eauto.
      simpl.
      inv HBinF1; eauto. 
      apply in_or_app; simpl; auto.
    destruct J as [t0 J].
    destruct oresult; inv H5.
    destruct ft; tinv H7.
    remember (fit_gv (los, nts) ft g) as R.
    destruct R; inv H7.
    eapply preservation_cmd_updated_case with (t0:=t0) in HwfS1; simpl; eauto.
      inv J.
      apply wf_State__inv in HwfS1.
      destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
      inv Hwfc. inv H20. inv H11. inv H22.
      eapply fit_gv_gv2gvs__wf_gvs_aux; eauto.
Qed.

(*********************************************)
(** * Progress *)

Lemma state_tmn_typing : forall TD ifs s m f l1 ps1 cs1 tmn1 defs id1 lc,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn ifs s m f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs TD f lc defs ->
  wf_fdef ifs s m f -> uniqFdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  exists t, exists gv, 
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_GVs TD gv t.
Proof.
  intros TD ifs s m f l1 ps1 cs1 tmn1 defs id1 lc Hreach HwfInstr Hinscope 
    HwfDefs HwfF HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr; 
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  
 
  assert (
     In (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id1)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id_))
              id_list)))
    ) as G.
    rewrite H5 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=block_intro l1 ps1 cs1 tmn1)
    (insn1:=insn_terminator tmn1)(id1:=id1) in H6; auto.

  inv H6.
  clear - H11 HwfDefs Hinscope H0 Hreach H9 HuniqF H HwfF.
  eapply wf_defs_elim; eauto.
    unfold inscope_of_tmn in Hinscope.
    destruct f. destruct f.
    remember ((dom_analyze (fdef_intro (fheader_intro f t i0 a v) b)) !! l1) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H11 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      destruct J' as [J' _].
      destruct J' as [[cs2 [c1 [cs3 [J1 J2]]]] | [ps2 [p1 [ps3 [J1 J2]]]]]; 
        subst.
        rewrite getCmdsIDs_app. simpl. rewrite J2.
        apply in_or_app. right.
        apply in_or_app. left.
        apply in_or_app. right. simpl. auto.
    
        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
     unfold blockStrictDominates in J'.
     rewrite <- HeqR in J'.
     destruct block'.
     assert (In l0 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as J.       
       simpl in Hreach.
       apply insnInFdefBlockB__blockInFdefB in H.
       eapply sdom_isnt_refl with (l':=l0) in Hreach; eauto.
         apply ListSet.set_diff_intro; auto.
           simpl. intro J. destruct J as [J | J]; auto.
         rewrite <- HeqR. simpl. auto.
     destruct Hinscope as [_ [Hinscope _]].
     assert (
       lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t i0 a v) b) l0 =
       ret block_intro l0 p c t0) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l0 p c t0) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma state_cmd_typing : forall TD ifs s m f b c defs id1 lc,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn ifs s m f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs TD f lc defs ->
  wf_fdef ifs s m f -> uniqFdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  exists t, exists gv, 
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_GVs TD gv t.
Proof.
  intros TD ifs s m f b c defs id1 lc Hnodup Hreach HwfInstr Hinscope HwfDefs 
    HwfF HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  

  assert (
     In (f, b, insn_cmd c, id1)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, b, insn_cmd c, id_))
              id_list)))
    ) as G.
    rewrite H5 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=b)(insn1:=insn_cmd c)(id1:=id1) 
    in H6; auto.

  inv H6. 
  eapply wf_defs_elim; eauto.
    unfold inscope_of_cmd, inscope_of_id in Hinscope.
    destruct b. destruct f. destruct f.
    remember ((dom_analyze (fdef_intro (fheader_intro f t0 i0 a v) b)) !! l0) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H11 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      simpl in J'.
      destruct J' as [[ps2 [p1 [ps3 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]];
        subst.

        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
        clear - J2 Hnodup.
        apply in_or_app. right.
        apply in_or_app. left. 
          simpl in Hnodup. apply NoDup_inv in Hnodup.
          destruct Hnodup as [_ Hnodup].
          apply NoDup_inv in Hnodup.
          destruct Hnodup as [Hnodup _].
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3).
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3) in Hnodup.
          apply NoDup__In_cmds_dominates_cmd; auto.
            rewrite getCmdsIDs_app.
            apply in_or_app. right. simpl. rewrite J2. simpl. auto.
    
     clear H0 HwfDefs.
     unfold blockStrictDominates in J'.
     rewrite <- HeqR in J'.
     destruct block'.
     assert (In l1 (ListSet.set_diff eq_atom_dec bs_contents [l0])) as J.       
       simpl in Hreach.
       apply insnInFdefBlockB__blockInFdefB in H.
       eapply sdom_isnt_refl with (l':=l1) in Hreach; eauto.
         apply ListSet.set_diff_intro; auto.
           simpl. intro J. destruct J as [J | J]; auto.
         rewrite <- HeqR. simpl. auto.

     destruct Hinscope as [_ [Hinscope _]].
     assert (
       lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t0 i0 a v) b) l1
         = ret block_intro l1 p0 c1 t1) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l1 p0 c1 t1) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma const2GV_isnt_stuck : forall TD S gl c t,
  wf_const S TD c t ->
  feasible_typ TD t ->
  wf_global TD S gl ->
  exists gv, @const2GV GVsSig TD gl c = Some gv.
Proof.
  intros.
  destruct const2GV_isnt_stuck_mutind as [J _].
  unfold const2GV_isnt_stuck_Prop in J.
  unfold const2GV.
  inv H0.
  eapply J in H; eauto.
  destruct H as [gv H].
  rewrite H. eauto.
Qed.

Lemma getOperandValue_inCmdOps_isnt_stuck : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : wf_defs (los,nts) f lc l0)
  (v : value)
  (Hvincs : valueInCmdOperands v c),
  exists gv : GVs, 
    getOperandValue (los, nts) v lc gl = ret gv.
Proof.
  intros.
  destruct v as [vid | vc]; simpl.
    assert (exists t, exists gv, 
                lookupTypViaIDFromFdef f vid = munit t /\
                lookupAL _ lc vid = Some gv /\ 
                wf_GVs (los,nts) gv t) as Hlkup.
      eapply state_cmd_typing; eauto. 
      eapply wf_system__uniq_block; eauto.
      eapply wf_system__wf_cmd; eauto using In_middle.
      eapply wf_system__wf_fdef; eauto.
      eapply wf_system__uniqFdef; eauto.
      apply valueInCmdOperands__InOps; auto.
    destruct Hlkup as [gt [gv [Hlktyp [Hlkup Hwfgv]]]].
    simpl. rewrite Hlkup. eauto.

    assert (In c (cs1++c::cs)) as H. 
      apply in_or_app. simpl. auto.
    eapply wf_system__wf_cmd with (c:=c) in HbInF; eauto.
    eapply wf_cmd__wf_value with (v:=value_const vc) in HbInF; eauto.
    destruct HbInF as [t Hwfc].
    inv Hwfc.
    eapply const2GV_isnt_stuck with (S:=s)(t:=t); eauto.
Qed.

Lemma getOperandValue_inTmnOperans_isnt_stuck : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (Hinscope : wf_defs (los,nts) f lc l0)
  (v : value)
  (Hvincs : valueInTmnOperands v tmn),
  exists gv : GVs, getOperandValue (los, nts) v lc gl = ret gv.
Proof.
  intros.
  destruct v as [vid | vc].
    assert (HwfInstr:=HbInF).
    eapply wf_system__wf_tmn in HwfInstr; eauto.
    assert (exists t, exists gv, 
      lookupTypViaIDFromFdef f vid = munit t /\
      lookupAL _ lc vid = Some gv /\ 
      wf_GVs (los,nts) gv t) as Hlkup.
      eapply state_tmn_typing; eauto. 
      eapply wf_system__wf_fdef; eauto.
      eapply wf_system__uniqFdef; eauto.
      apply valueInTmnOperands__InOps; auto.
    destruct Hlkup as [gt [gv [Hlktyp [Hlkup Hwfgv]]]].
    simpl.
    rewrite Hlkup. eauto.

    eapply wf_system__wf_tmn in HbInF; eauto.
    eapply wf_tmn__wf_value with (v:=value_const vc) in HbInF; eauto.
    destruct HbInF as [ct Hwfc].
    inv Hwfc.
    eapply const2GV_isnt_stuck with (S:=s)(t:=ct); eauto.
Qed.

Lemma values2GVs_isnt_stuck : forall
  l22
  (s : system)
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  (i1 : inbounds)
  (t : typ)
  (v : value)
  (l2 : list_sz_value)
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn)
           (insn_gep i0 i1 t v l2))
  (Hinscope : wf_defs (los,nts) f lc l0)
  (Hex : exists l21, l2 = app_list_sz_value l21 l22),
  exists vidxs, values2GVs (los, nts) l22 lc gl = Some vidxs.
Proof.
  induction l22; intros; simpl; eauto.
    destruct Hex as [l21 Hex]; subst.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInListValue. right. 
        apply in_app_list_value_right; simpl; auto.

    destruct J as [gv J].
    rewrite J.         
    eapply IHl22 in HbInF; eauto.  
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF. eauto.

      exists (app_list_sz_value l21 (Cons_list_sz_value s v Nil_list_sz_value)).
        rewrite cons_eq_app_list_value.
        rewrite cons_eq_app_list_value.
        apply app_list_value_assoc.
Qed.

Lemma wf_phinodes__getIncomingValuesForBlockFromPHINodes : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  l0
  (lc : GVsMap)
  (gl : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1
  (Hwfg : wf_global (los,nts) s gl)
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs (los,nts) f lc t)
  (HuniqF : uniqFdef f)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block nil s (module_intro los nts ps) f 
             (block_intro l1 ps1 cs1 tmn1))
  (H8 : wf_phinodes nil s (module_intro los nts ps) f
         (block_intro l0 ps' cs' tmn') ps2)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs : list (id * GVs),
     getIncomingValuesForBlockFromPHINodes (los, nts) ps2 
       (block_intro l1 ps1 cs1 tmn1) gl lc =
       ret RVs.
Proof.
  intros.
  induction ps2; simpl.
    exists nil. auto.
  
    destruct a. inv H8. inv H6.
    assert (exists v, getValueViaLabelFromValuels l2 l1 = Some v) as J.      
      clear - H14 HbInF HuniqF Hsucc.
      inv H14.
      unfold check_list_value_l in H0.
      remember (split (unmake_list_value_l l2)) as R.
      destruct R.
      destruct H0 as [J1 [J2 J3]].
      eapply In__getValueViaLabelFromValuels; eauto.
      destruct J2 as [_ J2].
      apply J2.
      eapply successors_predOfBlock; eauto.

    destruct J as [v J].
    rewrite J.
    destruct v as [vid | vc].
    Case "vid".
      assert (exists gv1, lookupAL _ lc vid = Some gv1) as J1.
        Focus.
        destruct H14 as [Hwfops Hwfvls].             
        assert (Hnth:=J).
        eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
        destruct Hnth as [n Hnth].
        assert (HwfV:=J).
        eapply wf_value_list__getValueViaLabelFromValuels__wf_value in HwfV; eauto.
        eapply wf_phi_operands__elim in Hwfops; eauto.
        destruct Hwfops as [vb [b1 [Hlkvb [Hlkb1 Hdom]]]].
        assert (b1 = block_intro l1 ps1 cs1 tmn1) 
          as EQ.
          clear - Hlkb1 HbInF HuniqF.
          apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
          rewrite HbInF in Hlkb1. inv Hlkb1; auto.

        subst.
        clear - Hdom Hinscope HeqR J Hreach H2 HbInF Hlkvb Hlkb1 HuniqF.
        destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
        clear Hreach.        
        unfold blockDominates in J3.         
        destruct vb.
        unfold inscope_of_tmn in HeqR.
        destruct f. destruct f.
        remember ((dom_analyze (fdef_intro (fheader_intro f t2 i0 a v) b)) !! l1)
          as R1.
        destruct R1.
        symmetry in HeqR.    
        apply fold_left__spec in HeqR.
        destruct (eq_atom_dec l3 l1); subst.
        SCase "l3=l1".
          destruct HeqR as [HeqR _].
          assert (In vid t) as G.
            clear - J HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
            assert (J':=Hlkvb).
            apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
            apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto.
            destruct Hlkb1 as [J1 J2].
            eapply blockInFdefB_uniq in J2; eauto.
            destruct J2 as [J2 [J4 J5]]; subst.
            apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
            simpl in J'.
            apply HeqR.
            rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsIDs cs1)++getArgsIDs a).
            apply in_or_app; auto.       
          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [? [gv1 [? [Hinscope ?]]]].
          exists gv1. auto.

        SCase "l3<>l1".
          destruct J3 as [J3 | Heq]; subst; try congruence.
          assert (In l3 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as G.
            apply ListSet.set_diff_intro; auto.
              simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
          assert (
            lookupBlockViaLabelFromFdef 
              (fdef_intro (fheader_intro f t2 i0 a v) b) l3 = 
              ret block_intro l3 p c t1) as J1.
            clear - Hlkvb HuniqF.
            apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
            apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkvb; auto.
          destruct HeqR as [_ [HeqR _]].
          apply HeqR in J1; auto.
          assert (In vid t) as InVid.
            clear - J1 HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
            apply J1.
            apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [? [gv1 [? [Hinscope ?]]]].
          exists gv1. auto.
        Unfocus.
  
      destruct J1 as [gv1 J1].
      simpl. rewrite J1. 
      apply IHps2 in H7.
        destruct H7 as [RVs H7].
        rewrite H7. 
        exists ((i0, gv1) :: RVs). auto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 t0 l2]).
        simpl_env. auto.
  
    Case "vc".
      eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H2; eauto.
      inv H2.
      destruct (@const2GV_isnt_stuck (los,nts) s gl vc t0); auto.
      simpl. rewrite H.
      apply IHps2 in H7.
        destruct H7 as [RVs H7].
        rewrite H7. simpl.
        exists ((i0, x) :: RVs). auto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 t0 l2]).
        simpl_env. auto.
Qed.

Lemma params2GVs_isnt_stuck : forall
  p22
  (s : system)
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  n c t v p2
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVsMap)
  (gl : GVMap)
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn)
           (insn_call i0 n c t v p2))
  (Hinscope : wf_defs (los,nts) f lc l0)
  (Hex : exists p21, p2 = p21 ++ p22),
  exists gvs, params2GVs (los, nts) p22 lc gl = Some gvs.
Proof.
  induction p22; intros; simpl; eauto.

    destruct a as [[t0 attr0] v0].
    destruct Hex as [p21 Hex]; subst.
    assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv)
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInParams. right. 
        assert (J:=@in_split_r _ _ (p21 ++ (t0, attr0, v0) :: p22) 
          (t0, attr0, v0)).
        remember (split (p21 ++ (t0, attr0, v0) :: p22)) as R.
        destruct R.
        simpl in J. apply J.
        apply In_middle.
    destruct J as [gv J]. 
    rewrite J.         
    eapply IHp22 in HbInF; eauto.  
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF. eauto.

      exists (p21 ++ [(t0, attr0,v0)]). simpl_env. auto.
Qed.

Lemma initializeFrameValues__total_aux : forall los nts Ps s ifs fattr ft fid va 
  bs2 la2 la1 lc1 
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  gvs2,
  exists lc2, @_initializeFrameValues GVsSig (los,nts) la2 gvs2 lc1 = Some lc2.
Proof.
  induction la2; simpl in *; intros.
    eauto.

    destruct a. destruct p.
    assert (HwfF':=HwfF).
    simpl_env in HwfF'.
    rewrite_env ((la1 ++ [(t, a, i0)]) ++ la2) in HwfF'.
    inv HwfF.
    assert (In (t, a, i0)
            (map_list_typ_attributes_id
              (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
              (typ_, attributes_, id_)) typ_attributes_id_list)) as JJ.
    rewrite <- H11.
    apply in_or_app; simpl; auto.
    apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
      auto.
    apply feasible_typ_list__in_args__feasible_typ with (t:=t)(a:=a)(i0:=i0) 
      in H13; auto.   
    destruct gvs2.
      apply IHla2 with (gvs2:=nil)(lc1:=lc1) in HwfF'.
      destruct HwfF' as [lc2 J].
      rewrite J. 
      apply gundef__total' in H13. 
      destruct H13 as [gv H13]. rewrite H13.
      eauto.

      apply IHla2 with (gvs2:=gvs2)(lc1:=lc1) in HwfF'.
      destruct HwfF' as [lc2 J].
      rewrite J. 
      assert (exists gvs2, GVsSig.(lift_op1) (fit_gv (los, nts) t) g t
        = Some gvs2) as W.
        inv H13.
        apply GVsSig.(lift_op1__isnt_stuck); eauto using fit_gv__total.
      destruct W as [gvs2' W].
      rewrite W. eauto.
Qed.

Lemma initLocal__total : forall los nts Ps s ifs fattr ft fid va bs2 la2  
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  gvs2,
  exists lc2, @initLocals GVsSig (los,nts) la2 gvs2 = Some lc2.
Proof.
  intros.
  unfold initLocals.
  eapply initializeFrameValues__total_aux with (la1:=nil); eauto.
Qed.

Ltac gvs_inhabited_inv H := apply GVsSig.(inhabited_inv) in H; inv H.

Lemma wf_params_spec' : forall TD gvss lp, 
  wf_params TD gvss lp ->
  exists gvs, gvs @@ gvss.
Proof.
  induction gvss; simpl; intros.
    exists nil. simpl. auto.

    destruct lp as [|[[]]]; tinv H.
    destruct H as [J1 J2].
    inv J1. gvs_inhabited_inv H1.
    apply IHgvss in J2. destruct J2 as [gvs J2].
    exists (x::gvs). simpl. auto.
Qed.
 
Lemma params2GVs_inhabited : forall los nts Ps F gl lc 
  (Hwfc : wf_lc (los,nts) F lc)
  S (Hwfg : wf_global (los, nts) S gl) tvs lp gvss,
  wf_value_list
          (make_list_system_module_fdef_value_typ
             (map_list_typ_attributes_value
                (fun (typ_' : typ) attr (value_'' : value) =>
                 (S, (module_intro los nts Ps), F, value_'', typ_'))
                tvs)) ->
  lp = map_list_typ_attributes_value
        (fun (typ_' : typ) attr (value_'' : value) => (typ_', attr, value_''))
        tvs ->
  params2GVs (los,nts) lp lc gl = Some gvss -> exists gvs, gvs @@ gvss.
Proof.
  intros.
  eapply params2GVs_wf_gvs in H; eauto.
  apply wf_params_spec' in H; auto.
Qed.

Definition undefined_state (cfg: Config) (S : State): Prop :=
match cfg with
| {| CurTargetData := td; CurProducts := ps; Globals := gl; FunTable := fs |} =>
  match S with
  | {| ECS := {|
                CurCmds := nil;
                Terminator := insn_return _ _ _;
                Allocas := als |} :: 
              {| CurCmds := c::_ |} :: _;
       Mem := M |} => free_allocas td M als = None
  | _ => False
  end \/
  match S with
  | {| ECS := {|
                CurBB := _;
                CurCmds := nil;
                Terminator := insn_return_void _;
                Allocas := als |} :: 
              {| CurCmds := c::_ |} :: _;
       Mem := M |} => free_allocas td M als = None \/ 
                      match getCallerReturnID c with
                      | Some _ => True
                      | _ => False
                      end
  | _ => False
  end \/
  match S with
  | {| ECS := {|
                CurBB := block_intro _ _ _ (insn_unreachable _);
                CurCmds := nil;
                Terminator := (insn_unreachable _)
               |} :: _
     |} => True
  | _ => False
  end \/
  match S with
  | {| ECS := 
         {| CurCmds := insn_malloc _ t v a::_ ; 
            Locals := lc|} :: _;
       Mem := M |}
  | {| ECS := 
         {| CurCmds := insn_alloca _ t v a::_ ; 
            Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gvs =>
           match getTypeAllocSize td t with
           | Some asz => exists gn, gn @ gvs /\ 
               match malloc td M asz gn a with
               | None => True
               | _ => False
               end
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| ECS := {| CurCmds := insn_free _ _ v::_ ; 
                             Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gvs => exists gv, gv @ gvs /\
           match free td M gv with
           | None => True
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| ECS := {| CurCmds := insn_load _ t v a::_ ; 
                             Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gvs => exists gv, gv @ gvs /\ 
           match mload td M gv t a with
           | None => True
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| ECS := {| CurCmds := insn_store _ t v v0 a::_ ; 
                             Locals := lc|} :: _;
       Mem := M |} =>
       match getOperandValue td v lc gl, 
             getOperandValue td v0 lc gl with
       | Some gvs, Some mgvs => exists gv, exists mgv, gv @ gvs /\ mgv @ mgvs /\ 
           match mstore td M mgv t gv a with
           | None => True
           | _ => False
           end
       | _, _ => False
       end
  | _ => False
  end \/
  match S with
  | {|
       ECS := {| CurCmds := insn_call i0 n _ ft v p::_ ; 
                             Locals := lc|} :: _;
       Mem := M |} => 
       match getOperandValue td v lc gl with
       | Some fptrs =>
            exists fptr, fptr @ fptrs /\
            match lookupFdefViaPtr ps fs fptr, 
                  lookupExFdecViaPtr ps fs fptr with
            | None, Some (fdec_intro (fheader_intro fa rt fid la va)) =>
                match params2GVs td p lc gl with
                | Some gvss =>
                  exists gvs, gvs @@ gvss /\
                  match callExternalFunction M fid gvs with
                  | Some (oresult, _) =>
                     match exCallUpdateLocals td ft n i0 oresult lc with
                     | None => True
                     | _ => False
                     end
                  | None => True
                  end
                | _ => False
                end
            | None, None => True
            | _, _ => False
            end
       | _ => False
       end
  | _ => False
  end
end.

Ltac undefbehave := unfold undefined_state; simpl; 
  try solve [
    auto | 
    right; auto | 
    right; right; auto |  
    right; right; right; right; auto |
    right; right; right; right; right; auto |
    right; right; right; right; right; right; auto |
    right; right; right; right; right; right; right; auto |
    right; right; right; right; right; right; right; right; auto
  ].
   
Lemma progress : forall cfg S1,
  wf_State cfg S1 -> 
  s_isFinialState S1 = true \/ 
  (exists S2, exists tr, sInsn cfg S1 S2 tr) \/
  undefined_state cfg S1.
Proof.
  intros cfg S1 HwfS1.
  destruct cfg as [s [los nts] ps gl fs].
  destruct S1 as [ecs M].
  destruct HwfS1 as [Hwfg1 [HwfSys1 [HmInS1 [Hnonempty HwfECs]]]].
  destruct ecs; try congruence.
  destruct e as [f b cs tmn lc als].
  destruct HwfECs as [[Hreach 
                        [HbInF [HfInPs [Hwflc [Hinscope [l1 [ps1 [cs1 Heq]]]]]]]]
                      [HwfECs HwfCall]].
  subst b.
  destruct cs.
  Case "cs=nil".
    remember (inscope_of_tmn f (block_intro l1 ps1 (cs1 ++ nil) tmn) tmn) as R.
    destruct R; try solve [inversion Hinscope].
    destruct tmn.
    SCase "tmn=ret".
      simpl in HwfCall.
      destruct ecs.
        simpl; auto.      

        right.
        destruct e as [f' b' cs' tmn' lc' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c; try solve [inversion J]. clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        left. symmetry in HeqRm.
        rename HeqRm into J.
        assert (exists lc'', 
          returnUpdateLocals (los,nts) (insn_call i1 n c t0 v0 p) v 
            lc lc' gl = Some lc'') as Hretup.
          unfold returnUpdateLocals. simpl.
          assert (exists gv : GVs, 
            getOperandValue (los, nts) v lc gl = ret gv) as H.
            eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
              simpl. auto.
          destruct H as [gv H]. rewrite H.
          destruct n.
            exists lc'. auto.

            destruct HwfECs as [[Hreach' 
              [HbInF' [HfInPs' [Hwflc' [Hinscope' [l1' [ps1' [cs1' Heq']]]]]]]] 
              [HwfECs HwfCall]]; subst.
            eapply wf_system__wf_cmd with (c:=insn_call i1 false c t0 v0 p) 
              in HbInF'; eauto using in_middle.
            inv HbInF'. inv H6.
            assert (exists gvs2, 
              GVsSig.(lift_op1) (fit_gv (layouts5, namedts5) typ1) gv typ1
                = Some gvs2) as W.
              inv H17.
              apply GVsSig.(lift_op1__isnt_stuck); eauto using fit_gv__total.
            destruct W as [gvs2' W]. rewrite W.
            eauto.
          
        destruct Hretup as [lc'' Hretup].
        exists (mkState ((mkEC f' b' cs' tmn' lc'' als')::ecs) M').
        exists trace_nil.
        eauto.  

    SCase "tmn=ret void".
      simpl in HwfCall.
      destruct ecs.
        simpl; auto.      

        right.
        destruct e as [f' b' cs' tmn' lc' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c; try solve [inversion J]. clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        symmetry in HeqRm.
        rename HeqRm into J.
        destruct n; try solve [undefbehave].
        left.
        exists (mkState ((mkEC f' b' cs' tmn' lc' als')::ecs) M').
        exists trace_nil.
        eauto.  

    SCase "tmn=br". 
      right. left.
      assert (wf_fdef nil s (module_intro los nts ps) f) as HwfF.
        eapply wf_system__wf_fdef; eauto.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists cond, getOperandValue (los,nts) v lc gl = 
        Some cond) as Hget.
        eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
          simpl. auto.
      destruct Hget as [cond Hget].
      assert (Hwfc := HbInF).
      eapply wf_system__wf_tmn in Hwfc; eauto.
      assert (exists c, c @ cond) as Hinh.
        inv Hwfc. 
        eapply getOperandValue__inhabited in Hget; eauto.
        gvs_inhabited_inv Hget. eauto.
      destruct Hinh as [c Hinh].
      assert (exists l', exists ps', exists cs', exists tmn',
              Some (block_intro l' ps' cs' tmn') = 
              (if isGVZero (los,nts) c
                 then lookupBlockViaLabelFromFdef f l3
                 else lookupBlockViaLabelFromFdef f l2)) as HlkB.
        inv Hwfc. 
        destruct block1 as [l2' ps2 cs2 tmn2].
        destruct block2 as [l3' ps3 cs3 tmn3].
        destruct (isGVZero (los, nts) c).
          exists l3'. exists ps3. exists cs3. exists tmn3.
          rewrite H11. auto.

          exists l2'. exists ps2. exists cs2. exists tmn2.
          rewrite H10. auto.

      destruct HlkB as [l' [ps' [cs' [tmn' HlkB]]]].
      assert (exists lc', switchToNewBasicBlock (los, nts) 
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc = 
          Some lc') as Hswitch.
         assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           simpl_env in *.
           destruct (isGVZero (los, nts) c).
             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H9 H10.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               eapply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1)
                 (tmn:=insn_br i0 v l2 l'); simpl; eauto.
               simpl. auto.    
               exists nil. auto.

             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H9 H10.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               eapply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1)
                 (tmn:=insn_br i0 v l' l3); simpl; eauto.
               simpl. auto.    
               exists nil. auto.
         
         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. 
         exists (updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (mkState ((mkEC f (block_intro l' ps' cs' tmn') cs' tmn' lc' 
              als)::ecs) M).
      exists trace_nil. eauto.

    SCase "tmn=br_uncond". 
      right. left.
      assert (wf_fdef nil s (module_intro los nts ps) f) as HwfF.
        eapply wf_system__wf_fdef; eauto.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists ps', exists cs', exists tmn',
        Some (block_intro l2 ps' cs' tmn') = lookupBlockViaLabelFromFdef f l2) 
          as HlkB.
        eapply wf_system__wf_tmn in HbInF; eauto.
        inv HbInF.        
        exists ps1. exists (cs1++nil). exists (insn_br_uncond i0 l2).
        rewrite H6. 
        apply lookupBlockViaLabelFromFdef_inv in H6; auto.
        destruct H6 as [H6 _]; subst. auto.

      destruct HlkB as [ps' [cs' [tmn' HlkB]]].

      assert (exists lc', switchToNewBasicBlock (los, nts) 
        (block_intro l2 ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc = 
          Some lc') as Hswitch.
         assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           eapply wf_system__lookup__wf_block in HlkB; eauto.
           inv HlkB. clear H9 H10.
           eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
             with (l0:=l2); eauto.      
             eapply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1++nil)
               (tmn:=insn_br_uncond i0 l2); simpl; eauto.
             simpl. auto.
             exists nil. auto.
         
         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. 
         exists (updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (mkState ((mkEC f (block_intro l2 ps' cs' tmn') cs' tmn' lc' 
              als)::ecs) M).
      exists trace_nil. eauto.

    SCase "tmn=unreachable".
      undefbehave.

  Case "cs<>nil".
    assert (wf_insn nil s (module_intro los nts ps) f 
      (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) (insn_cmd c)) as Hwfc.
      assert (In c (cs1++c::cs)) as H. 
        apply in_or_app. simpl. auto.
      eapply wf_system__wf_cmd with (c:=c) in HbInF; eauto.
    remember (inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c) as R.
    destruct R; try solve [inversion Hinscope].
    right.
    destruct c.
  SCase "c=bop".
    left.
    assert (exists gv3, BOP (los,nts) lc gl b s0 v v0 = Some gv3) 
      as Hinsn_bop.
      unfold BOP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      inv Hwfc. apply wf_value__wf_typ in H7. destruct H7.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using mbop_is_total.
      eauto.
    destruct Hinsn_bop as [gv3 Hinsn_bop].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_bop i0 b s0 v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv3);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=fbop".
    left.
    assert (exists gv3, FBOP (los,nts) lc gl f0 f1 v v0 = Some gv3) 
      as Hinsn_fbop.
      unfold FBOP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      inv Hwfc. apply wf_value__wf_typ in H7. destruct H7.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using mfbop_is_total.
      eauto.

    destruct Hinsn_fbop as [gv3 Hinsn_fbop].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_fbop i0 f0 f1 v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv3);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=extractvalue".
    left.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', extractGenericValue (los, nts) t gv l2 = Some gv') as J'.
      unfold extractGenericValue.
      inv Hwfc. destruct H13 as [idxs [o [J1 J2]]].
      rewrite J1. rewrite J2. 
      apply GVsSig.(lift_op1__isnt_stuck); eauto using mget'_is_total.
      eauto.
    destruct J' as [gv' J'].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_extractvalue i0 t v l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv');
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=insertvalue".
    left.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', getOperandValue (los, nts) v0 lc gl = Some gv') 
      as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [gv' J'].
    assert (exists gv'', insertGenericValue (los, nts) t gv l2 t0 gv' = 
      Some gv'') as J''.
      unfold insertGenericValue.
      inv Hwfc. destruct H16 as [idxs [o [J1 J2]]].
      rewrite J1. rewrite J2. apply wf_value__wf_typ in H10. destruct H10.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using mset'_is_total.
      eauto.
    destruct J'' as [gv'' J''].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_insertvalue i0 t v t0 v0 l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv'');
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=malloc". 
    inv Hwfc. inv H12.
    eapply feasible_typ_inv'' in H; eauto.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gn, gn @ gvs) as Hinh.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [gn Hinh].
    remember (malloc (los, nts) M asz gn a) as R.
    destruct R as [[M' mb] |].
      left.
      exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_malloc i0 t v a :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := 
               (updateAddAL _ lc i0 ($ (blk2GV (los, nts) mb) # typ_pointer t$));
                Allocas := als |} :: ecs;
         Mem := M' |}.
      exists trace_nil.
      eauto.
      
      unfold undefined_state.
      right. rewrite J. rewrite J2. right. right. right. left.
      exists gn. rewrite <- HeqR0. undefbehave.

  SCase "free". 
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gv, gv @ gvs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [gv Hinh].
    remember (free (los, nts) M gv) as R.
    destruct R as [M'|].
      left.
      exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_free i0 t v :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Mem := M' |}.
      exists trace_nil.
      eauto.      
      
      unfold undefined_state.
      right. rewrite J. right. right. right. right. left. 
      exists gv. rewrite <- HeqR0. undefbehave.

  SCase "alloca".
    inv Hwfc. inv H12.
    apply feasible_typ_inv'' in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gn, gn @ gvs) as Hinh.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [gn Hinh].
    remember (malloc (los, nts) M asz gn a) as R.
    destruct R as [[M' mb] |].
      left.
      exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_alloca i0 t v a :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := 
               (updateAddAL _ lc i0 ($ (blk2GV (los, nts) mb) # typ_pointer t$));
                Allocas := (mb::als) |} :: ecs;
         Mem := M' |}.
      exists trace_nil.
      eauto.      
      
      right.
      unfold undefined_state.
      right. rewrite J. rewrite J2. right. right. left. exists gn.
      rewrite <- HeqR0. undefbehave.

  SCase "load".
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gv, gv @ gvs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [gv Hinh].
    remember (mload (los,nts) M gv t a) as R.
    destruct R as [gv' |].
      left.
      exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_load i0 t v a :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc i0 ($ gv' # t$);
                Allocas := als |} :: ecs;
         Mem := M |}.
      exists trace_nil.
      eauto.      

      right.
      unfold undefined_state.
      right. rewrite J. right. right. right. right. left. exists gv.
      rewrite <- HeqR0. undefbehave.
      
  SCase "store".
    assert (exists gvs, getOperandValue (los, nts) v lc gl = Some gvs) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gvs J].
    assert (exists gvs, getOperandValue (los, nts) v0 lc gl = Some gvs) 
      as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [mgvs J0].
    inv Hwfc.
    assert (exists gv, gv @ gvs) as Hinh1.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh1 as [gv Hinh1].
    assert (exists mgv, mgv @ mgvs) as Hinh2.
      eapply getOperandValue__inhabited in J0; eauto.
      gvs_inhabited_inv J0. eauto.
    destruct Hinh2 as [mgv Hinh2].
    remember (mstore (los,nts) M mgv t gv a) as R.
    destruct R as [M' |].
      left.
      exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_store i0 t v v0 a :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Mem := M' |}.
      exists trace_nil.
      eauto.      

      right.
      unfold undefined_state.
      right. rewrite J. rewrite J0. right. right. right. right. right. left.
      exists gv. exists mgv.  rewrite <- HeqR0. undefbehave.

  SCase "gep".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [mp J].
    assert (exists vidxs, values2GVs (los, nts) l2 lc gl = Some vidxs) 
      as J2.
      eapply values2GVs_isnt_stuck; eauto.
        exists Nil_list_sz_value. auto.
    destruct J2 as [vidxss J2].
    inv Hwfc.
    assert (Hins:=H13).
    eapply values2GVs__inhabited in Hins; eauto.
    destruct Hins as [vidxs Hins].
    assert (exists mp', GEP (los, nts) t mp vidxs i1 = Some mp') as J3.
      unfold GEP, gep. 
      apply GVsSig.(lift_op1__isnt_stuck); eauto using GEP_is_total.
    destruct J3 as [mp' J3].
    left.
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 mp');
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "trunc". 
    left.
    assert (exists gv2, TRUNC (los,nts) lc gl t t0 v t1 = Some gv2) 
      as Hinsn_trunc.
      unfold TRUNC.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. inv Hwfc.
      apply GVsSig.(lift_op1__isnt_stuck); eauto using mtrunc_is_total.

    destruct Hinsn_trunc as [gv2 Hinsn_trunc].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_trunc i0 t t0 v t1 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "ext".
    left.
    assert (exists gv2, EXT (los,nts) lc gl e t v t0 = Some gv2) 
      as Hinsn_ext.
      unfold EXT.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. inv Hwfc.
      apply GVsSig.(lift_op1__isnt_stuck); eauto using mext_is_total.

    destruct Hinsn_ext as [gv2 Hinsn_ext].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_ext i0 e t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "cast". 
    left.
    assert (exists gvs2, CAST (los,nts) lc gl c t v t0 = Some gvs2) 
      as Hinsn_cast.
      unfold CAST.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J. inv Hwfc.
      apply GVsSig.(lift_op1__isnt_stuck); eauto using mcast_is_total.
      
    destruct Hinsn_cast as [gv2 Hinsn_cast].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_cast i0 c t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "icmp". 
    left.
    assert (exists gv2, ICMP (los,nts) lc gl c t v v0 = Some gv2) 
      as Hinsn_icmp.
      unfold ICMP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0. inv Hwfc.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using micmp_is_total.

    destruct Hinsn_icmp as [gv2 Hinsn_icmp].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_icmp i0 c t v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "fcmp". 
    left.
    assert (exists gv2, FCMP (los,nts) lc gl f0 f1 v v0 = Some gv2) 
      as Hinsn_fcmp.
      unfold FCMP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0. inv Hwfc. apply wf_value__wf_typ in H12. destruct H12.
      apply GVsSig.(lift_op2__isnt_stuck); eauto using mfcmp_is_total.

    destruct Hinsn_fcmp as [gv2 Hinsn_fcmp].
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_fcmp i0 f0 f1 v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "select". 
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) 
      as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [cond J].
    assert (exists c, c @ cond) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J; eauto.
      gvs_inhabited_inv J. eauto.
    destruct Hinh as [c Hinh].
    assert (exists gv0, getOperandValue (los, nts) v0 lc gl = Some gv0) 
      as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [gv0 J0].
    assert (exists gv1, getOperandValue (los, nts) v1 lc gl = Some gv1) 
      as J1.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J1 as [gv1 J1].
    left.
    exists 
         {|
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_select i0 v t v0 v1 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (if isGVZero (los, nts) c 
                           then updateAddAL _ lc i0 gv1 
                           else updateAddAL _ lc i0 gv0);
                Allocas := als |} :: ecs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "call". 
    assert (exists gvs, params2GVs (los, nts) p lc gl = Some gvs) as G.
      eapply params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvss G].
    assert (exists fptrs, getOperandValue (los, nts) v lc gl = 
      Some fptrs) as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [fptrs J'].
    assert (exists fptr, fptr @ fptrs) as Hinh.
      inv Hwfc.
      eapply getOperandValue__inhabited in J'; eauto.
      gvs_inhabited_inv J'. eauto.
    destruct Hinh as [fptr Hinh].
    remember (lookupFdefViaPtr ps fs fptr) as Hlk. 
    destruct Hlk as [f' |].
    SSCase "internal call".
    destruct f' as [[fa rt fid la va] lb].
    assert (J:=HeqHlk).
    symmetry in J.
    apply lookupFdefViaPtr_inversion in J; auto.
    destruct J as [fn [Hlkft J]].
    apply lookupFdefViaIDFromProducts_inv in J; auto.
    eapply wf_system__wf_fdef in J; eauto.
    assert (Hinit := J).
    apply initLocal__total with (gvs2:=gvss) in Hinit; auto.
    destruct Hinit as [lc2 Hinit].
    inv J. destruct block5 as [l5 ps5 cs5 tmn5].
    left.
    exists 
         {|
         ECS :=(mkEC 
                       (fdef_intro (fheader_intro fa rt fid 
                         (map_list_typ_attributes_id
                         (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) 
                         => (typ_, attributes_, id_)) typ_attributes_id_list)
                         va) lb) 
                       (block_intro l5 ps5 cs5 tmn5) cs5 tmn5 lc2
                       nil)::
               {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_call i0 n c t v p :: cs) tmn;
                CurCmds := insn_call i0 n c t v p :: cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Mem := M |}.
    exists trace_nil.
    eauto.     

    remember (lookupExFdecViaPtr ps fs fptr) as Helk. 
    destruct Helk as [f' |].
    SSCase "external call".
    assert (exists gvs, gvs @@ gvss) as G'.
      inv Hwfc.
      eapply params2GVs_inhabited in G; eauto.
    destruct G' as [gvs G']. 
    destruct f' as [[fa rt fid la va]].
    remember (callExternalFunction M fid gvs) as R.
    destruct R as [[oresult Mem']|].
      remember (exCallUpdateLocals (los, nts) t n i0 oresult lc) as R'.
      destruct R' as [lc' |]; tinv J.
        left.
        exists 
          {|
          ECS :={|
                 CurFunction := f;
                 CurBB := block_intro l1 ps1
                            (cs1 ++ insn_call i0 n c t v p :: cs) tmn;
                 CurCmds := cs;
                 Terminator := tmn;
                 Locals := lc';
                 Allocas := als |} :: ecs;
          Mem := Mem' |}.
        exists trace_nil.
        eauto.     

        right.
        unfold undefined_state.
        right. right. right. right. right. right. right. 
        rewrite J'. rewrite G. exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk. 
        split; auto. exists gvs. 
        rewrite <- HeqR0. rewrite <- HeqR'. undefbehave.

      right.
      unfold undefined_state.
      right. rewrite J'. rewrite G. right. right. right. right. right. right.
      exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk.
      split; auto. exists gvs.  rewrite <- HeqR0. undefbehave.

   SSCase "stuck".
     right.
     unfold undefined_state.
     right. rewrite J'. rewrite G. right. right. right. right. right. right.
     exists fptr. rewrite <- HeqHlk. rewrite <- HeqHelk. split; auto. 
Qed.

End OpsemPP. End OpsemPP.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
