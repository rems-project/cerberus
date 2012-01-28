Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Require Import Lattice.
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
Require Import Floats.
Require Import AST.
Require Import Maps.
Require Import opsem.
Require Import opsem_props.

(************** Opsem PP *********************************************** ***)

Module OpsemPP. 

Export Opsem.
Export OpsemProps.
Import AtomSet.

Inductive wf_GVs : GenericValue -> Prop :=
| wf_GVs_intro : forall gvs, 
    wf_GVs gvs.

Hint Constructors wf_GVs.

Inductive wf_defs (f:fdef) (lc:GVMap) : list atom -> Prop :=
| wf_defs_nil : wf_defs f lc nil
| wf_defs_cons : forall id1 gvs1 defs',
    lookupIDFromFdef f id1 = Some tt ->
    lookupAL _ lc id1 = Some gvs1 -> 
    wf_GVs gvs1 ->
    wf_defs f lc defs' ->
    wf_defs f lc (id1::defs').

Lemma wf_defs_elim : forall ids1 F lc,
  wf_defs F lc ids1 ->
  forall id1, List.In id1 ids1 ->
  exists gvs1,
    lookupIDFromFdef F id1 = Some tt /\
    lookupAL _ lc id1 = Some gvs1 /\
    wf_GVs gvs1.
Proof.
  induction ids1; intros; simpl in H0; inv H0.  
    inv H.
    exists gvs1. split; auto.

    inv H.
    eapply IHids1 in H6; eauto.
Qed.    

Lemma wf_defs_intro : forall ids1 F lc,
  (forall id1, List.In id1 ids1 ->
   exists gvs1,
     lookupIDFromFdef F id1 = Some tt /\
     lookupAL _ lc id1 = Some gvs1 /\
     wf_GVs gvs1) ->
  wf_defs F lc ids1.
Proof.
  induction ids1; intros.
    apply wf_defs_nil.  

    destruct (@H a) as [gvs1 [J1 [J2 J3]]]; simpl; auto.
    eapply wf_defs_cons; eauto.
      apply IHids1.
      intros id1 J.
      apply H. simpl. auto.
Qed.

Lemma wf_defs_eq : forall ids2 ids1 F' lc',
  set_eq _ ids1 ids2 ->
  wf_defs F' lc' ids1 ->
  wf_defs F' lc' ids2.
Proof.
  intros.
  apply wf_defs_intro.
  intros id1 Hin.
  destruct H as [J1 J2].
  eapply wf_defs_elim in H0; eauto.
Qed.

Lemma wf_defs_updateAddAL : forall g F' lc' ids1 ids2 i1,
  wf_defs F' lc' ids1 ->
  set_eq _ (i1::ids1) ids2 ->
  lookupIDFromFdef F' i1 = ret tt ->
  wf_GVs g ->
  wf_defs F' (updateAddAL _ lc' i1 g) ids2.
Proof.
  intros g F' lc' ids1 ids2 i1 HwfDefs Heq Hlkup Hwfgvs.  
  apply wf_defs_intro.  
  intros id1 Hin.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  destruct (eq_dec i1 id1); subst.
    exists g. 
    split; auto.
    split; auto. 
      apply lookupAL_updateAddAL_eq; auto.      

    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    eapply wf_defs_elim in HwfDefs; eauto.
    destruct HwfDefs as [gv2 [J1 [J2 J3]]].
    exists gv2.
    split; auto.
    split; auto. 
      rewrite <- lookupAL_updateAddAL_neq; auto.      
Qed.

Definition wf_lc (f:fdef) (lc:GVMap) : Prop := forall i0 gvs0, 
  lookupIDFromFdef f i0 = Some tt ->
  lookupAL _ lc i0 = Some gvs0 -> 
  wf_GVs gvs0.

Lemma getOperandValue__wf_gvs : forall f v lc gvs,
  wf_lc f lc ->
  wf_value f v ->
  getOperandValue v lc = Some gvs ->
  wf_GVs gvs.
Proof.
  intros f v lc gvs Hwflc Hwfv Hget. auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec1_aux : forall f
    b lc id1 t l3 cs tmn ps2 ps1 lc' ,
  wf_lc f lc ->
  Some lc' = getIncomingValuesForBlockFromPHINodes ps2 b lc ->
  List.In id1 (getPhiNodesIDs ps2) ->
  uniqFdef f ->
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_phinodes f (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  lookupIDFromFdef f id1 = ret t ->
  exists gvs, lookupAL _ lc' id1 = Some gvs /\ wf_GVs gvs.
Proof.    
  intros f b lc id1 t l3 cs tmn ps2 ps1 lc' Hwflc H H0 Huniq Hbinf Hwfps Hlk.
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
    eapply lookupIDFromFdef__lookupIDFromPhiNodes in J; eauto.
    destruct a.
    simpl in H0. simpl in J.
    inv Hwfps. inv H5.
    destruct H0 as [H0 | H0]; subst.
      rewrite NoDup_lookupIDFromPhiNodes in J; auto.
      inv J.
      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].
        eapply wf_value_list__getValueViaBlockFromValuels__wf_value in H3; eauto.
        remember (getOperandValue v lc) as R.
        destruct R as [g|]; tinv H.
        symmetry in HeqR. eapply getOperandValue__wf_gvs in HeqR; eauto.
        destruct (getIncomingValuesForBlockFromPHINodes ps2 b lc); inv H.
        exists g. simpl. 
        destruct (id1 == id1) as [e' | n]; try solve [contradict n; auto].
          split; auto.

      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].   
        remember (getOperandValue v lc) as R.
        destruct R; tinv H. 
        remember (getIncomingValuesForBlockFromPHINodes ps2 b lc) 
          as R.
        destruct R; inversion H; subst.         
        simpl.
        destruct (id1==i0); subst.
          clear - Huniq' H0.
          rewrite getPhiNodesIDs_app in Huniq'.
          apply NoDup_split in Huniq'.
          destruct Huniq' as [_ Huniq'].
          inv Huniq'. congruence.
      
          eapply IHps2 with (ps1:=ps1 ++ [insn_phi i0 l0]); simpl_env; eauto.
Qed.

Hint Resolve wf_fdef__uniqFdef.

Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall f b 
    lc id1 t l3 cs tmn ps lc' ,
  wf_lc f lc ->
  Some lc' = getIncomingValuesForBlockFromPHINodes ps b lc ->
  In id1 (getPhiNodesIDs ps) ->
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_fdef f ->
  lookupIDFromFdef f id1 = ret t ->
  exists gvs, lookupAL _ lc' id1 = Some gvs /\ wf_GVs gvs.
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H2.
    apply lookupBlockViaLabelFromFdef_inv in H2; auto.
    destruct H2; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec1_aux with (ps1:=nil); 
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2_aux : forall f
  b lc l3 cs tmn (Hwflc: wf_lc f lc) 
  (Huniq: uniqFdef f) ps2 ps1 rs,
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_phinodes f (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  Some rs = getIncomingValuesForBlockFromPHINodes ps2 b lc ->
  (forall id0 gvs, In (id0,gvs) rs -> 
     lookupIDFromFdef f id0 = Some tt ->
     wf_GVs gvs).
Proof.    
  intros f b lc l3 cs tmn Hwflc Huniq ps2 ps1 rs Hbinf. auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2 : forall f b 
  lc l3 cs tmn (Hwflc: wf_lc f lc) 
  (Huniq: uniqFdef f) ps rs,
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_fdef f ->
  Some rs = getIncomingValuesForBlockFromPHINodes ps b lc ->
  (forall id0 gvs, In (id0,gvs) rs -> 
     lookupIDFromFdef f id0 = Some tt ->
     wf_GVs gvs).
Proof.
  intros. auto.
Qed.

Lemma updateValuesForNewBlock_spec2 : forall f lc id1 gv,
  lookupAL _ lc id1 = Some gv ->
  lookupIDFromFdef f id1 = Some tt ->
  wf_lc f lc ->
  forall rs, 
  (forall id0 gv, 
     In (id0,gv) rs -> lookupIDFromFdef f id0 = Some tt ->
     wf_GVs gv) ->
  exists gv', 
    lookupIDFromFdef f id1 = Some tt /\
    lookupAL _ (updateValuesForNewBlock rs lc) id1 = Some gv' /\
    wf_GVs gv'.
Proof.
  induction rs; intros; simpl in *.   
    exists gv. eauto.

    destruct a. 
    destruct (id1==i0); subst.
      exists g. rewrite lookupAL_updateAddAL_eq; eauto.
      rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall f lc,
  wf_lc f lc ->
  forall rs, 
  (forall id0 gv, 
     In (id0,gv) rs -> lookupIDFromFdef f id0 = Some tt ->
     wf_GVs gv) ->
  wf_lc f (updateValuesForNewBlock rs lc).
Proof.  
  induction rs; intros; simpl in *; auto.
    destruct a.
    intros x gvx Htyp Hlk.
    destruct (i0==x); subst.
      rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk. eauto.

      rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
Qed.

Lemma wf_lc_br_aux : forall f b1 b2 lc lc' l3 
  (Hswitch : switchToNewBasicBlock b1 b2 lc = ret lc')
  (Hlkup : Some b1 = lookupBlockViaLabelFromFdef f l3)
  (HwfF : wf_fdef f)
  (Hwflc : wf_lc f lc),
  wf_lc f lc'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  remember (getIncomingValuesForBlockFromPHINodes
              (getPHINodesFromBlock b1) b2 lc) as R1.
  destruct R1; inv Hswitch.
  apply updateValuesForNewBlock_spec3; auto.
Qed.

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' 
  (l3 : l)
  (ps : phinodes)
  (cs : list cmd) tmn
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock (block_intro l' ps' cs' tmn')
         (block_intro l3 ps cs tmn) lc = ret lc')
  (t : list atom)
  (Hwfdfs : wf_defs F lc t)
  (ids0' : list atom)
  (Hwflc : wf_lc F lc)
  (HwfF : wf_fdef F)
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs F lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  apply wf_defs_intro.
  intros id1 Hid1.
  remember (getIncomingValuesForBlockFromPHINodes ps'
                (block_intro l3 ps cs tmn) lc) as R1.
  destruct R1; inv Hswitch.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    assert (J:=Hlkup).
    eapply InPhiNodes_lookupIDFromFdef in Hlkup; eauto.
    eapply getIncomingValuesForBlockFromPHINodes_spec1 in HeqR1; eauto.
    destruct HeqR1 as [gv [HeqR1 Hwfgv]].
    eapply updateValuesForNewBlock_spec4 in HeqR1; eauto.

    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin.
    apply wf_defs_elim with (id1:=id1) in Hwfdfs; auto.
    destruct Hwfdfs as [gv1 [J1 [J2 J3]]].
    eapply updateValuesForNewBlock_spec2 with (rs:=g) in J2; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 
  lc lc',
wf_lc F lc ->
wf_fdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 lc lc'
    Hwflc HwfF HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  assert (uniqFdef F) as Huniq. auto.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd, inscope_of_id.
  destruct F as [bs].
  remember (dom_analyze (fdef_intro bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms Huniq HwfF.
    simpl in Huniq.
    eapply dom_successors; eauto.

  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound').
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil)(bs:=bs)(l0:=l') in J1.
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

      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4; auto.
      
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
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps')(bs:=bs)
      (l0:=l') in J1.
    destruct J1 as [r J1].
    exists r.  split; auto.

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
        contradict J; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. 
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4; auto.
      
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
  lc lc' bid,
wf_lc F lc ->
wf_fdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c lc lc',
wf_lc F lc ->
wf_fdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros.
  remember (isGVZero c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Lemma wf_lc_updateAddAL : forall f lc gv i0,
  wf_lc f lc -> 
  lookupIDFromFdef f i0 = ret tt ->
  wf_GVs gv -> 
  wf_lc f (updateAddAL _ lc i0 gv).
Proof.
  intros.
  intros x gvx Htyp Hlk.
  destruct (eq_atom_dec i0 x); subst.
    rewrite lookupAL_updateAddAL_eq in Hlk.
    inv Hlk. rewrite H0 in Htyp. inv Htyp. auto.

    rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
Qed.

Lemma BOP__wf_gvs : forall F lc bop0 v1 v2 gvs3,
  wf_lc F lc ->
  wf_value F v1 ->
  wf_value F v2 ->
  BOP lc bop0 v1 v2 = ret gvs3 ->
  wf_GVs gvs3.
Proof.
  intros F lc bop0 v1 v2 gvs3 Hwflc Hwfv1 Hwfv2 
    Hbop. auto.
Qed.

Lemma ICMP__wf_gvs : forall F lc c v1 v2 gvs3,
  wf_lc F lc ->
  wf_value F v1 ->
  wf_value F v2 ->
  ICMP lc c v1 v2 = ret gvs3 ->
  wf_GVs gvs3.
Proof.
  intros F lc c v1 v2 gvs3 Hwflc Hwfv1 Hwfv2 Hiop. auto.
Qed.
 
(*********************************************)
(** * Preservation *)

Definition wf_ExecutionContext (f:fdef) (ec:ExecutionContext) : Prop :=
let '(mkEC b cs tmn lc) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
wf_fdef f /\
wf_lc f lc /\
match cs with
| nil => 
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs f lc ids
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs f lc ids
    | None => False
    end
end /\
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Lemma wf_State__inv : forall F B c cs tmn lc,
  wf_ExecutionContext F (mkEC B (c::cs) tmn lc) ->
  wf_lc F lc /\ 
  wf_insn F B (insn_cmd c).
Proof.
  intros.
  destruct H as 
    [Hreach1 [HBinF1 [HwfF [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]; subst.
  split; auto. 
    eapply wf_fdef__wf_cmd; eauto using in_middle.
Qed.  

Lemma preservation_cmd_updated_case : forall
  (F : fdef)
  (B : block)
  (lc : GVMap)
  (gv3 : GenericValue)
  (cs : list cmd)
  (tmn : terminator)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  (Hwfgv : wf_GVs gv3)
  (HwfS1 : wf_ExecutionContext F
            {| CurBB := B;
               CurCmds := c0 :: cs;
               Terminator := tmn;
               Locals := lc
            |}),
   wf_ExecutionContext F
     {| CurBB := B;
        CurCmds := cs;
        Terminator := tmn;
        Locals := updateAddAL _ lc id0 gv3
     |}.
Proof.
  intros.
  destruct HwfS1 as 
     [Hreach1 [HBinF1 [HwfF1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]];
     subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  assert (uniqFdef F) as HuniqF. auto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
       subst.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs3')) as Hnotin.
          eapply wf_fdef__uniq_block with (f:=F) in HwfF1; eauto.        
          simpl in HwfF1.
          apply NoDup_inv in HwfF1.
          destruct HwfF1 as [_ J].
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
        eapply wf_fdef__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL; eauto.
          eapply uniqF__lookupIDFromFdef; eauto.
        
      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_fdef__uniq_block with (f:=F) in HwfF1; eauto.        
          simpl in HwfF1.
          apply NoDup_inv in HwfF1.
          destruct HwfF1 as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_fdef__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL; eauto.
          eapply uniqF__lookupIDFromFdef; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma preservation : forall F S1 S2 tr,
  sInsn F S1 S2 tr -> wf_ExecutionContext F S1 -> wf_ExecutionContext F S2.
Proof.
  intros F S1 S2 tr HsInsn HwfS1.
  (sInsn_cases (induction HsInsn) Case).
Focus.
Case "sBranch".
  destruct HwfS1 as 
     [Hreach1 [HBinF1 [HwfF [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]; 
     subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
    assert (HuniqF := HwfF). 
    eapply wf_fdef__uniqFdef with (f:=F) in HuniqF; eauto.
    split; auto.
      clear - Hreach1 H0 HBinF1 HwfF HuniqF.
      unfold isReachableFromEntry in *.
      destruct (isGVZero c).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
        destruct H0 as [H0 _].
        eapply reachable_successors; eauto.
          simpl. auto.
      
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
        destruct H0 as [H0 _].
        eapply reachable_successors; eauto.
          simpl. auto.
    split. 
      clear - H0 HBinF1 HwfF HuniqF.
      destruct (isGVZero c).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
          destruct H0; auto.
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
          destruct H0; auto.
    split; auto.
    split.
      destruct (isGVZero c);
        eapply wf_lc_br_aux in H0; eauto.
    split.
      clear - H0 HeqR1 H1 Hinscope1 HBinF1 HwfF HuniqF Hwflc1.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "sBranch_uncond".
  destruct HwfS1 as 
     [Hreach1 [HBinF1 [HwfF [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]; 
     subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
    assert (HuniqF := HwfF).
    eapply wf_fdef__uniqFdef with (f:=F) in HuniqF; eauto.
    split; auto.
      clear - Hreach1 H HBinF1 HwfF HuniqF.
      unfold isReachableFromEntry in *.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
      destruct H as [H _].
      eapply reachable_successors; eauto.
        simpl. auto.
    split.
      clear - H HBinF1 HwfF HuniqF.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
        destruct H; auto.
    split; auto.
    split. eapply wf_lc_br_aux in H0; eauto.
    split.
      clear - H0 HeqR1 Hinscope1 H HBinF1 HwfF HuniqF Hwflc1.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "sBop". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
Case "sIcmp". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
Qed.

(*********************************************)
(** * Progress *)

Lemma state_tmn_typing : forall f l1 ps1 cs1 tmn1 defs id1 lc,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs f lc defs ->
  wf_fdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  exists gv, 
    lookupIDFromFdef f id1 = munit tt /\
    lookupAL _ lc id1 = Some gv /\ wf_GVs gv.
Proof.
  intros f l1 ps1 cs1 tmn1 defs id1 lc Hreach HwfInstr Hinscope 
    HwfDefs HuniqF HinOps.
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
    rewrite H1 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=block_intro l1 ps1 cs1 tmn1)
    (insn1:=insn_terminator tmn1)(id1:=id1) in H2; auto.

  inv H2.
  eapply wf_defs_elim; eauto.
    unfold inscope_of_tmn in Hinscope.
    destruct f.
    remember ((dom_analyze (fdef_intro b)) !! l1) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H7 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      destruct J' as [J' _].
      destruct J' as [[cs2 [c1 [cs3 [J1 J2]]]] | [ps2 [p1 [ps3 [J1 J2]]]]]; 
        subst.
        rewrite getCmdsIDs_app. simpl. rewrite J2.
        apply in_or_app. right.
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
       lookupBlockViaLabelFromFdef (fdef_intro b) l0 =
       ret block_intro l0 p c t) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l0 p c t) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma state_cmd_typing : forall f b c defs id1 lc,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs f lc defs ->
  wf_fdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  exists gv, 
    lookupIDFromFdef f id1 = munit tt /\
    lookupAL _ lc id1 = Some gv /\ wf_GVs gv.
Proof.
  intros f b c defs id1 lc Hnodup Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps.
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
    rewrite H1 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=b)(insn1:=insn_cmd c)(id1:=id1) 
    in H2; auto.

  inv H2. 
  eapply wf_defs_elim; eauto.
    unfold inscope_of_cmd, inscope_of_id in Hinscope.
    destruct b. destruct f.
    remember ((dom_analyze (fdef_intro b)) !! l0) as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H7 as [J' | [J' | J']]; try solve [contradict J'; auto].
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
       lookupBlockViaLabelFromFdef (fdef_intro b) l1
         = ret block_intro l1 p0 c1 t0) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l1 p0 c1 t0) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma getOperandValue_inCmdOps_isnt_stuck : forall
  (f : fdef)
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVMap)
  (HwfSys1 : wf_fdef f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : wf_defs f lc l0)
  (v : value)
  (Hvincs : valueInCmdOperands v c),
  exists gv, getOperandValue v lc = ret gv.
Proof.
  intros.
  destruct v as [vid | vc]; simpl; eauto.
    assert (exists gv, 
                lookupIDFromFdef f vid = munit tt /\
                lookupAL _ lc vid = Some gv /\ 
                wf_GVs gv) as Hlkup.
      eapply state_cmd_typing; eauto. 
      eapply wf_fdef__uniq_block; eauto.
      eapply wf_fdef__wf_cmd; eauto using In_middle.
      apply valueInCmdOperands__InOps; auto.
    destruct Hlkup as [gv [Hlktyp [Hlkup Hwfgv]]].
    simpl. rewrite Hlkup. eauto.
Qed.

Lemma getOperandValue_inTmnOperans_isnt_stuck : forall
  (f : fdef)
  (tmn : terminator)
  (lc : GVMap)
  (HwfSys1 : wf_fdef f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (Hinscope : wf_defs f lc l0)
  (v : value)
  (Hvincs : valueInTmnOperands v tmn),
  exists gv, getOperandValue v lc = ret gv.
Proof.
  intros.
  destruct v as [vid | vc]; simpl; eauto.
    assert (HwfInstr:=HbInF).
    eapply wf_fdef__wf_tmn in HwfInstr; eauto.
    assert (exists gv, 
      lookupIDFromFdef f vid = munit tt /\
      lookupAL _ lc vid = Some gv /\ 
      wf_GVs gv) as Hlkup.
      eapply state_tmn_typing; eauto. 
      apply valueInTmnOperands__InOps; auto.
    destruct Hlkup as [gv [Hlktyp [Hlkup Hwfgv]]].
    rewrite Hlkup. eauto.
Qed.

Lemma wf_phinodes__getIncomingValuesForBlockFromPHINodes : forall
  (f : fdef)
  l0
  (lc : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs f lc t)
  (HuniqF : uniqFdef f)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block f (block_intro l1 ps1 cs1 tmn1))
  (H8 : wf_phinodes f (block_intro l0 ps' cs' tmn') ps2)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs,
     getIncomingValuesForBlockFromPHINodes ps2 
       (block_intro l1 ps1 cs1 tmn1) lc =
       ret RVs.
Proof.
  intros.
  induction ps2; simpl.
    exists nil. auto.
  
    destruct a. inv H8. inv H3.
    assert (exists v, getValueViaLabelFromValuels l2 l1 = Some v) as J.      
      clear - H7 HbInF HuniqF Hsucc.
      inv H7.
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
        destruct H7 as [Hwfops Hwfvls].             
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
        clear - Hdom Hinscope HeqR J Hreach H1 HbInF Hlkvb Hlkb1 HuniqF.
        destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
        clear Hreach.        
        unfold blockDominates in J3.         
        destruct vb.
        unfold inscope_of_tmn in HeqR.
        destruct f.
        remember ((dom_analyze (fdef_intro b)) !! l1) as R1.
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
            apply HeqR; auto.

          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [gv1 [? [Hinscope ?]]].
          exists gv1. auto.

        SCase "l3<>l1".
          destruct J3 as [J3 | Heq]; subst; try congruence.
          assert (In l3 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as G.
            apply ListSet.set_diff_intro; auto.
              simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
          assert (
            lookupBlockViaLabelFromFdef (fdef_intro b) l3 = 
              ret block_intro l3 p c t0) as J1.
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
          destruct Hinscope as [gv1 [? [Hinscope ?]]].
          exists gv1. auto.
        Unfocus.
  
      destruct J1 as [gv1 J1].
      simpl. rewrite J1. 
      apply IHps2 in H4.
        destruct H4 as [RVs H4].
        rewrite H4. 
        exists ((i0, gv1) :: RVs). auto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 l2]).
        simpl_env. auto.
  
    Case "vc". 
      eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H1; eauto.
      inv H1.
      simpl.
      apply IHps2 in H4.
        destruct H4 as [RVs H4].
        rewrite H4. simpl. eauto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 l2]).
        simpl_env. auto.
Qed.

Lemma progress : forall f S1,
  wf_ExecutionContext f S1 -> 
  s_isFinialState S1 = true \/ 
  (exists S2, exists tr, sInsn f S1 S2 tr).
Proof.
  intros f S1 HwfS1.
  destruct S1 as [b cs tmn lc].
  destruct HwfS1 as [Hreach 
                      [HbInF [HwfF [Hwflc [Hinscope [l1 [ps1 [cs1 Heq]]]]]]]].
  subst b.
  destruct cs.
  Case "cs=nil".
    remember (inscope_of_tmn f (block_intro l1 ps1 (cs1 ++ nil) tmn) tmn) as R.
    destruct R; try solve [inversion Hinscope].
    destruct tmn.
    SCase "tmn=ret void".
      simpl. auto.

    SCase "tmn=br". 
      right.
      assert (uniqFdef f) as HuniqF. auto.
      assert (exists c, getOperandValue v lc = Some c) as Hget.
        eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
          simpl. auto.
      destruct Hget as [c Hget].
      assert (Hwfc := HbInF).
      eapply wf_fdef__wf_tmn in Hwfc; eauto.
      assert (exists l', exists ps', exists cs', exists tmn',
              Some (block_intro l' ps' cs' tmn') = 
              (if isGVZero c
                 then lookupBlockViaLabelFromFdef f l3
                 else lookupBlockViaLabelFromFdef f l2)) as HlkB.
        inv Hwfc. 
        destruct block1 as [l2' ps2 cs2 tmn2].
        destruct block2 as [l3' ps3 cs3 tmn3].
        destruct (isGVZero c).
          exists l3'. exists ps3. exists cs3. exists tmn3.
          rewrite H7. auto.

          exists l2'. exists ps2. exists cs2. exists tmn2.
          rewrite H6. auto.

      destruct HlkB as [l' [ps' [cs' [tmn' HlkB]]]].
      assert (exists lc', switchToNewBasicBlock
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) lc = 
          Some lc') as Hswitch.
         assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes ps'
             (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) lc =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_fdef__blockInFdefB__wf_block in HwfB; eauto.
           simpl_env in *.
           destruct (isGVZero c).
             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_fdef__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H6 H7.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1)
                 (tmn:=insn_br i0 v l2 l'); simpl; auto.
               simpl. auto.    
               exists nil. auto.

             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_fdef__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H6 H7.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1)
                 (tmn:=insn_br i0 v l' l3); simpl; auto.
               simpl. auto.    
               exists nil. auto.
         
         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. 
         exists (updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (mkEC (block_intro l' ps' cs' tmn') cs' tmn' lc').
      exists trace_nil. eauto.

    SCase "tmn=br_uncond". 
      right.
      assert (uniqFdef f) as HuniqF. auto.
      assert (exists ps', exists cs', exists tmn',
        Some (block_intro l2 ps' cs' tmn') = lookupBlockViaLabelFromFdef f l2) 
          as HlkB.
        eapply wf_fdef__wf_tmn in HbInF; eauto.
        inv HbInF.        
        exists ps1. exists (cs1++nil). exists (insn_br_uncond i0 l2).
        rewrite H3. 
        apply lookupBlockViaLabelFromFdef_inv in H3; auto.
        destruct H3 as [H3 _]; subst. auto.

      destruct HlkB as [ps' [cs' [tmn' HlkB]]].

      assert (exists lc', switchToNewBasicBlock
        (block_intro l2 ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) lc = 
          Some lc') as Hswitch.
         assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes ps'
             (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) lc =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_fdef__blockInFdefB__wf_block in HwfB; eauto.
           eapply wf_fdef__lookup__wf_block in HlkB; eauto.
           inv HlkB. clear H6 H7.
           eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
             with (l0:=l2); eauto.      
             apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1++nil)
               (tmn:=insn_br_uncond i0 l2); simpl; auto.
             simpl. auto.
             exists nil. auto.
         
         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. 
         exists (updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (mkEC (block_intro l2 ps' cs' tmn') cs' tmn' lc').
      exists trace_nil. eauto.

  Case "cs<>nil".
    assert (wf_insn f 
      (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) (insn_cmd c)) as Hwfc.
      assert (In c (cs1++c::cs)) as H. 
        apply in_or_app. simpl. auto.
      eapply wf_fdef__wf_cmd with (c:=c) in HbInF; eauto.
    remember (inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c) as R.
    destruct R; try solve [inversion Hinscope].
    right.
    destruct c.
  SCase "c=bop".
    assert (exists gv3, BOP lc b v v0 = Some gv3) as Hinsn_bop.
      unfold BOP.      
      assert (exists gv, getOperandValue v lc= Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue v0 lc = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. eauto.
    destruct Hinsn_bop as [gv3 Hinsn_bop].
    exists {|
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_bop i0 b v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv3)
           |}.
     exists trace_nil. eauto.

  SCase "icmp". 
    assert (exists gv2, ICMP lc c v v0 = Some gv2) as Hinsn_icmp.
      unfold ICMP.      
      assert (exists gv, getOperandValue v lc = Some gv) 
        as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue v0 lc = Some gv) 
        as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0. eauto. 

    destruct Hinsn_icmp as [gv2 Hinsn_icmp].
    exists {|
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_icmp i0 c v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2)
            |}.
     exists trace_nil. eauto.
Qed.

End OpsemPP.

(************** Opsem Dominator ******************************************* ***)

Module OpsemDom. 

Export Opsem.
Export OpsemProps.
Import AtomSet.

Definition eval_rhs (lc:GVMap) (c:cmd) : option GenericValue :=
match c with
| insn_bop _ bop0 v1 v2 => BOP lc bop0 v1 v2
| insn_icmp _ cond0 v1 v2 => ICMP lc cond0 v1 v2
end.

Definition wf_GVs (f:fdef) (lc:GVMap) (id1:id) (gvs1:GenericValue) : Prop :=
forall c1, 
  lookupInsnViaIDFromFdef f id1 = Some (insn_cmd c1) -> 
  (eval_rhs lc c1 = Some gvs1 /\
   forall b1, cmdInFdefBlockB c1 f b1 = true -> isReachableFromEntry f b1).

Definition wf_defs (f:fdef)(lc:GVMap)(ids0:list atom) : Prop :=
forall id0 gvs0, 
  In id0 ids0 -> 
  lookupAL _ lc id0 = Some gvs0 -> 
  wf_GVs f lc id0 gvs0.

Lemma wf_defs_eq : forall ids2 ids1 F' lc',
  set_eq _ ids1 ids2 ->
  wf_defs F' lc' ids1 ->
  wf_defs F' lc' ids2.
Proof.
  intros.
  intros id2 gvs1 Hin Hlk.
  destruct H as [J1 J2]. eauto.
Qed.

Export Opsem.

Hint Resolve wf_fdef__uniqFdef.

Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall f  
    lc id1 l3 cs tmn ps lc' gvs b,
  Some lc' = getIncomingValuesForBlockFromPHINodes ps b lc ->
  In id1 (getPhiNodesIDs ps) ->
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_fdef f ->
  lookupAL _ lc' id1 = Some gvs -> 
  wf_GVs f lc id1 gvs.
Proof.
  intros. intros c1 Hin. eapply phinode_isnt_cmd in H1; eauto. inv H1.
Qed.

Export OpsemProps.
Require Import Maps.

Lemma eval_rhs_updateValuesForNewBlock : forall c lc rs,
  (forall i, i `in` dom rs -> ~ In i (getCmdOperands c)) ->
  eval_rhs (updateValuesForNewBlock rs lc) c = eval_rhs lc c.
Proof.
  induction rs; simpl; intros; auto.
    destruct a.
    destruct c; simpl.
      unfold BOP.
      destruct v; destruct v0; simpl in *; auto.
        destruct (id_dec a i1); subst.
          assert (i1 `in` add i1 (dom rs)) as IN. auto.
          apply H in IN. contradict IN; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          destruct (id_dec a i2); subst.
            assert (i2 `in` add i2 (dom rs)) as IN. auto.
            apply H in IN. contradict IN; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec a i1); subst.
          assert (i1 `in` add i1 (dom rs)) as IN. auto.
          apply H in IN. contradict IN; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec a i1); subst.
          assert (i1 `in` add i1 (dom rs)) as IN. auto.
          apply H in IN. contradict IN; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
      unfold ICMP.
      destruct v; destruct v0; simpl in *; auto.
        destruct (id_dec a i1); subst.
          assert (i1 `in` add i1 (dom rs)) as IN. auto.
          apply H in IN. contradict IN; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          destruct (id_dec a i2); subst.
            assert (i2 `in` add i2 (dom rs)) as IN. auto.
            apply H in IN. contradict IN; auto.
            rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec a i1); subst.
          assert (i1 `in` add i1 (dom rs)) as IN. auto.
          apply H in IN. contradict IN; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec a i1); subst.
          assert (i1 `in` add i1 (dom rs)) as IN. auto.
          apply H in IN. contradict IN; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' b
  (Hreach : isReachableFromEntry F b) 
  (Hreach': isReachableFromEntry F (block_intro l' ps' cs' tmn'))
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock (block_intro l' ps' cs' tmn') b lc = ret lc')
  (t : list atom)
  (Hwfdfs : wf_defs F lc t)
  (ids0' : list atom)
  (HwfF : wf_fdef F)
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef F))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = (dom_analyze F) !! l')
  (Hinscope : (fold_left (inscope_of_block F l') contents' 
    (ret (getPhiNodesIDs ps')) = ret ids0'))
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs F lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  intros id1 gvs Hid1 Hlk.
  remember (getIncomingValuesForBlockFromPHINodes ps' b lc) as R1.
  destruct R1 as [rs|]; inv Hswitch.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    apply updateValuesForNewBlock_spec6 in Hlk; auto.
    eapply getIncomingValuesForBlockFromPHINodes_spec1 with (gvs:=gvs) in HeqR1;
      eauto.
      intros c1 Hlkc1. eapply phinode_isnt_cmd in Hlkup; eauto. inv Hlkup.
      eapply getIncomingValuesForBlockFromPHINodes_spec6 in HeqR1; eauto.

    assert (Hnotin' := Hnotin).
    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin. assert (HeqR1':=HeqR1).
    eapply getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1; eauto.
    eapply updateValuesForNewBlock_spec7 in Hlk; eauto.
    apply Hwfdfs in Hlk; auto.
      intros c1 Hlkc1.
      destruct (@Hlk c1) as [Hlkc1' Hreach'']; auto.
      split; auto.
      rewrite <- Hlkc1'; eauto.
      apply eval_rhs_updateValuesForNewBlock.
           intros i0 Hin.
           destruct (in_dec id_dec i0 (getCmdOperands c1)); auto.
           assert (exists b1, wf_insn_base F b1 (insn_cmd c1)) as HwfI.
             eapply wf_fdef__wf_insn_base; eauto.
           destruct HwfI as [b1 HwfI].
           inv HwfI.
           assert (exists n, nth_list_id n id_list = Some i0) as Hnth.
             eapply getCmdOperands__nth_list_id; eauto.
           destruct Hnth as [n Hnth]. 
           eapply wf_operand_list__wf_operand in Hnth; eauto.
           inv Hnth.
           assert (isReachableFromEntry F b1) as Hreachb1.
             apply Hreach'' in H0. auto.
           assert (block_intro l' ps' cs' tmn' = block') as EQ.
             apply getIncomingValuesForBlockFromPHINodes_spec7 with (id1:=i0) 
               in HeqR1'; auto.
             eapply lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq; 
               eauto.
             simpl. apply in_or_app. auto.
           subst.
           destruct b1 as [l0 p c t0].
           assert (In l0 contents') as Hindom'.
             clear - Hlkc1 Hid1 Heqdefs' Hnotin' Hinscope H HwfF.
             apply fold_left__spec in Hinscope.
             destruct Hinscope as [_ [_ Hinscope]].
             apply Hinscope in Hid1.
             destruct Hid1 as [Hid1 | [b1 [l1 [J1 [J2 J3]]]]]; try congruence.
             destruct b1.
             assert (l1 = l2) as EQ.
               apply lookupBlockViaLabelFromFdef_inv in J2; auto.
               destruct J2; auto.
             subst.
             eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2;
               eauto.
             eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H; eauto.
             apply lookupInsnViaIDFromFdef__eqid in Hlkc1. subst.
             simpl in J2. rewrite H in J2. inv J2.
             apply ListSet.set_diff_elim1 in J1; auto.             
           assert (blockInFdefB (block_intro l' ps' cs' tmn') F = true)as HbInF'.
             symmetry in Hlkup.
             apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
             destruct Hlkup; auto.
           assert (l0 <> l') as Hneq.
             clear - HwfF Hindom' Hreach' HbInF' Heqdefs'.
             assert (strict_domination F l0 l') as Hdom12.
               eapply sdom_is_sound; eauto.
                 rewrite <- Heqdefs'. simpl. auto.
             destruct Hdom12; auto.
           assert (blockInFdefB (block_intro l0 p c t0) F = true)as HbInF0.
             eauto using insnInFdefBlockB__blockInFdefB.
           assert (In l' (DomDS.L.bs_contents (bound_fdef F) 
             ((dom_analyze F) !! l0))) as Hindom.
             destruct H7 as [H7 | [H7 | H7]]; try congruence.
               apply insnDominates_spec3 with (F:=F) in H7; auto.
               rewrite H7 in H5. inv H5. congruence.

               clear - H7.
               unfold blockStrictDominates in H7.
               destruct ((dom_analyze F) !! l0); simpl; auto.
           eapply adom_acyclic in Hindom; eauto.
           rewrite <- Heqdefs'. simpl. auto.
Qed.

Lemma isReachableFromEntry_successors : forall f l3 ps cs tmn l' b'
  (Hreach : isReachableFromEntry f (block_intro l3 ps cs tmn))
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Huniq : wf_fdef f)
  (Hsucc : In l' (successors_terminator tmn))
  (Hlkup : lookupBlockViaLabelFromFdef f l' = Some b'),
  isReachableFromEntry f b'.
Proof.
  intros.
  unfold isReachableFromEntry in *. destruct b'.
  apply lookupBlockViaLabelFromFdef_inv in Hlkup; auto.
  destruct Hlkup as [Hlkup _]. subst.
  eapply reachable_successors; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 
  lc lc' (Hreach : isReachableFromEntry F (block_intro l3 ps cs tmn)),
wf_fdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 lc lc' Hreach
    HwfF HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  assert (uniqFdef F) as Huniq. auto.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd, inscope_of_id.
  destruct F as [bs].
  remember (dom_analyze (fdef_intro bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms Huniq HwfF.
    simpl in Huniq.
    eapply dom_successors; eauto.

  assert (isReachableFromEntry (fdef_intro bs) (block_intro l' ps' nil tmn')) 
    as Hreach'.
    eapply isReachableFromEntry_successors in Hlkup; eauto.

  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound').
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil)(bs:=bs)(l0:=l') in J1.
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

      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4; auto.
      
            apply J5 in J9; auto.
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      subst. simpl in J1. simpl_env in J1.   
      eapply wf_defs_br_aux in Hswitch; eauto.
        
  Case "cs'<>nil".
    assert (J1:=inbound').
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n]; 
      try solve [contradict n; auto].
    simpl_env.
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps')(bs:=bs)
      (l0:=l') in J1.
    destruct J1 as [r J1].
    exists r.  split; auto.

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
        contradict J; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. 
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4; auto.
      
            apply J5 in J9; auto. 
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      subst. eapply wf_defs_br_aux in Hswitch; eauto.
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs ids0 l' ps' cs' tmn' l0 
  lc lc' bid,
isReachableFromEntry F (block_intro l3 ps cs (insn_br_uncond bid l0)) ->
wf_fdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c lc lc',
isReachableFromEntry F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) ->
wf_fdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) lc = Some lc' ->
wf_defs F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs F lc' ids0'.
Proof.
  intros.
  remember (isGVZero c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Lemma state_tmn_typing : forall f l1 ps1 cs1 tmn1 defs id1 lc gv,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs f lc defs ->
  wf_fdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  lookupAL _ lc id1 = Some gv ->
  wf_GVs f lc id1 gv /\ In id1 defs.
Proof.
  intros f l1 ps1 cs1 tmn1 defs id1 lc gv Hreach HwfInstr Hinscope 
    HwfDefs HuniqF HinOps Hlkup.
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
    rewrite H1 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=block_intro l1 ps1 cs1 tmn1)
    (insn1:=insn_terminator tmn1)(id1:=id1) in H2; auto.

  assert (In id1 defs) as Hin.
    inv H2.
    unfold inscope_of_tmn in Hinscope.
    destruct f.
    remember ((dom_analyze (fdef_intro b)) !! l1) as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H7 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      destruct J' as [J' _].
      destruct J' as [[cs2 [c1' [cs3 [J1 J2]]]] | [ps2 [p1 [ps3 [J1 J2]]]]]; 
        subst.
        rewrite getCmdsIDs_app. simpl. rewrite J2.
        apply in_or_app. right.
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
        lookupBlockViaLabelFromFdef (fdef_intro b) l0 =
        ret block_intro l0 p c t) as J1.
        apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
          eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
      apply Hinscope with (b1:=block_intro l0 p c t) in J; auto.
        apply J.
        eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
  auto.
Qed.

Lemma state_cmd_typing : forall f b c defs id1 lc gv,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs f lc defs ->
  wf_fdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  lookupAL _ lc id1 = Some gv ->
  wf_GVs f lc id1 gv /\ In id1 defs.
Proof.
  intros f b c defs id1 lc gv Hnodup Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps Hlkup.
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
    rewrite H1 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=b)(insn1:=insn_cmd c)(id1:=id1) 
    in H2; auto.

  assert (In id1 defs) as Hin.
    inv H2. 
    unfold inscope_of_cmd, inscope_of_id in Hinscope.
    destruct b. destruct f.
    remember ((dom_analyze (fdef_intro b)) !! l0) as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H7 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      simpl in J'.
      destruct J' as [[ps2 [p1 [ps3 [J1 J2]]]] | [cs1 [c1' [cs2 [cs3 [J1 J2]]]]]]
        ; subst.

        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
        clear - J2 Hnodup.
        apply in_or_app. right.
          simpl in Hnodup. apply NoDup_inv in Hnodup.
          destruct Hnodup as [_ Hnodup].
          apply NoDup_inv in Hnodup.
          destruct Hnodup as [Hnodup _].
          rewrite_env ((cs1 ++ c1' :: cs2) ++ c :: cs3).
          rewrite_env ((cs1 ++ c1' :: cs2) ++ c :: cs3) in Hnodup.
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
        lookupBlockViaLabelFromFdef (fdef_intro b) l1
          = ret block_intro l1 p0 c1 t0) as J1.
        apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
          eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
      apply Hinscope with (b1:=block_intro l1 p0 c1 t0) in J; auto.
        apply J.
        eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
  auto.
Qed.
 
(*********************************************)
(** * Preservation *)

Definition wf_ExecutionContext (f:fdef) (ec:ExecutionContext) : Prop :=
let '(mkEC b cs tmn lc) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
wf_fdef f /\
match cs with
| nil => 
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs f lc ids
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs f lc ids
    | None => False
    end
end /\
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Lemma wf_State__inv : forall F B c cs tmn lc,
  wf_ExecutionContext F (mkEC B (c::cs) tmn lc) ->
  wf_insn F B (insn_cmd c).
Proof.
  intros.
  destruct H as 
    [Hreach1 [HBinF1 [HwfF [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]; subst.
  eapply wf_fdef__wf_cmd; eauto using in_middle.
Qed.  

Lemma eval_rhs_updateAddAL : forall id1 gvs1 c lc,
  ~ In id1 (getCmdOperands c) ->
  eval_rhs (updateAddAL GenericValue lc id1 gvs1) c = eval_rhs lc c.
Proof.
  destruct c; simpl; intros.
    unfold BOP.    
    destruct v; destruct v0; simpl in *; auto.
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec id1 i2); subst.
          contradict H; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
    unfold ICMP.    
    destruct v; destruct v0; simpl in *; auto.
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        destruct (id_dec id1 i2); subst.
          contradict H; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
      destruct (id_dec id1 i1); subst.
        contradict H; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma wf_defs_updateAddAL : forall g1 lc' ids1 ids2 F1 B1 l3 ps1 
  cs tmn1 c (HinCs: In c cs)
  (Hreach: isReachableFromEntry F1 (block_intro l3 ps1 cs tmn1))
  (HBinF1: blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true)
  (HBinF2: blockInFdefB B1 F1 = true)
  (HwfF1 : wf_fdef F1) (HcInB : cmdInBlockB c B1 = true)
  (Hinscope : ret ids1 = inscope_of_id F1 B1 (getCmdLoc c)),
  wf_defs F1 lc' ids1 ->
  set_eq _ (getCmdLoc c::ids1) ids2 ->
  wf_GVs F1 lc' (getCmdLoc c) g1 ->
  wf_defs F1 (updateAddAL _ lc' (getCmdLoc c) g1) ids2.
Proof.
  intros g1 lc' ids1 ids2 F1 B1 l3 ps1 cs tmn1 c HinCs Hreach HBinF1 
    HBinF2 HwfF1 HcInB HInscope HwfDefs Heq Hwfgvs.
  intros id1 gvs1 Hin Hlk.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  intros c1 Hlkc1.
  assert (id1 = getCmdLoc c1) as EQ.
    apply lookupInsnViaIDFromFdef__eqid in Hlkc1. simpl in Hlkc1. auto.
  subst.
  assert (J:=Hlkc1).
  apply wf_fdef__wf_insn_base in J; auto.
  destruct J as [b1 HwfI].
  inv HwfI.
  destruct (eq_dec (getCmdLoc c) (getCmdLoc c1)).
  Case "1".
    rewrite e in *.
    rewrite lookupAL_updateAddAL_eq in Hlk; auto.  
    inv Hlk.
    destruct (@Hwfgvs c1) as [Heval Hreach']; auto.
    split; auto.
    rewrite <- Heval; auto.
    apply eval_rhs_updateAddAL.
    destruct (in_dec id_dec (getCmdLoc c1) (getCmdOperands c1)); auto.
    assert (exists n, nth_list_id n id_list = Some (getCmdLoc c1)) as Hnth.
      eapply getCmdOperands__nth_list_id; eauto.
    destruct Hnth as [n Hnth]. 
    eapply wf_operand_list__wf_operand in Hnth; eauto.
    inv Hnth.
    assert (b1 = block') as EQ.
      eapply insnInFdefBlockB__lookupBlockViaIDFromFdef__eq; eauto.
    subst.
    clear - Hinc1 HInscope H7 Hreach HinCs HwfF1 HBinF1 Hreach' H0 H.
    apply Hreach' in H0.
    destruct H7 as [H7 | [H7 | H7]]; auto.
      contradict H7. 
         assert (H':=H).
         apply insnInFdefBlockB__blockInFdefB in H'.
         apply uniqFdef__uniqBlockLocs in H'; auto.
         apply insnInFdefBlockB__insnInBlockB in H.
         apply insnDominates_spec1; auto.
      contradict H7. 
      apply insnInFdefBlockB__blockInFdefB in H.
      apply blockStrictDominates_isnt_refl; auto.

  Case "2".
    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
    assert (Hlk':=Hlk).
    apply HwfDefs in Hlk; auto.
    destruct (@Hlk c1) as [Heval Hreach']; auto.
    split; auto.
    rewrite <- Heval; eauto.
    apply eval_rhs_updateAddAL.
    destruct (in_dec id_dec (getCmdLoc c) (getCmdOperands c1)); auto.
    assert (exists n, nth_list_id n id_list = Some (getCmdLoc c)) as Hnth.
      eapply getCmdOperands__nth_list_id; eauto.
    destruct Hnth as [n' Hnth]. 
    eapply wf_operand_list__wf_operand in Hnth; eauto.
    inv Hnth.
    clear - HInscope Hin H7 Hreach HinCs H0 HwfF1 HBinF1 HBinF2 Hreach' H5 
      HcInB n H.
    assert (isReachableFromEntry F1 b1) as Hreach''.
      apply Hreach' in H0; auto.
    destruct b1 as [l0 p c0 t]. 
    destruct B1 as [l1 p0 c2 t0]. simpl in HInscope.
    remember ((dom_analyze F1) !! l1) as R.
    destruct R.
    assert (block' = block_intro l3 ps1 cs tmn1) as RQ.
      clear - HinCs HBinF1 H5 HwfF1 Hin.
      symmetry.
      eapply lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq; eauto.
        symmetry.
        apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
        simpl. apply in_or_app. right. apply in_or_app.
        left. apply getCmdLoc_in_getCmdsLocs; auto.
    subst.
    destruct H7 as [H7 | [H7 | H7]]; auto.
    SCase "1".
      assert (block_intro l1 p0 c2 t0 = block_intro l0 p c0 t) as EQ.
        apply insnInFdefBlockB__blockInFdefB in H0.
        eapply cmdInBlockB_eqBlock with (c:=c); eauto.
        eapply insnDominates_spec5 in H7; eauto.
        rewrite H7 in H5. inv H5. simpl. apply In_InCmdsB; auto.
      inv EQ.
      assert (insnDominates (getCmdLoc c1) (insn_cmd c) (block_intro l0 p c0 t))
        as Hdom.
        clear - Hin HInscope HcInB H HwfF1. 
        symmetry in HInscope.
        apply fold_left__spec in HInscope. 
        destruct HInscope as [_ [_ HInscope]].
        apply HInscope in Hin. clear HInscope.
        destruct Hin as [Hin | [b1 [l1 [J1 [J2 J3]]]]].
        SSCase "1".
          simpl in HcInB. apply InCmdsB_in in HcInB.
          eapply cmds_dominates_cmd__insnDominates; eauto.

        SSCase "2".
          destruct b1.
          assert (l1 = l2) as EQ.
            apply lookupBlockViaLabelFromFdef_inv in J2; auto.
            destruct J2; auto.
          subst.
          eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2; 
            eauto.
          eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H; eauto.
          rewrite H in J2. inv J2.          
          apply ListSet.set_diff_elim2 in J1. contradict J1; simpl; auto.

      apply insnDominates_spec2 in Hdom; try solve [simpl; auto].
        eapply uniqFdef__uniqBlockLocs; eauto.
        eapply insnDominates_spec5 in Hdom; eauto.
        apply insnInFdefBlockB__insnInBlockB in H; auto.

    SCase "2".
      assert (block_intro l1 p0 c2 t0 = block_intro l3 ps1 cs tmn1) as EQ.
        apply In_InCmdsB in HinCs.
        eapply cmdInBlockB_eqBlock; eauto.
      inv EQ.
      assert (l0 <> l3) as Hneq.
        simpl in H7.
        remember ((dom_analyze F1) !! l0) as R. 
        destruct R.
        simpl in Hreach''. apply insnInFdefBlockB__blockInFdefB in H.
        eapply sdom_isnt_refl with (l':=l3) in Hreach''; eauto.
          rewrite <- HeqR0. simpl. auto.

      assert (In l0 bs_contents) as Hindom'.
        clear - H0 HeqR HInscope Hin Hneq HBinF1 HwfF1. 
        symmetry in HInscope.
        apply fold_left__spec in HInscope.
        destruct HInscope as [_ [_ HInscope]].
        apply HInscope in Hin.
        destruct Hin as [Hid1 | [b1 [l1 [J1 [J2 J3]]]]].
          clear - HBinF1 H0 Hid1 Hneq HwfF1.
          apply InGetBlockIDs__lookupBlockViaIDFromFdef with (i0:=getCmdLoc c1) 
            in HBinF1; auto.
            apply insnInFdefBlockB__lookupBlockViaIDFromFdef in H0; auto.
            rewrite H0 in HBinF1. inv HBinF1. congruence.

            simpl.
            apply cmds_dominates_cmd_spec' in Hid1; auto.

          destruct b1.
          assert (l1 = l2) as EQ.
            apply lookupBlockViaLabelFromFdef_inv in J2; auto.
            destruct J2; auto.
          subst.
          eapply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef in J2;
            eauto.
          eapply insnInFdefBlockB__lookupBlockViaIDFromFdef in H0; eauto.
          rewrite H0 in J2. inv J2.
          apply ListSet.set_diff_elim1 in J1; auto.             

      assert (In l3 (DomDS.L.bs_contents (bound_fdef F1) 
             ((dom_analyze F1) !! l0))) as Hindom.       
        clear - H7.
        unfold blockStrictDominates in H7.
        destruct ((dom_analyze F1) !! l0). simpl. auto.
      apply insnInFdefBlockB__blockInFdefB in H0.
      eapply adom_acyclic in Hindom; eauto.
      rewrite <- HeqR. simpl. auto.
Qed. 

Lemma preservation_cmd_updated_case : forall
  (F : fdef)
  (B : block)
  (lc : GVMap)
  (gv3 : GenericValue)
  (cs : list cmd)
  (tmn : terminator)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  (Hwfgv : wf_GVs F lc id0 gv3)
  (HwfS1 : wf_ExecutionContext F
            {| CurBB := B;
               CurCmds := c0 :: cs;
               Terminator := tmn;
               Locals := lc
            |}),
   wf_ExecutionContext F
     {| CurBB := B;
        CurCmds := cs;
        Terminator := tmn;
        Locals := updateAddAL _ lc id0 gv3
     |}.
Proof.
  intros.
  destruct HwfS1 as 
     [Hreach1 [HBinF1 [HwfF1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]];
     subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  assert (HeqR1':=HeqR1).
  unfold inscope_of_cmd in HeqR1'.
  assert (uniqFdef F) as HuniqF. auto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
      subst.
      assert (cmdInBlockB c0 (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) = true) 
        as Hin.
        simpl. apply In_InCmdsB. apply in_middle.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs3')) as Hnotin.
          eapply wf_fdef__uniq_block with (f:=F) in HwfF1; eauto.        
          simpl in HwfF1.
          apply NoDup_inv in HwfF1.
          destruct HwfF1 as [_ J].
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
        eapply wf_fdef__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL; eauto.
 
      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_fdef__uniq_block with (f:=F) in HwfF1; eauto.        
          simpl in HwfF1.
          apply NoDup_inv in HwfF1.
          destruct HwfF1 as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_fdef__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma BOP__wf_gvs : forall
  (F1 : fdef) (v : value) (v0 : value) lc
  (id1 : id) (bop0 : bop) gvs3
  (H11 : BOP lc bop0 v v0 = ret gvs3)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1 
    (block_intro l3 ps1 (cs1' ++ insn_bop id1 bop0 v v0 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_bop id1 bop0 v v0 :: cs1) tmn1)
           F1 = true),
  wf_GVs F1 lc id1 gvs3.
Proof.
  intros. 
  destruct F1 as [bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 = 
    Some (insn_cmd (insn_bop id1 bop0 v v0))) as Hlk1.
    inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_bop id1 bop0 v v0) as EQ. 
    simpl in *. rewrite Hlkc1 in Hlk1. inv Hlk1. auto.
  subst. 
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_bop id1 bop0 v v0 :: cs1) tmn1 
      = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma ICMP__wf_gvs : forall
  (F1 : fdef) (v : value) (v0 : value) lc
  (id1 : id) (cnd0 : cond) gvs3
  (H11 : ICMP lc cnd0 v v0 = ret gvs3)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hreach: isReachableFromEntry F1 
    (block_intro l3 ps1 (cs1' ++ insn_icmp id1 cnd0 v v0 :: cs1) tmn1))
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_icmp id1 cnd0 v v0 :: cs1) tmn1)
           F1 = true),
  wf_GVs F1 lc id1 gvs3.
Proof.
  intros. 
  destruct F1 as [bs1].
  assert (lookupInsnViaIDFromBlocks bs1 id1 = 
    Some (insn_cmd (insn_icmp id1 cnd0 v v0))) as Hlk1.
    inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  intros c1 Hlkc1.
  assert (c1 = insn_icmp id1 cnd0 v v0) as EQ. 
    simpl in *. rewrite Hlkc1 in Hlk1. inv Hlk1. auto.
  subst.
  split; auto.
    intros.
    assert (block_intro l3 ps1 (cs1' ++ insn_icmp id1 cnd0 v v0 :: cs1) tmn1 
      = b1) as EQ.
      eapply blockInFdefB__cmdInFdefBlockB__eqBlock; eauto using in_middle.
    subst. auto.
Qed.

Lemma preservation : forall F S1 S2 tr,
  sInsn F S1 S2 tr -> wf_ExecutionContext F S1 -> wf_ExecutionContext F S2.
Proof.
  intros F S1 S2 tr HsInsn HwfS1.
  (sInsn_cases (induction HsInsn) Case);
  assert (HwfS1':=HwfS1);
  destruct HwfS1' as 
     [Hreach1 [HBinF1 [HwfF [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]; subst.
Focus.
Case "sBranch".
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
    assert (HuniqF := HwfF). 
    eapply wf_fdef__uniqFdef with (f:=F) in HuniqF; eauto.
    split; auto.
      clear - Hreach1 H0 HBinF1 HwfF HuniqF.
      symmetry in H0.
      destruct (isGVZero c);
        eapply isReachableFromEntry_successors in H0; 
          try solve [eauto | simpl; auto].
    split. 
      clear - H0 HBinF1 HwfF HuniqF.
      symmetry in H0.
      destruct (isGVZero c);
        apply lookupBlockViaLabelFromFdef_inv in H0; 
          try solve [auto | destruct H0; auto].
    split; auto.
    split.
      clear - H0 HeqR1 H1 Hinscope1 HBinF1 HwfF HuniqF Hreach1.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "sBranch_uncond".
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
    assert (HuniqF := HwfF).
    eapply wf_fdef__uniqFdef with (f:=F) in HuniqF; eauto.
    split; auto.
      symmetry in H.
      eapply isReachableFromEntry_successors in H; 
        try solve [eauto | simpl; auto].
    split.
      clear - H HBinF1 HwfF HuniqF.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
        destruct H; auto.
    split; auto.
    split.
      clear - H0 HeqR1 Hinscope1 H HBinF1 HwfF HuniqF Hreach1.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "sBop". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply BOP__wf_gvs; eauto.
Case "sIcmp". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  eapply ICMP__wf_gvs; eauto.
Qed.

End OpsemDom.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
