Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import Values.
Require Import vellvm.
Require Import trace.
Require Import Memory.
Require Import alist.
Require Import Integers.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import genericvalues.
Require Import dopsem.
Require Import sb_def.
Require Import sb_ds_trans.
Require Import sb_msim.
Require Import sb_ds_gv_inject.
Require Import sb_ds_sim.
Require Import sb_ds_trans_axioms.
Require Import sb_ds_trans_lib.
Require Import sb_ds_trans_tactics.

Import SB_ds_pass.
Export SBspec.

Definition base2GV := blk2GV.
Definition bound2GV (TD:TargetData) (b:mblock) (s:sz) n : GenericValue :=
((Vptr b (Int.repr 31 ((Size.to_Z s)*n)), AST.Mint 31)::nil).

Ltac inv_trans_cmd :=
  repeat match goal with
  | Htcmd: match lookupAL (id * id) ?rm2 ?id0 with
       | munit _ => _
       | merror => _ 
       end = Some _ |- _ => 
    let bid := fresh "bid" in
    let eid := fresh "eid" in
     remember (lookupAL (id * id) rm2 id0) as R1;
     destruct R1 as [[bid eid]|]; try solve [inversion Htcmd]
  | Htcmd : context [ let '(_, _) := mk_tmp ?exids in _ ] |- _ =>
    let tmp := fresh "tmp" in
    let ex_ids := fresh "ex_ids" in
    remember (mk_tmp exids) as R9;
    destruct R9 as [tmp ex_ids]
  | Htcmd : Some _ = Some _ |- _ => inv Htcmd
  end.

Notation "$ gv # t $" := (DGVs.(gv2gvs) gv t) (at level 41).

Lemma SBpass_is_correct__dsMalloc : forall (mi : meminj) (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : AssocList SBspecAux.metadata)
  (gl : GVMap) (fs : GVMap) (id0 : atom) (t : typ) (v : value) (align0 : align)
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           SBspec.ECS := {|
                          SBspec.CurFunction := F;
                          SBspec.CurBB := B;
                          SBspec.CurCmds := insn_malloc id0 t v align0 :: cs;
                          SBspec.Terminator := tmn;
                          SBspec.Locals := lc;
                          SBspec.Rmap := rm;
                          SBspec.Allocas := als |} :: EC;
           SBspec.Mem := Mem;
           SBspec.Mmap := MM |} Cfg St)
  (gn : GenericValue) (Mem' : mem) (tsz : sz) (mb : mblock) (lc' : DGVMap)
  (rm' : SBspecAux.rmetadata) (n : Z) (H : getTypeAllocSize TD t = ret tsz)
  (H0 : getOperandValue TD v lc gl = ret gn) 
  (H1 : malloc TD Mem tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : SBspec.prop_reg_metadata lc rm id0 (blk2GV TD mb) (bound2MD mb tsz n) 
          = (lc', rm')),
  exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         SBspec.ECS := {|
                        SBspec.CurFunction := F;
                        SBspec.CurBB := B;
                        SBspec.CurCmds := cs;
                        SBspec.Terminator := tmn;
                        SBspec.Locals := lc';
                        SBspec.Rmap := rm';
                        SBspec.Allocas := als |} :: EC;
         SBspec.Mem := Mem';
         SBspec.Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  inv_trans_cmd.
  invert_prop_reg_metadata.
  assert (Hmalloc:=H1).
  apply mem_simulation__malloc with (MM:=MM)(mgb:=mgb)(Mem2:=M2)(mi:=mi) in H1;
    auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H16 [H12 [H13 [H14 H15]]]]]]]].

  eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H0; eauto.
  destruct H0 as [gn' [H00 H01]].
  assert (GV2int (los, nts) Size.ThirtyTwo gn = 
    GV2int (los, nts) Size.ThirtyTwo gn') as Heqgn.
    eapply simulation__eq__GV2int; eauto.

  match goal with
  | |- context [insn_cast ?tmp _ _ _ _ :: insn_malloc ?id0 _ _ _ ::
                insn_gep ?tmp0 _ _ _ _ ::
                insn_cast ?bid _ _ _ _ :: insn_cast ?eid _ _ _ _ :: _] =>
  exists (Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
               (updateAddALs _ lc2
                       ((tmp, gn')::
                        (id0, ($ (blk2GV (los, nts) mb') # typ_pointer t $))::
                        (tmp0, (bound2GV (los, nts) mb' tsz n))::
                        (bid, (base2GV (los, nts) mb'))::
                        (eid, (bound2GV (los, nts) mb' tsz n))::nil))
             als2):: 
            ECs2) Mem2')
  end.
  exists mi'.

  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eauto using getCmdID_in_getFdefLocs.
  assert (Hspec := Hgenmeta).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].

  assert (id_fresh_in_value v tmp) as Hfresh_ctmp.
    assert (Hwfc := HBinF).
    destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
    eapply wf_system__wf_cmd in Hwfc; eauto using in_middle.
      inv Hwfc. 
      eapply wf_value_id__in_getFdefLocs in H19; auto.
        eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

  assert (tmp <> id0) as Hntmp_neq_id0.
    apply tmp_is_fresh2 with (i0:=id0)(d:=getFdefLocs (fdef_intro fh1 bs1)) 
      (ex_ids1:=ex_ids) in HeqR9; auto.
  assert (bid <> tmp /\ eid <> tmp) as Hntmp'.
    eapply tmp_is_fresh3 with (bid:=bid)(eid:=eid)(ex_ids1:=ex_ids) in HeqR9; 
      eauto.
  destruct Hntmp' as [Hntmpb Hntmpe].
  assert (tmp0 <> tmp) as Hneq''.
    unfold mk_tmp in *.
    destruct (atom_fresh_for_list ex_ids3).
    destruct (atom_fresh_for_list ex_ids0).
    inv HeqR9. inv HeqR0. 
    simpl in n1. intro J. subst. auto.
 
  assert (incl ex_ids ex_ids0) as Hinc'.
    eapply mk_tmp_inc in HeqR9; eauto.
  assert (incl ex_ids ex_ids5) as Hinc''.
    eapply mk_tmp_inc in HeqR9; eauto.
    eapply mk_tmp_inc in HeqR0; eauto.
 
  split.
  SCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.
      eapply Opsem.sCast; eauto.        
        unfold Opsem.CAST. simpl. 
        replace (@getOperandValue DGVs) with LLVMgv.getOperandValue; auto.
        rewrite H00. unfold i32, mbitcast. auto.

    next_insn.
      unfold malloc in H11.
      rewrite Heqgn in H11; eauto.
      match goal with
      | |- context [insn_malloc] =>
        eapply Opsem.sMalloc; eauto
      | |- context [insn_alloca] =>
        eapply Opsem.sAlloca; eauto
      end.
        rewrite <- getOperandValue_eq_fresh_id; auto.

    next_insn.
      eapply Opsem.sGEP with (mp:=blk2GV (los,nts) mb')(vidxs:=[gn']); eauto.
        simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

        assert(getOperandValue (los,nts) (value_id tmp)
          (updateAddAL _ (updateAddAL _ lc2 tmp gn') id0 
          ($ blk2GV (los, nts) mb' # typ_pointer t $)) gl2 = Some gn') as EQ'.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          simpl. apply lookupAL_updateAddAL_eq; auto.
        
        simpl. simpl in EQ'.
        rewrite EQ'. clear EQ'.
        auto.

        Local Transparent lift_op1.
        unfold bound2GV, Opsem.GEP, blk2GV, GV2ptr, ptr2GV, 
          val2GV, gep, lift_op1, LLVMgv.GEP. simpl. unfold MDGVs.lift_op1.
        simpl.
        rewrite <- Heqgn. rewrite H2.
        unfold Constant.typ2utyp.
        assert (exists ut, 
          Constant.typ2utyp_aux (Constant.subst_nts_by_nts nts nts) 
            (typ_array 0%nat t) = Some (typ_array 0%nat ut) /\
          getTypeAllocSize (los, nts) ut = getTypeAllocSize (los, nts) t) as EQ1.
          destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
          eapply wf_system__wf_cmd in HBinF; eauto using in_middle.
            inv HBinF. inv H23.
            simpl. destruct H0 as [J3 J4].
            unfold Constant.typ2utyp in J3.
            rewrite J3. simpl. eauto.

        destruct EQ1 as [ut [EQ1 EQ2]].
        unfold mgetoffset. simpl. rewrite H.
        rewrite Int.add_commut.
        rewrite Int.add_zero. auto.

    next_insn.
      apply Opsem.sCast; auto.
        unfold Opsem.CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR0 Hinc1 Hinc' Hin.
          eapply tmp_is_fresh2 with (d:=getFdefLocs (fdef_intro fh1 bs1)); eauto.
 
    next_insn.
      apply Opsem.sCast; auto.
        unfold Opsem.CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR0 Hinc3 Hinc' HeqR1.
          eapply tmp_is_fresh3 with (tmp:=tmp0) in HeqR1; eauto.
          destruct HeqR1; auto.

  repeat (split; eauto 2 using inject_incr__preserves__als_simulation,
                              cmds_at_block_tail_next, cmds_at_block_tails_next,
                              inject_incr__preserves__sbECs_simulate_ECs_tail,
                              inject_incr__preserves__fable_simulation).
    exists ex_ids. exists rm2.
    exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
    repeat (
      match goal with
      | |- _ /\ _ => split; auto
      | |- context [reg_simulation] => idtac 
      end).
    unfold base2GV, bound2GV, blk2GV, ptr2GV, val2GV.
    Local Transparent updateAddALs gv2gvs. simpl. unfold MDGVs.gv2gvs.
    eapply reg_simulation__updateAddAL_md; eauto.
      eapply reg_simulation__updateAddAL_tmp with (ex_ids5:=ex_ids5)
        (ex_ids3':=ex_ids0); eauto.
      eapply reg_simulation__updateAddAL_lc; eauto.
      eapply reg_simulation__updateAddAL_tmp with (ex_ids5:=ex_ids0)
        (ex_ids3':=ex_ids3); eauto.
        eapply inject_incr__preserves__reg_simulation; eauto.
        match goal with
        | H : mi' mb = Some (_, _) |- _ => clear - H
        end.
        apply gv_inject_cons; eauto.
          eapply MoreMem.val_inject_ptr; eauto.
            rewrite Int.add_zero. auto.
Opaque gv2gvs lift_op1.
Qed.

Lemma SBpass_is_correct__dsAlloca : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : AssocList metadata) (gl : GVMap) (fs : GVMap) (id0 : atom) (t : typ)  
  (v : value) (align0 : align) (EC : list ExecutionContext) (cs : list cmd)
  (tmn : terminator) (Mem0 : mem) (MM : mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_alloca id0 t v align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gn : GenericValue) (Mem' : mem) (tsz : sz) (mb : mblock) (lc' : DGVMap)
  (rm' : rmetadata) (n : Z) (H : getTypeAllocSize TD t = ret tsz)
  (H0 : getOperandValue TD v lc gl = ret gn) 
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : prop_reg_metadata lc rm id0 (blk2GV TD mb) (bound2MD mb tsz n) =
       (lc', rm')),
  exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := mb :: als |} :: EC;
         Mem := Mem';
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  inv_trans_cmd.
  invert_prop_reg_metadata.
  assert (Hmalloc:=H1).
  apply mem_simulation__malloc with (MM:=MM)(mgb:=mgb)(Mem2:=M2)(mi:=mi) in H1;
    auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H16 [H12 [H13 [H14 H15]]]]]]]].

  eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H0; eauto.
  destruct H0 as [gn' [H00 H01]].
  assert (GV2int (los, nts) Size.ThirtyTwo gn = 
    GV2int (los, nts) Size.ThirtyTwo gn') as Heqgn.
    eapply simulation__eq__GV2int; eauto.

  match goal with
  | |- context [insn_cast ?tmp _ _ _ _ :: insn_alloca ?id0 _ _ _ ::
                insn_gep ?tmp0 _ _ _ _ ::
                insn_cast ?bid _ _ _ _ :: insn_cast ?eid _ _ _ _ :: _] =>
  exists (Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
               (updateAddALs _ lc2
                       ((tmp, gn')::
                        (id0, ($ (blk2GV (los, nts) mb') # typ_pointer t $))::
                        (tmp0, (bound2GV (los, nts) mb' tsz n))::
                        (bid, (base2GV (los, nts) mb'))::
                        (eid, (bound2GV (los, nts) mb' tsz n))::nil))
            (mb'::als2)):: 
            ECs2) Mem2')
  end.
  exists mi'.

  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eauto using getCmdID_in_getFdefLocs.
  assert (Hspec := Hgenmeta).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].

  assert (id_fresh_in_value v tmp) as Hfresh_ctmp.
    assert (Hwfc := HBinF).
    destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
    eapply wf_system__wf_cmd in Hwfc; eauto using in_middle.
      inv Hwfc. 
      eapply wf_value_id__in_getFdefLocs in H17; auto.
        eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

  assert (tmp <> id0) as Hntmp_neq_id0.
    apply tmp_is_fresh2 with (i0:=id0)(d:=getFdefLocs (fdef_intro fh1 bs1)) 
      (ex_ids1:=ex_ids) in HeqR9; auto.
  assert (bid <> tmp /\ eid <> tmp) as Hntmp'.
    eapply tmp_is_fresh3 with (bid:=bid)(eid:=eid)(ex_ids1:=ex_ids) in HeqR9; 
      eauto.
  destruct Hntmp' as [Hntmpb Hntmpe].
  assert (tmp0 <> tmp) as Hneq''.
    unfold mk_tmp in *.
    destruct (atom_fresh_for_list ex_ids3).
    destruct (atom_fresh_for_list ex_ids0).
    inv HeqR9. inv HeqR0. 
    simpl in n1. intro J. subst. auto.
 
  assert (incl ex_ids ex_ids0) as Hinc'.
    eapply mk_tmp_inc in HeqR9; eauto.
  assert (incl ex_ids ex_ids5) as Hinc''.
    eapply mk_tmp_inc in HeqR9; eauto.
    eapply mk_tmp_inc in HeqR0; eauto.
 
  split.
  SCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.
      eapply Opsem.sCast; eauto.        
        unfold Opsem.CAST. simpl. 
        replace (@getOperandValue DGVs) with LLVMgv.getOperandValue; auto.
        rewrite H00. unfold i32, mbitcast. auto.

    next_insn.
      unfold malloc in H11.
      rewrite Heqgn in H11; eauto.
      match goal with
      | |- context [insn_malloc] =>
        eapply Opsem.sMalloc; eauto
      | |- context [insn_alloca] =>
        eapply Opsem.sAlloca; eauto
      end.
        rewrite <- getOperandValue_eq_fresh_id; auto.

    next_insn.
      eapply Opsem.sGEP with (mp:=blk2GV (los,nts) mb')(vidxs:=[gn']); eauto.
        simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

        assert(getOperandValue (los,nts) (value_id tmp)
          (updateAddAL _ (updateAddAL _ lc2 tmp gn') id0 
          ($ blk2GV (los, nts) mb' # typ_pointer t $)) gl2 = Some gn') as EQ'.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          simpl. apply lookupAL_updateAddAL_eq; auto.
        
        simpl. simpl in EQ'.
        rewrite EQ'. clear EQ'.
        auto.

        Local Transparent lift_op1.
        unfold bound2GV, Opsem.GEP, blk2GV, GV2ptr, ptr2GV, 
          val2GV, gep, lift_op1, LLVMgv.GEP. simpl. unfold MDGVs.lift_op1.
        simpl.
        rewrite <- Heqgn. rewrite H2.
        unfold Constant.typ2utyp.
        assert (exists ut, 
          Constant.typ2utyp_aux (Constant.subst_nts_by_nts nts nts) 
            (typ_array 0%nat t) = Some (typ_array 0%nat ut) /\
          getTypeAllocSize (los, nts) ut = getTypeAllocSize (los, nts) t) as EQ1.
          destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
          eapply wf_system__wf_cmd in HBinF; eauto using in_middle.
            inv HBinF. inv H23.
            simpl. destruct H0 as [J3 J4].
            unfold Constant.typ2utyp in J3.
            rewrite J3. simpl. eauto.

        destruct EQ1 as [ut [EQ1 EQ2]].
        unfold mgetoffset. simpl. rewrite H.
        rewrite Int.add_commut.
        rewrite Int.add_zero. auto.

    next_insn.
      apply Opsem.sCast; auto.
        unfold Opsem.CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR0 Hinc1 Hinc' Hin.
          eapply tmp_is_fresh2 with (d:=getFdefLocs (fdef_intro fh1 bs1)); eauto.
 
    next_insn.
      apply Opsem.sCast; auto.
        unfold Opsem.CAST. simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.

          clear - HeqR0 Hinc3 Hinc' HeqR1.
          eapply tmp_is_fresh3 with (tmp:=tmp0) in HeqR1; eauto.
          destruct HeqR1; auto.

  repeat (split; eauto 2 using inject_incr__preserves__als_simulation,
                              cmds_at_block_tail_next, cmds_at_block_tails_next,
                              inject_incr__preserves__sbECs_simulate_ECs_tail,
                              inject_incr__preserves__fable_simulation).
    exists ex_ids. exists rm2.
    exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
    repeat (
      match goal with
      | |- _ /\ _ => split; auto
      | |- context [reg_simulation] => idtac 
      end).
    unfold base2GV, bound2GV, blk2GV, ptr2GV, val2GV.
    Transparent updateAddALs gv2gvs. simpl. unfold MDGVs.gv2gvs.
    eapply reg_simulation__updateAddAL_md; eauto.
      eapply reg_simulation__updateAddAL_tmp with (ex_ids5:=ex_ids5)
        (ex_ids3':=ex_ids0); eauto.
      eapply reg_simulation__updateAddAL_lc; eauto.
      eapply reg_simulation__updateAddAL_tmp with (ex_ids5:=ex_ids0)
        (ex_ids3':=ex_ids3); eauto.
        eapply inject_incr__preserves__reg_simulation; eauto.
        match goal with
        | H : mi' mb = Some (_, _) |- _ => clear - H
        end.
        apply gv_inject_cons; eauto.
          eapply MoreMem.val_inject_ptr; eauto.
            rewrite Int.add_zero. auto.
Opaque gv2gvs lift_op1.
Qed.

Lemma SBpass_is_correct__dsFree : forall (mi : MoreMem.meminj)
  (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : rmetadata) (gl : GVMap)
  (fs : GVMap) (fid : id) (t : typ) (v : value) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (als : list mblock)
  (MM : mmetadata) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_free fid t v :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (Mem' : mem)
  (mptr0 : GenericValue)
  (H : getOperandValue TD v lc gl = ret mptr0)
  (H0 : free TD Mem0 mptr0 = ret Mem'),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem';
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  inv Htcmd.
  apply free_inv in H0.
  destruct H0 as [blk [i0 [hi [lo [HeqR0 [J12 [HeqR2 H0]]]]]]].
  eapply simulation__getOperandValue in H; eauto.
  destruct H as [mptr0' [H1 H2]].
  eapply simulation__GV2ptr in HeqR0; eauto.
  destruct HeqR0 as [v' [J1 J2]].
  inv J2.
  eapply mem_simulation__free in H0; eauto.
  destruct H0 as [Mem2' [Hfree2 [Hwfmi2  Hmsim2]]].
  exists (Opsem.mkState
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 lc2
             als2):: 
            ECs2) Mem2').
  exists mi.
  split.
  SCase "opsem".
    simpl.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply Opsem.sop_star_cons; eauto.
      eapply Opsem.sFree with (mptr:=mptr0'); eauto.
        unfold free.     
        rewrite J1.
        inversion_clear Hwfmi.
        assert (H4':=H4).
        apply mi_range_block in H4'. subst.
        rewrite Int.add_zero.
        destruct (zeq (Int.signed 31 i0) 0).
          apply mi_bounds in H4.
          rewrite <- H4. rewrite <- HeqR2.
          assert (lo + 0 = lo) as EQ''. auto with zarith. 
          rewrite EQ'' in Hfree2. clear EQ''.
          assert (hi + 0 = hi) as EQ''. auto with zarith.
          rewrite EQ'' in Hfree2. clear EQ''.
          auto.

          clear - J12 n. contradict J12; auto.          

  repeat (split; auto).
    eapply cmds_at_block_tail_next; eauto.

    simpl_env in Heqb2. simpl in Heqb2.
    eapply cmds_at_block_tail_next; eauto.

  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
Qed.

Lemma SBpass_is_correct__dsLoad_nptr : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id) (t : typ)
  (align0 : align) (vp : value) (EC : list ExecutionContext) (cs : list cmd)
  (tmn : terminator) (Mem0 : mem) (als : list mblock) (MM : mmetadata) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_load id0 t vp align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gvp : GenericValue) (gv : GenericValue) (md : metadata)
  (H : SBspecAux.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD vp lc gl = ret gvp)
  (H1 : assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : isPointerTypB t = false),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc id0 gv;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  remember (SB_ds_pass.get_reg_metadata rm2 vp) as R.
  destruct R as [[bv ev]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R1. 
  destruct R1 as [ptmp ex_ids3'].
  remember (isPointerTypB t) as R4.
  destruct R4.
  SCase "t is ptr".
    unfold isPointerTyp in H3.
    inv H3.

  SCase "t isnt ptr".
  inv Htcmd.
  assert (J:=H1).
  unfold SBspecAux.assert_mptr in J.
  destruct md as [blk bofs eofs].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize (los,nts) t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  eapply simulation__mload in H2; eauto.
  destruct H2 as [gv2 [H21 H22]].
  assert (J':=Hrsim).
  destruct J' as [Hrsim1 Hrsim2].
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
  rewrite J1 in HeqR. inv HeqR.

  exists (Opsem.mkState
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
                  (updateAddALs _ lc2 ((ptmp,gvp2)::(id0,($ gv2 # t $))::nil))
             als2):: 
            ECs2) M2).
  exists mi.
  split.
  SSCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.
      apply Opsem.sCast; auto.
        unfold Opsem.CAST. simpl. simpl in H00.
        replace (@getOperandValue DGVs) with LLVMgv.getOperandValue; auto.
        rewrite H00. auto.

    next_insn.
       clear - H00 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR3.
       eapply assert_mptr_fn__ok with (b:=b); eauto.

    next_insn.
      eapply Opsem.sLoad with (mp:=gvp2); eauto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (SB_ds_pass.getValueID vp[<=]
            ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            assert (Hwfc := HBinF).
            destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
            eapply wf_system__wf_cmd with (c:=insn_load id0 t vp align0)  
              in Hwfc; eauto.
              inv Hwfc. 
              eapply wf_value_id__in_getFdefLocs in H11; auto.
              apply in_or_app. right. simpl. auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

  repeat (split; eauto 2 using cmds_at_block_tail_next, 
                               cmds_at_block_tails_next).

  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
    Transparent updateAddALs. simpl.
    eapply reg_simulation__updateAddAL_lc; eauto.
      eapply reg_simulation__updateAddAL_tmp; eauto.
        eauto using getCmdID_in_getFdefLocs.

    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
Qed.

Lemma SBpass_is_correct__dsLoad_ptr : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id) (t : typ)
  (align0 : align) (vp : value) (EC : list ExecutionContext) (cs : list cmd)
  (tmn : terminator) (Mem0 : mem) (als : list mblock) (MM : mmetadata) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_load id0 t vp align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  md' lc' rm'
  (gvp : GenericValue) (gv : GenericValue) (md : metadata)
  (H : SBspecAux.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD vp lc gl = ret gvp)
  (H1 : assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : isPointerTypB t = true)
  (H4 : get_mem_metadata TD MM gvp = md')
  (H5 : prop_reg_metadata lc rm id0 gv md' = (lc', rm')),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  remember (SB_ds_pass.get_reg_metadata rm2 vp) as R.
  destruct R as [[bv ev]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R1. 
  destruct R1 as [ptmp ex_ids3'].
  remember (isPointerTypB t) as R4.
  destruct R4; try solve [inv H3].
  remember (lookupAL (id * id) rm2 id0) as R5.
  destruct R5 as [[bid0 eid0]|]; inv Htcmd.
  assert (J:=H1).
  unfold SBspecAux.assert_mptr in J.
  destruct md as [blk bofs eofs].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize (los,nts) t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  unfold SBspecAux.get_reg_metadata in H.
  assert (H2':=H2).
  eapply simulation__mload in H2'; eauto.
  destruct H2' as [gv2 [H21 H22]].
  assert (J':=Hrsim).
  destruct J' as [Hrsim1 Hrsim2].
  case_eq (SBspecAux.get_mem_metadata (los,nts) MM gvp).
  intros blk0 bofs0 eofs0 JJ.
  assert (Hmsim':=HsimM).
  destruct Hmsim' as [Hmsim1 [Hmgb [Hzeroout Hmsim2]]].
  assert (JJ':=JJ).
  assert (exists b, exists ofs, exists cm, gvp = (Vptr b ofs, cm)::nil) as EQ.
    clear - H2.
    apply mload_inv in H2.
    destruct H2 as [b [ofs [m [mc [J1 [J2 J3]]]]]]. eauto.
  destruct EQ as [pb [pofs [cm EQ]]]. subst.

  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eauto using getCmdID_in_getFdefLocs.
  assert (Hspec := Hgenmeta).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].

  assert (getOperandValue (los, nts) (value_id ptmp) 
      (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) id0 gv2) gl2 = ret gvp2) as K.
    simpl.
    rewrite <- lookupAL_updateAddAL_neq; auto.
      rewrite lookupAL_updateAddAL_eq; auto.
      apply tmp_is_fresh2 with (i0:=id0)(d:=getFdefLocs (fdef_intro fh1 bs1)) 
        (ex_ids1:=ex_ids) in HeqR1; auto.

  eapply Hmsim2 with (bid0:=bid0)(eid0:=eid0)(lc2:=
    (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) id0 gv2)) in JJ'; eauto.
  destruct JJ' as [bgv' [egv' [JJ1 [JJ2 JJ4]]]].
  assert (HeqR9':=H).
  apply Hrsim2 in HeqR9'.      
  destruct HeqR9' as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
  rewrite J1 in HeqR. inv HeqR.
  exists (Opsem.mkState
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
           (cs2' ++ cs23) tmn2 
             (updateAddALs _ lc2 
              ((ptmp,gvp2)::(id0,($ gv2 # t $))::(bid0,bgv')::(eid0,egv')::nil))
             als2):: 
            ECs2) M2).
  exists mi.
  split.
  SSCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.
      apply Opsem.sCast; auto.
        unfold Opsem.CAST. simpl. simpl in H00.
        replace (@Opsem.getOperandValue DGVs) with LLVMgv.getOperandValue; auto.
        rewrite H00. auto.

    next_insn.
       clear - H00 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR3 HeqR5.
       eapply assert_mptr_fn__ok with (b:=b); eauto.

    next_insn.
      eapply Opsem.sLoad with (mp:=gvp2); eauto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
        assert (SB_ds_pass.getValueID vp[<=]
            ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            assert (Hwfc := HBinF).
            destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
            eapply wf_system__wf_cmd in Hwfc; eauto using in_middle.
              inv Hwfc. 
              eapply wf_value_id__in_getFdefLocs in H13; auto.
        eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

  repeat (split; eauto 2 using inject_incr__preserves__als_simulation,
                              cmds_at_block_tail_next, cmds_at_block_tails_next,
                              inject_incr__preserves__sbECs_simulate_ECs_tail,
                              inject_incr__preserves__fable_simulation).

  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
    inv H5. rewrite JJ.
    Transparent updateAddALs. simpl.
    eapply reg_simulation__updateAddAL_prop; eauto.
      eapply reg_simulation__updateAddAL_tmp; eauto.
    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
Qed.

Lemma SBpass_is_correct__dsStore_nptr : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (sid : id) (t : typ) 
  (align0 : align) (v : value) (vp : value) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata) 
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_store sid t v vp align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv : GenericValue) (gvp : GenericValue) (md : metadata) (Mem' : mem)
  (H : SBspecAux.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD v lc gl = ret gv)
  (H1 : getOperandValue TD vp lc gl = ret gvp)
  (H2 : assert_mptr TD t gvp md)
  (H3 : mstore TD Mem0 gvp t gv align0 = ret Mem')
  (H4 : isPointerTypB t = false),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem';
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  remember (SB_ds_pass.get_reg_metadata rm2 vp) as R.
  destruct R as [[bv ev]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R1. 
  destruct R1 as [ptmp ex_ids3'].
  remember (isPointerTypB t) as R4.
  destruct R4; try solve [inv H4].
  inv Htcmd.
  assert (J:=H2).
  unfold SBspecAux.assert_mptr in J.
  destruct md as [blk bofs eofs].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (getTypeAllocSize (los,nts) t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gv2 [H00 H01]].            
  eapply simulation__getOperandValue in H1; eauto.
  destruct H1 as [gvp2 [H10 H11]].            
  unfold SBspecAux.get_reg_metadata in H.
  assert (Hmstore:=H3).
  eapply simulation__mstore in H3; eauto.
  destruct H3 as [Mem2' [H31 [H33 H32]]].
  assert (J':=Hrsim).
  destruct J' as [Hrsim1 Hrsim2].
  assert (HeqR8':=H).
  apply Hrsim2 in HeqR8'.      
  destruct HeqR8' as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
  rewrite <- HeqR in J1. inv J1.
  exists (Opsem.mkState
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
              (updateAddALs _ lc2 ((ptmp, gvp2)::nil))
             als2):: 
            ECs2) Mem2').
  exists mi.
  split.
  SSCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.
      apply Opsem.sCast; auto.
        unfold Opsem.CAST. simpl. simpl in H10.
        replace (@Opsem.getOperandValue DGVs) with LLVMgv.getOperandValue; auto.
        rewrite H10. auto.

    next_insn.
       clear - H00 J2 J3 J4 J5 J H10 H11 HeqR0 HeqR3.
       eapply assert_mptr_fn__ok with (b:=b); eauto.

    next_insn.
      assert (Hwfc := HBinF).
      destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
      assert (In (insn_store sid t v vp align0)
        (cs11 ++ insn_store sid t v vp align0 :: cs)) as HinCs.
        apply in_or_app. right. simpl. auto.
      eapply wf_system__wf_cmd with (c:=insn_store sid t v vp align0) in Hwfc; 
        eauto.
      inv Hwfc. 
      eapply Opsem.sStore with (mp2:=gvp2)(gv1:=gv2); eauto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (SB_ds_pass.getValueID v[<=]
            ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            eapply wf_value_id__in_getFdefLocs in H13; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (SB_ds_pass.getValueID vp[<=]
            ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            eapply wf_value_id__in_getFdefLocs in H17; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

  repeat (split; eauto 2 using inject_incr__preserves__als_simulation,
                              cmds_at_block_tail_next, cmds_at_block_tails_next,
                              inject_incr__preserves__sbECs_simulate_ECs_tail,
                              inject_incr__preserves__fable_simulation).
  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
    Transparent updateAddALs. simpl.
    eapply reg_simulation__updateAddAL_tmp; eauto.
    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.
Qed.

Lemma SBpass_is_correct__dsStore_ptr : forall (mi : MoreMem.meminj) 
  (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : rmetadata) (gl : GVMap) (fs : GVMap)
  (sid : id) (t : typ) (align0 : align) (v : value) (vp : value) 
  (EC : list ExecutionContext) (cs : list cmd) (tmn : terminator) (Mem0 : mem)
  (MM : mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_store sid t v vp align0 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv : GenericValue) (gvp : GenericValue) (md : metadata)
  (md' : metadata) (Mem' : mem) (MM' : mmetadata)
  (H : SBspecAux.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD v lc gl = ret gv)
  (H1 : getOperandValue TD vp lc gl = ret gvp)
  (H2 : assert_mptr TD t gvp md)
  (H3 : mstore TD Mem0 gvp t gv align0 = ret Mem')
  (H4 : isPointerTypB t = true)
  (H5 : SBspecAux.get_reg_metadata TD gl rm v = ret md')
  (H6 : set_mem_metadata TD MM gvp md' = MM'),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem';
         Mmap := MM' |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  remember (SB_ds_pass.get_reg_metadata rm2 vp) as R.
  destruct R as [[bv ev]|]; try solve [inversion Htcmd].
  remember (mk_tmp ex_ids3) as R1. 
  destruct R1 as [ptmp ex_ids3'].
  remember (isPointerTypB t) as R4.
  destruct R4; try solve [inv H4].
  remember (SB_ds_pass.get_reg_metadata rm2 v) as R5.
  destruct R5 as [[bv0 ev0]|]; inv Htcmd.
  assert (J:=H2).
  unfold SBspecAux.assert_mptr in J.
  destruct md as [blk bofs eofs].
  remember (GV2ptr (los,nts) (getPointerSize (los,nts)) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v0; try solve [inversion J].
  remember (getTypeAllocSize (los,nts) t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gv2 [H00 H01]].            
  eapply simulation__getOperandValue in H1; eauto.
  destruct H1 as [gvp2 [H10 H11]].            
  unfold SBspecAux.get_reg_metadata in H.
  assert (H3':=H3).
  eapply simulation__mstore in H3'; eauto.
  destruct H3' as [Mem2' [H31 [H33 H32]]].
  assert (J':=Hrsim).
  destruct J' as [Hrsim1 Hrsim2].

  destruct md' as [md_blk' md_bofs' md_eofs'].
  assert (HeqR9':=H).
  apply Hrsim2 in HeqR9'.      
  destruct HeqR9' as [bv2 [ev2 [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
  assert (H5':=H5).      
  apply Hrsim2 in H5'.
  destruct H5' as [bv2' [ev2' [bgv2' [egv2' [J1' [J2' [J3' [J4' J5']]]]]]]].
  simpl in HeqR5.
  rewrite J1' in HeqR5.
  inv HeqR5.
  rewrite <- HeqR in J1. inv J1.

  assert (exists Mem2'',
    Opsem.sInsn (opsem.OpsemAux.mkCfg S2 (los, nts) Ps2 gl2 fs2)
      (Opsem.mkState
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
              (insn_call fake_id true attrs smmd_typ smmd_fn
                ((p8,nil,value_id ptmp) :: (p8,nil,bv2') :: (p8,nil,ev2') 
                    :: (p8,nil,vnullp8) :: (i32,nil,vint1) :: (i32,nil,vint1) 
                    :: nil):: 
               cs2' ++ cs23) tmn2 
              (updateAddAL _ lc2 ptmp gvp2)
             als2):: 
            ECs2) Mem2')
      (Opsem.mkState
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
              (cs2' ++ cs23) tmn2 
              (updateAddAL _ lc2 ptmp gvp2)
             als2):: 
            ECs2) Mem2'') trace_nil /\
      mem_simulation mi (los,nts) mgb
        (SBspecAux.set_mem_metadata (los,nts) MM gvp 
          (SBspecAux.mkMD md_blk' md_bofs' md_eofs')) 
        Mem' Mem2'') as W.

    assert (exists b : Values.block, exists ofs : int32, exists cm,
      gvp = (Vptr b ofs,cm)::nil /\ 
      mstore_aux Mem0 gv b (Int.signed 31 ofs) = ret Mem') 
      as EQ.
      clear - H3.
      eapply mstore_inversion; eauto.
    destruct EQ as [b2 [ofs2 [cm [EQ Hmstore_aux]]]]. subst.

    eapply simulation__set_mmetadata_fn with (pgv':=gvp2)(bgv':=bgv2')
      (egv':=egv2')(rm:=rm)(v:=v); simpl; eauto.
      clear - HeqR1 HeqR3.
      rewrite lookupAL_updateAddAL_eq; auto.

      clear - J2' H31 J1' HeqR1 HeqR3 Hgenmeta Hinc.
      rewrite <- getOperandValue_eq_fresh_id; eauto.
        eapply get_reg_metadata__fresh with (rm2:=rm2) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.

      clear - J3' H31 J1' HeqR1 HeqR3 Hgenmeta Hinc.
      rewrite <- getOperandValue_eq_fresh_id; eauto.
        eapply get_reg_metadata__fresh with (rm2:=rm2) in J1'; 
          eauto; try fsetdec. destruct J1'; auto.

  destruct W as [Mem2'' [W1 W2]].

  exists (Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
              (updateAddALs _ lc2 ((ptmp, gvp2)::nil))
             als2):: 
            ECs2) Mem2'').
  exists mi.
  split.
  SSCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.
      apply Opsem.sCast; auto.
        unfold Opsem.CAST. simpl. simpl in H10.
        replace (@Opsem.getOperandValue DGVs) with LLVMgv.getOperandValue; auto.
        rewrite H10. auto.

    next_insn.
       clear - H00 J2 J3 J4 J5 J H10 H11 HeqR0 HeqR3.
       eapply assert_mptr_fn__ok with (b:=b); eauto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply Opsem.sop_star_cons with (state2:=
      (Opsem.mkState
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
              (insn_call fake_id true attrs smmd_typ smmd_fn
                ((p8,nil,value_id ptmp) :: (p8,nil,bv2') :: (p8,nil,ev2') 
                    :: (p8,nil,vnullp8) :: (i32,nil,vint1) :: (i32,nil,vint1) 
                    :: nil):: 
               cs2' ++ cs23) tmn2 
              (updateAddAL _ lc2 ptmp gvp2)
             als2):: 
            ECs2) Mem2')); auto.
      assert (Hwfc := HBinF).
      destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
      assert (In (insn_store sid t v vp align0)
        (cs11 ++ insn_store sid t v vp align0 :: cs)) as HinCs.
        apply in_or_app. right. simpl. auto.
      eapply wf_system__wf_cmd with (c:=insn_store sid t v vp align0) in Hwfc; 
        eauto.
      inv Hwfc. 
      eapply Opsem.sStore with (mp2:=gvp2)(gv1:=gv2); eauto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (SB_ds_pass.getValueID v[<=]
            ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            eapply wf_value_id__in_getFdefLocs in H15; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

        rewrite <- getOperandValue_eq_fresh_id; auto.
          assert (SB_ds_pass.getValueID vp[<=]
            ids2atoms (getFdefLocs (fdef_intro fh1 bs1))) as Hindom.
            eapply wf_value_id__in_getFdefLocs in H19; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply Opsem.sop_star_cons; eauto.

  repeat (
    match goal with
    | |- wf_sb_mi _ _ _ _ => idtac 
    | |- _ => 
         split; eauto 2 using inject_incr__preserves__als_simulation,
                              cmds_at_block_tail_next, cmds_at_block_tails_next,
                              inject_incr__preserves__sbECs_simulate_ECs_tail,
                              inject_incr__preserves__fable_simulation
    end).

  exists ex_ids. exists rm2.
  exists ex_ids5. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
    Transparent updateAddALs. simpl.
    eapply reg_simulation__updateAddAL_tmp; eauto.
    split; auto.
      clear - Hinc HeqR1. eapply mk_tmp_inc; eauto.

    clear - H33 H31 H3 Hwfmi W1.
    inversion H33.
    apply mstore_inversion in H3.
    destruct H3 as [b [ofs [cm [Heq H3]]]]; subst.
    apply set_mmetadata_fn__prop in W1.
    destruct W1 as [W1 [W2 W3]].
    split; auto.
    SSSCase "Hmap4".
      intros b1 b2 delta2 J.
      apply Hmap2 in J.
      eauto with zarith.
    SSSCase "mappedblocks0".
      intros b1 b2 delta J.
      apply mi_mappedblocks in J.
      eauto.
    SSSCase "bounds0".
      intros b1 b2 delta J.
      apply mi_bounds in J.
      rewrite <- W3. auto.
Qed.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-impredicative-set") ***
*** End: ***
 *)
