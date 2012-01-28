Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import Values.
Require Import vellvm.
Require Import genericvalues.
Require Import trace.
Require Import Memory.
Require Import alist.
Require Import Integers.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import opsem.
Require Import dopsem.
Require Import sb_def.
Require Import sb_ds_trans.
Require Import sb_msim.
Require Import sb_ds_gv_inject.
Require Import sb_ds_bsim.
(*
Require Import sb_ds_trans_axioms.
Require Import sb_ds_trans_lib.
Require Import sb_ds_trans_tactics.
*)

Import SB_ds_pass.
Export SBspec.

(*
Lemma SBpass_is_correct__dsCall : forall (mi : MoreMem.meminj) 
  (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) rid noret0 ca ft fv lp
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem0 : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (fid : id) (ogvs : list (DGVs.(GVsT) * monad metadata)) 
  (l' : l) (ps' : phinodes) (cs' : cmds) (tmn' : terminator) (fa : fnattrs)
  (rt : typ) (la : args) (va : varg) (lb : blocks) (rm' : rmetadata)
  (lc' : DGVMap) fptr
  (HJ : getOperandValue TD fv lc gl = Some fptr) 
  (H : OpsemAux.lookupFdefViaPtr Ps fs fptr =
      ret fdef_intro (fheader_intro fa rt fid la va) lb)
  (H0 : getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
       ret block_intro l' ps' cs' tmn')
  (H1 : params2GVs TD lp lc gl rm = ret ogvs)
  (H2 : initLocals TD la ogvs = Some (lc', rm')),
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
                CurFunction := fdef_intro (fheader_intro fa rt fid la va) lb;
                CurBB := block_intro l' ps' cs' tmn';
                CurCmds := cs';
                Terminator := tmn';
                Locals := lc';
                Rmap := rm';
                Allocas := nil |}
                :: {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                   Terminator := tmn;
                   Locals := lc;
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
  remember (trans_params rm2 lp 1) as R.
  destruct R as [cs1|]; try solve [inversion Htcmd].
  remember (call_suffix rid noret0 ca ft fv lp rm2) as R1.
  destruct R1 as [cs2|]; try solve [inversion Htcmd].
  inv Htcmd.
  unfold call_suffix in HeqR1.
  remember (if negb noret0 && isReturnPointerTypB ft
             then
              match lookupAL (id * id) rm2 rid with
              | ret (bid0, eid0) =>
                  ret (insn_call bid0 false attrs gsb_typ gsb_fn
                         ((i32, vint0) :: nil)
                       :: insn_call eid0 false attrs gse_typ gse_fn
                            ((i32, vint0) :: nil)
                          :: insn_call fake_id true attrs dstk_typ dstk_fn
                               nil :: nil)
              | merror => merror
              end
             else ret [insn_call fake_id true attrs dstk_typ dstk_fn nil]) as R2.
  destruct R2 as [cs22|]; inv HeqR1.

  assert (Hlkf:=H).
  eapply lookupFdefViaPtr__simulation in H; eauto.
  destruct H as [fptr2 [f2 [Hget2 [Hinj2 [Hlkf' Htfdef2]]]]].
  assert (Htfdef2':=Htfdef2).
  apply trans_fdef_inv in Htfdef2.
  assert (JJ:=Hlkf).
  apply lookupFdefViaPtr_isnt_callLib in JJ.
  rewrite JJ in Htfdef2.
  destruct Htfdef2 as [ex_ids3 [rm3 [cs3 [ex_ids3' [bs3 [l1 [ps1 [cs4 [tmn1 [J1
    [J2 [J3 J4]]]]]]]]]]]]; subst.

  assert (Hpsim := H1).
  eapply trans_params_simulation in Hpsim; eauto.
     simpl_env. simpl.
     assert (Hop:=Hlkf').
     replace LLVMgv.getOperandValue with (@Opsem.getOperandValue DGVs) in Hget2; 
       auto.
     eapply shadow_stack_init with (S2:=S2)(B2:=B2)(ft:=ft)(cs2':=cs2')(lc':=lc')
       (rm':=rm')(gl:=gl2)(mi:=mi)(lp:=lp)(cs1:=cs1)(rm2:=rm2)(Mem0:=Mem0)
       (MM:=MM)(noret0:=noret0)(M2:=M2)(ex_ids3:=ex_ids3)(ogvs:=ogvs)(mgb:=mgb)
       (lb:=lb)(als2:=als2)(tmn2:=tmn2)(ca:=ca)(rid:=rid)(cs22:=cs22)(cs23:=cs23)
       (bs2:=bs2)(fh2:=fh2)(ECs2:=ECs2)(rm3:=rm3)(fv:=fv) in Hop; eauto.
     destruct Hop as [M2' [lc2' [Hop [Hwfmi2 [Hrsim2 Hmsim2]]]]].
     exists (Opsem.mkState 
      ((Opsem.mkEC 
        (fdef_intro (fheader_intro fa rt (wrapper_fid fid) la va)
                (block_intro l1 ps1 (cs3 ++ cs4) tmn1 :: bs3))
        (block_intro l1 ps1 (cs3 ++ cs4) tmn1)
        cs4
      tmn1 lc2' nil):: 
      (Opsem.mkEC (fdef_intro fh2 bs2) B2
        (insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22 ++ cs2' ++ cs23)
      tmn2 lc2 als2):: ECs2) M2').
     exists mi. 
     split; auto.
     clear Hop.
     assert (Hentry:=H0).
     apply trans_blocks_inv in J3.
     destruct J3 as [b1 [bs1' [ex_ids4' [J31 [J32 J33]]]]]; subst.
     simpl in H0. inv H0.
     apply trans_block_inv in J31.
     destruct J31 as [p' [c' [cs5 [J31 [J35 [J36 J37]]]]]].
     inv J37.
     repeat (split; auto).
       eapply entryBlockInFdef; eauto.
       eapply lookupFdefViaPtr_inv; eauto.        
       exists l'. exists ps'. exists nil. auto.
       exists l'. exists p'. exists cs3. auto.
       exists ex_ids3. exists rm3. exists ex_ids3. exists ex_ids4'.
       exists c'. exists cs5.
       split; auto. split; auto. split; auto using incl_refl.
       clear - Heqb2. destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
       exists l2. exists ps2. 
       exists 
           (cs21 ++
            ((insn_call fake_id true attrs astk_typ astk_fn
                (val32 (Z_of_nat (length lp + 1)) :: nil)
              :: cs1))).
       simpl_env. auto.
       exists ex_ids. exists rm2. exists ex_ids5. exists ex_ids4.
       exists (insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22).
       exists cs2'. exists cs23.
       repeat (split; auto).
         unfold call_suffix.
         rewrite <- HeqR2. auto.
Qed.
       

Lemma SBpass_is_correct__dsExCall : forall (mi : MoreMem.meminj) 
  (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) rid noret0 ca ft fv lp
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem0 : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_call rid noret0 ca ft fv lp :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (fid : id) (rt : typ) (fa : fnattrs) (la : args) (va : varg)
  (oresult : monad GenericValue) (Mem' : mem) (lc' : DGVMap)
  (rm' : rmetadata) (gvs : list GenericValue) fptr
  (HJ : getOperandValue TD fv lc gl = Some fptr)
  (H : OpsemAux.lookupExFdecViaPtr Ps fs fptr =
      ret fdec_intro (fheader_intro fa rt fid la va))
  (H0 : LLVMgv.params2GVs TD lp lc gl = ret gvs)
  (H1 : callExternalFunction Mem0 fid gvs = ret (oresult, Mem'))
  (H2 : exCallUpdateLocals TD ft noret0 rid oresult lc rm = ret (lc', rm')),
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
         Mem := Mem';
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd.
  remember (trans_params rm2 lp 1) as R.
  destruct R as [cs1|]; try solve [inversion Htcmd].
  remember (call_suffix rid noret0 ca ft fv lp rm2) as R1.
  destruct R1 as [cs2|]; try solve [inversion Htcmd].
  inv Htcmd.
  unfold call_suffix in HeqR1.
  remember (if negb noret0 && isReturnPointerTypB ft
             then
              match lookupAL (id * id) rm2 rid with
              | ret (bid0, eid0) =>
                  ret (insn_call bid0 false attrs gsb_typ gsb_fn
                         ((i32, vint0) :: nil)
                       :: insn_call eid0 false attrs gse_typ gse_fn
                            ((i32, vint0) :: nil)
                          :: insn_call fake_id true attrs dstk_typ dstk_fn
                               nil :: nil)
              | merror => merror
              end
             else ret [insn_call fake_id true attrs dstk_typ dstk_fn nil]) as R2.
  destruct R2 as [cs22|]; inv HeqR1.

  assert (Hlkf:=H).
  eapply lookupExFdecViaGV__simulation in H; eauto.
  destruct H as [fptr2 [f2 [Hget2 [Hlkf' [Hinj2 Htfdec2]]]]].
  inv Htfdec2. 

     simpl_env. simpl.
     assert (Hop:=Hlkf').
     eapply shadow_stack_exfdec with (S2:=S2)(B2:=B2)(ft:=ft)(cs2':=cs2')
       (lc':=lc')(oresult:=oresult)(bs1:=bs1)(fh1:=fh1)(lc:=lc)
       (rm':=rm')(mi:=mi)(lp:=lp)(cs1:=cs1)(rm2:=rm2)(Mem0:=Mem0)
       (MM:=MM)(noret0:=noret0)(M2:=M2)(gvs:=gvs)(Mem':=Mem')
       (mgb:=mgb)(als2:=als2)(tmn2:=tmn2)(ca:=ca)(rid:=rid)(cs22:=cs22)
       (cs23:=cs23)(bs2:=bs2)(fh2:=fh2)(ECs2:=ECs2)(rm:=rm) in Hop; eauto.
     destruct Hop as [M2' [lc2' [Hop [Hwfmi2 [Hrsim2 Hmsim2]]]]].
     exists (Opsem.mkState 
              ((Opsem.mkEC (fdef_intro fh2 bs2) B2 (cs2' ++ cs23)
                tmn2 lc2' als2):: ECs2) M2').
     exists mi. 
     split; auto.
     clear Hop.
     repeat (split; auto).
       clear - Heqb1. destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
       exists l1. exists ps1. exists (cs11++[insn_call rid noret0 ca ft fv lp]).
       simpl_env. auto.
       
       clear - Heqb2. destruct Heqb2 as [l2 [ps2 [cs2 Heqb2]]]; subst.
       exists l2. exists ps2. 
       exists (cs2 ++
           ((insn_call fake_id true attrs astk_typ astk_fn
            (val32 (Z_of_nat (length lp + 1)) :: nil)
           :: cs1 ++ insn_call rid noret0 ca ft (wrap_call fv) lp :: cs22))).
       simpl_env. auto.
       exists ex_ids. exists rm2. exists ex_ids5. exists ex_ids4.
       exists cs2'. exists cs23.
       repeat (split; auto).
Qed.

Lemma SBpass_is_correct__dsBranch_uncond : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (bid : id) (l0 : l) Cfg
  (EC : list ExecutionContext) (Mem0 : mem) (MM : mmetadata) (als : list mblock)
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := nil;
                  Terminator := insn_br_uncond bid l0;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (l' : l) (ps' : phinodes) (cs' : cmds) (tmn' : terminator) (lc' : DGVMap)
  (rm' : rmetadata) 
  (H : ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef F l0)
  (H0 : switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc rm =
       ret (lc', rm')),
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
                CurBB := block_intro l' ps' cs' tmn';
                CurCmds := cs';
                Terminator := tmn';
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_br.
  inv Htcmds. inv Httmn.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.
  destruct fh1. destruct HuniqF as [HuniqBlocks HuniqArgs].
  simpl in H. symmetry in H.
  assert (Htfdef':=Htfdef). 
  apply trans_fdef_inv in Htfdef'.
  rewrite Hclib in Htfdef'.
  destruct Htfdef' as [ex_ids1 [rm2' [cs1' [ex_ids' [bs' [l1 [ps1 [cs1 [tmn1 [J1
    [J2 [J3 J4]]]]]]]]]]]].
  inv J4.
  rewrite Hgenmeta in J1. inv J1.

  assert (Htblocks := J3).
  eapply lookup_trans_blocks__trans_block with (ex_ids0:=ex_ids1) in J3; 
    eauto using incl_refl.
  destruct J3 as [ex_ids1' [ex_ids2 [b2' [Hlk' [Htblock Hinc']]]]].
  simpl in Htblock.

  apply trans_block_inv in Htblock.
  destruct Htblock as [ps2 [cs2 [cs [JJ1 [JJ2 [JJ3 eq]]]]]]; subst.

  assert (HBinF':=H).
  apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in HBinF';
    auto. 
  destruct HBinF' as [EQ HBinF']; subst.

  assert (exists lc2', Opsem.switchToNewBasicBlock (los,nts) 
    (block_intro l' ps2 (cs2 ++ cs) tmn') B2 gl2 lc2 = Some lc2' /\
    reg_simulation mi (los, nts) gl2
            (fdef_intro (fheader_intro f t i0 a v) bs1) rm' rm2' lc' lc2') 
    as Hswitch2.
    eapply switchToNewBasicBlock__reg_simulation; eauto.

  destruct Hswitch2 as [lc2' [Hswitch2 Hrsim']].
  exists (Opsem.mkState 
          ((Opsem.mkEC 
            (fdef_intro (fheader_intro f t (wrapper_fid i0) a v)
               (block_intro l1 ps1 (cs1'++ cs1) tmn1 :: bs'))
            (block_intro l' ps2 (cs2 ++ cs) tmn')
            (cs2 ++ cs) tmn' lc2' als2):: 
            ECs2) M2).
  exists mi.
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply Opsem.sop_star_cons; eauto.
      eapply Opsem.sBranch_uncond; eauto.
        simpl. unfold lookupBlockViaLabelFromBlocks in Hlk'.
        rewrite <- Hlk'. simpl.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l' l1); 
          subst; auto.

          simpl in Hlk'.
          destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l1 l1).
            inv Hlk'.
           apply trans_blocks_inv in Htblocks.
           destruct Htblocks as [b1 [bs1' [ex_ids3 [J1 [J7 J8]]]]]; subst.
           destruct b1.
           apply trans_block_inv in J1.
           destruct J1 as [p' [cs'' [cs0' [J9 [J10 [J11 J12]]]]]].
           inv J12. 
           eapply wf_system__wf_fdef in HFinPs; eauto.
           clear - HBinF H Heqb1 HFinPs.
           destruct Heqb1 as [l1 [ps1 [cs1'' Heq1]]]; subst.
           eapply getEntryBlock_inv with (l':=l0)(a:=l0) in HBinF; simpl; eauto.
           contradict HBinF; auto.

           contradict n; auto.

  repeat (split; auto).
    exists l'. exists ps'. exists nil. auto.
    exists l'. exists ps2. exists nil. auto.
    exists ex_ids1. exists rm2'. exists ex_ids1'. exists ex_ids2. exists cs2.
    exists cs. 
    repeat (split; auto).
Qed.

Lemma SBpass_is_correct__dsBranch : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (bid : id) (Cond : value)
  (l1 : l) (l2 : l) (EC : list ExecutionContext) (Mem0 : mem) (MM : mmetadata)
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
                  CurCmds := nil;
                  Terminator := insn_br bid Cond l1 l2;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (c : GenericValue)
  (l' : l)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  (lc' : DGVMap)
  (rm' : rmetadata)
  (H : getOperandValue TD Cond lc gl = ret c)
  (H0 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (H1 : switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc rm =
       ret (lc', rm')),
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
                CurBB := block_intro l' ps' cs' tmn';
                CurCmds := cs';
                Terminator := tmn';
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_br.
  inv Htcmds. inv Httmn.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.
  destruct fh1. destruct HuniqF as [HuniqBlocks HuniqArgs].
  simpl in H. symmetry in H.
  assert (Htfdef':=Htfdef). 
  apply trans_fdef_inv in Htfdef'.
  rewrite Hclib in Htfdef'.
  destruct Htfdef' as [ex_ids1 [rm2' [cs1' [ex_ids' [bs' [l1' [ps1 [cs1 [tmn1 [J1
    [J2 [J3 J4]]]]]]]]]]]].
  inv J4.
  rewrite Hgenmeta in J1. inv J1.

  symmetry in H.
  eapply simulation__getOperandValue in H; eauto.
  destruct H as [c' [H Hinj]].

  erewrite simulation__isGVZero in H0; eauto.
  assert (exists ex_ids1' : ids, exists ex_ids2 : ids, exists b2 : block,
    (if isGVZero (los,nts) c' 
     then lookupBlockViaLabelFromBlocks (block_intro l1' ps1 cs1 tmn1 :: bs') l2
     else lookupBlockViaLabelFromBlocks (block_intro l1' ps1 cs1 tmn1 :: bs') l1)
      = ret b2 /\
    trans_block ex_ids1' rm2' (block_intro l' ps' cs' tmn') = ret (ex_ids2, b2) 
      /\
    incl ex_ids1 ex_ids1') as Hfind.
   destruct (isGVZero (los,nts) c');
      eapply lookup_trans_blocks__trans_block with (ex_ids:=ex_ids1);
        eauto using incl_refl.
  destruct Hfind as [ex_ids1' [ex_ids2 [b2' [Hlk' [Htblock Hinc']]]]].
  simpl in Htblock.

  apply trans_block_inv in Htblock.
  destruct Htblock as [ps2 [cs2 [cs [JJ1 [JJ2 [JJ3 eq]]]]]]; subst.

  assert (blockInFdefB (block_intro l' ps' cs' tmn') 
    (fdef_intro (fheader_intro f t i0 a v) bs1)) as HBinF'.
    symmetry in H0.
    destruct (isGVZero (los,nts) c').
      apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in H0
        ; auto. destruct H0; eauto.
      apply genLabel2Block_blocks_inv with (f:=(fheader_intro f t i0 a v)) in H0
        ; auto. destruct H0; eauto.

  assert (exists lc2', Opsem.switchToNewBasicBlock (los,nts) 
    (block_intro l' ps2 (cs2 ++ cs) tmn') B2 gl2 lc2 = Some lc2' /\
    reg_simulation mi (los, nts) gl2
            (fdef_intro (fheader_intro f t i0 a v) bs1) rm' rm2' lc' lc2') 
    as Hswitch2.
    eapply switchToNewBasicBlock__reg_simulation; eauto.

  destruct Hswitch2 as [lc2' [Hswitch2 Hrsim']].
  exists (Opsem.mkState
          ((Opsem.mkEC 
            (fdef_intro (fheader_intro f t (wrapper_fid i0) a v)
               (block_intro l1' ps1 (cs1'++ cs1) tmn1 :: bs'))
            (block_intro l' ps2 (cs2 ++ cs) tmn')
            (cs2 ++ cs) tmn' lc2' als2):: 
            ECs2) M2).
  exists mi.
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply Opsem.sop_star_cons; eauto.
      eapply Opsem.sBranch; eauto.
        apply trans_blocks_inv in J3.
        destruct J3 as [b1 [bs1' [ex_ids3 [J1 [J7 J8]]]]]; subst.
        destruct b1.
        apply trans_block_inv in J1.
        destruct J1 as [p' [cs'' [cs0' [J9 [J10 [J11 J12]]]]]].
        inv J12. 
        eapply wf_system__wf_fdef in HFinPs; eauto.
        destruct Heqb1 as [l3 [ps1 [cs1'' Heq1]]]; subst.
        assert (l1 <> l0 /\ l2 <> l0) as HA.
          clear - HBinF H HFinPs.
          split.
            eapply getEntryBlock_inv with (l':=l1)(a:=l0) in HBinF; 
              simpl; eauto.
            eapply getEntryBlock_inv with (l':=l2)(a:=l0) in HBinF; 
              simpl; eauto.

        rewrite <- Hlk'. unfold lookupBlockViaLabelFromBlocks. simpl.
        destruct HA as [HA1 HA2].
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l2 l0); 
          subst; try solve [auto | contradict HA2; auto].
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l1 l0); 
          subst; try solve [auto | contradict HA1; auto].

  repeat (split; auto).
    exists l'. exists ps'. exists nil. auto.
    exists l'. exists ps2. exists nil. auto.
    exists ex_ids1. exists rm2'. exists ex_ids1'. exists ex_ids2. exists cs2.
    exists cs. 
    repeat (split; auto).
Qed.

Ltac next_insn' M2' :=
  rewrite <- (@trace_app_nil__eq__trace trace_nil);
  match goal with
  | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
           ((Opsem.mkEC ?F2 ?B2 (_ :: ?cs2) ?tmn2 ?lc2 ?als2)::?ECs2) _) 
       (Opsem.mkState ((Opsem.mkEC _ _ _ _ _ _)::_) _) _ ] => 
    apply Opsem.sop_star_cons with (state2:=
      Opsem.mkState 
        ((Opsem.mkEC F2 B2 cs2 tmn2 lc2 als2):: 
          ECs2) M2'); eauto 
  end.

Ltac ret_insn :=
  rewrite <- (@trace_app_nil__eq__trace trace_nil);
  match goal with
  | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
         (_::
         (Opsem.mkEC ?F ?B (insn_call _ false _ _ _ _::?cs) ?tmn ?lc ?als)::
         ?ECs2) _) 
       (Opsem.mkState 
           ((Opsem.mkEC _ _ _ _ (updateAddALs ?T ?lc ((?k,?v)::_)) _)::_) 
       ?M) _ ] => 
    apply Opsem.sop_star_cons with 
      (state2:=Opsem.mkState 
        ((Opsem.mkEC F B cs tmn (updateAddAL _ lc k v) als)::ECs2) M);
    try rewrite (@simpl_cons_updateAddALs T)

  | |- context [ Opsem.sop_star _ 
       (Opsem.mkState (_::(Opsem.mkEC ?F ?B (_::?cs) ?tmn ?lc ?als)::?ECs2) _) 
       (Opsem.mkState _ ?M) _ ] => 
    apply Opsem.sop_star_cons with 
      (state2:=Opsem.mkState ((Opsem.mkEC F B cs tmn lc als)::ECs2) M)
  end.

Lemma cmds_at_block_tails_next' : forall B2' cs23' cs24' tmn2' cs22,
  (exists l2 : l, exists ps2 : phinodes, exists cs21 : list cmd,
    B2' = block_intro l2 ps2 (cs21 ++ cs22 ++ cs23' ++ cs24') tmn2') ->
  exists l2 : l, exists ps2 : phinodes, exists cs21 : list cmd,
    B2' = block_intro l2 ps2 (cs21 ++ cs23' ++ cs24') tmn2'.
Proof.
  intros.
  destruct H as [l2' [ps2' [cs21' Heqb2']]]; subst.
  exists l2'. exists ps2'. exists (cs21' ++ cs22). simpl_env. auto.
Qed.

Lemma SBpass_is_correct__dsReturn : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (rid : id)
  (RetTy : typ) (Result : value) (lc : DGVMap) (rm : SBspecAux.rmetadata)
  (gl : GVMap) (fs : GVMap) (F' : fdef) (B' : block) (c' : cmd) (cs' : list cmd)
  (tmn' : terminator) (lc' : DGVMap) (rm' : SBspecAux.rmetadata)
  (EC : list SBspec.ExecutionContext) (Mem : mem) (MM : SBspecAux.mmetadata)
  (als : list mblock) (als' : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           SBspec.ECS := {|
                          SBspec.CurFunction := F;
                          SBspec.CurBB := B;
                          SBspec.CurCmds := nil;
                          SBspec.Terminator := insn_return rid RetTy Result;
                          SBspec.Locals := lc;
                          SBspec.Rmap := rm;
                          SBspec.Allocas := als |}
                          :: {|
                             SBspec.CurFunction := F';
                             SBspec.CurBB := B';
                             SBspec.CurCmds := c' :: cs';
                             SBspec.Terminator := tmn';
                             SBspec.Locals := lc';
                             SBspec.Rmap := rm';
                             SBspec.Allocas := als' |} :: EC;
           SBspec.Mem := Mem;
           SBspec.Mmap := MM |} Cfg St)
  (Mem' : mem)
  (lc'' : DGVMap)
  (rm'' : SBspecAux.rmetadata)
  (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas TD Mem als = ret Mem')
  (H1 : SBspec.returnUpdateLocals TD c' RetTy Result lc lc' rm rm' gl =
       ret (lc'', rm'')),
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
                        SBspec.CurFunction := F';
                        SBspec.CurBB := B';
                        SBspec.CurCmds := cs';
                        SBspec.Terminator := tmn';
                        SBspec.Locals := lc'';
                        SBspec.Rmap := rm'';
                        SBspec.Allocas := als' |} :: EC;
         SBspec.Mem := Mem';
         SBspec.Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_return.
  inv Htcmds.
  simpl in H1.
  unfold call_suffix in Hcall'.
  unfold SBspec.returnUpdateLocals in H1.
  remember (SBspec.returnResult (los, nts) RetTy Result lc rm gl2) as Ret.
  destruct Ret as [[gr md]|]; try solve [inv H1].
  unfold SBspec.returnResult in HeqRet.
  remember (getOperandValue (los, nts) Result lc gl2) as ogr.
  destruct ogr as [ogr|]; try solve [inv HeqRet].

  assert (exists bv2, exists ev2, exists bgv2, exists egv2,  
    exists blk1, exists bofs1, exists eofs1,
    cs23 =(insn_call fake_id true attrs ssb_typ ssb_fn
             ((p8, bv2) :: (i32, vint0) :: nil)
           :: insn_call fake_id true attrs sse_typ sse_fn
                ((p8, ev2) :: (i32, vint0) :: nil) :: nil) /\
    Opsem.params2GVs (los, nts) ((p8, bv2) :: (i32, vint0) :: nil) lc2 gl2 =
      munit (bgv2 :: int2GV 0 :: nil) /\
    Opsem.params2GVs (los, nts) ((p8, ev2) :: (i32, vint0) :: nil) lc2 gl2 =
      munit (egv2 :: int2GV 0 :: nil) /\
    gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 /\
    gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2 /\
    md = mkMD blk1 bofs1 eofs1 /\ ogr = gr) as Heq_cs23.
    simpl in Httmn.
    destruct (isPointerTypB RetTy).
      remember (SBspecAux.get_reg_metadata (los, nts) gl2 rm Result) as oRmd.
      destruct oRmd as [[blk1 bofs1 eofs1]|]; inv HeqRet.
      assert (exists bv2, exists ev2, exists bgv2, exists egv2, 
        SB_ds_pass.get_reg_metadata rm2 Result = Some (bv2, ev2) /\
        getOperandValue (los,nts) bv2 lc2 gl2 = Some bgv2 /\
        getOperandValue (los,nts) ev2 lc2 gl2 = Some egv2 /\
        gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 /\
        gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2) as J.
        clear - HeqoRmd Hrsim. 
        destruct Hrsim as [_ Hrsim].
        apply Hrsim; auto.
      destruct J as [bv2 [ev2 [bgv2 [egv2 [Hgetrmd [Hgetbgv2 [Hgetegv2 [Hinj1 
        Hinj2]]]]]]]]. rewrite Hgetrmd in Httmn. 
      inv Httmn.
      exists bv2. exists ev2. exists bgv2. exists egv2. 
      exists blk1. exists bofs1. exists eofs1. 
      simpl. 
      rewrite Hgetbgv2. rewrite Hgetegv2. repeat (split; eauto).
    
      inv Httmn.
      exists vnullp8. exists vnullp8. exists null. exists null.
      exists Mem.nullptr. exists (Int.repr 31 0). exists (Int.repr 31 0).
      inv HeqRet.
      repeat (split; eauto 2 using gv_inject_null_refl).

  destruct Heq_cs23 as [bv2 [ev2 [bgv2 [egv2 [blk1 [bofs1 [eofs1 [Heq_cs23 
    [Hp2bv2 [Hp2ev2 [Hinj1 [Hinj2 [Heqmd Heqgr]]]]]]]]]]]]]; subst.
  destruct (@stk_ret_sim (los,nts) Mem0 M2 mi mgb MM bgv2 egv2) as 
    [M2' [M2'' [Hsbase [Hsbound [Hmsim3 [Hwfmi3 [Hgbase Hgbound]]]]]]]; auto.
  eapply free_allocas_sim in Hmsim3; eauto.
  destruct Hmsim3 as [M2''' [Hfree2' [Hmsim2' Hwfmi2']]].
  destruct n.
  SCase "nret = true".
    inv Hcall'.
    inv H1.
    exists (Opsem.mkState
        ((Opsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' lc2' als2'):: ECs2)
        M2''').
      exists mi.
      split.
      SSSCase "sop_star".
        simpl. next_insn' M2'.
          destruct (@ssb_is_found (los, nts) Ps2 lc2 gl2 fs2) as [fptr2 [J1 J2]].
          eapply Opsem.sExCall with (fid:=ssb_fid)
            (gvs:=(bgv2 :: int2GV 0 :: nil))(oresult:=None); eauto.

        next_insn' M2''.
          destruct (@sse_is_found (los, nts) Ps2 lc2 gl2 fs2) as [fptr2 [J1 J2]].
          eapply Opsem.sExCall with (fid:=sse_fid)
            (gvs:=(egv2 :: int2GV 0 :: nil))(oresult:=None); eauto.

        ret_insn.
          eapply Opsem.sReturn; eauto.
            unfold Opsem.returnUpdateLocals. simpl.
            clear - Hrsim Heqogr Hwfg Hwfmi.
            symmetry in Heqogr.
            eapply simulation__getOperandValue in Heqogr; eauto.
            destruct Heqogr as [gv' [J1 J2]]. 
            replace (@Opsem.getOperandValue DGVs) with LLVMgv.getOperandValue; 
              auto.
            rewrite J1. auto.

        next_insn' M2'''.
          destruct (@dstk_is_found (los, nts) Ps2 lc2 gl2 fs2)as [fptr2 [J1 J2]].
          eapply Opsem.sExCall; simpl; eauto.
            eapply dstk_spec; eauto.

      split; auto using inject_incr_refl.
      SSSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next, 
                                   cmds_at_block_tails_next').
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          repeat (split; auto).

  SCase "nret = false".
    assert (In i0 (getFdefLocs (fdef_intro fh1' bs1'))) as Hin.
      eauto using getCmdID_in_getFdefLocs.
    destruct t; tinv H1.
    remember (lift_op1 DGVs (fit_gv (los, nts) t) gr t) as Fit.
    destruct Fit; tinv H1. simpl in Hcall'.
    symmetry in Heqogr.
    eapply simulation__getOperandValue in Heqogr; eauto.
    destruct Heqogr as [gr2 [J1 J2]]. 
    symmetry in HeqFit. 
    Local Transparent lift_op1. simpl in HeqFit.
    unfold MDGVs.lift_op1 in HeqFit.
    eapply simulation__fit_gv in HeqFit; eauto.
    destruct HeqFit as [gr2' [HeqFit HinjFit]].

    destruct (isPointerTypB t); inv H1.
    SSCase "ct is ptr".
      remember (lookupAL (id * id) rm2' i0) as R.
      destruct R as [[bid0 eid0]|]; inv Hcall'.

      exists (Opsem.mkState 
        ((Opsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' 
            (updateAddALs _ lc2' 
              ((i0,gr2')::(bid0,bgv2)::(eid0,egv2)::nil))
            als2'):: ECs2)
        M2''').
      exists mi.
      split.
      SSSSCase "sop_star".
        Opaque updateAddALs. simpl. 
        next_insn' M2'.
          destruct (@ssb_is_found (los, nts) Ps2 lc2 gl2 fs2) as [fptr2 [Z1 Z2]].
          eapply Opsem.sExCall with (fid:=ssb_fid)
            (gvs:=(bgv2 :: int2GV 0 :: nil))(oresult:=None); eauto.
      
        next_insn' M2''.
          destruct (@sse_is_found (los, nts) Ps2 lc2 gl2 fs2) as [fptr2 [Z1 Z2]].
          eapply Opsem.sExCall with (fid:=sse_fid)
            (gvs:=(egv2 :: int2GV 0 :: nil))(oresult:=None); eauto.
      
        ret_insn.
          eapply Opsem.sReturn; eauto.
            unfold Opsem.returnUpdateLocals.
            replace (@Opsem.getOperandValue DGVs) with LLVMgv.getOperandValue; 
              auto.   
            rewrite J1. simpl. unfold MDGVs.lift_op1. rewrite HeqFit. auto.
      
        next_insn.
          destruct (@gsb_is_found (los, nts) Ps2 lc2 gl2 fs2) as [fptr2 [Z1 Z2]].
          eapply Opsem.sExCall with (fid:=gsb_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some bgv2); eauto.
            simpl. eauto.
            clear - Hfree2' Hgbase.
            eapply free_doesnt_change_gsb; eauto.
            unfold gsb_typ, p8. simpl.
            inv Hinj1. inv H6. inv H5. auto.
      
        next_insn.
          destruct (@gse_is_found (los, nts) Ps2 lc2 gl2 fs2) as [fptr2 [Z1 Z2]].
          eapply Opsem.sExCall with (fid:=gse_fid)
            (gvs:=(int2GV 0 :: nil))(oresult:=Some egv2); eauto.
            simpl. eauto.
            clear - Hfree2' Hgbound.
            eapply free_doesnt_change_gse; eauto.
            unfold gsb_typ, p8. simpl.
            inv Hinj2. inv H6. inv H5. auto.
      
        next_insn.
          destruct (@dstk_is_found (los, nts) Ps2 lc2 gl2 fs2)as [fptr2 [Z1 Z2]].
          eapply Opsem.sExCall; simpl; eauto.
            eapply dstk_spec; eauto.
      
      split; auto using inject_incr_refl.
      SSSSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next, 
                                   cmds_at_block_tails_next').
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          split; auto.              
          split.
            Transparent updateAddALs. simpl.
            eapply reg_simulation__updateAddAL_prop with (ex_ids3:=ex_ids'); 
              eauto using simulation___cgv2gv.
            repeat (split; auto).

    SSCase "ct isnt ptr".
      inv Hcall'.

      exists (Opsem.mkState
        ((Opsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' (updateAddALs _ lc2' ((i0,gr2')::nil))
            als2'):: ECs2)
        M2''').
      exists mi.
      split.
      SSSSCase "sop_star".
        Opaque updateAddALs. simpl. 
        next_insn' M2'.
          destruct (@ssb_is_found (los, nts) Ps2 lc2 gl2 fs2) as [fptr2 [Z1 Z2]].
          eapply Opsem.sExCall with (fid:=ssb_fid)
            (gvs:=(bgv2 :: int2GV 0 :: nil))(oresult:=None); eauto.

        next_insn' M2''.
          destruct (@sse_is_found (los, nts) Ps2 lc2 gl2 fs2) as [fptr2 [Z1 Z2]].
          eapply Opsem.sExCall with (fid:=sse_fid)
            (gvs:=(egv2 :: int2GV 0 :: nil))(oresult:=None); eauto.

        ret_insn.
          eapply Opsem.sReturn; eauto.
            unfold Opsem.returnUpdateLocals. simpl.
            replace (@Opsem.getOperandValue DGVs) with LLVMgv.getOperandValue; 
              auto.
            rewrite J1. simpl. unfold MDGVs.lift_op1. rewrite HeqFit. auto.

        next_insn' M2'''.
          destruct (@dstk_is_found (los, nts) Ps2 lc2 gl2 fs2)as [fptr2 [Z1 Z2]].
          eapply Opsem.sExCall; simpl; eauto.
            eapply dstk_spec; eauto.

      split; auto using inject_incr_refl.
      SSSSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next, 
                                   cmds_at_block_tails_next').
          exists ex_ids'. exists rm2'.
          exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
          apply reg_simulation__updateAddAL_lc with (i0:=i0)(gv:=g)
            (gv':= gr2') (ex_ids3:=ex_ids') in Hrsim'; 
            eauto using simulation___cgv2gv.
          Transparent updateAddALs. simpl.
          repeat (split; auto).

Qed.

Lemma SBpass_is_correct__dsReturnVoid : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block)
  (rid : id) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) (F' : fdef) (B' : block) (c' : cmd) (tmn' : terminator)
  (lc' : DGVMap) (rm' : SBspecAux.rmetadata) (EC : list SBspec.ExecutionContext)
  (cs' : list cmd) (Mem : mem) (MM : SBspecAux.mmetadata) (als : list mblock)
  (als' : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           SBspec.ECS := {|
                          SBspec.CurFunction := F;
                          SBspec.CurBB := B;
                          SBspec.CurCmds := nil;
                          SBspec.Terminator := insn_return_void rid;
                          SBspec.Locals := lc;
                          SBspec.Rmap := rm;
                          SBspec.Allocas := als |}
                          :: {|
                             SBspec.CurFunction := F';
                             SBspec.CurBB := B';
                             SBspec.CurCmds := c' :: cs';
                             SBspec.Terminator := tmn';
                             SBspec.Locals := lc';
                             SBspec.Rmap := rm';
                             SBspec.Allocas := als' |} :: EC;
           SBspec.Mem := Mem;
           SBspec.Mmap := MM |} Cfg St)
  (Mem' : mem)
  (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas TD Mem als = ret Mem')
  (H1 : getCallerReturnID c' = merror),
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
                        SBspec.CurFunction := F';
                        SBspec.CurBB := B';
                        SBspec.CurCmds := cs';
                        SBspec.Terminator := tmn';
                        SBspec.Locals := lc';
                        SBspec.Rmap := rm';
                        SBspec.Allocas := als' |} :: EC;
         SBspec.Mem := Mem';
         SBspec.Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof. 
  intros.
  destruct_ctx_return.
  inv Htcmds.
  simpl in H1.
  destruct n; inv H1.
  unfold call_suffix in Hcall'. inv Hcall'.
  inv Httmn.
  eapply free_allocas_sim in HsimM; eauto.
  destruct HsimM as [M2' [Hfree2' [Hmsim2' Hwfmi2']]].
  exists (Opsem.mkState
        ((Opsem.mkEC (fdef_intro fh2' bs2') B2'
            (cs23' ++ cs24') tmn2' lc2' als2'):: ECs2)
        M2').
  exists mi.
  split.
    SCase "sop_star".
      simpl. ret_insn.
        eapply Opsem.sReturnVoid; eauto.
    
      next_insn.
        destruct (@dstk_is_found (los, nts) Ps2 lc2 gl2 fs2)as [fptr2 [Z1 Z2]].
        eapply Opsem.sExCall; simpl; eauto.
          eapply dstk_spec; eauto.
    
    split; auto using inject_incr_refl.
    SSSCase "sim".
    repeat (split; eauto 2 using cmds_at_block_tail_next, 
                                 cmds_at_block_tails_next').
        exists ex_ids'. exists rm2'.
        exists ex_ids3'. exists ex_ids4'. exists cs23'. exists cs24'.
        repeat (split; auto).
Qed.

Require Import sb_ds_trans_cmd_cases.
Require Import sb_ds_trans_mem_cases.
*)

Lemma mismatch_cons_false : forall A ECs (EC:A), ECs = EC :: ECs -> False.
Proof.
  induction ECs; intros; inversion H; eauto.
Qed.

Ltac ctx_simpl_aux :=
  match goal with
  | [H1 : lookupExFdecViaPtr ?Ps ?fs ?gv = _,
     H2 : lookupExFdecViaPtr ?Ps ?fs ?gv = _ |- _ ] => 
    rewrite H1 in H2; inv H2
  | [H1 : getOperandValue ?TD ?vp ?lc ?gl = _,
     H2 : getOperandValue ?TD ?vp ?lc ?gl = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : getTypeAllocSize ?TD ?t = _,
     H2 : getTypeAllocSize ?TD ?t = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : malloc ?TD ?Mem0 ?tsz0 ?gn ?align0 = _,
     H2 : malloc ?TD ?Mem0 ?tsz0 ?gn ?align0 = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : Opsem.params2GVs ?TD ?lp ?lc ?gl = _,
     H2 : Opsem.params2GVs ?TD ?lp ?lc ?gl = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : callExternalFunction ?Mem0 ?fid ?gvs = _,
     H2 : callExternalFunction ?Mem0 ?fid ?gvs = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H : updateAddAL _ ?lc ?id0 _ = updateAddAL _ ?lc ?id0 _ |- _ ] => rewrite H
  | [H1 : mload ?TD ?m ?gv ?t ?a = _,
     H2 : mload ?TD ?m ?gv ?t ?a = _ |- _ ] => rewrite H1 in H2; inv H2
  | [H1 : Opsem.params2GVs ?TD ?lp ?lc ?gl = _,
     H2 : Opsem.params2GVs ?TD ?lp ?lc ?gl = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  | [H1 : callExternalFunction ?Mem0 ?fid ?gvs = _,
     H2 : callExternalFunction ?Mem0 ?fid ?gvs = _ |- _ ] =>
    rewrite H1 in H2; inv H2
  end.

Ltac ctx_simpl := repeat dgvs_instantiate_inv; repeat ctx_simpl_aux. 

Definition get_next_chunk (sbEC:SBspec.ExecutionContext) : option (list cmd) :=
  match sbEC with
  | SBspec.mkEC f1 _ (c::cs12) _ _ _ _ =>
    let '(los, nts) := TD in
    match gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids, rm2) /\



         trans_cmds ex_ids3 rm2 cs12 = Some (ex_ids4,cs22) /\
         trans_terminator rm2 tmn1 = Some cs23 /\
         cs2 = cs22 ++ cs23
  end.


Lemma SBpass_is_bcorrect : forall mi mgb sbCfg sbSt Cfg St St' tr,
  sbState_bsimulates_State mi mgb sbCfg sbSt Cfg St ->
  Opsem.sop_star Cfg St St' tr ->
  exists sbSt', exists mi',
    SBspec.sInsn sbCfg sbSt sbSt' tr /\
    sbState_bsimulates_State mi' mgb sbCfg sbSt' Cfg St' /\
    Values.inject_incr mi mi'.
Proof.
  intros mi mgb sbCfg sbSt Cfg St St' tr Hsim Hop.
  inv Hop.
  rename H into Hsbop.
  rename H0 into Hllvmop.
  (sb_sInsn_cases (induction Hsbop) Case); inv Hllvmop; ctx_simpl. 
Case "sReturn". eapply SBpass_is_correct__dsReturn; eauto.
Case "sReturnVoid". eapply SBpass_is_correct__dsReturnVoid; eauto.
Case "sBranch". eapply SBpass_is_correct__dsBranch; eauto.
Case "sBranch_uncond". eapply SBpass_is_correct__dsBranch_uncond; eauto.
Case "sBop". eapply SBpass_is_correct__dsBop; eauto.
Case "sFBop". eapply SBpass_is_correct__dsFBop; eauto.
Case "sExtractValue". eapply SBpass_is_correct__dsExtractValue; eauto.
Case "sInsertValue". eapply SBpass_is_correct__dsInsertValue; eauto.
Case "sMalloc". eapply SBpass_is_correct__dsMalloc; eauto.
Case "sFree". eapply SBpass_is_correct__dsFree; eauto.
Case "sAlloca". eapply SBpass_is_correct__dsAlloca; eauto.
Case "sLoad_nptr". eapply SBpass_is_correct__dsLoad_nptr; eauto.
Case "sLoad_ptr". eapply SBpass_is_correct__dsLoad_ptr; eauto.
Case "sStore_nptr". eapply SBpass_is_correct__dsStore_nptr; eauto.
Case "sStore_ptr". eapply SBpass_is_correct__dsStore_ptr; eauto.
Case "sGEP". eapply SBpass_is_correct__dsGEP; eauto.
Case "sTrunc". eapply SBpass_is_correct__dsTrunc; eauto.
Case "sExt". eapply SBpass_is_correct__dsExt; eauto.
Case "sBitcast_nptr". eapply SBpass_is_correct__dsBitcase_nptr; eauto.
Case "sBitcast_ptr". eapply SBpass_is_correct__dsBitcase_ptr; eauto.
Case "sInttoptr". eapply SBpass_is_correct__dsInttoptr; eauto.
Case "sOthercast". eapply SBpass_is_correct__dsOthercast; eauto.
Case "sIcmp". eapply SBpass_is_correct__dsIcmp; eauto.
Case "sFcmp". eapply SBpass_is_correct__dsFcmp; eauto.
Case "sSelect_nptr". eapply SBpass_is_correct__dsSelect_nptr; eauto.
Case "sSelect_ptr". 
  eapply SBpass_is_correct__dsSelect_ptr; eauto.
  unfold prop_reg_metadata.
  destruct (isGVZero TD c); eauto.
Case "sCall". 
  eapply SBpass_is_correct__dsCall; eauto.
  apply mismatch_cons_false in H27. inv H27.
Case "sExCall". 
  symmetry in H32. apply mismatch_cons_false in H32. inv H32.
  eapply SBpass_is_correct__dsExCall; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)


