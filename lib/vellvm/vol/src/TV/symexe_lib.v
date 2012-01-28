Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import alist.
Require Import infrastructure_props.
Require Import CoqListFacts.
Require Import Coqlib.
Require Import opsem_props.
Require Import dopsem.
Require Import symexe_def.

Export SimpleSE.
Export OpsemProps.

(* cmd2sbs *)

Lemma cmds2sbs_nil_inv : forall cs,
  cmds2sbs cs = (nil, nil) ->
  cs = nil.
Proof.
  destruct cs; intros; auto.
    simpl in H.
    destruct (isCall_dec c).
      destruct (cmds2sbs cs).
      destruct l0.
        inversion H.
        destruct s. inversion H.
      destruct (cmds2sbs cs).
      inversion H.
Qed.

Lemma cmds2sb_inv : forall cs sb,
  cmds2sbs cs = (sb::nil, nil) ->
  exists cs', exists call0,
    cs = cs'++call0::nil /\
    cmds2sbs cs' = (nil, NBs sb) /\
    call_cmd sb = call0.
Proof.
  induction cs; intros; simpl in *.
    inversion H.

    remember (cmds2sbs cs) as R.
    remember (isCall_dec a) as R'.
    destruct R'.
      destruct R.
      destruct l0.
        inversion H.

        destruct s. inversion H; subst. clear H.
        destruct (@IHcs (mkSB NBs0 call_cmd0 call_cmd_isCall0)) 
          as [cs' [call0 [J1 [J2 J3]]]]; subst; auto.
        clear IHcs.
        simpl in *.
        exists (a::cs').
        exists (call_cmd0).
        split; auto.
        split; auto.
          simpl.
          rewrite J2.
          rewrite <- HeqR'. auto.

      destruct R.
      inversion H; subst. clear H.
      symmetry in HeqR.
      apply cmds2sbs_nil_inv in HeqR. subst.
      exists nil. exists a.
      split; auto.
Qed.

Definition dbCmds__cmds2nbs : forall TD lc als gl Mem1 cs lc' als' Mem2 tr, 
  dbCmds TD gl lc als Mem1 cs lc' als' Mem2 tr ->
  exists nbs, cmds2sbs cs = (nil, nbs).
Proof.
  intros.
  induction H; simpl.
    exists nil. auto.

    destruct IHdbCmds as [nbs J].
    destruct (isCall_dec c).
      rewrite J. exists (mkNB c e::nbs). auto.

      apply dbCmd_isNotCallInst in H.
      rewrite e in H. inversion H.
Qed.

Lemma dbCall_isCall : forall S TD Ps lc gl fs Mem1 c lc' Mem2 tr,
  dbCall S TD Ps fs gl lc Mem1 c lc' Mem2 tr ->
  isCall c = true.
Proof.
  intros S TD Ps lc gl fs Mem1 c lc' Mem2 tr HdbCall.
  induction HdbCall; auto.
Qed.

Lemma cmdscall2sbs : forall cs call0 nbs
  (isCall0:isCall call0=true),
  cmds2sbs cs = (nil, nbs) ->
  isCall_dec call0 = right isCall0 ->
  cmds2sbs (cs++call0::nil) = (mkSB nbs call0 isCall0::nil, nil).
Proof.
  induction cs; intros; simpl in *.
    inversion H; subst.
    rewrite H0. auto.

    destruct (isCall_dec a).
      remember (cmds2sbs cs) as R.
      destruct R.
      destruct l0.
        inversion H; subst. clear H.
        apply IHcs with (nbs:=l1) in H0; auto.
        rewrite H0; auto.
     
        destruct s. inversion H.

      destruct (cmds2sbs cs).
      inversion H.
Qed.

Lemma dbSubblock__cmds2sb : 
  forall S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr,
  dbSubblock S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  exists sb, cmds2sbs cs = (sb::nil, nil).
Proof.
  intros.
  inversion H; subst.
  apply dbCmds__cmds2nbs in H0.
  destruct H0 as [nbs H0].
  remember (isCall_dec call0) as R.
  destruct R.
    apply dbCall_isCall in H1.
    rewrite e in H1. inversion H1.

    exists (mkSB nbs call0 e).
    apply cmdscall2sbs; auto.
Qed.

Lemma cmds_cons2sbs : forall cs cs' sb sbs',
  cmds2sbs cs = (sb::nil, nil) ->
  cmds2sbs cs' = (sbs', nil) ->
  cmds2sbs (cs++cs') = (sb::sbs', nil).
Proof.
  induction cs; intros; simpl.
    simpl in H. inversion H.

    simpl in H.
    destruct (isCall_dec a).
      remember (cmds2sbs cs) as R.
      destruct R.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          apply IHcs with (sb:=mkSB NBs0 call_cmd0 call_cmd_isCall0) in H0; auto.
          clear IHcs.
          rewrite H0. auto.
 
      remember (cmds2sbs cs) as R.
      destruct R.
      inversion H; subst. clear H.
      symmetry in HeqR.
      apply cmds2sbs_nil_inv in HeqR. subst.
      simpl.
      rewrite H0. auto.
Qed.

Lemma dbSubblocks__cmds2sbs : 
  forall S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr,
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  exists sbs, cmds2sbs cs = (sbs, nil).
Proof.
  intros.
  induction H; simpl.
    exists nil. auto.

    apply dbSubblock__cmds2sb in H.
    destruct H as [sb H].
    destruct IHdbSubblocks as [sbs H1].
    exists (sb::sbs).
    apply cmds_cons2sbs; auto.
Qed.

Lemma cmds_cons2sbs_inv : forall cs cs' sbs0 sb sbs',
  cmds2sbs (cs++cs') = (sbs0, nil) ->
  cmds2sbs cs = (sb::nil, nil) ->
  cmds2sbs cs' = (sbs', nil) ->
  sbs0 = sb::sbs'.
Proof.
  intros.
  apply cmds_cons2sbs with (cs':=cs')(sbs':=sbs') in H0; auto.
  rewrite H in H0.
  inversion H0; auto.
Qed.

Lemma cmds2sbs_cons_inv : forall cs0 sb sbs',
  cmds2sbs cs0 = (sb::sbs', nil) ->
  exists cs, exists cs',
    cmds2sbs cs = (sb::nil, nil) /\
    cmds2sbs cs' = (sbs', nil) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.

    simpl in H.
    remember (isCall_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          destruct (@IHcs0 (mkSB NBs0 call_cmd0 call_cmd_isCall0) sbs') 
            as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
          exists (a::cs). exists cs'.
          split; auto.
            simpl.
            rewrite <- HeqR.
            rewrite J1. auto.

      destruct R'.
      inversion H; subst. clear H.
      destruct sbs'.
        symmetry in HeqR'.
        apply cmds2sbs_nil_inv in HeqR'. subst.
        exists (a::nil). exists nil.
        simpl. rewrite <- HeqR. auto.

        destruct (@IHcs0 s sbs') as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
        exists (a::nil). exists (cs++cs').
        simpl. rewrite <- HeqR. auto.
Qed.

Lemma cmds_rcons2sbs : forall cs cs' sbs nbs,
  cmds2sbs cs = (sbs, nil) ->
  cmds2sbs cs' = (nil, nbs) ->
  cmds2sbs (cs++cs') = (sbs, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; subst. auto.

    simpl in *.
    remember (cmds2sbs cs) as R.
    destruct (isCall_dec a).
      destruct R.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          apply IHcs with (sbs:=mkSB NBs0 call_cmd0 call_cmd_isCall0::l0) in H0; 
            auto.
          rewrite H0. auto.

      destruct R.
      inversion H; subst. clear H.
      apply IHcs with (sbs:=l0) in H0; auto.
      rewrite H0. auto.
Qed.

Lemma cmds_rcons2sbs_inv : forall cs cs' sbs0 nbs0 sbs nbs,
  cmds2sbs (cs++cs') = (sbs0, nbs0) ->
  cmds2sbs cs = (sbs, nil) ->
  cmds2sbs cs' = (nil, nbs) ->
  sbs0 = sbs /\ nbs0 = nbs.
Proof.
  intros.
  apply cmds_rcons2sbs with (cs':=cs')(nbs:=nbs) in H0; auto.
  rewrite H in H0. inversion H0; auto.
Qed.
 
Lemma cmds2nbranchs__cmds2nbs : forall cs nbs,
  cmds2nbranchs cs = Some nbs ->
  cmds2sbs cs = (nil, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; auto.

    simpl in *.
    unfold cmd2nbranch in H.
    destruct (isCall_dec a).
      destruct (cmds2sbs cs).
        remember (cmds2nbranchs cs) as R.
        destruct R.
          inversion H; subst. clear H.
          assert (ret l2 = ret l2) as EQ. auto.
          apply IHcs in EQ.
          inversion EQ; subst. auto.

          inversion H.
      inversion H.
Qed.

Lemma cmds2nbs__nbranchs2cmds : forall nbs cs,
  cmds2sbs cs = (nil, nbs) ->
  nbranchs2cmds nbs = cs.
Proof.
  induction nbs; intros.
    apply cmds2sbs_nil_inv in H. subst. auto.

    simpl.
    destruct a.
    destruct cs.
      simpl in H. inversion H.

      simpl in H.
      destruct (isCall_dec c).
        remember (cmds2sbs cs) as R.
        destruct R.
        destruct l0.
          inversion H; subst.
          rewrite IHnbs with (cs:=cs); auto.

          destruct s.
          inversion H; subst.

        destruct (cmds2sbs cs).
        inversion H.
Qed.


Lemma cmds2nbranchs__nbranchs2cmds : forall cs nbs,
  cmds2nbranchs cs = Some nbs ->
  nbranchs2cmds nbs = cs.
Proof.
  intros.
  apply cmds2nbs__nbranchs2cmds.
  apply cmds2nbranchs__cmds2nbs; auto.
Qed.

Lemma cmds2sbs_inv : forall cs sbs nbs,
  cmds2sbs cs = (sbs, nbs) ->
  exists cs1, exists cs2, 
    cs = cs1++cs2 /\
    cmds2sbs cs1 = (sbs, nil) /\
    cmds2sbs cs2 = (nil, nbs).
Proof.
  induction cs; intros.
    simpl in H. inversion H; subst.
    exists nil. exists nil. auto.

    simpl in H.
    remember (isCall_dec a) as R.
    remember (cmds2sbs cs) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H; subst. clear H.
          
          destruct (@IHcs nil l1) as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
          apply cmds2sbs_nil_inv in J2. subst.
          exists nil. exists (a::cs2).
          simpl. rewrite <- HeqR. 
          simpl in HeqR'. rewrite <- HeqR'.
          split; auto.

       destruct s.
       inversion H; subst. clear H.
       destruct (@IHcs (mkSB NBs0 call_cmd0 call_cmd_isCall0::l0) nbs) 
         as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
       clear IHcs.
       exists (a::cs1). exists cs2.
       simpl. rewrite <- HeqR. rewrite J2. auto.
    
     destruct R'.
     inversion H; subst. clear H.
     destruct (@IHcs l0 nbs) as [cs1 [cs2 [J1 [J2 J3]]]]; subst; auto.
     clear IHcs.
     exists (a::cs1). exists cs2.
     simpl. rewrite <- HeqR. rewrite J2. auto.
Qed.

Lemma cmds2sbs_cons_inv' : forall cs0 sb sbs' nbs,
  cmds2sbs cs0 = (sb::sbs', nbs) ->
  exists cs, exists cs',
    cmds2sbs cs = (sb::nil, nil) /\
    cmds2sbs cs' = (sbs', nbs) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.

    simpl in H.
    remember (isCall_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.

          destruct s. inversion H; subst. clear H.
          destruct (@IHcs0 (mkSB NBs0 call_cmd0 call_cmd_isCall0) sbs' nbs) 
            as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
          exists (a::cs). exists cs'.
          split; auto.
            simpl.
            rewrite <- HeqR.
            rewrite J1. auto.

      destruct R'.
      inversion H; subst. clear H.
      destruct sbs'.
        symmetry in HeqR'.
        exists (a::nil). exists cs0.
        simpl. rewrite <- HeqR. auto.

        destruct (@IHcs0 s sbs' nbs) as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
        exists (a::nil). exists (cs++cs').
        simpl. rewrite <- HeqR. auto.
Qed.
  
Lemma cmds2nbs_app_inv : forall cs0 nbs1 nbs2,
  cmds2sbs cs0 = (nil, nbs1++nbs2) ->
  exists cs, exists cs',
    cmds2sbs cs = (nil, nbs1) /\
    cmds2sbs cs' = (nil, nbs2) /\
    cs0 = cs++cs'.
Proof.
  induction cs0; intros.
    simpl in H. inversion H.
    symmetry in H1.
    apply app_eq_nil in H1.
    destruct H1; subst.
    exists nil. exists nil. auto.

    simpl in H.
    remember (isCall_dec a) as R.
    remember (cmds2sbs cs0) as R'.
    destruct R.
      destruct R'.
        destruct l0.
          inversion H.
          apply cons_eq_app in H1.
          destruct H1 as [[qs [J1 J2]] | [J1 J2]]; subst.
            destruct (@IHcs0 qs nbs2) as [cs [cs' [J1 [J2 J3]]]]; subst; auto.
            clear IHcs0.
            exists (a::cs). exists cs'.
            simpl. rewrite <- HeqR. rewrite J1. split; auto.

            exists nil. exists (a::cs0). 
            simpl. rewrite <- HeqR. rewrite <- HeqR'. split; auto.

          destruct s. inversion H; subst.

      destruct R'.
      inversion H; subst. 
Qed.

Lemma nbranchs2cmds_app : forall nbs1 nbs2,
  nbranchs2cmds (nbs1++nbs2) = nbranchs2cmds nbs1 ++ nbranchs2cmds nbs2.
Proof.
  induction nbs1; intros; auto.
    simpl. destruct a. rewrite IHnbs1. auto.
Qed.

Lemma cmds_cons2nbranchs_inv : forall c cs' nbs,
  cmds2nbranchs (c::cs') = Some nbs ->
  exists nb, exists nbs',
    cmd2nbranch c = Some nb /\
    cmds2nbranchs cs' = Some nbs' /\
    nbs = nb::nbs'.
Proof.
  intros.
  simpl in H.
  destruct (cmd2nbranch c); try solve [inversion H].
  destruct (cmds2nbranchs cs'); inversion H; subst.
  exists n. exists l0. auto.
Qed.

Lemma cmd2nbranch_Some_isCallInst : forall c nb,
  cmd2nbranch c = Some nb ->
  exists H, nb = mkNB c H.
Proof.
  intros.
  unfold cmd2nbranch in H.
  destruct nb.
  destruct (isCall_dec c); inversion H; subst.
    exists notcall0. auto. 
Qed.

(* wf *)
Lemma wf_nbranchs__decomposes__app : forall nbs1 nbs2,
  wf_nbranchs (nbs1++nbs2) ->
  wf_nbranchs nbs1 /\ wf_nbranchs nbs2.
Proof.
  intros.
  inversion H; subst.
  apply cmds2nbs_app_inv in H0.
  destruct H0 as [cs1 [cs2 [J1 [J2 J3]]]]; subst.
  rewrite getCmdsLocs_app in H1.
  apply NoDup_inv in H1.
  destruct H1.
  split; eapply wf_nbranchs_intro; eauto.
Qed.

Lemma wf_nbranchs__inv : forall nb nbs,
  wf_nbranchs (nb::nbs) ->
  wf_nbranchs nbs.
Proof.
  intros.
  simpl_env in H.
  apply wf_nbranchs__decomposes__app in H.
  destruct H; auto.
Qed.

Lemma wf_nbranchs_nil : wf_nbranchs nil.
Proof.
  apply wf_nbranchs_intro with (cs:=nil); simpl; auto using NoDup_nil.
Qed.

Hint Resolve wf_nbranchs_nil.

Lemma uniqCmds___wf_subblocks_wf_nbranchs : forall cs sbs nbs,
  NoDup (getCmdsLocs cs) ->
  cmds2sbs cs = (sbs, nbs) ->
  wf_subblocks sbs /\ wf_nbranchs nbs.
Proof.
  induction cs; intros.
    simpl in H0. inversion H0; subst.
    split; auto using wf_nbranchs_nil.

    simpl in *.
    remember (cmds2sbs cs) as R.
    destruct R as [sbs' nbs'].
    remember (isCall_dec a) as R'.
    destruct R'.
      destruct sbs'.
        inversion H0; subst. clear H0.
        split; auto.
          apply wf_nbranchs_intro with (cs:=a::cs); auto.
            simpl.
            rewrite <- HeqR'.
            rewrite <- HeqR. auto.

        destruct s. 
        inversion H0; subst. clear H0.
        inversion H; subst.
        apply IHcs with (nbs0:=nbs)(sbs:=mkSB NBs0 call_cmd0 call_cmd_isCall0::
          sbs') in H3; auto.
        destruct H3 as [H3 H4].
        split; auto.
          inversion H3; subst.
          apply wf_subblocks_cons; auto.
            apply wf_subblock_intro.

            symmetry in HeqR.
            apply cmds2sbs_cons_inv' in HeqR.
            destruct HeqR as [cs1 [cs2 [Hcs1NBs0call0 [Hcs2sbs EQ]]]]; subst.
            apply cmds2sb_inv in Hcs1NBs0call0.
            destruct Hcs1NBs0call0 as [cs1' [call0 [EQ [Hcs1'nbs EQ']]]]; subst.
            simpl in *.
            simpl_env in H.
            rewrite getCmdsLocs_app in H.
            rewrite ass_app in H.
            apply NoDup_inv in H. destruct H as [H _].
            apply wf_nbranchs_intro with (cs:=a::cs1'); auto.
              simpl.
              rewrite <- HeqR'.
              rewrite Hcs1'nbs. auto.

      inversion H0; subst. clear H0.
      simpl_env in H.
      apply NoDup_inv in H. destruct H as [H1 H2].
      apply IHcs with (sbs:=sbs')(nbs0:=nbs) in H2; auto.
      destruct H2.
      split; auto.
        apply wf_subblocks_cons; auto.
          apply wf_subblock_intro; auto.
Qed.

Lemma uniqBlock__wf_block : forall B,
  uniqBlocks [B] -> wf_block B.
Proof.
  intros B HuniqBlocks.
  unfold uniqBlocks in HuniqBlocks.
  simpl in HuniqBlocks. destruct B.
  destruct HuniqBlocks as [J1 J2].
  remember (cmds2sbs c) as R.
  destruct R as [sbs nbs].
  simpl in J2. simpl_env in J2.
  apply NoDup_inv in J2. destruct J2.
  apply NoDup_inv in H0. destruct H0.
  apply uniqCmds___wf_subblocks_wf_nbranchs with (sbs:=sbs)(nbs:=nbs) in H0;auto.
  destruct H0.
  apply wf_block_intro with (sbs:=sbs)(nbs:=nbs); auto.
Qed.

Lemma uniqBlocks__wf_block : forall lb n B,
  uniqBlocks lb ->
  nth_error lb n = Some B ->
  wf_block B.
Proof.
  induction lb; intros.
    apply nil_nth_error_Some__False in H0.
    inversion H0.

    apply nth_error_cons__inv in H0.
    simpl_env in H. 
    apply uniqBlocks_inv in H.
    destruct H as [J1 J2].
    destruct H0 as [EQ | [n' [EQ H0]]]; subst; eauto.
      apply uniqBlock__wf_block; auto.
Qed.

Lemma uniqFdef__wf_block : forall fh lb n B,
  uniqFdef (fdef_intro fh lb) ->
  nth_error lb n = Some B ->
  wf_block B.
Proof.
  intros.
  unfold uniqFdef in H.
  eapply uniqBlocks__wf_block; eauto.
    destruct fh. inversion H; auto.
Qed.

(* Properties of se *)
Lemma se_cmd_uniq : forall smap0 sm0 sf0 se0 c,
  uniq smap0 ->
  uniq (STerms (se_cmd (mkSstate smap0 sm0 sf0 se0) c)).
Proof.
  intros smap0 sm0 sf0 se0 [c nocall] Huniq.
  destruct c; simpl; 
    try solve [
      apply updateAddAL_uniq; auto | 
      auto | 
      inversion nocall].
Qed.

Lemma se_cmd_dom_mono : forall smap0 sm0 sf0 se0 c,
  dom smap0 [<=] dom (STerms (se_cmd (mkSstate smap0 sm0 sf0 se0) c)).
Proof.
  intros smap0 sm0 sf0 se0 [c nocall].
  assert (forall sm id0 st0, dom sm [<=] dom (updateAddAL sterm sm id0 st0))as J.
    intros. assert (J:=@updateAddAL_dom_eq _ sm id0 st0). fsetdec. 
  destruct c; simpl; try solve [eauto using J| fsetdec].
    destruct v; simpl; try solve [simpl in nocall; inversion nocall].
Qed.

Lemma se_cmd_uniq_aux : forall c sstate0,
  uniq (STerms sstate0) ->
  uniq (STerms (se_cmd sstate0 c)).
Proof.
  intros [c nocall] sstate0 Huniq.
  destruct c; simpl; try solve [apply updateAddAL_uniq; auto | auto].
    destruct v; simpl; try solve [simpl in nocall; inversion nocall].
Qed.

Lemma se_cmds_uniq_aux : forall cs sstate0,
  uniq (STerms sstate0) ->
  uniq (STerms (se_cmds sstate0 cs)).
Proof.
  induction cs; intros; simpl; auto using se_cmd_uniq_aux.
Qed.

Lemma se_cmds_uniq : forall cs smap0 sm0 sf0 se0,
  uniq smap0 ->
  uniq (STerms (se_cmds (mkSstate smap0 sm0 sf0 se0) cs)).
Proof.
  intros.
  apply se_cmds_uniq_aux; auto. 
Qed.

Lemma se_cmds_init_uniq : forall cs,
  uniq (STerms (se_cmds sstate_init cs)).
Proof.
  unfold sstate_init. intro. auto using se_cmds_uniq.
Qed.

Lemma se_cmds_rev_cons : forall cs c sstate0,
  se_cmds sstate0 (cs++c::nil) = se_cmd (se_cmds sstate0 cs) c.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmds_app : forall cs cs' sstate0,
  se_cmds sstate0 (cs++cs') = se_cmds (se_cmds sstate0 cs) cs'.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmds_cons : forall cs c sstate0,
  se_cmds sstate0 ((c::nil)++cs) = se_cmds (se_cmd sstate0 c) cs.
Proof.
  induction cs; intros; simpl; auto.
Qed.

Lemma se_cmd_dom_upper : forall sstate0 c nc,
  dom (STerms (se_cmd sstate0 (mkNB c nc))) [<=] 
    dom (STerms sstate0) `union` {{getCmdLoc c}}.
Proof.
  intros [smap0 sm0 sf0 se0] c nc.
  destruct c; simpl; try solve [rewrite updateAddAL_dom_eq; fsetdec | fsetdec].
    destruct v; simpl; try solve [simpl in nc; inversion nc].
Qed.

Lemma se_cmd_dom_mono' : forall sstate0 c,
  dom (STerms sstate0) [<=] dom (STerms (se_cmd sstate0 c)).
Proof.
  intros [smap0 sm0 sf0 se0] c. 
  simpl.
  apply se_cmd_dom_mono; auto.
Qed.

Definition se_cmds_dom_mono_prop (cs:list nbranch) :=
  forall smap0 sm0 sf0 se0,
  dom smap0 [<=]
    dom (STerms (se_cmds (mkSstate smap0 sm0 sf0 se0) cs)).

Lemma se_cmds_dom_mono: forall cs, se_cmds_dom_mono_prop cs.
Proof.
  apply (@rev_ind nbranch); unfold se_cmds_dom_mono_prop; intros; simpl.
    fsetdec.

    rewrite se_cmds_rev_cons.
    assert (J:=@se_cmd_dom_mono' (se_cmds (mkSstate smap0 sm0 sf0 se0) l0) x).
    assert (J':=@H smap0 sm0 sf0 se0).
    fsetdec.
Qed.

Lemma se_cmds_dom_mono' : forall sstate0 cs,
  dom (STerms sstate0) [<=] dom (STerms (se_cmds sstate0 cs)).
Proof.
  intros [smap0 sm0 sf0 se0] cs. 
  simpl.
  apply se_cmds_dom_mono; auto.
Qed.

(* props of lookupSmap *)

Lemma lookupSmap_in : forall sm id0 st0,
  uniq sm ->
  binds id0 st0 sm ->
  lookupSmap sm id0 = st0.
Proof.
  induction sm; intros.
    inversion H0.

    destruct a.
    simpl in *.
    inversion H; subst.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl;
      analyze_binds_uniq H0; auto.
Qed.

Lemma id2Sterm_in : forall sm id0 st0,
  uniq sm ->
  binds id0 st0 sm ->
  value2Sterm sm (value_id id0) = st0.
Proof.
  intros. simpl. apply lookupSmap_in; auto.
Qed.

Lemma lookupSmap_notin : forall sm id0,
  uniq sm ->
  id0 `notin` dom sm ->
  lookupSmap sm id0 = sterm_val (value_id id0).
Proof.
  induction sm; intros; simpl; auto.
    destruct a.
    simpl in *.
    inversion H; subst.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst; simpl;
      analyze_binds_uniq H0; auto.
Qed.

Lemma id2Sterm_notin : forall sm id0,
  uniq sm ->
  id0 `notin` dom sm ->
  value2Sterm sm (value_id id0) = sterm_val (value_id id0).
Proof.
  intros. simpl. apply lookupSmap_notin; auto.
Qed.

Lemma const2Sterm : forall sm c,
  value2Sterm sm (value_const c) = sterm_val (value_const c).
Proof.
  intros. auto.
Qed.
       
Lemma lookupSmap_in_lookupAL : forall m id0,
  id0 `in` dom m ->
  lookupAL _ m id0 = Some (lookupSmap m id0).
Proof.
  induction m; intros id0 id0inm; simpl.
    contradict id0inm; auto.

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; 
        simpl; auto.
        contradict n; auto.
      assert (id0 = a \/ id0 `in` dom m) as id0in. simpl in id0inm. fsetdec.
      destruct id0in as [EQ | id0in]; subst.
        contradict n; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
          subst; auto.
          contradict n; auto.
Qed.

Lemma lookupSmap_updateAddAL_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupSmap m id1 = lookupSmap (updateAddAL _ m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) id1 id0); subst; auto.
      contradict H; auto.

    destruct a.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
        subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
          subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
            subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a); 
            subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
            subst; simpl; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 a); 
              subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 a); 
              subst; simpl; auto.
Qed.   

Lemma lookupSmap_updateAddAL_eq : forall m id0 gv0,
  lookupSmap (updateAddAL _ m id0 gv0) id0 = gv0.
Proof.
  induction m; intros; simpl.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 id0); 
      subst; simpl; auto.
      contradict n; auto.  

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
      subst; simpl.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) a a); 
        subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); 
        subst; simpl; auto.
        contradict n; auto.
Qed.

Lemma lookupSmap_se_cmd_neq : forall c id' smap1 smem1 sframe1 seffects1 nc,
  getCmdLoc c <> id' ->
  lookupSmap (STerms (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) 
    (mkNB c nc))) id' =
  lookupSmap smap1 id'.
Proof.
  destruct c; intros id' smap1 smem1 sframe1 seffects1 nc HnEQ; simpl;
    try solve [rewrite <- lookupSmap_updateAddAL_neq; auto | auto].
    destruct v; simpl; try solve [inversion nc].
Qed.

Lemma init_denotes_id : forall TD lc gl als Mem0,
  sstate_denotes_state TD lc gl als Mem0 sstate_init lc als Mem0 trace_nil.
Proof.
  intros TD lc gl als Mem0.
  split; auto.
    split; intros; simpl in *; auto.
      assert (id' `in` dom lc) as id'_in_lc. fsetdec.
      apply indom_lookupAL_Some in id'_in_lc.
      destruct id'_in_lc as [gv' id'_gv'_in_lc].
      exists gv'. split; auto.
Qed.

(* props of denotes *)

Lemma id_denotes_gv : forall id0 TD Mem0 gl lc,
  id0 `in` dom lc ->
  exists gv0,
    sterm_denotes_genericvalue TD lc gl Mem0 (sterm_val (value_id id0)) gv0 /\
    lookupAL _ lc id0 = Some gv0.
Proof.
  intros id0 TD Mem0 gl lc Hin.
  apply indom_lookupAL_Some in Hin.
  destruct Hin as [gv0 Hin].
  exists gv0. split; auto.
Qed.

Lemma init_denotes_gvmap :forall TD lc gl Mem0,
  uniq lc ->
  smap_denotes_gvmap TD lc gl Mem0 nil lc.
Proof.
  intros TD lc gl Mem0 Uniqc.
  unfold smap_denotes_gvmap.
  split; intros; simpl; auto.
    apply id_denotes_gv; auto. 
      fsetdec.
Qed.

(* The denotational rules are determinastic. *)

Definition sterm_denotes_genericvalue_det_prop TD lc gl Mem0 st0 gv1 
  (sd:sterm_denotes_genericvalue TD lc gl Mem0 st0 gv1) :=
  forall gv2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv2 ->
  gv1 = gv2.

Definition sterms_denote_genericvalues_det_prop TD lc gl Mem0 sts0 gvs1
  (ds:sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs1) :=
  forall gvs2,
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs2 ->
  gvs1 = gvs2.

Definition smem_denotes_mem_det_prop TD lc gl Mem0 st0 Mem1
  (sd:smem_denotes_mem TD lc gl Mem0 st0 Mem1) :=
  forall Mem2,
  smem_denotes_mem TD lc gl Mem0 st0 Mem2 ->
  Mem1 = Mem2.

Lemma sdenotes_det : 
  (forall TD lc gl Mem0 st0 gv1 sd, 
    @sterm_denotes_genericvalue_det_prop TD lc gl Mem0 st0 gv1 sd) /\
  (forall TD lc gl Mem0 sts0 gvs1 sd, 
    @sterms_denote_genericvalues_det_prop TD lc gl Mem0 sts0 gvs1 sd) /\
  (forall TD lc gl Mem0 st0 Mem1 sd, 
    @smem_denotes_mem_det_prop TD lc gl Mem0 st0 Mem1 sd).
Proof.
(sd_mutind_cases
  apply sd_mutind with
    (P  := sterm_denotes_genericvalue_det_prop)
    (P0 := sterms_denote_genericvalues_det_prop)
    (P1 := smem_denotes_mem_det_prop) Case);
  unfold sterm_denotes_genericvalue_det_prop, 
         sterms_denote_genericvalues_det_prop, 
         smem_denotes_mem_det_prop; intros.
Case "sterm_val_denotes".
  inversion H; subst.
  rewrite e in H5. inversion H5; auto.
Case "sterm_bop_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e.
  inversion e; auto.
Case "sterm_fbop_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e.
  inversion e; auto.
Case "sterm_extractvalue_denotes".
  inversion H0; subst.
  apply H in H9; subst.
  rewrite H10 in e.
  inversion e; auto.
Case "sterm_insertvalue_denotes".
  inversion H1; subst.
  apply H in H12; subst.
  apply H0 in H13; subst.
  rewrite H14 in e.
  inversion e; auto.
Case "sterm_malloc_denotes".
  inversion H1; subst.
  rewrite e in H12. inversion H12; subst.
  apply H in H10; subst.
  apply H0 in H13; subst.
  rewrite H14 in e0. inversion e0; auto.
Case "sterm_alloca_denotes".
  inversion H1; subst.
  rewrite e in H12. inversion H12; subst.
  apply H in H10; subst.
  apply H0 in H13; subst.
  rewrite H14 in e0. inversion e0; auto.
Case "sterm_load_denotes".
  inversion H1; subst.
  apply H0 in H12; subst.
  apply H in H11; subst.
  rewrite e in H13. inversion H13; auto.
Case "sterm_gep_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_trunc_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_ext_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_cast_denotes".
  inversion H0; subst.
  apply H in H10; subst.
  rewrite H11 in e.
  inversion e; auto.
Case "sterm_icmp_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_fcmp_denotes".
  inversion H1; subst.
  apply H in H11; subst.
  apply H0 in H12; subst.
  rewrite H13 in e. inversion e; auto.
Case "sterm_select_denotes".
  inversion H2; subst.
  apply H in H11; subst.
  apply H0 in H13; subst.
  apply H1 in H14; subst; auto.
Case "sterms_nil_denote".
  inversion H; auto.
Case "sterms_cons_denote".
  inversion H1; subst.
  apply H in H10; subst.
  apply H0 in H11; subst; auto.
Case "smem_init_denotes".
  inversion H; auto.
Case "smem_malloc_denotes".
  inversion H1; subst.
  apply H in H10; subst. 
  apply H0 in H13; subst. 
  rewrite H12 in e. inversion e; subst.
  rewrite H14 in e0. inversion e0; auto.
Case "smem_free_denotes".
  inversion H1; subst.
  apply H in H9; subst. 
  apply H0 in H11; subst. 
  rewrite H12 in e. inversion e; auto.
Case "smem_alloca_denotes".
  inversion H1; subst.
  apply H in H10; subst. 
  apply H0 in H13; subst. 
  rewrite H12 in e. inversion e; subst.
  rewrite H14 in e0. inversion e0; auto.
Case "smem_load_denotes".
  inversion H0; subst.
  apply H in H10; auto. 
Case "smem_store_denotes".
  inversion H2; subst.
  apply H in H13; subst. 
  apply H0 in H14; subst. 
  apply H1 in H15; subst. 
  rewrite H16 in e. inversion e; auto.
Qed.

Lemma sterm_denotes_genericvalue_det : forall TD lc gl Mem0 st0 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv2 ->
  gv1 = gv2.
Proof.
  destruct sdenotes_det as [J _].
  unfold sterm_denotes_genericvalue_det_prop in J.
  eauto.
Qed.

Lemma sterms_denote_genericvalues_det : forall TD lc gl Mem0 sts0 gvs1 gvs2,
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs1 ->
  sterms_denote_genericvalues TD lc gl Mem0 sts0 gvs2 ->
  gvs1 = gvs2.
Proof.
  destruct sdenotes_det as [_ [J _]].
  unfold sterms_denote_genericvalues_det_prop in J.
  eauto.
Qed.

Lemma smem_denotes_mem_det : forall TD lc gl Mem0 st0 Mem1 Mem2,
  smem_denotes_mem TD lc gl Mem0 st0 Mem1 ->
  smem_denotes_mem TD lc gl Mem0 st0 Mem2 ->
  Mem1 = Mem2.
Proof.
  destruct sdenotes_det as [_ [_ J]].
  unfold smem_denotes_mem_det_prop in J.
  eauto.
Qed.

Lemma sframe_denotes_frame_det : forall TD lc gl als Mem0 st0 als1 als2,
  sframe_denotes_frame TD lc gl als Mem0 st0 als1 ->
  sframe_denotes_frame TD lc gl als Mem0 st0 als2 ->
  als1 = als2.
Proof.
  intros.
  generalize dependent als2.
  induction H; intros.
    inversion H0; auto.

    inversion H4; subst.
    apply smem_denotes_mem_det with (Mem1:=Mem4) in H; auto; subst.
    apply sterm_denotes_genericvalue_det with (gv1:=gv1) in H2; auto; subst.
    rewrite H1 in H18. inversion H18; subst.
    rewrite H20 in H3. inversion H3; subst.
    apply IHsframe_denotes_frame in H17; subst; auto.
Qed.

Lemma seffects_denote_trace_det : forall ses tr1 tr2,
  seffects_denote_trace ses tr1 ->
  seffects_denote_trace ses tr2 ->
  tr1 = tr2.
Proof.
  intros. 
  inversion H; subst.
  inversion H0; subst; auto.
Qed.

Lemma lookupSmap_inv : forall m id0 st0,
  lookupSmap m id0 = st0 ->
  (id0 `in` dom m /\ binds id0 st0 m) \/ 
  (id0 `notin` dom m /\ st0 = sterm_val (value_id id0)).
Proof.
  induction m; intros id0 st0 HlkSmap; simpl in *.
    right. auto.

    destruct a.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id0 a); subst.
      left. auto.

      remember (lookupSmap m id0) as st0.
      symmetry in Heqst0.
      apply IHm in Heqst0.
      destruct Heqst0 as [[id0in binds_id0_st0] | [id0notin EQ]]; subst; auto.
Qed.


Lemma sterm_val_denotes_in : forall TD lc gl Mem0 id0 gv,
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_val (value_id id0)) gv ->
  id0 `in` dom lc.
Proof.
  intros TD lc gl Mem0 id0 gv Hdenotes.
  inversion Hdenotes; subst.
  simpl in H4.
  apply lookupAL_Some_indom in H4; auto.
Qed.

Lemma smap_denotes_gvmap_det : forall TD lc gl Mem0 smap0 lc1 lc2,
  uniq smap0 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc1 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc2 ->
  eqAL _ lc1 lc2.
Proof.
  intros TD lc gl Mem0 smap0 lc1 lc2 Uniq J1 J2.
  destruct J1 as [J11 J12].
  destruct J2 as [J21 J22].
  intros id0.
  remember (lookupAL _ lc1 id0) as ogv1.
  remember (lookupAL _ lc2 id0) as ogv2.
  destruct ogv1 as [gv1 | ].
    symmetry in Heqogv1.
    apply J12 in Heqogv1.
    destruct (@AtomSetProperties.In_dec id0 (dom smap0)) 
      as [id0_in_smap0 | id0_notin_smap0].
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J21 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc2]].
      rewrite id0_in_lc2 in Heqogv2. inversion Heqogv2; subst.
      apply sterm_denotes_genericvalue_det with (gv2:=gv1) in id0_denotes_gv'; 
      subst; auto.
      
      apply lookupSmap_notin in id0_notin_smap0; auto.
      rewrite id0_notin_smap0 in Heqogv1.
      assert (id0_in_lc:=@sterm_val_denotes_in TD lc gl Mem0 id0 gv1 Heqogv1).
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J21 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc2]].
      rewrite id0_in_lc2 in Heqogv2. inversion Heqogv2; subst.
      rewrite id0_notin_smap0 in id0_denotes_gv'.
      apply sterm_denotes_genericvalue_det with (gv2:=gv1) in id0_denotes_gv'; 
      subst; auto.
    
  destruct ogv2 as [gv2 | ]; auto.
    symmetry in Heqogv2.
    apply J22 in Heqogv2.
    destruct (@AtomSetProperties.In_dec id0 (dom smap0)) 
      as [id0_in_smap0 | id0_notin_smap0].
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.   
      apply J11 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc1]].
      rewrite id0_in_lc1 in Heqogv1.
      inversion Heqogv1.

      apply lookupSmap_notin in id0_notin_smap0; auto.
      rewrite id0_notin_smap0 in Heqogv2.
      assert (id0_in_lc:=@sterm_val_denotes_in TD lc gl Mem0 id0 gv2 Heqogv2).
      assert (id0 `in` dom smap0 `union` dom lc) as id0_in_smap0_lc. auto.
      apply J11 in id0_in_smap0_lc.
      destruct id0_in_smap0_lc as [gv' [id0_denotes_gv' id0_in_lc1]].
      rewrite id0_in_lc1 in Heqogv1. inversion Heqogv1; subst.
Qed.

Lemma sstate_denotes_state_det : forall TD lc gl als Mem0 sstate0 lc1 als1 Mem1 
  tr1 lc2 als2 Mem2 tr2,
  uniq (STerms sstate0) ->
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc gl als Mem0 sstate0 lc2 als2 Mem2 tr2 ->
  eqAL _ lc1 lc2 /\ als1 = als2 /\ Mem1 = Mem2 /\ tr1 = tr2.
Proof.
 intros TD lc gl als Mem0 sstate0 lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 Uniq J1 J2.
  destruct J1 as [J11 [J12 [J13 J14]]].
  destruct J2 as [J21 [J22 [J23 J24]]].
  apply smem_denotes_mem_det with (Mem2:=Mem2) in J12; auto; subst.
  apply sframe_denotes_frame_det with (als2:=als2) in J13; auto; subst.
  apply seffects_denote_trace_det with (tr2:=tr2) in J14; auto; subst.
  apply smap_denotes_gvmap_det with (lc2:=lc2) in J11; auto.
Qed.

Lemma smap_denotes_gvmap_eqEnv : forall TD lc gl Mem0 smap0 lc1 lc2,
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc1 ->
  eqAL _ lc1 lc2 ->
  smap_denotes_gvmap TD lc gl Mem0 smap0 lc2.
Proof.
  intros TD lc gl Mem0 smap0 lc1 lc2 [H1 H2] H3.
  split; intros.
    apply H1 in H.
    destruct H as [gv' [st'_denotes_gv' id'_gv'_is_env1]].
    exists gv'. rewrite <- H3.
    split; auto.

    rewrite <- H3 in H.
    apply H2 in H; auto.
Qed.

(* p&p *)
Lemma se_dbCmd_preservation : forall TD lc als gl Mem0 c lc' als' Mem' tr,
  dbCmd TD gl lc als Mem0 c lc' als' Mem' tr ->
  uniq lc ->
  uniq lc'.
Proof.
  intros TD lc als gl Mem0 c lc' als' Mem' tr HdbCmd Uniqlc.
  (se_dbCmd_cases (inversion HdbCmd) Case); subst; auto using updateAddAL_uniq.
  Case "dbSelect".
    destruct (isGVZero TD cond0); eauto using updateAddAL_uniq.
Qed.

Lemma se_dbCmds_preservation : forall TD lc als gl Mem0 cs lc' als' Mem' tr,
  dbCmds TD gl lc als Mem0 cs lc' als' Mem' tr ->
  uniq lc ->
  uniq lc'.
Proof.
  intros TD lc als gl Mem0 cs lc' als' Mem' tr HdbCmd Uniqlc.
  induction HdbCmd; auto. 
    apply se_dbCmd_preservation in H; auto.
Qed.

Lemma se_dbTerminator_preservation : forall TD M F B gl lc c B' lc' tr,
  dbTerminator TD M F gl B lc c B' lc' tr ->
  uniq lc ->
  uniqFdef F ->
  blockInFdefB B F ->
  uniq lc' /\ blockInFdefB B' F.
Proof.
  intros TD M F gl B lc c B' lc' tr HdbTerminator Uniqlc UniqF Hblockin.
  inversion HdbTerminator; subst.
    destruct (isGVZero TD c0).
      split; eauto using (@switchToNewBasicBlock_uniq DGVs).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
        destruct H0; auto.

      split; eauto using (@switchToNewBasicBlock_uniq DGVs).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
        destruct H0; auto.

    symmetry in H.
    apply lookupBlockViaLabelFromFdef_inv in H; auto.
    destruct H.
    split; eauto using (@switchToNewBasicBlock_uniq DGVs).
Qed.

Definition se_dbCall_preservation_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr
  (db:dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr) :=
  forall los nts,
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  TD = (los, nts) ->
  uniq lc' .
Definition se_dbSubblock_preservation_prop S TD Ps fs gl lc als Mem cs lc' als' 
  Mem' tr (db:dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  forall los nts,
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  TD = (los, nts) ->
  uniq lc'.
Definition se_dbSubblocks_preservation_prop S TD Ps fs gl lc als Mem cs lc' als'
  Mem' tr (db:dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  forall los nts,
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  TD = (los, nts) ->
  uniq lc'.
Definition se_dbBlock_preservation_prop S TD Ps fs gl F state1 state2 tr
  (db:dbBlock S TD Ps fs gl F state1 state2 tr) :=
  forall B1 lc als Mem B1' lc' als' Mem' los nts,
  state1 = mkState (mkEC B1 lc als) Mem ->
  state2 = mkState (mkEC B1' lc' als') Mem' ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro los nts Ps) F ->
  TD = (los, nts) ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro los nts Ps) F.
Definition se_dbBlocks_preservation_prop S TD Ps fs gl F state1 state2 tr
  (db:dbBlocks S TD Ps fs gl F state1 state2 tr) :=
  forall B1 lc als Mem B1' lc' als' Mem' los nts,
  state1 = (mkState (mkEC B1 lc als) Mem) ->
  state2 = (mkState (mkEC B1' lc' als') Mem') ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro los nts Ps) F ->
  TD = (los, nts) ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro los nts Ps) F.
Definition se_dbFdef_preservation_prop fv rt lp S TD Ps lc gl fs Mem lc' als' 
  Mem' B' Rid oResult tr
  (db:dbFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr) :=
  forall fa fid la va lb los nts fptr,
  getOperandValue TD fv lc gl = Some fptr -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  TD = (los, nts) ->
  uniq lc' /\ 
  blockInSystemModuleFdef B' S (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb).

Local Hint Resolve (@initLocals_uniq DGVs).

Lemma se_db_preservation :
  (forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db, 
     se_dbCall_preservation_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db,
     se_dbSubblock_preservation_prop S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db,
     se_dbSubblocks_preservation_prop S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl F state1 state2 tr db,
     se_dbBlock_preservation_prop S TD Ps fs gl F state1 state2 tr db) /\
  (forall S TD Ps fs gl F state1 state2 tr db,
     se_dbBlocks_preservation_prop S TD Ps fs gl F state1 state2 tr db) /\
  (forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     se_dbFdef_preservation_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
Proof.
(se_db_mutind_cases
  apply db_mutind with
    (P  := se_dbCall_preservation_prop)
    (P0 := se_dbSubblock_preservation_prop)
    (P1 := se_dbSubblocks_preservation_prop)
    (P2 := se_dbBlock_preservation_prop)
    (P3 := se_dbBlocks_preservation_prop)
    (P4 := se_dbFdef_preservation_prop) Case);
  unfold se_dbCall_preservation_prop, 
         se_dbSubblock_preservation_prop, se_dbSubblocks_preservation_prop,
         se_dbBlock_preservation_prop, se_dbBlocks_preservation_prop,
         se_dbFdef_preservation_prop; intros; subst; eauto.
Case "dbCall_internal".
  inversion d; subst; apply callUpdateLocals_uniq in e1; auto.      

Case "dbCall_external".
  apply exCallUpdateLocals_uniq in e4; auto.      

Case "dbSubblock_intro".
  apply se_dbCmds_preservation in d; eauto.
 
Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  apply blockInSystemModuleFdef_inv in H4.
  destruct H4 as [Hblockin [Hinproducts [Hmodulein Hproductin]]].
  eapply H in H2; eauto.
  apply se_dbCmds_preservation in d0; auto.
  assert (uniqFdef F) as uniqF.
    apply uniqSystem__uniqFdef in Hproductin; auto.
  apply se_dbTerminator_preservation in d1; auto.
  destruct d1 as [uniqc' B1inF].
  split; auto using blockInSystemModuleFdef_intro.

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  split; auto.
 
Case "dbBlocks_cons".
  inversion d; subst.
  assert (J:=H4).
  eapply H with (B1:=block_intro l0 ps (cs++cs') tmn)(lc0:=lc)(als0:=als)
            (Mem:=Mem0)(B1':=B')(lc':=lc4)(als':=als3)(Mem':=Mem3) in J; eauto.
  clear H.
  destruct J as [uniqc4 B'in].
  eapply H0; eauto.

Case "dbFdef_func".
  rewrite e in H1. inv H1. rewrite e0 in H2. inv H2.
  apply entryBlockInSystemBlockFdef'' with (los:=los)(nts:=nts)(Ps:=Ps)(S:=S)
    (fv:=fptr0)(fs:=fs)in e1; auto.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(lc:=lc0)(als:=nil)(Mem:=Mem0)
    (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))
    (lc':=lc1)(als':=als1)(Mem':=Mem1) in e1; eauto.
  clear H. destruct e1 as [uniqc1 Bin].
  eapply H0 in uniqc1; eauto. clear H0.
  apply se_dbCmds_preservation in d1; auto.

Case "dbFdef_proc".
  rewrite e in H1. inv H1. rewrite e0 in H2. inv H2.
  apply entryBlockInSystemBlockFdef'' with (los:=los)(nts:=nts)(Ps:=Ps)(S:=S)
    (fv:=fptr0)(fs:=fs)in e1; auto.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(lc:=lc0)(als:=nil)(Mem:=Mem0)
    (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(lc':=lc1)
    (als':=als1)(Mem':=Mem1) in e1; eauto.
  clear H. destruct e1 as [uniqc1 Bin].
  eapply H0 in uniqc1; eauto. clear H0.
  apply se_dbCmds_preservation in d1; auto.
Qed.

Lemma se_dbCall_preservation : forall S los nts Ps fs lc gl Mem0 call0 lc' Mem' 
  tr,
  dbCall S (los, nts) Ps fs gl lc Mem0 call0 lc' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniq lc' .
Proof.
  intros.
  destruct se_db_preservation as [J _].
  unfold se_dbCall_preservation_prop in J. eauto.
Qed.

Lemma se_dbSubblock_preservation : forall S los nts Ps fs gl lc als Mem cs lc' 
  als' Mem' tr,
  dbSubblock S (los, nts) Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniq lc'.
Proof.
  intros.
  destruct se_db_preservation as [_ [J _]].
  unfold se_dbSubblock_preservation_prop in J. eauto.
Qed.

Lemma se_dbSubblocks_preservation : forall S los nts Ps fs gl lc als Mem cs lc' als' Mem' tr,
  dbSubblocks S (los, nts) Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniq lc'.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [J _]]].
  unfold se_dbSubblocks_preservation_prop in J. eauto.
Qed.

Lemma se_dbBlock_preservation : forall S los nts Ps fs gl F tr B1 lc als Mem B1'
    lc' als' Mem',
  dbBlock S (los, nts) Ps fs gl F
    (mkState (mkEC B1 lc als) Mem) 
    (mkState (mkEC B1' lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro los nts Ps) F ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [J _]]]].
  unfold se_dbBlock_preservation_prop in J. eauto.
Qed.

Lemma se_dbBlocks_preservation : forall S los nts Ps fs gl F tr B1 lc als Mem
    B1' lc' als' Mem',
  dbBlocks S (los, nts) Ps fs gl F 
    (mkState (mkEC B1 lc als) Mem)
    (mkState (mkEC B1' lc' als') Mem') tr ->
  uniq lc ->
  uniqSystem S ->
  blockInSystemModuleFdef B1 S (module_intro los nts Ps) F ->
  uniq lc' /\ 
  blockInSystemModuleFdef B1' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [_ [J _]]]]].
  unfold se_dbBlocks_preservation_prop in J. eauto.
Qed.

Lemma se_dbFdef_preservation : forall fv rt lp S los nts Ps lc gl fs Mem lc' als'
    Mem' B' Rid oResult tr fid fa la va lb fptr,
  dbFdef fv rt lp S (los, nts) Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  getOperandValue (los, nts) fv lc gl = Some fptr -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  uniq lc ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  uniq lc' /\ 
  blockInSystemModuleFdef B' S (module_intro los nts Ps) (fdef_intro (fheader_intro fa rt fid la va) lb).
Proof.
  intros.
  destruct se_db_preservation as [_ [_ [_ [_ [_ J]]]]].
  unfold se_dbFdef_preservation_prop in J. eauto.
Qed.

(* eqEnv *)
Lemma dbCmd_eqEnv : forall TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 tr ->
  eqAL _ lc1 lc1' ->
  exists lc2', 
    dbCmd TD gl lc1' als1 Mem1 c lc2' als2 Mem2 tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros TD c lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmd HeqEnv.
  (se_dbCmd_cases (inversion HdbCmd) Case); subst.
Case "dbBop".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite (@BOP_eqAL DGVs) with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbFBop".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite (@FBOP_eqAL DGVs) with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbExtractValue".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv').
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H; auto. 
  split; eauto using eqAL_updateAddAL.
  
Case "dbInsertValue".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv'').
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H; auto. 
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbMalloc".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbFree".
  exists lc1'.
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H; auto. 
  split; eauto.

Case "dbAlloca".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 (blk2GV TD mb)).
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbLoad".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv).
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbStore".
  exists lc1'.
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H; auto. 
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H0; auto. 
  split; eauto using eqAL_updateAddAL.

Case "dbGEP".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 mp').
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H; auto. 
  rewrite (@values2GVs_eqAL DGVs) with (lc2:=lc1') in H0; auto. 
(* rewrite GEP_eqAL with (lc2:=lc1') in H0; auto. *)
  split; eauto using eqAL_updateAddAL.

Case "dbTrunc".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite (@TRUNC_eqAL DGVs) with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbExt".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite (@EXT_eqAL DGVs) with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbCast".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv2).
  rewrite (@CAST_eqAL DGVs) with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbIcmp".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite (@ICMP_eqAL DGVs) with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbFcmp".
  assert (HupdateEnv:=HeqEnv).
  exists (updateAddAL _ lc1' id0 gv3).
  rewrite (@FCMP_eqAL DGVs) with (lc2:=lc1') in H; auto.
  split; eauto using eqAL_updateAddAL.

Case "dbSelect".
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H; auto. 
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H0; auto. 
  rewrite (@getOperandValue_eqAL DGVs) with (lc2:=lc1') in H1; auto. 
  assert (HupdateEnv:=HeqEnv).
  exists (if isGVZero TD cond0 then updateAddAL _ lc1' id0 gv2 else updateAddAL _ lc1' id0 gv1).
  split; auto.
    destruct (isGVZero TD cond0); auto using eqAL_updateAddAL.
Qed.

Lemma dbCmds_eqEnv : forall TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1',
  dbCmds TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr ->
  eqAL _ lc1 lc1' ->
  exists lc2', 
    dbCmds TD gl lc1' als1 Mem1 cs lc2' als2 Mem2 tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros TD cs lc1 als1 gl Mem1 lc2 als2 Mem2 tr lc1' HdbCmds HeqEnv.
  generalize dependent lc1'.
  induction HdbCmds; intros.
    exists lc1'. split; auto.

    apply dbCmd_eqEnv with (lc1':=lc1') in H; auto.
    destruct H as [lc2' [HdbCmd HeqEnv']].
    apply IHHdbCmds in HeqEnv'; auto.
    destruct HeqEnv' as [lc3' [HdbCmds' HeqEnv'']].
    exists lc3'.
    split; eauto.
Qed.

Lemma dbTerminator_eqEnv : forall TD M F gl lc1 tmn lc2 tr lc1' B B',
  dbTerminator TD M F gl B lc1 tmn B' lc2 tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbTerminator TD M F gl B lc1' tmn B' lc2' tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros TD M F gl lc1 tmn lc2 tr lc1' B B' HdbTerminator HeqAL.
  inversion HdbTerminator; subst.
    symmetry in H1.
    apply eqAL_switchToNewBasicBlock' with (lc':=lc1') in H1; auto.
    destruct H1 as [lc2' [H10 H11]].
    exists lc2'.
    split; auto.
      apply dbBranch with (c:=c); auto.
        erewrite <- getOperandValue_eqAL; eauto.

    symmetry in H0.
    apply eqAL_switchToNewBasicBlock' with (lc':=lc1') in H0; auto.
    destruct H0 as [lc2' [H00 H01]].
    exists lc2'.
    split; auto.
Qed.     

Definition dbCall_eqEnv_prop S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr
  (db:dbCall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr) := 
  forall lc1',
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbCall S TD Ps fs gl lc1' Mem0 call0 lc2' Mem' tr /\
    eqAL _ lc2 lc2'.
Definition dbSubblock_eqEnv_prop S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr
  (db:dbSubblock S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr) :=
  forall lc1',
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbSubblock S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    eqAL _ lc2 lc2'.
Definition dbSubblocks_eqEnv_prop S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr
  (db:dbSubblocks S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr) :=
  forall lc1',
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbSubblocks S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    eqAL _ lc2 lc2'.
Definition dbBlock_eqEnv_prop S TD Ps fs gl F state1 state2 tr
  (db:dbBlock S TD Ps fs gl F state1 state2 tr) :=
  forall B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  state1 = mkState (mkEC B1 lc1 als) Mem ->
  state2 = mkState (mkEC B1' lc2 als') Mem' ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbBlock S TD Ps fs gl F 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    eqAL _ lc2 lc2'.
Definition dbBlocks_eqEnv_prop S TD Ps fs gl F state1 state2 tr
  (db:dbBlocks S TD Ps fs gl F state1 state2 tr) :=
  forall B1 lc1 als Mem B1' lc2 als' Mem' lc1',
  state1 = mkState (mkEC B1 lc1 als) Mem ->
  state2 = mkState (mkEC B1' lc2 als') Mem' ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbBlocks S TD Ps fs gl F 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    eqAL _ lc2 lc2'.
Definition dbFdef_eqEnv_prop fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid 
  oResult tr
  (db:dbFdef fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr) :=
  forall fid fa la va lb lc1' fptr,
  getOperandValue TD fv lc1 gl = Some fptr -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbFdef fv rt lp S TD Ps lc1' gl fs Mem lc2' als' Mem' B' Rid oResult tr /\
    eqAL _ lc2 lc2'.

Lemma db_eqEnv :
  (forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db, 
     dbCall_eqEnv_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db,
     dbSubblock_eqEnv_prop S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db,
     dbSubblocks_eqEnv_prop S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db) /\
  (forall S TD Ps fs gl F state1 state2 tr db,
     dbBlock_eqEnv_prop S TD Ps fs gl F state1 state2 tr db) /\
  (forall S TD Ps fs gl F state1 state2 tr db,
     dbBlocks_eqEnv_prop S TD Ps fs gl F state1 state2 tr db) /\
  (forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     dbFdef_eqEnv_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid 
       oResult tr db).
Proof.
(se_db_mutind_cases
  apply db_mutind with
    (P  := dbCall_eqEnv_prop)
    (P0 := dbSubblock_eqEnv_prop)
    (P1 := dbSubblocks_eqEnv_prop)
    (P2 := dbBlock_eqEnv_prop)
    (P3 := dbBlocks_eqEnv_prop)
    (P4 := dbFdef_eqEnv_prop) Case);
  unfold dbCall_eqEnv_prop, 
         dbSubblock_eqEnv_prop, dbSubblocks_eqEnv_prop,
         dbBlock_eqEnv_prop, dbBlocks_eqEnv_prop,
         dbFdef_eqEnv_prop; intros; subst; auto.
Case "dbCall_internal".
  inversion d; subst.
    apply H with (lc1':=lc1') in H2; auto. clear H.
    destruct H2 as [lc2' [HdbBlocks HeqEnv]].
    apply (@eqAL_callUpdateLocals' DGVs) with (lc1':=lc1')(lc2':=lc2') in e1; auto.
    destruct e1 as [lc2'' [J1 J2]].
    exists lc2''.
    split; eauto using dbCall_internal.

    apply H with (lc1':=lc1') in H2; auto. clear H.
    destruct H2 as [lc2' [HdbBlocks HeqEnv]].
    apply (@eqAL_callUpdateLocals' DGVs) with (lc1':=lc1')(lc2':=lc2') in e1; auto.
    destruct e1 as [lc2'' [J1 J2]].
    exists lc2''.
    split; eauto using dbCall_internal.

Case "dbCall_external".
  apply (@eqAL_exCallUpdateLocals' DGVs) with (lc':=lc1')in e4; auto.
  destruct e4 as [lc2' [J1 J2]].
  exists lc2'.
  split; eauto using (@eqAL_exCallUpdateLocals DGVs).
    eapply dbCall_external; eauto.
      erewrite getOperandValue_eqAL; eauto using eqAL_sym.
    rewrite <- (@eqAL_params2GVs DGVs) with (lc:=lc); auto.

Case "dbSubblock_intro".
  apply dbCmds_eqEnv with (lc1':=lc1') in d; auto.
  destruct d as [lc2' [HdbCmds HeqEnv2]].
  apply H in HeqEnv2. clear H.
  destruct HeqEnv2 as [lc3' [HdbCall HeqEnv3]].
  exists lc3'.
  split; eauto.

Case "dbSubblocks_nil".
  exists lc1'. split; auto.
 
Case "dbSubblocks_cons".
  apply H in H1. clear H.
  destruct H1 as [lc2' [HdbSubblock Heq2]].
  apply H0 in Heq2. clear H0.
  destruct Heq2 as [lc3' [HdbSubblocks Heq3]].
  exists lc3'. split; eauto.

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  apply H in H2. clear H.
  destruct H2 as [lc2' [HdbSubblocks Heq2]].
  apply dbCmds_eqEnv with (lc1':=lc2') in d0; auto.
  destruct d0 as [lc3' [HdbCmds Heq3]].
  apply dbTerminator_eqEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc5' [HdbTerminator Heq5]].
  exists lc5'. split; eauto.

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  exists lc1'. split; auto.
 
Case "dbBlocks_cons".
  inversion d; subst.
  apply H with (B1:=block_intro l0 ps (cs++cs') tmn)(als0:=als)(Mem:=Mem0) 
               (B1':=B')(als':=als3)(Mem':=Mem3)(lc3:=lc5) in H3; auto.
  clear H.
  destruct H3 as [lc5' [HdbBlock Heq5]].
  apply H0 with (als'0:=als')(als:=als3)(Mem:=Mem3)(Mem'0:=Mem')(lc3:=lc2)(B1:=B')(B1'0:=B1') in Heq5; auto.
  clear H0.
  destruct Heq5 as [lc2' [HdbBlocks Heq2]].
  exists lc2'. split; eauto.

Case "dbFdef_func".
  rewrite e in H1. inv H1. rewrite e0 in H2. inv H2.
  assert (J:=@eqAL_params2GVs DGVs lp TD lc gl lc1' H3).
  rewrite e2 in J.
  assert (eqAL _ lc0 lc0) as J'.
    apply eqAL_refl.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(als:=nil)(Mem:=Mem0)(lc3:=lc1)
    (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))
    (als':=als1)(Mem':=Mem1) in J'; auto.
  clear H. destruct J' as [lc2' [HdbBlocks Heq2]].
  apply H0 in Heq2. clear H0.
  destruct Heq2 as [lc3' [Hsubblocks Heq3]].
  apply dbCmds_eqEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc4' [HdbCmds Heq4]].
  exists lc4'. split; eauto.
    eapply dbFdef_func; eauto.
      erewrite getOperandValue_eqAL; eauto using eqAL_sym.

Case "dbFdef_proc".
  rewrite e in H1. inv H1. rewrite e0 in H2. inv H2.
  assert (J:=@eqAL_params2GVs _ lp TD lc gl lc1' H3).
  rewrite e2 in J.
  assert (eqAL _ lc0 lc0) as J'.
    apply eqAL_refl.
  apply H with (B1:=block_intro l1 ps1 cs1 tmn1)(als:=nil)(Mem:=Mem0)(lc3:=lc1)
    (B1':=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))(als':=als1)
    (Mem':=Mem1) in J'; auto.
  clear H. destruct J' as [lc2' [HdbBlocks Heq2]].
  apply H0 in Heq2. clear H0.
  destruct Heq2 as [lc3' [Hsubblocks Heq3]].
  apply dbCmds_eqEnv with (lc1':=lc3') in d1; auto.
  destruct d1 as [lc4' [HdbCmds Heq4]].
  exists lc4'. split; eauto.
    eapply dbFdef_proc; eauto.
      erewrite getOperandValue_eqAL; eauto using eqAL_sym.
Qed.

Lemma dbCall_eqEnv : forall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr lc1',
  dbCall S TD Ps fs gl lc1 Mem0 call0 lc2 Mem' tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbCall S TD Ps fs gl lc1' Mem0 call0 lc2' Mem' tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [J _].
  unfold dbCall_eqEnv_prop in J. eauto.
Qed.

Lemma dbSubblock_eqEnv:forall S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr lc1',
  dbSubblock S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbSubblock S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [J _]].
  unfold dbSubblock_eqEnv_prop in J. eauto.
Qed.

Lemma dbSubblocks_eqEnv:forall S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr lc1',
  dbSubblocks S TD Ps fs gl lc1 als Mem cs lc2 als' Mem' tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbSubblocks S TD Ps fs gl lc1' als Mem cs lc2' als' Mem' tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [_ [J _]]].
  unfold dbSubblocks_eqEnv_prop in J. eauto.
Qed.

Lemma dbBlock_eqEnv : forall S TD Ps fs gl F tr B1 lc1 als Mem B1' lc2 als' Mem'
  lc1',
  dbBlock S TD Ps fs gl F
    (mkState (mkEC B1 lc1 als) Mem) 
    (mkState (mkEC B1' lc2 als') Mem') 
    tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbBlock S TD Ps fs gl F 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [_ [_ [J _]]]].
  unfold dbBlock_eqEnv_prop in J. eauto.
Qed.

Lemma dbBlocks_eqEnv : forall S TD Ps fs gl F tr B1 lc1 als Mem B1' lc2 als' 
    Mem' lc1',
  dbBlocks S TD Ps fs gl F
    (mkState (mkEC B1 lc1 als) Mem)
    (mkState (mkEC B1' lc2 als') Mem')
    tr ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbBlocks S TD Ps fs gl F 
     (mkState (mkEC B1 lc1' als) Mem) 
     (mkState (mkEC B1' lc2' als') Mem') 
     tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [_ [_ [_ [J _]]]]].
  unfold dbBlocks_eqEnv_prop in J. eauto.
Qed.

Lemma dbFdef_eqEnv : forall fv fid rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' 
    Rid oResult tr fa la va lb lc1' fptr,
  dbFdef fv rt lp S TD Ps lc1 gl fs Mem lc2 als' Mem' B' Rid oResult tr ->
  getOperandValue TD fv lc1 gl = Some fptr -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  eqAL _ lc1 lc1' ->
  exists lc2',
    dbFdef fv rt lp S TD Ps lc1' gl fs Mem lc2' als' Mem' B' Rid oResult tr /\
    eqAL _ lc2 lc2'.
Proof.
  intros.
  destruct db_eqEnv as [_ [_ [_ [_ [_ J]]]]].
  unfold dbFdef_eqEnv_prop in J. eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)


