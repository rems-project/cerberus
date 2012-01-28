Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
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
Require Import dopsem.
Require Import symexe_def.
Require Import symexe_lib.
Require Import symexe_complete.
Require Import alist.
Require Import infrastructure_props.

Export SimpleSE.

(* Symbolic execuction is sound:
   Given a concrete initial state and that its symbolic execution results
   denote some concrete states w.r.t the initial state, it is possible to
   execute the subblock to completion from this initial state. *)

Lemma value2Sterm_denotes__implies__genericvalue : forall TD lc0 Mem0 smap1 lc 
    gl v gv,
  uniq smap1 ->
  smap_denotes_gvmap TD lc0 gl Mem0 smap1 lc ->
  sterm_denotes_genericvalue TD lc0 gl Mem0 (value2Sterm smap1 v) gv ->
  @getOperandValue DGVs TD v lc gl = Some gv.
Proof.
  intros D lc0 Mem0 smap1 lc gl v gv Huniq Hdenotes J.
  unfold smap_denotes_gvmap in Hdenotes.
  destruct Hdenotes as [J1 J2].
  destruct v.
    simpl in J.
    destruct (@AtomSetProperties.In_dec i0 (dom smap1)) as [i0_in_sstate1 | i0_notin_sstate1].
      apply in_dom_ext_right with (D2:=dom lc0) in i0_in_sstate1.
      apply J1 in i0_in_sstate1.
      destruct i0_in_sstate1 as [gv' [i0_denotes_gv' id0_gv'_in_lc]].
      apply sterm_denotes_genericvalue_det with (gv2:=gv') in J; auto.
      subst. auto.      

      rewrite lookupSmap_notin in J; auto.
      inversion J; subst.
      simpl in H4.
      apply lookupAL_Some_indom in H4.
      apply in_dom_ext_left with (D2:=dom smap1) in H4.
      apply J1 in H4.
      destruct H4 as [gv' [i0_denotes_gv' id0_gv'_in_lc]].
      rewrite lookupSmap_notin in i0_denotes_gv'; auto.
      apply sterm_denotes_genericvalue_det with (gv2:=gv') in J; simpl; auto.
      subst. auto.

    rewrite const2Sterm in J.
    inversion J. auto.
Qed.

Lemma value2Sterm_denote__imply__genericvalues : forall l0 TD lc0 Mem0 smap1 lc 
    gl gvs0,
  uniq smap1 ->
  smap_denotes_gvmap TD lc0 gl Mem0 smap1 lc ->
  sterms_denote_genericvalues TD lc0 gl Mem0 
    (make_list_sterm 
      (map_list_sz_value 
        (fun sz' v' => (sz', value2Sterm smap1 v')) l0)) gvs0 ->
  @values2GVs DGVs TD l0 lc gl = Some gvs0.
Proof.
  induction l0; intros; simpl in *.
    inversion H1; subst; auto.

    inversion H1; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11
      ; auto.
    rewrite H11.
    erewrite IHl0; eauto.
Qed.

Lemma aux__se_cmd__denotes__exists_op_cmd : forall TD c nc lc als gl Mem1 lc' 
    als' Mem2 lc0 als0 Mem0 sstate1 tr1 tr2,
  uniq sstate1.(STerms) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 sstate1 lc als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd sstate1 (mkNB c nc)) lc' als' 
    Mem2 tr2 ->
  exists lc',  exists als', exists Mem2, exists tr,
    dbCmd TD gl lc als Mem1 c lc' als' Mem2 tr /\
    tr2 = trace_app tr1 tr.
Proof.
  intros TD c nc lc als gl Mem1 lc' als' Mem2 lc0 als0 Mem0 sstate1 tr1 tr2 
    Huniq Hdenotes1 Hdenotes2.
  destruct Hdenotes2 as [[Hsterms_denote21 Hsterms_denote22] [Hsmem_denotes2 [Hsframe_denotes2 Hseffects_denote2]]].
  destruct Hdenotes1 as [Hsterms_denote1 [Hsmem_denotes1 [Hsframe_denotes1 Hseffects_denote1]]].
  inversion Hseffects_denote1; subst.
  inversion Hseffects_denote2; subst.
  (cmd_cases (destruct c) Case).
  Case "insn_bop".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_bop i0 b s v v0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env']].
    simpl in bop_denotes_gv3. 
    inversion bop_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (@BOP DGVs TD lc gl b s v v0 = Some gv3) as J.
      unfold BOP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_fbop".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_fbop i0 f f0 v v0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv3 [fbop_denotes_gv3 gv3_in_env']].
    simpl in fbop_denotes_gv3. 
    inversion fbop_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (@FBOP DGVs TD lc gl f f0 v v0 = Some gv3) as J.
      unfold FBOP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_extractvalue".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_extractvalue i0 t v l0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv' [extractvalue_denotes_gv' gv_in_env']].
    inversion extractvalue_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H9; auto.
    exists (updateAddAL _ lc i0 gv'). exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_insertvalue".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_insertvalue i0 t v t0 v0 l0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv' [insertvalue_denotes_gv' gv_in_env']].
    inversion insertvalue_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    exists (updateAddAL _ lc i0 gv'). exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_malloc".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_malloc i0 t v a) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv' [malloc_denotes_gv' gv_in_env']].
    inversion malloc_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H9; auto.
    subst.
    exists (updateAddAL _ lc i0 (blk2GV TD mb)). exists als. exists Mem5. exists trace_nil.
    split; eauto.

  Case "insn_free".
    inversion Hsmem_denotes2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H8; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H10; auto.
    subst.
    exists lc. exists als. exists Mem2. exists trace_nil.
    split; eauto.

  Case "insn_alloca".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_alloca i0 t v a) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv' [alloca_denotes_gv' gv_in_env']].
    inversion alloca_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H9; auto.
    subst.
    exists (updateAddAL _ lc i0 (blk2GV TD mb)). exists (mb::als). exists Mem5. exists trace_nil.
    split; eauto.

  Case "insn_load".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_load i0 t v a) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv' [load_denotes_gv' gv_in_env']].
    inversion load_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H11; auto.
    subst.
    exists (updateAddAL _ lc i0 gv'). exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_store".
    inversion Hsmem_denotes2; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    apply smem_denotes_mem_det with (Mem2:=Mem1) in H13; auto.
    subst.
    exists lc. exists als. exists Mem2. exists trace_nil.
    split; eauto.

  Case "insn_gep".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_gep i0 i1 t v l0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv' [gep_denotes_gv' gv_in_env']].
    inversion gep_denotes_gv'; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denote__imply__genericvalues with (lc:=lc)(gl:=gl) in H11; auto.
    exists (updateAddAL _ lc i0 gv'). exists als. exists Mem1. exists trace_nil.
    split; eauto.

  Case "insn_trunc".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_trunc i0 t t0 v t1) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv3 [trunc_denotes_gv3 gv3_in_env']].
    inversion trunc_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (@TRUNC DGVs TD lc gl t t0 v t1 = Some gv3) as J.
      unfold TRUNC. rewrite H10. auto.
    split; eauto.

  Case "insn_ext".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_ext i0 e t v t0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv3 [ext_denotes_gv3 gv3_in_env']].
    inversion ext_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (@EXT DGVs TD lc gl e t v t0 = Some gv3) as J.
      unfold EXT. rewrite H10. auto.
    split; eauto.

  Case "insn_cast".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_cast i0 c t v t0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv3 [cast_denotes_gv3 gv3_in_env']].
    inversion cast_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (@CAST DGVs TD lc gl c t v t0 = Some gv3) as J.
      unfold CAST. rewrite H10. auto.
    split; eauto.

  Case "insn_icmp".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_icmp i0 c t v v0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv3 [icmp_denotes_gv3 gv3_in_env']].
    inversion icmp_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (@ICMP DGVs TD lc gl c t v v0 = Some gv3) as J.
      unfold ICMP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_fcmp".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_fcmp i0 f f0 v v0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv3 [fcmp_denotes_gv3 gv3_in_env']].
    inversion fcmp_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H10; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    exists (updateAddAL _ lc i0 gv3). exists als. exists Mem1. exists trace_nil. 
    assert (@FCMP DGVs TD lc gl f f0 v v0 = Some gv3) as J.
      unfold FCMP. rewrite H10. rewrite H11. auto.
    split; eauto.

  Case "insn_select".
    assert (i0 `in` dom (STerms (se_cmd sstate1 (mkNB (insn_select i0 v t v0 v1) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote21 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J. 
    destruct J as [gv3 [select_denotes_gv3 gv3_in_env']].
    inversion select_denotes_gv3; subst.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H9; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H11; auto.
    apply value2Sterm_denotes__implies__genericvalue with (lc:=lc)(gl:=gl) in H12; auto.
    exists (if isGVZero TD gv0 then updateAddAL _ lc i0 gv2 else updateAddAL _ lc i0 gv1). exists als. exists Mem1. exists trace_nil. 
    split; eauto.

  Case "insn_call". inversion nc.
Qed.

Lemma aux__se_cmd__denotes__op_cmd : forall TD c nc lc als gl Mem1 lc' als' Mem2 lc0 als0 Mem0 sstate1 tr1 tr2,
  uniq sstate1.(STerms) ->
  uniq (se_cmd sstate1 (mkNB c nc)).(STerms) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 sstate1 lc als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd sstate1 (mkNB c nc)) lc' als' Mem2 tr2 ->
  exists tr, exists slc,
    dbCmd TD gl lc als Mem1 c slc als' Mem2 tr /\
    tr2 = trace_app tr1 tr /\
    eqAL _ slc lc'.
Proof.
  intros TD c nc lc als gl Mem1 lc' als' Mem2 lc0 als0 Mem0 sstate1 tr1 tr2 
    Huniq Huniq' Hdenotes1 Hdenotes2.
  assert (J:=Hdenotes2).
  apply aux__se_cmd__denotes__exists_op_cmd with
    (lc:=lc)(als:=als)(gl:=gl)(Mem1:=Mem1)(tr1:=tr1)(c:=c) in J; simpl; auto.
  destruct J as [lc'' [als'' [Mem2' [tr [HdbCmd EQ]]]]]; subst.
  assert (Hdenotes2':=HdbCmd).
  apply op_cmd__satisfies__se_cmd with (lc0:=lc0)(als0:=als0)(Mem0:=Mem0)(sstate1:=sstate1)(tr1:=tr1)(nc:=nc) in Hdenotes2'; auto.
  apply sstate_denotes_state_det with (lc2:=lc')(als2:=als')(Mem2:=Mem2)(tr2:=trace_app tr1 tr) in Hdenotes2'; auto.
  destruct Hdenotes2' as [EQ1 [EQ2 [EQ3 EQ4]]]; subst.
  exists tr. exists lc''. split; auto.
Qed.

Lemma se_cmd__denotes__op_cmd : forall TD c nc lc als gl Mem1 lc' als' Mem2 tr,
  uniq lc ->
  sstate_denotes_state TD lc gl als Mem1 (se_cmd sstate_init (mkNB c nc)) lc' als' Mem2 tr ->
  exists slc,
    dbCmd TD gl lc als Mem1 c slc als' Mem2 tr /\ eqAL _ slc lc'. 
Proof.
  intros TD c nc lc als gl Mem1 lc' als' Mem2 tr Huniqc Hdenotes.
  assert (J:=Hdenotes).
  apply aux__se_cmd__denotes__op_cmd with
    (lc:=lc)(gl:=gl)(Mem1:=Mem1)(tr1:=trace_nil)(als:=als)(c:=c) in J; auto.
    simpl in J. destruct J as [tr0 [slc [J1 [J2 J3]]]]; subst. 
    exists slc.  split; auto.

    simpl. auto.   

    destruct c; simpl; auto.
      inversion nc.

    apply init_denotes_id; auto.
Qed.

Lemma binds_se_cmd : forall c nc i0 i1 st0 smap1 smem1 sframe1 seffects1,
  binds i0 st0 smap1 ->
  getCmdLoc c = i1 ->
  i0 <> i1 ->
  binds i0 st0 (STerms (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) (mkNB c nc) )).
Proof.
  destruct c; intros nc id0 id1 st0 smap1 smem1 sframe1 seffects1 Hbinds 
                     HgetCmdLoc id0_isnt_id1; simpl;
    simpl in HgetCmdLoc; subst; auto using binds_updateAddAL_neq.
    inversion nc.
Qed.
  
Lemma binds_se_cmds_onlyif : forall nbs i0 st0 smap1 smem1 sframe1 seffects1 c nc,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdLoc c = i0 ->
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)).
Proof.
  induction nbs; intros i0 st0 smap1 smem1 sframe1 seffects1 c nc Hwf HgetCmdLoc Hbinds; simpl in *; auto.
    remember (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) a) as R.
    destruct R as [smap0 smem0 sframe0 seffects0].
    apply IHnbs with (c:=c)(nc:=nc); auto.
      apply wf_nbranchs__inv in Hwf; auto.

      inversion Hwf; subst.
      apply cmds2nbs__nbranchs2cmds in H.
      simpl in H.
      destruct a.
      rewrite <- H in H0.
      simpl in H0.
      inversion H0; subst.
      rewrite nbranchs2cmds_app in H3.
      rewrite getCmdsLocs_app in H3.
      apply NotIn_inv in H3.
      destruct H3 as [_ H3].
      simpl in H3.
      assert (getCmdLoc c <> getCmdLoc nbranching_cmd0) as neq.
        destruct (getCmdLoc c == getCmdLoc nbranching_cmd0); auto.
      destruct nbranching_cmd0; simpl in HeqR; inversion HeqR; subst; 
        try solve [
          auto | 
          apply binds_updateAddAL_neq; auto |
          inversion notcall0
        ].
Qed.
         
Lemma binds_se_cmds_strengthen : forall nbs i1 st1 smap1 smem1 sframe1 seffects1,
  uniq smap1 ->
  binds i1 st1 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)) ->
  ~ In i1 (getCmdsLocs (nbranchs2cmds nbs)) ->
  binds i1 st1 smap1.
Proof.
  induction nbs; intros i1 st1 smap1 smem1 sframe1 seffects1 Uniq Binds i1_notin; simpl in *; auto.
    destruct a.
    destruct nbranching_cmd0; simpl in *; try solve [
      apply IHnbs in Binds; auto using updateAddAL_uniq;
        apply updateAddAL_inversion in Binds; auto;
        destruct Binds as [[_ J] | [EQ1 EQ2]]; subst; try solve [auto|contradict i1_notin; auto] |
      inversion notcall0
     ].
Qed.

Lemma binds_se_cmds_weaken : forall nbs i1 st1 smap1 smem1 sframe1 seffects1,
  uniq smap1 ->
  binds i1 st1 smap1 ->
  ~ In i1 (getCmdsLocs (nbranchs2cmds nbs)) ->
  binds i1 st1 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)).
Proof.
  induction nbs; intros i1 st1 smap1 smem1 sframe1 seffects1 Uniq Binds i1_notin; simpl in *; auto.
    destruct a.
    destruct nbranching_cmd0; simpl; try solve [
      simpl in i1_notin;
      apply IHnbs; auto using updateAddAL_uniq, binds_updateAddAL_neq |
      inversion notcall0 
      ].
Qed.

Lemma _binds_se_cmds_if : forall nbs i1 st1 smap1 smem1 sframe1 seffects1 i0 st0,
  uniq smap1 ->
  binds i1 st1 (STerms (se_cmds (mkSstate (updateAddAL _ smap1 i0 st0) smem1 sframe1 seffects1) nbs)) ->
  ~ In i1 (getCmdsLocs (nbranchs2cmds nbs)) ->
  i1 <> i0 ->
  binds i1 st1 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)).
Proof.
  intros nbs i1 st1 smap1 smem1 sframe1 seffects1 i0 st0 Uniq Binds i1_notin i1_isnt_i0.
  apply binds_se_cmds_strengthen in Binds; auto.
    apply updateAddAL_inversion in Binds; auto.
      destruct Binds as [[_ BInds] | [EQ1 EQ2]]; subst.
        apply binds_se_cmds_weaken; auto.
        contradict i1_isnt_i0; auto.
      apply updateAddAL_uniq; auto.
Qed.

Lemma binds_se_cmds_if : forall nbs i0 st0 smap1 smem1 sframe1 seffects1 c nc,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdLoc c = i0 ->
  uniq smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)) ->
  binds i0 st0 smap1.
Proof.
  induction nbs; intros i0 st0 smap1 smem1 sframe1 seffects1 c nc Hwf HgetCmdLoc Uniq Hbinds; simpl in *; auto.
    remember (se_cmd (mkSstate smap1 smem1 sframe1 seffects1) a) as R.
    destruct R as [smap0 smem0 sframe0 seffects0].
    apply IHnbs with (c:=c)(nc:=nc)(smem1:=smem0)(sframe1:=sframe0)(seffects1:=seffects0); auto.
      apply wf_nbranchs__inv in Hwf; auto.

      inversion Hwf; subst.
      apply cmds2nbs__nbranchs2cmds in H.
      simpl in H.
      destruct a.
      rewrite <- H in H0.
      simpl in H0.
      inversion H0; subst.
      rewrite nbranchs2cmds_app in H3.
      rewrite getCmdsLocs_app in H3.
      apply NotIn_inv in H3.
      destruct H3 as [_ H3].
      simpl in H3.
      assert (getCmdLoc c <> getCmdLoc nbranching_cmd0) as neq.
        destruct (getCmdLoc c == getCmdLoc nbranching_cmd0); auto.
      assert (~ In (getCmdLoc c) (getCmdsLocs (nbranchs2cmds nbs))) as notin.
        rewrite nbranchs2cmds_app in H4.
        rewrite getCmdsLocs_app in H4.
        simpl in H4.
        apply NoDup_last_inv; auto.
      destruct nbranching_cmd0; simpl in HeqR; inversion HeqR; subst; 
        try solve [
          auto | 
          eapply _binds_se_cmds_if; eauto |
          inversion notcall0
        ].
Qed.

Lemma binds_se_cmds : forall i0 st0 smap1 smem1 sframe1 seffects1 nbs c nc,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdLoc c = i0 ->
  binds i0 st0 smap1 ->
  binds i0 st0 (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)).
Proof.
  intros i0 st0 smap1 smem1 sframe1 seffects1 nbs c nc H1 H2.
  eapply binds_se_cmds_onlyif; eauto.
Qed.

Lemma binds_se_cmds__prefix_last : forall nbs c nc id' st' smap1 smem1 sframe1 seffects1 i0,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  binds id' st' (STerms (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) nbs)) ->
  getCmdLoc c = i0 ->
  uniq smap1 ->
  (id'=i0 /\ binds id' st' smap1) \/ 
  (id' <> i0 /\ 
   binds id' st' 
    (STerms (se_cmd 
              (se_cmds (mkSstate smap1 smem1 sframe1 seffects1) 
               nbs) 
             (mkNB c nc))
     )
  ).
Proof.
  intros nbs c nc id' st' smap1 smem1 sframe1 seffects1 i0 Wf Binds GetCmdID Uniq.
  destruct (i0==id'); subst.
    left. split; auto.
      eapply binds_se_cmds_if; eauto.
    right. split; auto.
      apply binds_se_cmd with (i1:=getCmdLoc c) ; auto.
Qed.

Lemma se_cmd_updateAddAL_inv : forall c nc st,
  STerms (se_cmd st (mkNB c nc)) = STerms st \/
  (exists st0, (STerms (se_cmd st (mkNB c nc))) = updateAddAL _ (STerms st) (getCmdLoc c) st0).
Proof.
  destruct c; intros; simpl; auto.
    right. 
    exists (sterm_bop b s 
                     (value2Sterm st.(STerms) v)
                     (value2Sterm st.(STerms) v0)). auto.
    right. 
    exists (sterm_fbop f f0 
                     (value2Sterm st.(STerms) v)
                     (value2Sterm st.(STerms) v0)). auto.
    right. 
    exists (sterm_extractvalue t
                     (value2Sterm st.(STerms) v)
                     l0). auto.

    right. 
    exists (sterm_insertvalue 
                     t 
                     (value2Sterm st.(STerms) v)
                     t0 
                     (value2Sterm st.(STerms) v0)
                     l0). auto.

    right. 
    exists (sterm_malloc st.(SMem) t (value2Sterm st.(STerms) v) a). auto.

    right. 
    exists (sterm_alloca st.(SMem) t (value2Sterm st.(STerms) v) a). auto.

    right. 
    exists (sterm_load st.(SMem) t 
                     (value2Sterm st.(STerms) v) a). auto.

    right. 
    exists (sterm_gep i1 t
             (value2Sterm st.(STerms) v)
             (make_list_sterm 
               (map_list_sz_value 
                 (fun sz' v' => (sz', value2Sterm st.(STerms) v')) l0))). auto.

    right. 
    exists (sterm_trunc t t0
                     (value2Sterm st.(STerms) v)
                     t1). auto.

    right. 
    exists (sterm_ext e t
                     (value2Sterm st.(STerms) v)
                     t0). auto.

    right. 
    exists (sterm_cast c t
                     (value2Sterm st.(STerms) v)
                     t0). auto.

    right. 
    exists (sterm_icmp c t
                     (value2Sterm st.(STerms) v)
                     (value2Sterm st.(STerms) v0)). auto.

    right. 
    exists (sterm_fcmp f f0
                     (value2Sterm st.(STerms) v)
                     (value2Sterm st.(STerms) v0)). auto.

    right. 
    exists (sterm_select 
                     (value2Sterm st.(STerms) v)
                     t
                     (value2Sterm st.(STerms) v0)
                     (value2Sterm st.(STerms) v1)). auto.

    inversion nc.
Qed.

Lemma in_se_cmds__prefix_last : forall nbs c nc id' smem1 sframe1 seffects1 i0,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdLoc c = i0 ->
  (id'=i0 /\ 
   lookupSmap (STerms (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs)) id' = sterm_val (value_id id') /\
   id' `notin` dom (STerms (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs))
   ) \/ 
  (id' <> i0 /\ 
   lookupSmap (STerms (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs)) id' = 
   lookupSmap (STerms 
                (se_cmd 
                  (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs) 
                  (mkNB c nc))) id'
  ).
Proof.
  intros nbs c nc id' smem1 sframe1 seffects1 i0 Wf GetCmdID.
  destruct (i0==id'); subst.
    left.
    destruct (@AtomSetProperties.In_dec id' (dom(STerms (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs)) )) as [id'_in | id'_notin].
      apply binds_In_inv in id'_in.
      destruct id'_in as [st' Binds].
      apply binds_se_cmds_if with (c:=c)(nc:=nc) in Binds; auto.
      inversion Binds.

      rewrite lookupSmap_notin; auto using se_cmds_uniq.
    right.
    destruct (@AtomSetProperties.In_dec id' (dom(STerms (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs)) )) as [id'_in | id'_notin].
      apply binds_In_inv in id'_in.
      destruct id'_in as [st' Binds].
      rewrite lookupSmap_in with (st0:=st'); auto using se_cmds_uniq.
      apply binds_se_cmds__prefix_last with (c:=c)(nc:=nc)(i0:=getCmdLoc c) in Binds; auto.
      destruct Binds as [[EQ Binds] | [nEQ Binds]].
        inversion Binds.
        rewrite lookupSmap_in with (st0:=st'); auto using se_cmd_uniq_aux, se_cmds_uniq.
 
      rewrite lookupSmap_notin; auto using se_cmds_uniq.
      rewrite lookupSmap_notin; auto using se_cmd_uniq_aux, se_cmds_uniq.
      assert (J:=@se_cmd_dom_upper (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs) c nc).
      fsetdec.
Qed.

Lemma in_se_cmds__prefix_last__eq : forall nbs c nc smem1 sframe1 seffects1 i0,
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdLoc c = i0 ->
  lookupSmap (STerms (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs)) i0 = sterm_val (value_id i0).
Proof.
  intros nbs c nc smem1 sframe1 seffects1 i0 Wf HgetCmdLoc.
  apply in_se_cmds__prefix_last with (id':=i0)(smem1:=smem1)(sframe1:=sframe1)(seffects1:=seffects1)(i0:=i0) in Wf; auto.
  destruct Wf as [[EQ [J J']] | [nEQ J]]; auto.
    contradict nEQ; auto.
Qed.

Lemma in_se_cmds__prefix_last__neq : forall nbs c nc smem1 sframe1 seffects1 id',
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->  
  getCmdLoc c <> id' ->
  lookupSmap (STerms (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs)) id' = 
  lookupSmap (STerms 
                (se_cmd 
                  (se_cmds (mkSstate nil smem1 sframe1 seffects1) nbs) 
                  (mkNB c nc))) id'.
Proof.
  intros nbs c nc smem1 sframe1 seffects1 id' Wf HgetCmdLoc.
  apply in_se_cmds__prefix_last with (id':=id')(smem1:=smem1)(sframe1:=sframe1)(seffects1:=seffects1)(i0:=getCmdLoc c) in Wf; auto.
  destruct Wf as [[EQ [J J']] | [nEQ J]]; auto.
    contradict EQ; auto.
Qed.

Lemma smap_denotes_gvmap_rollbackEnv : forall TD lc0 gl Mem0 nbs c nc lc2 gv3 i0,
  uniq lc0 ->
  uniq lc2 ->
  wf_nbranchs (nbs++(mkNB c nc::nil)) ->
  smap_denotes_gvmap TD lc0 gl Mem0 (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB c nc))) lc2 ->
  lookupAL _ lc2 i0 = Some gv3 ->
  getCmdLoc c = i0 ->
  smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0).
Proof.
  intros TD lc0 gl Mem0 nbs c nc lc2 gv3 i0
        Huniqc0 Huniqc2 Wf [Hsterms_denote1 Hsterms_denote2] gv3_in_env2 HgetCmdLoc.
  assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
    apply rollbackAL_uniq; auto.
  split; intros.
        assert (J:=Wf).
        apply in_se_cmds__prefix_last with (i0:=i0)(id':=id')(smem1:=smem_init)(sframe1:=sframe_init)(seffects1:=nil) in J; auto.
        destruct J as [[id'_is_i0 [lkSmap_id' id'_notin]] | [i0_isnt_id' lkSmap_id']]; subst.
          unfold sstate_init.
          rewrite lkSmap_id'.
          assert (getCmdLoc c `in` dom lc0) as id'_in_lc0.
            clear - id'_notin H. fsetdec.
          erewrite lookupAL_rollbackAL_Some_eq; eauto.
          apply id_denotes_gv; auto.

          unfold sstate_init.
          rewrite lkSmap_id'.
          assert (id' `in` union (dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB c nc)))) (dom lc0)) as id'_in.
            apply in_dom_app_inv in H.
            destruct H; auto.
              assert (J:=@se_cmd_dom_mono' (se_cmds sstate_init nbs) (mkNB c nc)).
              fsetdec.
          apply Hsterms_denote1 in id'_in.
          destruct id'_in as [gv' [id'_denotes_gv' id'_gv'_in_env2]].
          erewrite <- lookupAL_rollbackAL_neq with (id1:=id'); eauto.

        destruct (i0==id'); subst.
          rewrite <- e in H.
          erewrite lookupAL_rollbackAL_eq in H; eauto.
          unfold sstate_init.
          erewrite in_se_cmds__prefix_last__eq; eauto.
          rewrite <- e. auto.

          rewrite <- lookupAL_rollbackAL_neq with (id1:=id') in H; auto.
          apply Hsterms_denote2 in H.
          unfold sstate_init in H.
          rewrite <- in_se_cmds__prefix_last__neq in H; auto.
Qed.


Lemma se_cmds_denotes__decomposes__prefix_last__case1 : forall id' gl lc2 i0 TD Mem2 lc0,
  uniq (rollbackAL _ lc2 i0 lc0) ->
  i0 <> id' ->
  id' `in` union (add i0 empty) (dom (rollbackAL _ lc2 i0 lc0)) ->
  exists gv', sterm_denotes_genericvalue TD (rollbackAL _ lc2 i0 lc0) gl Mem2 (sterm_val (value_id id')) gv' /\ 
  lookupAL _ lc2 id' = Some gv'.
Proof.
  intros id' gl lc2 i0 TD Mem2 lc0 Uniqc1 i0_isnt_id' id'_in0.
            assert (id'=i0 \/ id' `in` dom (rollbackAL _ lc2 i0 lc0)) as id'_in. fsetdec.
            destruct id'_in as [i0_is_id' | id'_in_rollback]; subst.
              contradict i0_isnt_id'; auto.              
              
              apply indom_lookupAL_Some in id'_in_rollback.
              destruct id'_in_rollback as [gv' id'_in_rollback].
              exists gv'. split; auto.
                rewrite <- lookupAL_rollbackAL_neq with (id1:=id') in id'_in_rollback; auto.
Qed.

Lemma se_cmds_denotes__decomposes__prefix_last : forall nb TD lc0 gl als0 Mem0 nbs lc2 als2 Mem2 tr,
  uniq lc0 ->
  uniq lc2 ->
  wf_nbranchs (nbs++(nb::nil)) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd (se_cmds sstate_init nbs) nb) lc2 als2 Mem2 tr ->
  exists lc1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds sstate_init nbs) lc1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmd sstate_init nb) lc2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ 
    uniq lc1.
Proof.
  intros [c nc] TD lc0 gl als0 Mem0 nbs lc2 als2 Mem2 tr Huniqc0 Huniqc2 Wf Hdenotes.
  assert (uniq (STerms (se_cmds sstate_init nbs))) as Uniq1.
    eauto using se_cmds_init_uniq.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent lc2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent tr.
  generalize dependent nc.
  generalize dependent nbs.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes as [[Hsterms_denote1 Hsterms_denote2] [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]].
  Case "insn_bop".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_bop i0 b s v v0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [bop_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2  i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_bop i0 b s v v0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion bop_denotes_gv3; subst. clear bop_denotes_gv3.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion bop_denotes_gv3; subst.
            apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_fbop".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_fbop i0 f f0 v v0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [fbop_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2  i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_fbop i0 f f0 v v0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            inversion fbop_denotes_gv3; subst. clear fbop_denotes_gv3.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            apply sterm_fbop_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion fbop_denotes_gv3; subst.
            apply sterm_fbop_denotes with (gv1:=gv1)(gv2:=gv2); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_extractvalue".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_extractvalue i0 t v l0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [extractvalue_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_extractvalue i0 t v l0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion extractvalue_denotes_gv3; subst. clear extractvalue_denotes_gv3.
            apply sterm_extractvalue_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion extractvalue_denotes_gv3; subst.
            apply sterm_extractvalue_denotes with (gv1:=gv1); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_insertvalue".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_insertvalue i0 t v t0 v0 l0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [insertvalue_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_insertvalue i0 t v t0 v0 l0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion insertvalue_denotes_gv3; subst. clear insertvalue_denotes_gv3.
            apply sterm_insertvalue_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion insertvalue_denotes_gv3; subst.
            apply sterm_insertvalue_denotes with (gv1:=gv1)(gv2:=gv2); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_malloc".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_malloc i0 t v a) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [malloc_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem3. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_malloc i0 t v a)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion malloc_denotes_gv3; subst. clear malloc_denotes_gv3.
            apply smem_denotes_mem_det with (Mem2:=Mem4) in H7; auto. subst.
            apply sterm_denotes_genericvalue_det with (gv2:=gv1) in H10; auto. subst.
            rewrite H14 in H9. inversion H9; subst. clear H9.
            rewrite H11 in H16. inversion H16; subst. clear H16.
            eapply sterm_malloc_denotes; eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion malloc_denotes_gv3; subst.
            apply smem_denotes_mem_det with (Mem2:=Mem4) in H7; auto. subst.
            apply sterm_denotes_genericvalue_det with (gv2:=gv1) in H10; auto. subst.
            rewrite H14 in H9. inversion H9; subst. clear H9.
            rewrite H11 in H16. inversion H16; subst. clear H16.
            eapply sterm_malloc_denotes; eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

      split; simpl; eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.
    
  Case "insn_free".
    inversion Hsmem_denotes; subst.
    exists lc2. exists als2. exists Mem3. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
        split; auto.
    split; auto.
      split.
        split; intros; simpl; auto.
          simpl in H. simpl.
          apply id_denotes_gv with (TD:=TD)(Mem0:=Mem3)(gl:=gl); auto.
            fsetdec.

      split; simpl; eauto.
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2) in H6; try solve [auto | split; auto].
        eapply smem_free_denotes; eauto 
                  using genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.        

  Case "insn_alloca".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_alloca i0 t v a) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [alloca_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    inversion Hsframe_denotes; subst.
    apply smem_denotes_mem_det with (Mem2:=Mem3) in H13; auto. subst.
    apply sterm_denotes_genericvalue_det with (gv2:=gv1) in H10; auto. subst.
    rewrite H9 in H16. inversion H16; subst. clear H16.
    rewrite H11 in H18. inversion H18; subst. clear H18.
    exists (rollbackAL _ lc2 i0 lc0). exists als3. exists Mem3. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_alloca i0 t v a)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion alloca_denotes_gv3; subst. clear alloca_denotes_gv3.
            apply smem_denotes_mem_det with (Mem2:=Mem2) in H7; auto. subst.
            apply sterm_denotes_genericvalue_det with (gv2:=gv1) in H14; auto. subst.
            rewrite H13 in H9. inversion H9; subst. clear H9.
            rewrite H11 in H16. inversion H16; subst. clear H16.
            eapply sterm_alloca_denotes; eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion alloca_denotes_gv3; subst.
            apply smem_denotes_mem_det with (Mem2:=Mem2) in H7; auto. subst.
            apply sterm_denotes_genericvalue_det with (gv2:=gv1) in H14; auto. subst.
            rewrite H13 in H9. inversion H9; subst. clear H9.
            rewrite H11 in H16. inversion H16; subst. clear H16.
            eapply sterm_alloca_denotes; eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

      split; simpl; eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

      split; simpl; eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

  Case "insn_load".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_load i0 t v a) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [load_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_load i0 t v a)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion load_denotes_gv3; subst. clear load_denotes_gv3.
            apply smem_denotes_mem_det with (Mem2:=Mem2) in H11; auto. subst.
            eapply sterm_load_denotes with (gv0:=gv0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion load_denotes_gv3; subst.
            apply smem_denotes_mem_det with (Mem2:=Mem2) in H11; auto. subst.
            eapply sterm_load_denotes with (gv0:=gv0); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

      split; simpl; eauto.   

  Case "insn_store".
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    inversion Hsmem_denotes; subst.
    exists lc2. exists als2. exists Mem3. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
        split; auto.
    split; simpl; eauto.
      split.
        split; intros; simpl; auto.
          simpl in H.
          apply id_denotes_gv with (TD:=TD)(Mem0:=Mem3)(gl:=gl); auto.
            fsetdec.

      split; simpl; eauto.
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2) in H9; try solve [auto | split; auto].
        apply value2Sterm_denotes__implies__genericvalue with (lc:=lc2) in H10; try solve [auto | split; auto].
        eapply smem_store_denotes; eauto 
                  using genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.        

  Case "insn_gep".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_gep i0 i1 t v l0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [gep_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_gep i0 i1 t v l0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion gep_denotes_gv3; subst. clear gep_denotes_gv3.
            apply value2Sterm_denote__imply__genericvalues with (lc:=(rollbackAL _ lc2 i0 lc0)) in H10; try solve [auto | split; auto].
            eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.
              eapply genericvalues__imply__value2Sterm_denote; eauto 
                using init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion gep_denotes_gv3; subst.
            apply value2Sterm_denote__imply__genericvalues with (lc:=(rollbackAL _ lc2 i0 lc0)) in H10; try solve [auto | split; auto].
            eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.
              eapply genericvalues__imply__value2Sterm_denote; eauto using init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_trunc".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_trunc i0 t t0 v t1) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [trunc_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_trunc i0 t t0 v t1)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion trunc_denotes_gv3; subst. clear trunc_denotes_gv3.
            apply sterm_trunc_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion trunc_denotes_gv3; subst.
            apply sterm_trunc_denotes with (gv1:=gv1); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_ext".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_ext i0 e t v t0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [ext_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_ext i0 e t v t0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion ext_denotes_gv3; subst. clear ext_denotes_gv3.
            apply sterm_ext_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion ext_denotes_gv3; subst.
            apply sterm_ext_denotes with (gv1:=gv1); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_cast".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_cast i0 c t v t0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [cast_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_cast i0 c t v t0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion cast_denotes_gv3; subst. clear cast_denotes_gv3.
            apply sterm_cast_denotes with (gv1:=gv1); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion cast_denotes_gv3; subst.
            apply sterm_cast_denotes with (gv1:=gv1); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_icmp".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_icmp i0 c t v v0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [icmp_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_icmp i0 c t v v0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion icmp_denotes_gv3; subst. clear icmp_denotes_gv3.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion icmp_denotes_gv3; subst.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_fcmp".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_fcmp i0 f f0 v v0) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [fcmp_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_fcmp i0 f f0 v v0)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion fcmp_denotes_gv3; subst. clear fcmp_denotes_gv3.
            apply sterm_fcmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion fcmp_denotes_gv3; subst.
            apply sterm_fcmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_select".
    assert (i0 `in` dom (STerms (se_cmd (se_cmds sstate_init nbs) (mkNB (insn_select i0 v t v0 v1) nc))) `union` dom lc0) as J.
      apply in_dom_ext_right.
      simpl. apply in_updateAddAL_eq; auto.
    apply Hsterms_denote1 in J.
    simpl in J. rewrite lookupSmap_updateAddAL_eq in J.
    destruct J as [gv3 [select_denotes_gv3 gv3_in_env2]].
    simpl in Hsmem_denotes, Hsframe_denotes, Hseffects_denote.
    exists (rollbackAL _ lc2 i0 lc0). exists als2. exists Mem2. exists tr. exists trace_nil.
    assert (uniq (rollbackAL _ lc2 i0 lc0)) as Huniqc1.
      apply rollbackAL_uniq; auto.
    assert (smap_denotes_gvmap TD lc0 gl Mem0
              (STerms (se_cmds sstate_init nbs))
              (rollbackAL _ lc2 i0 lc0)) as env0_denote_env1.
      apply smap_denotes_gvmap_rollbackEnv with (c:=insn_select i0 v t v0 v1)(nc:=nc)(i0:=i0)(lc2:=lc2)(gv3:=gv3); 
        try solve [auto | split; auto].
    rewrite trace_app_nil__eq__trace.
    split.
      split; auto.
    split; auto.
      split; auto.
        split; intros.
          simpl in H. simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            exists gv3. split; eauto using lookupAL_rollbackAL_eq.
            clear Hsmem_denotes Hsframe_denotes Hseffects_denote.
            simpl. destruct (i0==i0) as [_ | FALSE]; try solve [contradict FALSE; auto].
            inversion select_denotes_gv3; subst. clear select_denotes_gv3.
            eapply sterm_select_denotes with (gv0:=gv0)(gv1:=gv1)(gv2:=gv2); eauto
                  using value2Sterm_denotes__implies__genericvalue,
                        genericvalue__implies__value2Sterm_denotes,
                        init_denotes_gvmap.

            apply se_cmds_denotes__decomposes__prefix_last__case1 with (i0:=i0)(lc0:=lc0); auto.

          assert (id'_in_env2:=H).
          apply Hsterms_denote2 in H.
          simpl.
          destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
            simpl in H. 
            rewrite lookupSmap_updateAddAL_eq in H.
            rewrite id'_in_env2 in gv3_in_env2.
            inversion gv3_in_env2; subst. clear gv3_in_env2.
            inversion select_denotes_gv3; subst.
            eapply sterm_select_denotes with (gv0:=gv0)(gv1:=gv1)(gv2:=gv2); eauto
              using value2Sterm_denotes__implies__genericvalue,
                    genericvalue__implies__value2Sterm_denotes,
                    init_denotes_gvmap.

            rewrite lookupAL_rollbackAL_neq with (id0:=i0)(lc0:=lc0) in id'_in_env2; auto.

  Case "insn_call". inversion nc.
Qed. 

Lemma se_cmds_denotes__composes__prefix_last__case1 : forall TD lc0 gl Mem0 nbs lc1 lc2 Mem1 id' c nc i0 st0,
  smap_denotes_gvmap TD lc0 gl Mem0 (STerms (se_cmds sstate_init nbs)) lc1 ->
  smap_denotes_gvmap TD lc1 gl Mem1 (STerms (se_cmd sstate_init (mkNB c nc))) lc2 ->
  getCmdLoc c = i0 ->
  i0 <> id' ->
  id' `in` dom (STerms (se_cmds sstate_init nbs)) `union` dom lc0 ->
  exists gv', 
    sterm_denotes_genericvalue TD lc0 gl Mem0 (lookupSmap (updateAddAL _ (STerms (se_cmds sstate_init nbs)) i0 st0) id') gv' /\ 
    lookupAL _ lc2 id' = ret gv'.
Proof.
  intros TD lc0 gl Mem0 nbs lc1 lc2 Mem1 id' c nc i0 st0 [Hsterms_denote11 Hsterms_denote12]
     [Hsterms_denote21 Hsterms_denote22] HgetCmdLoc i0_isnt_id' id'_in.
            rewrite <- lookupSmap_updateAddAL_neq; auto.
            assert (J:=id'_in).
            apply Hsterms_denote11 in J.
            destruct J as [gv' [id'_denotes_gv' id'_gv'_in_env1]].
            apply lookupAL_Some_indom in id'_gv'_in_env1.
            apply in_dom_ext_left with (D2:=dom (STerms (se_cmd sstate_init (mkNB c nc)))) in id'_gv'_in_env1.
            apply Hsterms_denote21 in id'_gv'_in_env1.           
            rewrite <- HgetCmdLoc in i0_isnt_id'.
	    unfold sstate_init in id'_gv'_in_env1.
            rewrite lookupSmap_se_cmd_neq in id'_gv'_in_env1; auto.
            destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
            inversion id'_denotes_gv'0; subst.
            simpl in H4.
            apply Hsterms_denote12 in H4.
            exists gv'0. split; auto.
Qed.

Lemma se_cmds_denotes__composes__prefix_last__case2 : forall TD lc1 gl Mem1 lc0 Mem0 v gv1 nbs,  
  uniq lc1 ->
  smap_denotes_gvmap TD lc0 gl Mem0 (STerms (se_cmds sstate_init nbs)) lc1 ->
  sterm_denotes_genericvalue TD lc1 gl Mem1 (value2Sterm nil v) gv1 ->
  sterm_denotes_genericvalue TD lc0 gl Mem0 (value2Sterm (STerms (se_cmds sstate_init nbs)) v) gv1.
Proof.
  intros TD lc1 gl Mem1 lc0 Mem0 v gv1 nbs U1 H1 H2.
  apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1) in H2; auto.
  apply genericvalue__implies__value2Sterm_denotes with (lc:=lc1); 
    eauto using se_cmds_init_uniq.
  apply init_denotes_gvmap; auto.
Qed.
    
Lemma se_cmds_denotes__composes__prefix_last__case3 : forall TD lc1 gl Mem1 lc0 Mem0 nbs gv' id' i0 st0,  
  uniq lc1 ->
  i0 <> id' ->
  smap_denotes_gvmap TD lc0 gl Mem0 (STerms (se_cmds sstate_init nbs)) lc1 ->
  sterm_denotes_genericvalue TD lc1 gl Mem1 (sterm_val (value_id id')) gv' ->
  sterm_denotes_genericvalue TD lc0 gl Mem0 (lookupSmap (updateAddAL _ (STerms (se_cmds sstate_init nbs)) i0 st0) id') gv'.
Proof.
  intros TD lc1 gl Mem1 lc0 Mem0 nbs gv' id' i0 st0 
    Uc1 i0_isnt_id' [Hsterms_denote11 Hsterms_denote12] st'_denotes_gv'.
  rewrite <- lookupSmap_updateAddAL_neq; auto.
  inversion st'_denotes_gv'; subst.
  simpl in H4.
  apply Hsterms_denote12 in H4. auto.
Qed.

Lemma se_cmds_denotes__composes__prefix_last : forall nb TD lc1 gl als1 Mem1 
  lc2 als2 Mem2 lc0 als0 Mem0 tr1 tr2 nbs ,
  uniq lc1 ->
  wf_nbranchs (nbs++(nb::nil)) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds sstate_init nbs) lc1 als1 Mem1 tr1 ->
  sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmd sstate_init nb) lc2 als2 Mem2 tr2 ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds sstate_init (nbs++nb::nil)) lc2 als2 Mem2 (trace_app tr1 tr2).
Proof.
  intros [c nc] TD lc1 gl als1 Mem1 lc2 als2 Mem2 lc0 als0 Mem0 tr1 tr2 nbs 
    Huniqc1 Wf Hdenotes1 Hdenotes2.
  assert (uniq (STerms (se_cmds sstate_init nbs))) as Uniq1.
    eauto using se_cmds_init_uniq.
  generalize dependent TD.
  generalize dependent lc0.
  generalize dependent gl.
  generalize dependent als0.
  generalize dependent Mem0.
  generalize dependent nbs.
  generalize dependent lc2.
  generalize dependent als2.
  generalize dependent Mem2.
  generalize dependent lc1.
  generalize dependent als1.
  generalize dependent Mem1.
  generalize dependent tr1.
  generalize dependent tr2.
  generalize dependent nc.
  (cmd_cases (destruct c) Case);
    intros;
    destruct Hdenotes1 as [JJ [Hsmem_denotes1 [Hsframe_denotes1 Hseffects_denote1]]];
    assert (Hsmap_denotes1:=JJ);
    destruct JJ as [Hsterms_denote11 Hsterms_denote12];
    destruct Hdenotes2 as [[Hsterms_denote21 Hsterms_denote22] [Hsmem_denotes2 [Hsframe_denotes2 Hseffects_denote2]]];
    rewrite se_cmds_rev_cons.
  Case "insn_bop".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_bop i0 b s v v0)(nc:=nc)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_bop id' b s v v0) nc))) `union` dom lc1) as binds_id'_bop.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_bop.
            simpl in binds_id'_bop.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_bop as [gv' [bop_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion bop_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2);
            try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.
 
  Case "insn_fbop".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_fbop i0 f f0 v v0)(nc:=nc)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_fbop id' f f0 v v0) nc))) `union` dom lc1) as binds_id'_fbop.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_fbop.
            simpl in binds_id'_fbop.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_fbop as [gv' [fbop_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion fbop_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_fbop_denotes with (gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_fbop_denotes with (gv1:=gv1)(gv2:=gv2);
            try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.
 
  Case "insn_extractvalue".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_extractvalue i0 t v l0)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_extractvalue id' t v l0) nc))) `union` dom lc1) as binds_id'_extractvalue.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_extractvalue.
            simpl in binds_id'_extractvalue.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_extractvalue as [gv' [extractvalue_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion extractvalue_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_extractvalue_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
            apply sterm_extractvalue_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_insertvalue".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_insertvalue i0 t v t0 v0 l0)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_insertvalue id' t v t0 v0 l0) nc))) `union` dom lc1) as binds_id'_insertvalue.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_insertvalue.
            simpl in binds_id'_insertvalue.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_insertvalue as [gv' [insertvalue_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion insertvalue_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_insertvalue_denotes with (gv1:=gv1) (gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_insertvalue_denotes with (gv1:=gv1) (gv2:=gv2);
              try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_malloc".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_malloc i0 t v a)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_malloc id' t v a) nc))) `union` dom lc1) as binds_id'_malloc.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_malloc.
            simpl in binds_id'_malloc.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_malloc as [gv' [malloc_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion malloc_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              inversion H7; subst.
              apply sterm_malloc_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0)(gv0:=gv0);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem4); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          inversion H8; subst.
          apply sterm_malloc_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0)(gv0:=gv0);
              try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem4); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H7; subst.
           simpl. eapply smem_malloc_denotes;
                   try solve [eauto | eapply se_cmds_denotes__composes__prefix_last__case2; eauto].

    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_free".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        assert (J:=H).
        apply Hsterms_denote11 in J.
        destruct J as [gv' [st'_denotes_gv' id'_gv'_in_env1]].
        apply lookupAL_Some_indom in id'_gv'_in_env1.
        apply in_dom_ext_left with (D2:=dom (STerms (se_cmd sstate_init (mkNB (insn_free i0 t v) nc)))) in id'_gv'_in_env1.
        apply Hsterms_denote21 in id'_gv'_in_env1.
        destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
        inversion id'_denotes_gv'0; subst.
        simpl in H5.
        apply Hsterms_denote12 in H5.
        exists gv'0. split; auto.

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        inversion H; subst.
        apply Hsterms_denote12; auto.

    split. clear Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H8; subst.
           simpl. 
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1) in H6; 
            try solve [eauto using init_denotes_gvmap| split; auto].
           eapply smem_free_denotes; eauto using genericvalue__implies__value2Sterm_denotes.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_alloca".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_alloca i0 t v a)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_alloca id' t v a) nc))) `union` dom lc1) as binds_id'_alloca.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_alloca.
            simpl in binds_id'_alloca.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_alloca as [gv' [alloca_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion alloca_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              inversion H7; subst. clear H7.
              apply sterm_alloca_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0)(gv0:=gv0);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem4); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          inversion H8; subst.
          apply sterm_alloca_denotes with (Mem1:=Mem4)(Mem2:=Mem5)(tsz0:=tsz0)(gv0:=gv0);
              try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem4); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H7; subst.
           simpl. eapply smem_alloca_denotes;
                   try solve [eauto | eapply se_cmds_denotes__composes__prefix_last__case2; eauto].

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hseffects_denote2 Hseffects_denote1.
           inversion Hsframe_denotes2; subst.
           inversion H11; subst. clear H11.
           inversion H9; subst. clear H9.
           simpl. eapply sframe_alloca_denotes;
                   try solve [eauto | eapply se_cmds_denotes__composes__prefix_last__case2; eauto].

           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

   Case "insn_load".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_load i0 t v a)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_load id' t v a) nc))) `union` dom lc1) as binds_id'_load.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_load.
            simpl in binds_id'_load.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_load as [gv' [load_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion load_denotes_gv'; subst.
              rewrite lookupSmap_updateAddAL_eq.
              inversion H9; subst. clear H9.
              eapply sterm_load_denotes with (gv0:=gv0);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem4); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          inversion H10; subst. clear H10.
          eapply sterm_load_denotes with (gv0:=gv0);
               try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem4); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H8; subst.
           simpl. eapply smem_load_denotes; eauto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

   Case "insn_store".
    split.
      clear Hsframe_denotes1 Hseffects_denote1 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl. simpl in H.
        simpl in H. simpl.
        assert (J:=H).
        apply Hsterms_denote11 in J.
        destruct J as [gv' [st'_denotes_gv' id'_gv'_in_env1]].
        apply lookupAL_Some_indom in id'_gv'_in_env1.
        apply in_dom_ext_left with (D2:=dom (STerms (se_cmd sstate_init (mkNB (insn_store i0 t v v0 a) nc)))) in id'_gv'_in_env1.
        apply Hsterms_denote21 in id'_gv'_in_env1.
        destruct id'_gv'_in_env1 as [gv'0 [id'_denotes_gv'0 id'_gv'0_in_env2]].
        inversion id'_denotes_gv'0; subst.
        simpl in H5.
        apply Hsterms_denote12 in H5.
        exists gv'0. split; auto.

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        inversion H; subst.
        apply Hsterms_denote12; auto.

    split. clear Hsterms_denote11 Hsterms_denote12 Hsterms_denote21 Hsterms_denote22
                 Hsframe_denotes2 Hsframe_denotes1 Hseffects_denote2 Hseffects_denote1.
           inversion Hsmem_denotes2; subst.
           inversion H11; subst.
           simpl. 
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1) in H9; 
            try solve [eauto using init_denotes_gvmap| split; auto].
           apply value2Sterm_denotes__implies__genericvalue with (lc:=lc1) in H10; 
            try solve [eauto using init_denotes_gvmap| split; auto].
           eapply smem_store_denotes; eauto using genericvalue__implies__value2Sterm_denotes.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_gep".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_gep i0 i1 t v l0)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_gep id' i1 t v l0) nc))) `union` dom lc1) as binds_id'_gep.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_gep.
            simpl in binds_id'_gep.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_gep as [gv' [gep_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion gep_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              eapply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
                apply value2Sterm_denote__imply__genericvalues with (lc:=lc1) in H9; auto.
                  apply genericvalues__imply__value2Sterm_denote with (lc:=lc1);
                    eauto using se_cmds_uniq.
                  apply init_denotes_gvmap; auto.

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_gep_denotes with (gv0:=gv0)(gvs0:=gvs0);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].
                apply value2Sterm_denote__imply__genericvalues with (lc:=lc1) in H10; auto.
                  apply genericvalues__imply__value2Sterm_denote with (lc:=lc1); 
                    eauto using se_cmds_uniq.
                  apply init_denotes_gvmap; auto.

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_trunc".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_trunc i0 t t0 v t1)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_trunc id' t t0 v t1) nc))) `union` dom lc1) as binds_id'_trunc.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_trunc.
            simpl in binds_id'_trunc.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_trunc as [gv' [trunc_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion trunc_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_trunc_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_trunc_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_ext".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_ext i0 e t v t0)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_ext id' e t v t0) nc))) `union` dom lc1) as binds_id'_ext.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_ext.
            simpl in binds_id'_ext.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_ext as [gv' [ext_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion ext_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_ext_denotes with (gv1:=gv1); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_ext_denotes with (gv1:=gv1);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_cast".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_cast i0 c t v t0)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_cast id' c t v t0) nc))) `union` dom lc1) as binds_id'_cast.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_cast.
            simpl in binds_id'_cast.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_cast as [gv' [cast_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion cast_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_cast_denotes with (gv1:=gv1); 
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_cast_denotes with (gv1:=gv1);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_icmp".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_icmp i0 c t v v0)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_icmp id' c t v v0) nc))) `union` dom lc1) as binds_id'_icmp.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_icmp.
            simpl in binds_id'_icmp.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_icmp as [gv' [icmp_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion icmp_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); 
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2);
                try solve [eauto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_fcmp".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_fcmp i0 f f0 v v0)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_fcmp id' f f0 v v0) nc))) `union` dom lc1) as binds_id'_fcmp.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_fcmp.
            simpl in binds_id'_fcmp.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_fcmp as [gv' [fcmp_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion fcmp_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_fcmp_denotes with (gv1:=gv1)(gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_fcmp_denotes with (gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_select".
    split.
      clear Hsmem_denotes1 Hsframe_denotes1 Hseffects_denote1 Hsmem_denotes2 Hsframe_denotes2 Hseffects_denote2.
      split; intros.
        simpl in H. simpl.
        apply se_cmd__denotes__op_cmd__case0 in H; auto.
        destruct H as [[i0_isnt_id' id'_in] | EQ]; subst.
            apply se_cmds_denotes__composes__prefix_last__case1 with (nbs:=nbs)(nc:=nc)(lc1:=lc1)(Mem1:=Mem1)(c:=insn_select i0 v t v0 v1)(i0:=i0); try solve [auto | split; auto].

            assert (id' `in` dom (STerms (se_cmd sstate_init (mkNB (insn_select id' v t v0 v1) nc))) `union` dom lc1) as binds_id'_select.
              simpl. auto.
            apply Hsterms_denote21 in binds_id'_select.
            simpl in binds_id'_select.
            destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' id') as [ _ | FALSE]; try solve [contradict FALSE; auto].
            destruct binds_id'_select as [gv' [select_denotes_gv' id'_gv'_in_env2]].
            exists gv'. split; auto.
              inversion select_denotes_gv'; subst.

              rewrite lookupSmap_updateAddAL_eq.
              apply sterm_select_denotes with (gv0:=gv0)(gv1:=gv1)(gv2:=gv2); 
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

        apply Hsterms_denote22 in H.
        simpl in H. simpl.
        destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id' i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          inversion H; subst.
          apply sterm_select_denotes with (gv0:=gv0)(gv1:=gv1)(gv2:=gv2);
                try solve [auto | apply se_cmds_denotes__composes__prefix_last__case2 with (lc1:=lc1)(Mem1:=Mem1); auto].

          apply se_cmds_denotes__composes__prefix_last__case3 with (lc1:=lc1)(Mem1:=Mem1)(i0:=i0); try solve [auto | split; auto].

    split. inversion Hsmem_denotes2; subst; auto.
    split. inversion Hsframe_denotes2; subst; auto.
           inversion Hseffects_denote1; inversion Hseffects_denote2; subst; auto.

  Case "insn_call". inversion nc.
Qed.

Definition se_cmds_denotes__decomposes__app_prop (nbs2:list nbranch) :=
forall TD lc0 gl als0 Mem0 nbs1 lc2 als2 Mem2 tr,
  uniq lc0 ->
  uniq lc2 ->
  wf_nbranchs (nbs1++nbs2) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds sstate_init (nbs1++nbs2)) lc2 als2 Mem2 tr ->
  exists lc1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds sstate_init nbs1) lc1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmds sstate_init nbs2) lc2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq lc1.

Lemma se_cmds_denotes__decomposes__app : forall nbs2, 
  se_cmds_denotes__decomposes__app_prop nbs2.
Proof.
  apply (@rev_ind nbranch); unfold se_cmds_denotes__decomposes__app_prop in *; intros; simpl.
  Case "nil".
    exists lc2. exists als2. exists Mem2. exists tr. exists trace_nil.
    rewrite trace_app_nil__eq__trace.
    rewrite <- app_nil_end in H2.
    split; auto.
    split; auto.
      apply init_denotes_id; auto.
  Case "cons".
    rewrite <- app_ass in H3.
    rewrite se_cmds_rev_cons in H3.
    rewrite <- app_ass in H2.
    apply se_cmds_denotes__decomposes__prefix_last in H3; auto.
    destruct H3 as [lc1 [als1 [Mem1 [tr1 [tr2 [env0_denotes_env1 [env1_denotes_env2 [EQ Huniqc1]]]]]]]]; subst.
    assert (J:=H2).
    apply wf_nbranchs__decomposes__app in J. 
    destruct J as [H41 H42].
    apply H in env0_denotes_env1; auto.
    destruct env0_denotes_env1 as [lc3 [als3 [Mem3 [tr3 [tr4 [env0_denotes_env3 [env3_denotes_env1 [EQ Huniqc3]]]]]]]]; subst.
    exists lc3. exists als3. exists Mem3. exists tr3. exists (trace_app tr4 tr2).
    rewrite trace_app_commute.
    split; auto.
    split; auto.
      rewrite app_ass in H2.
      apply wf_nbranchs__decomposes__app in H2. 
      destruct H2 as [H51 H52].
      apply se_cmds_denotes__composes__prefix_last with (lc1:=lc1)(als1:=als1)(Mem1:=Mem1); eauto.
Qed.

Lemma se_cmds_denotes__decomposes__head_tail : forall nb TD lc0 gl als0 Mem0 nbs lc2 als2 Mem2 tr,
  uniq lc0 ->
  uniq lc2 ->
  wf_nbranchs (nb::nbs) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds (se_cmd sstate_init nb) nbs) lc2 als2 Mem2 tr ->
  exists lc1, exists als1, exists Mem1, exists tr1, exists tr2,
    sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd sstate_init nb) lc1 als1 Mem1 tr1 /\
    sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmds sstate_init nbs) lc2 als2 Mem2 tr2 /\
    tr = trace_app tr1 tr2 /\ uniq lc1.
Proof.
  intros nb TD lc0 gl als0 Mem0 cs lc2 als2 Mem2 tr Huniqc0 Huniqc2 Wf Hdenotes.
  rewrite <- se_cmds_cons in Hdenotes.
  apply se_cmds_denotes__decomposes__app in Hdenotes; auto.
Qed.    
  
Lemma se_cmds__denote__exists_op_cmds : forall nbs TD lc1 als1 gl Mem1 lc2 als2 Mem2 tr,
  uniq lc1 ->
  uniq lc2 ->
  wf_nbranchs nbs ->
  sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmds sstate_init nbs) lc2 als2 Mem2 tr ->
  exists lc2', exists als2, exists Mem2', exists tr', 
    dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs) lc2' als2 Mem2' tr' /\
    eqAL _ lc2' lc2.
Proof.
  induction nbs; 
    intros TD lc1 als1 gl Mem1 lc2 als2 Mem2 tr Uniqc1 Uniqc2 Wf Hdenotes.

    simpl in *. 
    exists lc1. exists als1. exists Mem2. exists trace_nil. 
    assert (J:=@init_denotes_id TD lc1 gl als1 Mem1).
    apply sstate_denotes_state_det with (lc2:=lc2)(als2:=als2)(Mem2:=Mem2)(tr2:=tr) in J; simpl; auto.
    destruct J as [EQ1 [EQ2 [EQ3 EQ4]]]; subst; auto.

    simpl in Hdenotes.
    apply se_cmds_denotes__decomposes__head_tail in Hdenotes; auto.
    destruct Hdenotes as [lc3 [als3 [Mem3 [tr3 [tr3' [J1 [J2 [EQ Huniqc3]]]]]]]]; subst.
    destruct a as [c nc].
    apply se_cmd__denotes__op_cmd with
      (als:=als1)(c:=c) in J1; simpl; auto.
    destruct J1 as [slc [HdbCmd HeqEnv]].
    apply wf_nbranchs__inv in Wf.
    apply IHnbs in J2; simpl; auto.
    destruct J2 as [lc4 [als4 [Mem4 [tr4 [HdbCmds HeqEnv']]]]].
    apply dbCmds_eqEnv with (lc1':=slc) in HdbCmds; auto using eqAL_sym.
    destruct HdbCmds as [lc4' [HdbCmds' HeqEnv'']].
    exists lc4'. exists als4. exists Mem4. exists (trace_app tr3 tr4).
    split; eauto using eqAL_trans, eqAL_sym.      
Qed.

Lemma se_cmds__denote__op_cmds : forall TD nbs lc1 gl als1 Mem1 lc2 als2 Mem2 tr,
  uniq lc1 ->
  uniq lc2 ->
  wf_nbranchs nbs ->
  sstate_denotes_state TD lc1 gl als1 Mem1 (se_cmds sstate_init nbs) lc2 als2 Mem2 tr ->
  exists slc,
    dbCmds TD gl lc1 als1 Mem1 (nbranchs2cmds nbs) slc als2 Mem2 tr /\
    eqAL _ slc lc2.
Proof.
  intros TD nbs lc1 gl als1 Mem1 lc2 als2 Mem2 tr Huniqc1 Huniqc2 Wf Hdenotes.
  assert (J:=Hdenotes).
  apply se_cmds__denote__exists_op_cmds with
     (lc1:=lc1)(als1:=als1)(Mem1:=Mem1) in J; simpl; auto.
  destruct J as [lc2' [als2' [Mem2' [tr' [HdbCmds HeqEnv]]]]].
  assert (Hdenotes':=HdbCmds).
  apply op_cmds__satisfy__se_cmds in Hdenotes'; auto.
  apply sstate_denotes_state_det with (lc2:=lc2)(als2:=als2)(Mem2:=Mem2)(tr2:=tr) in Hdenotes'; auto using se_cmds_init_uniq.
  destruct Hdenotes' as [EQ1 [EQ2 [EQ3 EQ4]]]; subst.
  exists lc2'. split; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
