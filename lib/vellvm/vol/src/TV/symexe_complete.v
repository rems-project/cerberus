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
Require Import symexe_def.
Require Import symexe_lib.
Require Import alist.
Require Import ZArith.

Export SimpleSE.
Export LLVMgv.

(* Symbolic execuction is complete:
   Any concrete execution of a subblock satisfies its symbolic execution. *)

Lemma genericvalue__implies__value2Sterm_denotes : forall TD lc0 Mem0 smap1 lc gl
    v gv,
  uniq smap1 ->
  smap_denotes_gvmap TD lc0 gl Mem0 smap1 lc ->
  getOperandValue TD v lc gl = Some gv ->
  sterm_denotes_genericvalue TD lc0 gl Mem0 (value2Sterm smap1 v) gv.
Proof.
  intros D lc0 Mem0 smap1 lc gl v gv Huniq Hdenotes J.
  unfold getOperandValue in J.
  unfold smap_denotes_gvmap in Hdenotes.
  destruct Hdenotes as [J1 J2].
  destruct v.
    apply J2 in J; auto.
    rewrite const2Sterm; auto.
Qed.

Lemma genericvalues__imply__value2Sterm_denote : forall l0 TD lc0 Mem0 smap1 lc 
    gl gvs0,
  uniq smap1 ->
  smap_denotes_gvmap TD lc0 gl Mem0 smap1 lc ->
  values2GVs TD l0 lc gl = Some gvs0 ->
  sterms_denote_genericvalues TD lc0 gl Mem0 
    (make_list_sterm 
      (map_list_sz_value (fun sz' v' => (sz', value2Sterm smap1 v')) l0)) 
    gvs0.
Proof.
  induction l0; intros; simpl in *.
    inversion H1; subst; auto.

    remember (getOperandValue TD v lc gl) as ogv.
    destruct ogv; try solve [inversion H1].
    remember (values2GVs TD l0 lc gl) as ogvs.
    destruct ogvs; try solve [inversion H1].
    inversion H1; subst.
    apply sterms_cons_denote; eauto using genericvalue__implies__value2Sterm_denotes.
Qed.

Lemma se_cmd__denotes__op_cmd__case0 : forall X sm id0 st0 id1 D,
  uniq sm ->
  id1 `in` dom (updateAddAL X sm id0 st0) `union` D ->
  (id0 <> id1 /\ id1 `in` dom sm `union` D) \/ (id0 = id1).
Proof.
  intros.
  destruct (id0==id1); subst; auto.
    left.
    apply in_dom_app_inv in H0.
    destruct H0; auto.
      apply updateAddAL_in_inversion in H0; auto.
      destruct H0 as [[J1 J2] | EQ]; subst; auto.
        contradict n; auto.
Qed.
     

Lemma se_cmd__denotes__op_cmd__case1 : forall lc gl i0 gv3 id' smap1 TD lc0 Mem0 st0,
  i0 <> id' ->
  id' `in` dom smap1 `union` dom lc0 ->
  smap_denotes_gvmap TD lc0 gl Mem0 smap1 lc ->
  exists gv',
    sterm_denotes_genericvalue TD lc0 gl Mem0 (lookupSmap (updateAddAL _ smap1 i0 st0) id') gv' /\
    lookupAL _ (updateAddAL _ lc i0 gv3) id' = Some gv'.
Proof.
  intros lc gl i0 gv3 id' smap1 TD lc0 Mem0 st0 nEQ id'_indom Hsterm_denotes.
  rewrite <- lookupAL_updateAddAL_neq ; auto.
  rewrite <- lookupSmap_updateAddAL_neq ; auto.
  unfold smap_denotes_gvmap in Hsterm_denotes.
  destruct Hsterm_denotes as [J1 J2].  
  apply J1; auto.
Qed.

Lemma se_cmd__denotes__op_cmd__case2 : forall lc gl i0 gv3 id' smap1 TD lc0 Mem0 gv' st0,
  smap_denotes_gvmap TD lc0 gl Mem0 smap1 lc ->
  lookupAL _ (updateAddAL _ lc i0 gv3) id' = Some gv' ->
  id' <> i0 ->
  sterm_denotes_genericvalue TD lc0 gl Mem0 (lookupSmap (updateAddAL _ smap1 i0 st0) id') gv'.
Proof.
  intros lc gl i0 gv3 id' smap1 TD lc0 Mem0 gv' st0 Hsterm_denotes HlookupAL n.
  rewrite <- lookupAL_updateAddAL_neq in HlookupAL; auto.
  rewrite <- lookupSmap_updateAddAL_neq; auto.
  destruct Hsterm_denotes as [J1 J2].
  apply J2 in HlookupAL; auto.
Qed.

Lemma op_cmd__satisfies__se_cmd : forall TD c nc lc als gl lc0 als0 Mem0 lc' als' Mem1 Mem2 sstate1 tr tr1,
  dbCmd TD gl lc als Mem1 c lc' als' Mem2 tr -> 
  uniq sstate1.(STerms) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 sstate1 lc als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmd sstate1 (mkNB c nc)) lc' als' Mem2 (trace_app tr1 tr).
Proof.
  intros TD c nc lc als gl lc0 als0 Mem0 lc' als' Mem1 Mem2 sstate1 tr tr1
         HdsInsn Huniq Hdenotes.
  (cmd_cases (destruct c) Case);
              inversion HdsInsn; subst;
              destruct Hdenotes as [Hsterm_denotes [Hsmem_denotes [Hsframe_denotes Hseffects_denote]]];
              rewrite trace_app_nil__eq__trace.
  Case "insn_bop".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          apply BOP_inversion in H13.
          destruct H13 as [gv1 [gv2 [J1 [J2 J3]]]].
          exists gv3. split; auto.
          apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto using 
            genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst. 
          rewrite lookupSmap_updateAddAL_eq.
          apply BOP_inversion in H13.
          destruct H13 as [gv1 [gv2 [J1 [J2 J3]]]].
          apply sterm_bop_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_fbop".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          apply FBOP_inversion in H13.
          destruct H13 as [gv1 [gv2 [J1 [J2 J3]]]].
          exists gv3. split; auto.
          apply sterm_fbop_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst. 
          rewrite lookupSmap_updateAddAL_eq.
          apply FBOP_inversion in H13.
          destruct H13 as [gv1 [gv2 [J1 [J2 J3]]]].
          apply sterm_fbop_denotes with (gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_extractvalue".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          exists gv'. split; auto.
          apply sterm_extractvalue_denotes with (gv1:=gv); eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv'0 HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          apply sterm_extractvalue_denotes with (gv1:=gv); eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_insertvalue".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          exists gv''. split; auto.
           eapply sterm_insertvalue_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv'0 HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          eapply sterm_insertvalue_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_malloc".
    split; simpl; eauto using genericvalue__implies__value2Sterm_denotes.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          exists (blk2GV TD mb).
          split; auto.
            eapply sterm_malloc_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv'0 HlookupAL.
        simpl.
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          eapply sterm_malloc_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_free".
    split; simpl.
      destruct Hsterm_denotes as [J1 J2].
      split; auto.
    split; auto.     
      apply smem_free_denotes with (Mem1:=Mem1)(gv0:=mptr0); auto.
        eapply genericvalue__implies__value2Sterm_denotes; eauto.

  Case "insn_alloca".
    split; simpl; eauto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          exists (blk2GV TD mb).
          split; auto.
          eapply sterm_alloca_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

        intros id' gv'0 HlookupAL.
        simpl.
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          eapply sterm_alloca_denotes; eauto using genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.
    split; eauto using genericvalue__implies__value2Sterm_denotes.

  Case "insn_load".
    split; simpl; eauto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          exists gv.
          split; auto.
          apply sterm_load_denotes with (Mem1:=Mem2)(gv0:=mp); eauto.
            eapply genericvalue__implies__value2Sterm_denotes; eauto.
     
        intros id' gv'0 HlookupAL.
        simpl.
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          apply sterm_load_denotes with (Mem1:=Mem2)(gv0:=mp); eauto.
            eapply genericvalue__implies__value2Sterm_denotes; eauto.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_store".
    split; simpl.
      destruct Hsterm_denotes as [J1 J2].
      split; auto.
    split; auto.
      eapply smem_store_denotes; 
        eauto using genericvalue__implies__value2Sterm_denotes.

  Case "insn_gep". 
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          exists mp'.
          split; auto.
            eapply sterm_gep_denotes; eauto using 
              genericvalue__implies__value2Sterm_denotes, 
              genericvalues__imply__value2Sterm_denote.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          eapply sterm_gep_denotes; eauto using 
            genericvalue__implies__value2Sterm_denotes, 
            genericvalues__imply__value2Sterm_denote.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_trunc".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          apply TRUNC_inversion in H13.
          destruct H13 as [gv1 [J1 J2]].
          exists gv2. split; auto.
            apply sterm_trunc_denotes with (gv1:=gv1); eauto using        
              genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          apply TRUNC_inversion in H13.
          destruct H13 as [gv1 [J1 J2]].
          apply sterm_trunc_denotes with (gv1:=gv1); eauto using 
            genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_ext".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          apply EXT_inversion in H13.
          destruct H13 as [gv1 [J1 J2]].
          exists gv2. split; auto.
            apply sterm_ext_denotes with (gv1:=gv1); eauto using 
              genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          apply EXT_inversion in H13.
          destruct H13 as [gv1 [J1 J2]].
          apply sterm_ext_denotes with (gv1:=gv1); eauto using 
            genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_cast".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          apply CAST_inversion in H13.
          destruct H13 as [gv1 [J1 J2]].
          exists gv2. split; auto.
            apply sterm_cast_denotes with (gv1:=gv1); eauto using 
              genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          apply CAST_inversion in H13.
          destruct H13 as [gv1 [J1 J2]].
          apply sterm_cast_denotes with (gv1:=gv1); eauto using 
            genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_icmp".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          apply ICMP_inversion in H13.
          destruct H13 as [gv1 [gv2 [J1 [J2 J3]]]].
          exists gv3. split; auto.
            apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto using 
              genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          apply ICMP_inversion in H13.
          destruct H13 as [gv1 [gv2 [J1 [J2 J3]]]].
          apply sterm_icmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto using 
            genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_fcmp".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          eapply se_cmd__denotes__op_cmd__case1; eauto.

          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupSmap_updateAddAL_eq.
          apply FCMP_inversion in H13.
          destruct H13 as [gv1 [gv2 [J1 [J2 J3]]]].
          exists gv3. split; auto.
            apply sterm_fcmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto using 
              genericvalue__implies__value2Sterm_denotes.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupAL_updateAddAL_eq in HlookupAL.
          inversion HlookupAL; subst.
          rewrite lookupSmap_updateAddAL_eq.
          apply FCMP_inversion in H13.
          destruct H13 as [gv1 [gv2 [J1 [J2 J3]]]].
          apply sterm_fcmp_denotes with (gv1:=gv1)(gv2:=gv2); eauto using 
            genericvalue__implies__value2Sterm_denotes.

          eapply se_cmd__denotes__op_cmd__case2; eauto.

  Case "insn_select".
    split; auto.
      split.
        intros id' id'_indom.
        simpl in id'_indom. simpl. 
        apply se_cmd__denotes__op_cmd__case0 in id'_indom; auto.
        destruct id'_indom as [[nEQ id'_indom] | EQ1]; subst.
          destruct (isGVZero TD cond0); eapply se_cmd__denotes__op_cmd__case1; eauto.

          remember (isGVZero TD cond0) as R.
          destruct R; subst; rewrite lookupAL_updateAddAL_eq;
                          rewrite lookupSmap_updateAddAL_eq; auto.
            exists gv2.
            split; auto.
              apply sterm_select_denotes with (gv0:=cond0)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.
                rewrite <- HeqR. auto.

            exists gv1.
            split; auto.
              apply sterm_select_denotes with (gv0:=cond0)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.
                rewrite <- HeqR. auto.

        intros id' gv' HlookupAL.
        simpl. 
        destruct (id'==i0); subst.
          rewrite lookupSmap_updateAddAL_eq.
          apply sterm_select_denotes with (gv0:=cond0)(gv1:=gv1)(gv2:=gv2); eauto using genericvalue__implies__value2Sterm_denotes.
          destruct (isGVZero TD cond0);
            rewrite lookupAL_updateAddAL_eq in HlookupAL;
            inversion HlookupAL; subst; auto.

          destruct (isGVZero TD cond0); eapply se_cmd__denotes__op_cmd__case2; eauto.
Qed.

Lemma aux__op_cmds__satisfy__se_cmds : forall nbs TD lc0 als als0 Mem0 lc als' gl Mem1 sstate1 lc' Mem2 tr tr1,
  dbCmds TD gl lc als Mem1 (nbranchs2cmds nbs) lc' als' Mem2 tr ->
  uniq sstate1.(STerms) ->
  sstate_denotes_state TD lc0 gl als0 Mem0 sstate1 lc als Mem1 tr1 ->
  sstate_denotes_state TD lc0 gl als0 Mem0 (se_cmds sstate1 nbs) lc' als' Mem2 (trace_app tr1 tr).
Proof.
  induction nbs; 
    intros TD lc0 als als0 Mem0 lc als' gl Mem1 sstate1 lc' Mem2 tr tr1 
    HdbCmds Huniq Hdenotes.

    simpl in HdbCmds.
    inversion HdbCmds; subst; try solve [rewrite trace_app_nil__eq__trace; auto].

    destruct a as [c nc].
    simpl in HdbCmds.
    inversion HdbCmds; subst.
    apply op_cmd__satisfies__se_cmd with (lc0:=lc0)(sstate1:=sstate1)(als0:=als0)(Mem0:=Mem0)(tr1:=tr1)(nc:=nc) in H6; auto.
    rewrite trace_app_commute.
    apply IHnbs with (lc0:=lc0)(sstate1:=se_cmd sstate1 (mkNB c nc))(als0:=als0)(Mem0:=Mem0)(tr1:=trace_app tr1 t1) in H11; auto.
      apply se_cmd_uniq_aux; auto.
Qed.

Lemma op_cmds__satisfy__se_cmds : forall TD nbs lc als gl Mem lc' als' Mem' tr,
  uniq lc ->
  dbCmds TD gl lc als Mem (nbranchs2cmds nbs) lc' als' Mem' tr ->
  sstate_denotes_state TD lc gl als Mem (se_cmds sstate_init nbs) lc' als' Mem' tr.
Proof.
  intros TD nbs lc als gl Mem0 lc' als' Mem' tr Uniqc HdbCmds.
  apply aux__op_cmds__satisfy__se_cmds with (lc0:=lc)(als0:=als)(Mem0:=Mem0)(sstate1:=sstate_init) (tr1:=trace_nil)(nbs:=nbs) in HdbCmds; simpl; auto.
    apply init_denotes_id; auto.
Qed.           

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)

