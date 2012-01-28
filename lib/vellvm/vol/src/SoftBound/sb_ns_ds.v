Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import syntax.
Require Import infrastructure.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import opsem.
Require Import opsem_inst.
Require Import sb_def.

Module SBspecInstantiation.

Export OpsemInstantiation.
Export SBspec.

Section Sec.

Context {DGVs NDGVs : GenericValues}.

Hypothesis element_of__gv2gvs : forall gv t, 
  element_of (DGVs.(gv2gvs) gv t) (NDGVs.(gv2gvs) gv t).

Hypothesis element_of__cgv2gvs : forall gv t, 
  element_of (DGVs.(cgv2gvs) gv t) (NDGVs.(cgv2gvs) gv t).

Hypothesis element_of__lift_op1 : forall f xs1 xs2 t ys1,
  element_of xs1 xs2 ->
  DGVs.(lift_op1) f xs1 t = Some ys1 ->
  exists ys2, NDGVs.(lift_op1) f xs2 t = Some ys2 /\ element_of ys1 ys2.

Hypothesis element_of__lift_op2 : forall f xs1 ys1 xs2 ys2 t zxs1,
  element_of xs1 xs2 ->
  element_of ys1 ys2 ->
  DGVs.(lift_op2) f xs1 ys1 t = Some zxs1 ->
  exists zxs2, NDGVs.(lift_op2) f xs2 ys2 t = Some zxs2 /\ 
    element_of zxs1 zxs2.

Definition instantiate_EC (ec1 : @ExecutionContext DGVs) 
  (ec2 : @ExecutionContext NDGVs) : Prop :=
match ec1, ec2 with
| mkEC f1 b1 cs1 tmn1 lc1 rm1 als1, 
  mkEC f2 b2 cs2 tmn2 lc2 rm2 als2 =>
    f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\
    instantiate_locals lc1 lc2 /\ rm1 = rm2 /\ als1 = als2
end.

Fixpoint instantiate_ECs (ecs1 : @ECStack DGVs) (ecs2 : @ECStack NDGVs) 
  : Prop :=
match ecs1, ecs2 with
| nil, nil => True
| ec1::ecs1', ec2::ecs2' => instantiate_EC ec1 ec2 /\ instantiate_ECs ecs1' ecs2'
| _, _ => False
end.

Definition instantiate_State (st1 : @State DGVs) (st2 : @State NDGVs) 
  : Prop :=
match st1, st2 with
| mkState ecs1 M1 MM1, mkState ecs2 M2 MM2 =>
    instantiate_ECs ecs1 ecs2 /\ M1 = M2 /\ MM1 = MM2
end.

Ltac tinv H := try solve [inversion H].

Lemma instantiate_locals__returnResult : forall TD rt Result lc1 lc2 gl gv1 rm 
    md,
  @instantiate_locals DGVs NDGVs lc1 lc2 -> 
  returnResult TD rt Result lc1 rm gl = Some (gv1, md) ->
  exists gv2, 
    returnResult TD rt Result lc2 rm gl = Some (gv2, md) /\
    element_of gv1 gv2.
Proof.
  intros.  
  unfold returnResult in H0.
  remember (getOperandValue TD Result lc1 gl) as R.
  destruct R; tinv H0.
  symmetry in HeqR.
  eapply instantiate_locals__getOperandValue in HeqR; eauto.
  destruct HeqR as [gvs2 [J1 J2]].
  unfold returnResult.
  rewrite J1. 
  destruct (isPointerTypB rt); inv H0; eauto.
  destruct (get_reg_metadata TD gl rm Result); inv H2.
  exists gvs2. split; auto using @instantiate_locals__updateAddAL.
Qed.

Lemma instantiate_locals__returnUpdateLocals : forall TD lc1 lc2 lc1' lc2' Result
    gl lc1'' c rm rm' rt rm'',
  instantiate_locals lc1 lc2 -> 
  instantiate_locals lc1' lc2' -> 
  @returnUpdateLocals DGVs TD c rt Result lc1 lc1' rm rm' gl = 
    ret (lc1'',rm'') ->
  exists lc2'', 
    @returnUpdateLocals NDGVs TD c rt Result lc2 lc2' rm rm' gl = 
      ret (lc2'',rm'') /\
    instantiate_locals lc1'' lc2''. 
Proof.
  intros.
  unfold returnUpdateLocals in H1.
  remember (returnResult TD rt Result lc1 rm gl) as R.
  destruct R as [[gr md]|]; tinv H1.
  symmetry in HeqR.
  eapply instantiate_locals__returnResult in HeqR; eauto.
  destruct HeqR as [gvs2 [J1 J2]].
  unfold returnUpdateLocals.
  rewrite J1. 
  destruct c; tinv H1.
  destruct n; inv H1; eauto.
  destruct t; tinv H3.
  remember (lift_op1 _ (fit_gv TD t) gr t) as R.
  destruct R as [gr'|]; inv H3.
  symmetry in HeqR.
  eapply element_of__lift_op1 in HeqR; eauto.
  destruct HeqR as [ys2 [J3 J4]]. rewrite J3.
  exists (updateAddAL _ lc2' i0 ys2).   
  destruct (isPointerTypB t); inv H2; 
    eauto using @instantiate_locals__updateAddAL.
Qed.

Fixpoint instantiate_localms (lcm1 : list (id*DGVs.(GVsT)*option metadata)) 
  (lcm2 : list (id*NDGVs.(GVsT)*option metadata)) : Prop :=
match lcm1, lcm2 with
| nil, nil => True
| (id1,gv1,omd1)::lcm1', (id2,gvs2,omd2)::lcm2' => 
    id1=id2 /\ element_of gv1 gvs2 /\ instantiate_localms lcm1' lcm2' /\ 
    omd1 = omd2
| _, _ => False
end.

Lemma instantiate_locals__getIncomingValuesForBlockFromPHINodes : forall TD b
    gl lc1 lc2 (Hlc : instantiate_locals lc1 lc2) ps re1 rm,  
  getIncomingValuesForBlockFromPHINodes TD ps b gl lc1 rm = Some re1 ->
  exists re2,
    getIncomingValuesForBlockFromPHINodes TD ps b gl lc2 rm = Some re2 /\
    instantiate_localms re1 re2.
Proof.
  induction ps; simpl; intros.  
    inv H. exists nil. simpl. auto.

    destruct a.
    destruct (getValueViaBlockFromValuels l0 b); tinv H. 
    remember (getOperandValue TD v lc1 gl) as R.
    destruct R; tinv H.
    symmetry in HeqR.  
    eapply instantiate_locals__getOperandValue in HeqR; eauto.
    destruct HeqR as [gvs2 [J1 J2]].
    remember (getIncomingValuesForBlockFromPHINodes TD ps b gl lc1 rm) as R1.
    destruct R1; inv H. 
    rewrite J1.
    symmetry in HeqR1.
    destruct (@IHps l1 rm) as [re2 [J3 J4]]; auto.
    rewrite J3. 
    destruct (isPointerTypB t); inv H1.
      destruct (get_reg_metadata TD gl rm v); inv H0.
      exists ((i0, gvs2, ret m) :: re2). simpl. auto.

      exists ((i0, gvs2, merror) :: re2). simpl. auto.
Qed.

Lemma instantiate_locals__updateValuesForNewBlock : forall lc1 lc2 re1 re2 rm 
    lc1' rm',
  instantiate_locals lc1 lc2 ->
  instantiate_localms re1 re2 ->
  updateValuesForNewBlock re1 lc1 rm = (lc1', rm') ->
  exists lc2', 
    updateValuesForNewBlock re2 lc2 rm = (lc2', rm') /\
    instantiate_locals lc1' lc2'.
Proof.
  induction re1; destruct re2; simpl; intros; auto.
    inv H1. eauto.
    inv H0.
    destruct a. destruct p. inv H0.

    destruct a. destruct p0. destruct p. destruct p.
    destruct H0 as [eq [J1 [J2 eq']]]; subst.
    remember (updateValuesForNewBlock re1 lc1 rm) as R.
    destruct R as [lc' rm''].
    symmetry in HeqR. eapply IHre1 in HeqR; eauto.
    destruct HeqR as [lc2' [J3 J4]].
    rewrite J3.
    destruct o0; inv H1.
      exists (updateAddAL _ lc2' i1 g0). 
      split; auto using @instantiate_locals__updateAddAL.

      exists (updateAddAL _ lc2' i1 g0). 
      split; auto using @instantiate_locals__updateAddAL.
Qed.

Lemma instantiate_locals__switchToNewBasicBlock : forall TD lc1 lc2 gl lc1' b b'
    rm rm',
  instantiate_locals lc1 lc2 -> 
  @switchToNewBasicBlock DGVs TD b' b gl lc1 rm = Some (lc1',rm') ->
  exists lc2', @switchToNewBasicBlock NDGVs TD b' b gl lc2 rm = Some (lc2',rm') 
    /\ instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold switchToNewBasicBlock in H0.
  unfold switchToNewBasicBlock.
  remember (getIncomingValuesForBlockFromPHINodes TD 
    (getPHINodesFromBlock b') b gl lc1 rm) as R.
  destruct R; inv H0.
  symmetry in HeqR.
  eapply instantiate_locals__getIncomingValuesForBlockFromPHINodes in HeqR;eauto.
  destruct HeqR as [re2 [J1 J2]].
  rewrite J1.
  eapply instantiate_locals__updateValuesForNewBlock in H2; eauto.
  destruct H2 as [lc2' [J3 J4]].
  rewrite J3. eauto.
Qed.

Fixpoint instantiate_gvms (l1 : list (DGVs.(GVsT) * option metadata)) 
  (l2 : list (NDGVs.(GVsT) * option metadata)) :=
match l1, l2 with
| nil, nil => True
| (gv1,omd1)::l1', (gvs2,omd2)::l2' => 
    element_of gv1 gvs2 /\ omd1 = omd2 /\ instantiate_gvms l1' l2'
| _, _ => False
end.

Lemma instantiate_locals__params2GVs : forall TD lc1 lc2 gl rm
  (Hlc:instantiate_locals lc1 lc2) lp gvms1,
  params2GVs TD lp lc1 gl rm = Some gvms1 ->
  exists gvsms2, params2GVs TD lp lc2 gl rm = Some gvsms2 /\
    instantiate_gvms gvms1 gvsms2.
Proof.
  induction lp; simpl; intros.
    inv H. exists nil. simpl. auto.

    destruct a as [[t attr] v]. 
    remember (getOperandValue TD v lc1 gl) as R1.
    destruct R1; tinv H.
    remember (params2GVs TD lp lc1 gl rm) as R2.
    destruct R2; tinv H.
    inv H.
    symmetry in HeqR1.
    eapply instantiate_locals__getOperandValue in HeqR1; eauto.
    destruct HeqR1 as [gvs2 [H3 H4]].
    destruct (@IHlp l0) as [gvsss2 [J1 J2]]; auto.
    rewrite H3. rewrite J1. 
    destruct (isPointerTypB t); inv H1.
      exists ((gvs2, get_reg_metadata TD gl rm v) :: gvsss2). simpl. split; auto.
      exists ((gvs2, merror) :: gvsss2). simpl. split; auto.
Qed.

Lemma instantiate_locals__initializeFrameValues : forall TD lc1 lc2 rm
  (H2: instantiate_locals lc1 lc2) la gvs1 gvs2 lc1' rm'
  (H1 : instantiate_gvms gvs1 gvs2),
  _initializeFrameValues TD la gvs1 lc1 rm = Some (lc1', rm') ->
  exists lc2', 
    _initializeFrameValues TD la gvs2 lc2 rm = Some (lc2', rm') /\
    instantiate_locals lc1' lc2'.
Proof.
  induction la; simpl; intros; auto.
    inv H. eauto.

    destruct a. destruct p.
    destruct gvs1; simpl.
      remember (_initializeFrameValues TD la nil lc1 rm) as R.
      destruct R as [[lc1'' rm'']|]; tinv H.
      destruct gvs2; inv H1.
      symmetry in HeqR.
      destruct (gundef TD t); tinv H.
      apply IHla with (gvs2:=nil) in HeqR; simpl; eauto.
      destruct HeqR as [lc2' [J1 J2]].
      rewrite J1.
      destruct (isPointerTypB t); inv H.
        unfold prop_reg_metadata.
        eauto using @instantiate_locals__updateAddAL.

        eauto using @instantiate_locals__updateAddAL.

      destruct p.
      simpl in H1.
      destruct gvs2; tinv H1. 
      destruct p. destruct H1 as [J1 [J2 J3]]; subst.
      remember (_initializeFrameValues TD la gvs1 lc1 rm) as R.
      destruct R as [[lc1'' rm'']|]; tinv H.
      remember (lift_op1 DGVs (fit_gv TD t) g t) as R2.
      destruct R2; inv H.
      symmetry in HeqR.
      eapply IHla in HeqR; simpl; eauto.
      destruct HeqR as [lc2' [J1' J2']].
      rewrite J1'.
      unfold prop_reg_metadata.
      symmetry in HeqR2.
      eapply element_of__lift_op1 in HeqR2; eauto.
      destruct HeqR2 as [ys2 [J3' J4']].
      rewrite J3'.
      destruct (isPointerTypB t); inv H1;
        eauto using @instantiate_locals__updateAddAL.
      exists (updateAddAL _ lc2' i0 ys2).
      destruct o0; inv H0; eauto using @instantiate_locals__updateAddAL.
Qed.           

Lemma instantiate_locals__initLocals : forall TD gvs1 gvss2 lc1 rm
  (H : instantiate_gvms gvs1 gvss2) la,
  initLocals TD la gvs1 = Some (lc1, rm) ->
  exists lc2, 
    initLocals TD la gvss2 = Some (lc2, rm) /\ instantiate_locals lc1 lc2.
Proof.
  unfold initLocals.
  intros.
  eapply instantiate_locals__initializeFrameValues; eauto.
    simpl. auto.
Qed.

Lemma instantiate_locals__exCallUpdateLocals : forall TD lc1 lc2 lc1' rid oResult
    nr ft rm rm',
  instantiate_locals lc1 lc2 -> 
  @exCallUpdateLocals DGVs TD ft nr rid oResult lc1 rm = ret (lc1',rm') ->
  exists lc2', 
    @exCallUpdateLocals NDGVs TD ft nr rid oResult lc2 rm = ret (lc2',rm') /\
    instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold exCallUpdateLocals in H0.
  unfold exCallUpdateLocals.
  destruct nr; inv H0; eauto.
  destruct oResult; inv H2; eauto.
  destruct ft; inv H1; eauto using @instantiate_locals__updateAddAL.
  remember (fit_gv TD ft g) as R.
  destruct R; tinv H2.
  exists (updateAddAL _ lc2 rid (gv2gvs _ g0 ft)).
  destruct (isPointerTypB ft); inv H2; eauto using 
    @instantiate_locals__updateAddAL.
Qed.

Lemma returnUpdateLocals_sim : forall TD' c' rt Result lc1' lc2' rm rm' gl' 
    lc'' rm'', 
  @returnUpdateLocals NDGVs TD' c' rt Result lc1' lc2' rm rm' gl' = 
    ret (lc'', rm'') ->
  Opsem.returnUpdateLocals TD' c' Result lc1' lc2' gl' = ret lc''.
Proof.
  intros.  
  unfold returnUpdateLocals, returnResult in H.
  unfold Opsem.returnUpdateLocals.
  destruct (getOperandValue TD' Result lc1' gl'); tinv H.
  destruct (isPointerTypB rt); tinv H.
    destruct (get_reg_metadata TD' gl' rm Result) as [[md ?]|]; tinv H.
    destruct c'; tinv H.
    destruct n; try solve [inversion H; auto].
    unfold prop_reg_metadata in H.  
    destruct t; try solve [inversion H; auto].
    destruct (lift_op1 _ (fit_gv TD' t) g t); tinv H.
    destruct t; try solve [inversion H; auto].

    destruct c'; try solve [inversion H; auto].
    destruct n; try solve [inversion H; auto].
    unfold prop_reg_metadata in H.  
    destruct t; try solve [inversion H; auto].
    destruct (lift_op1 _ (fit_gv TD' t) g t); tinv H.
    destruct t; try solve [inversion H; auto].
Qed.

Lemma exCallUpdateLocals_sim : forall TD ft noret rid oResult lc rm lc'' rm'', 
  @exCallUpdateLocals NDGVs TD ft noret rid oResult lc rm = ret (lc'', rm'') ->
  Opsem.exCallUpdateLocals TD ft noret rid oResult lc = ret lc''.
Proof.
  intros.  
  unfold exCallUpdateLocals in H.
  unfold Opsem.exCallUpdateLocals.
  destruct noret0; try solve [inversion H; auto].
  destruct oResult; try solve [inversion H; auto].
  destruct ft; try solve [inversion H; auto].
  destruct (fit_gv TD ft g); tinv H; auto.
  destruct (isPointerTypB ft); inversion H; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall ps TD' b1' gl' lc1'
    rm l1,
  @getIncomingValuesForBlockFromPHINodes NDGVs TD' ps b1' gl' lc1' rm =
    Some l1 ->
  exists l2, exists l3, 
    Opsem.getIncomingValuesForBlockFromPHINodes TD' ps b1' gl' lc1' = Some l2 
    /\ split l1 = (l2, l3).
Proof.
  induction ps; simpl; intros.
    inversion H; subst.
    exists nil. exists nil. eauto.

    destruct a. 
    destruct (getValueViaBlockFromValuels l0 b1'); try solve [inversion H].
    remember (getOperandValue TD' v lc1' gl') as R0.
    destruct R0; try solve [inversion H].
    remember (getIncomingValuesForBlockFromPHINodes TD' ps b1' gl'
          lc1' rm) as R.
    destruct R; try solve [inversion H].
    symmetry in HeqR.
    apply IHps in HeqR.
    destruct HeqR as [l3 [l4 [J1 J2]]].
    rewrite J1.
    destruct (isPointerTypB t); inv H; eauto.
      destruct v.
        simpl in *.
        destruct (lookupAL _ rm i1); inversion H1; subst.
          simpl. rewrite J2. eauto.

        destruct (get_reg_metadata TD' gl' rm (value_const c)) as [md|]; 
          inv H1; eauto.
        simpl.
        rewrite J2. eauto.

      simpl. rewrite J2.
      destruct v; simpl in *; eauto.
Qed.

Lemma updateValuesForNewBlock_sim : forall l0 lc1' rm lc' rm' l2 l3,
  @updateValuesForNewBlock NDGVs l0 lc1' rm = (lc', rm') ->
  split l0 = (l2, l3) ->
  Opsem.updateValuesForNewBlock l2 lc1' = lc'.
Proof.
  induction l0; simpl; intros.   
    inversion H0; subst.
    inversion H; subst.
    simpl; auto.

    destruct a. destruct p. 
    remember (updateValuesForNewBlock l0 lc1' rm) as R.
    destruct R.
    remember (split l0) as R1.
    destruct R1. inversion H0; subst.
    simpl. unfold prop_reg_metadata in H.
    destruct o.
      inversion H; subst.
      erewrite IHl0 with (lc1':=lc1'); eauto.

      inversion H; subst.
      erewrite IHl0 with (lc1':=lc1'); eauto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD' b' b1' gl' lc1' rm lc' rm',
  @switchToNewBasicBlock NDGVs TD' b' b1' gl' lc1' rm = ret (lc', rm') ->
  Opsem.switchToNewBasicBlock TD' b' b1' gl' lc1' = ret lc'.
Proof.
  intros.
  unfold switchToNewBasicBlock in H.
  unfold Opsem.switchToNewBasicBlock.
  remember (getIncomingValuesForBlockFromPHINodes TD'
    (getPHINodesFromBlock b') b1' gl' lc1' rm) as R.
  destruct R; try solve [inversion H].
  symmetry in HeqR.
  apply getIncomingValuesForBlockFromPHINodes_sim in HeqR.
  destruct HeqR as [l2 [l3 [J1 J2]]].
  rewrite J1.
  inversion H; subst.
  eapply updateValuesForNewBlock_sim in H1; eauto.
  rewrite H1. auto.
Qed.

Lemma params2GVs_sim : forall lp gl' TD' lc1' rm ogvs,
  @params2GVs NDGVs TD' lp lc1' gl' rm = ret ogvs ->
  exists gvs, exists l2, Opsem.params2GVs TD' lp lc1' gl' = ret gvs /\
    split ogvs = (gvs, l2).
Proof.
  induction lp; simpl; intros.
    inversion H; subst. 
    exists nil. exists nil. auto.

    destruct a as [[t attr] v]. 
    destruct (getOperandValue TD' v lc1' gl'); tinv H.
    remember (params2GVs TD' lp lc1' gl' rm) as R.
    destruct R; try solve [inversion H].
    symmetry in HeqR.
    apply IHlp in HeqR; auto.      
    destruct HeqR as [gvs [l2 [J1 J2]]].
    destruct (isPointerTypB t); inversion H; subst; 
      simpl; rewrite J2; rewrite J1; eauto.
Qed.

Lemma initializeFrameValues_sim : forall TD la rm ogvs lc lc' rm' gvs l2,
  @_initializeFrameValues NDGVs TD la ogvs lc rm = Some (lc', rm') ->
  split ogvs = (gvs, l2) ->
  Opsem._initializeFrameValues TD la gvs lc = Some lc'.
Proof.
  induction la; simpl; intros.
    inversion H; subst; auto.

    destruct a. destruct p.
    destruct ogvs.
      simpl in H0. inversion H0; subst.
      remember (_initializeFrameValues TD la nil lc rm) as R.
      destruct R as [[lc1 rm1]|]; tinv H.
      destruct (gundef TD t); tinv H.
      unfold prop_reg_metadata in H.
      symmetry in HeqR.
      eapply IHla in HeqR; eauto. 
      rewrite HeqR.
      destruct (isPointerTypB t); inversion H; subst; auto.

      destruct p.
      simpl in H0.
      remember (split ogvs) as R'.
      destruct R'.
      inversion H0; subst.
      remember (_initializeFrameValues TD la ogvs lc rm) as R.
      destruct R as [[lc1 rm1]|]; tinv H.
      symmetry in HeqR.
      eapply IHla in HeqR; eauto. rewrite HeqR.
      destruct (lift_op1 _ (fit_gv TD t) g t); tinv H.
      destruct (isPointerTypB t); try solve [inversion H; subst; auto].
        unfold prop_reg_metadata in H.
        destruct o; try solve [inversion H; subst; auto].
Qed.

Lemma initLocals_params2GVs_sim : forall lp gl' TD' lc1' rm ogvs la lc' rm',
  @params2GVs NDGVs TD' lp lc1' gl' rm = ret ogvs ->
  initLocals TD' la ogvs = ret (lc', rm') ->
  exists gvs, Opsem.params2GVs TD' lp lc1' gl' = ret gvs /\
    Opsem.initLocals TD' la gvs = ret lc'.
Proof.
  unfold initLocals, Opsem.initLocals.
  intros.
  apply params2GVs_sim in H.
  destruct H as [gvs [l2 [J1 J2]]].
  exists gvs.
  split; eauto using initializeFrameValues_sim.
Qed.

Ltac ctx_simpl_aux :=
  match goal with
  | [H1 : lookupExFdecViaPtr ?Ps ?fs ?gv = _,
     H2 : lookupExFdecViaPtr ?Ps ?fs ?gv = _ |- _ ] => 
    rewrite H1 in H2; inv H2
  | [H1 : Opsem.getOperandValue ?TD ?vp ?lc ?gl = _,
     H2 : Opsem.getOperandValue ?TD ?vp ?lc ?gl = _ |- _ ] =>
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
  end.

Ltac ctx_simpl := repeat ctx_simpl_aux. 

Ltac instantiate_dsInsn_tac :=
  split;  
    (eauto ||
    (eapply sInsn_intro; try solve [
       simpl; eauto using returnUpdateLocals_sim, 
                          switchToNewBasicBlock_sim,
                          exCallUpdateLocals_sim] ) ||
    (repeat (split; auto using @instantiate_locals__updateAddAL,
                               element_of__gv2gvs)))
  .

Ltac simpl_nd_sbds :=
  match goal with
  | [Hsim : instantiate_State {| ECS := _::_::_ |} ?st2 |- _ ] =>
     destruct st2 as [ECs' M' MM'];
     destruct Hsim as [Hsim [eq6 eq7]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' rm1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct ECs' as [|[f2' b2' cs2' tmn2' lc2' rm2' als2'] ECs'];
       try solve [inversion Hsim2];
     destruct Hsim2 as [Hsim2 Hsim3];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 [J6 J7]]]]]]; subst;
     destruct Hsim2 as [J1 [J2 [J3 [J4 [Hsim2 [J6 J7]]]]]]; subst
  | [Hsim : instantiate_State {| ECS := _::_|} ?st2 |- _ ] =>
     destruct st2 as [ECs' M' MM'];
     destruct Hsim as [Hsim [eq6 eq7]]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' rm1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 [J6 J7]]]]]]; subst
  end.

Lemma mismatch_cons_false : forall A ECs (EC:A), ECs = EC :: ECs -> False.
Proof.
  induction ECs; intros; inversion H; eauto.
Qed.

Lemma instantiate_dsInsn : forall cfg st1 st2 st1' tr,
  instantiate_State st1 st2 ->
  @sInsn DGVs cfg st1 st1' tr ->
  (exists st2', @sInsn NDGVs cfg st2 st2' tr /\ instantiate_State st1' st2').
Proof.
  intros cfg st1 st2 st1' tr Hsim Hop.  
  inv Hop.
  rename H into Hop.
  rename H0 into Hllvmop.
  (sb_sInsn_cases (induction Hop) Case); inv Hllvmop.
Case "sReturn". simpl_nd_sbds. 
  eapply instantiate_locals__returnUpdateLocals in H; eauto.
  destruct H as [lc2'' [H1 H2]].
  exists (mkState
    ((mkEC f2' b2' cs' tmn2' lc2'' rm'' als2')::ECs') Mem' MM').
  instantiate_dsInsn_tac.
Case "sReturnVoid". simpl_nd_sbds. 
  exists (mkState 
    ((mkEC f2' b2' cs' tmn2' lc2' rm2' als2')::ECs') Mem' MM').
  instantiate_dsInsn_tac.
Case "sBranch". simpl_nd_sbds. 
  eapply instantiate_locals__switchToNewBasicBlock in H; eauto.
  eapply instantiate_locals__getOperandValue in H23; eauto.
  destruct H23 as [gvs2 [J1 J2]].
  destruct H as [lc2' [J3 J4]].
  exists (mkState 
    ((mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' rm' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sBranch_uncond". simpl_nd_sbds. 
  eapply instantiate_locals__switchToNewBasicBlock in H; eauto.
  destruct H as [lc2' [J1 J2]]. 
  exists (mkState
    ((mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' rm' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sBop". simpl_nd_sbds. 
  eapply instantiate_locals__BOP in H15; eauto.
  destruct H15 as [gvs3' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sFBop". simpl_nd_sbds. 
  eapply instantiate_locals__FBOP in H15; eauto.
  destruct H15 as [gvs3' [J1 J2]]. 
  exists (mkState 
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sExtractValue". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H14; eauto.
  destruct H14 as [gvs2 [J1 J2]].
  eapply instantiate_locals__extractGenericValue in H15; eauto.
  destruct H15 as [gvs2' [J3 J4]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sInsertValue". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H16; eauto.
  destruct H16 as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H17; eauto.
  destruct H17 as [gvs2' [J1' J2']].
  eapply instantiate_locals__insertGenericValue in H18; eauto.
  destruct H18 as [gvs2'' [J3 J4]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2'') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sMalloc". simpl_nd_sbds. 
  ctx_simpl.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns [J1 J2]]. inv H4.
  exists (mkState 
    ((mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 (gv2gvs _ (blk2GV TD mb) (typ_pointer t))) 
      (updateAddAL _ rm1' id0 (bound2MD mb tsz0 n)) als1')::ECs') 
      Mem' MM').
  instantiate_dsInsn_tac.
Case "sFree". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H13; eauto.
  destruct H13 as [gvs [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' lc1' rm1'
    als1')::ECs') Mem' MM').
  instantiate_dsInsn_tac.
Case "sAlloca". simpl_nd_sbds. 
  ctx_simpl.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns [J1 J2]]. inv H4.
  exists (mkState
    ((mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 (gv2gvs _ (blk2GV TD mb) (typ_pointer t)))
      (updateAddAL _ rm1' id0 (bound2MD mb tsz0 n))
      (mb::als1'))::ECs') Mem' MM').
  instantiate_dsInsn_tac.
Case "sLoad_nptr". simpl_nd_sbds.
  ctx_simpl. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs2 [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 (gv2gvs _ gv t))
    rm1' als1')::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sLoad_ptr". simpl_nd_sbds.
  ctx_simpl. inv H6.
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs2 [J1 J2]].
  exists (mkState 
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 (gv2gvs _ gv t))
    (updateAddAL _ rm1' id0 (get_mem_metadata TD MM' gvp)) als1')::ECs') 
    M' MM').
  instantiate_dsInsn_tac.
Case "sStore_nptr". simpl_nd_sbds.
  ctx_simpl. 
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [mps2' [J3 J4]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' lc1' rm1' als1')::ECs') Mem' MM').
  instantiate_dsInsn_tac.
Case "sStore_ptr". simpl_nd_sbds.
  repeat ctx_simpl. 
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [mps2' [J3 J4]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' lc1' rm1' als1')::ECs') Mem' 
      (set_mem_metadata TD MM' gvp md')).
  instantiate_dsInsn_tac.
Case "sGEP". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H21; eauto.
  destruct H21 as [mps [J1 J2]].
  eapply instantiate_locals__values2GVs in H22; eauto.
  destruct H22 as [vidxss' [J3 J4]].
  eapply instantiate_locals__GEP in H24; eauto.
  destruct H24 as [vidxs2 [mps2' [J5 [J6 J7]]]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 mps2') 
      (updateAddAL _ rm1' id0 md) als1') ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sTrunc". simpl_nd_sbds.
  eapply instantiate_locals__TRUNC in H15; eauto.
  destruct H15 as [gvs2' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sExt". simpl_nd_sbds. 
  eapply instantiate_locals__EXT in H15; eauto.
  destruct H15 as [gvs2' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sBitcast_nptr". simpl_nd_sbds. 
  eapply instantiate_locals__CAST in H16; eauto.
  destruct H16 as [gvs2' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sBitcast_ptr". simpl_nd_sbds. 
  eapply instantiate_locals__CAST in H22; eauto.
  destruct H22 as [gvs2' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2')
      (updateAddAL _ rm1' id0 md) als1') ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sInttoptr". simpl_nd_sbds. 
  eapply instantiate_locals__CAST in H16; eauto.
  destruct H16 as [gvs2' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') 
      (updateAddAL _ rm1' id0 null_md) als1') 
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sOthercast". simpl_nd_sbds. 
  eapply instantiate_locals__CAST in H16; eauto.
  destruct H16 as [gvs2' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sIcmp". simpl_nd_sbds. 
  eapply instantiate_locals__ICMP in H15; eauto.
  destruct H15 as [gvs3' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sFcmp". simpl_nd_sbds. 
  eapply instantiate_locals__FCMP in H15; eauto.
  destruct H15 as [gvs3' [J1 J2]]. 
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
Case "sSelect_nptr". simpl_nd_sbds. 
  eapply instantiate_locals__getOperandValue in H16; eauto.
  destruct H16 as [gvs0' [J1 J2]].
  eapply instantiate_locals__getOperandValue in H17; eauto.
  destruct H17 as [gvs1' [J3 J4]].
  eapply instantiate_locals__getOperandValue in H18; eauto.
  destruct H18 as [gvs2' [J5 J6]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (if isGVZero TD c 
                                   then updateAddAL _ lc1' id0 gvs2' 
                                   else updateAddAL _ lc1' id0 gvs1') rm1' als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac.
    destruct (isGVZero TD c); auto using @instantiate_locals__updateAddAL.
Case "sSelect_ptr". simpl_nd_sbds. 
  ctx_simpl. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs0' [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs1' [J3 J4]].
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [gvs2' [J5 J6]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (if isGVZero TD c 
                                   then updateAddAL _ lc1' id0 gvs2' 
                                   else updateAddAL _ lc1' id0 gvs1')
                                   (if isGVZero TD c 
                                   then updateAddAL _ rm1' id0 md2 
                                   else updateAddAL _ rm1' id0 md1) als1')
      ::ECs') M' MM').
  instantiate_dsInsn_tac. rewrite H25.
    destruct (isGVZero TD c); auto using @instantiate_locals__updateAddAL.
Case "sCall". simpl_nd_sbds. 
  apply lookupFdefViaPtr_inversion in H36.
  destruct H36 as [fn [J1 J2]].
  eapply instantiate_locals__getOperandValue in H34; eauto.
  destruct H34 as [gvs2 [J11 J12]].
  eapply instantiate_locals__params2GVs in H; eauto.
  destruct H as [gvss2 [H11 H12]].
  eapply instantiate_locals__initLocals in H0; eauto.
  destruct H0 as [lc2' [H21 H22]].
  exists (mkState
    ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' 
                       lc2' rm'
                       nil)::
     (mkEC f1' b1' (insn_call rid noret0 ca ft fv lp :: cs) tmn1' 
      lc1' rm1' als1') ::ECs') M' MM').
  instantiate_dsInsn_tac.
    simpl.
    eapply initLocals_params2GVs_sim in H11; eauto.
    destruct H11 as [gvs' [J33 J44]].
    eapply Opsem.sCall; eauto.
      unfold lookupFdefViaPtr. 
      rewrite J1. simpl. rewrite J2. auto.

  apply mismatch_cons_false in H27. inv H27.

Case "sExCall". 
  symmetry in H32.
  apply mismatch_cons_false in H32. inv H32.

  simpl_nd_sbds. 
  ctx_simpl. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J11 J12]].
  eapply OpsemInstantiation.instantiate_locals__params2GVs in H2; eauto.
  destruct H2 as [gvss2 [H11 H12]].
  eapply instantiate_locals__exCallUpdateLocals in H5; eauto.
  destruct H5 as [lc2' [H21 H22]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' lc2' rm' als1') ::ECs') Mem' MM').
  instantiate_dsInsn_tac.
    eapply sExCall; eauto.
      eapply instantiate_list_gvs__incl; eauto.
    eapply Opsem.sExCall; eauto.
      eapply instantiate_list_gvs__incl; eauto.
      eapply exCallUpdateLocals_sim; eauto.
Qed.

End Sec.

End SBspecInstantiation.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-impredicative-set") ***
*** End: ***
 *)

