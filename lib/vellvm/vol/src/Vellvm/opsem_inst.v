Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
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
Require Import Floats.
Require Import AST.
Require Import Maps.
Require Import opsem.
Require Import opsem_props.
Require Import opsem_wf.

Module OpsemInstantiation.

Import Opsem.
Export OpsemProps.

Section Sec.

Context {DGVs : GenericValues} {NDGVs : GenericValues}.

Definition element_of (gvs1:DGVs.(GVsT)) (gvs2: NDGVs.(GVsT)) : Prop :=
forall gv1, 
  DGVs.(instantiate_gvs) gv1 gvs1 -> NDGVs.(instantiate_gvs) gv1 gvs2.

Hint Unfold element_of.

Lemma element_of__incl : forall x y x0,
  element_of x y ->
  DGVs.(instantiate_gvs) x0 x ->
  NDGVs.(instantiate_gvs) x0 y.
Proof. auto. Qed.

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

Fixpoint instantiate_locals (lc1 : list (id * DGVs.(GVsT))) 
  (lc2 : list (id * NDGVs.(GVsT))): Prop :=
match lc1, lc2 with
| nil, nil => True
| (id1,gvs1)::lc1', (id2,gvs2)::lc2' => 
    id1=id2 /\ element_of gvs1 gvs2 /\ instantiate_locals lc1' lc2'
| _, _ => False
end.

Definition instantiate_EC (ec1 : @ExecutionContext DGVs) 
  (ec2 : @ExecutionContext NDGVs) : Prop :=
match ec1, ec2 with
| mkEC f1 b1 cs1 tmn1 lc1 als1, mkEC f2 b2 cs2 tmn2 lc2 als2 =>
    f1 = f2 /\ b1 = b2 /\ cs1 = cs2 /\ tmn1 = tmn2 /\
    instantiate_locals lc1 lc2 /\ als1 = als2
end.

Fixpoint instantiate_ECs (ecs1 : @ECStack DGVs) (ecs2 : @ECStack NDGVs) : Prop :=
match ecs1, ecs2 with
| nil, nil => True
| ec1::ecs1', ec2::ecs2' => instantiate_EC ec1 ec2 /\ instantiate_ECs ecs1' ecs2'
| _, _ => False
end.

Definition instantiate_State (st1 : @State DGVs) (st2 : @State NDGVs) : Prop :=
match st1, st2 with
| mkState ecs1 M1, mkState ecs2 M2 => instantiate_ECs ecs1 ecs2 /\ M1 = M2
end.

Lemma instantiate_locals__lookup : forall lc1 lc2 id1 gv1,
  instantiate_locals lc1 lc2 -> 
  lookupAL _ lc1 id1 = Some gv1 ->
  exists gvs2, lookupAL _ lc2 id1 = Some gvs2 /\ element_of gv1 gvs2.
Proof.
  induction lc1; destruct lc2; simpl; intros id1 gv1 Hinst Hlk.  
    inv Hlk.
    inv Hinst.
    destruct a. inv Hinst.     

    destruct a. destruct p.
    destruct Hinst as [J1 [J2 J3]]; subst.
    destruct (id1 == i1); subst; eauto.
      inv Hlk. eauto.
Qed.

Lemma same_singleton_set : forall gv,
  Same_set GenericValue (Singleton _ gv) (Singleton _ gv).
Proof.
  unfold Same_set, Included. auto.
Qed.

Lemma instantiate_locals__getOperandValue : forall TD v lc1 lc2 gl gvs1,
  instantiate_locals lc1 lc2 -> 
  getOperandValue TD v lc1 gl = Some gvs1 ->
  exists gvs2, getOperandValue TD v lc2 gl = Some gvs2 /\
    element_of gvs1 gvs2.
Proof.
  intros.
  destruct v; simpl in *.
    eapply instantiate_locals__lookup; eauto.

    unfold const2GV in H0. unfold const2GV.
    destruct (_const2GV TD gl c) as [[gv ?]|]; inv H0.
    eauto using element_of__cgv2gvs.
Qed.

Lemma instantiate_locals__updateAddAL : forall gvs3 gvs3',
  element_of gvs3 gvs3' ->
  forall lc1 lc2 id0,
  instantiate_locals lc1 lc2 -> 
  instantiate_locals (updateAddAL _ lc1 id0 gvs3) (updateAddAL _ lc2 id0 gvs3').
Proof.
  induction lc1; destruct lc2; simpl; intros id0 H1; auto.
    inv H1.  
    destruct a. inv H1.
    destruct a. destruct p. destruct H1 as [eq [H1 H2]]; subst.
    destruct (id0 == i1); subst; simpl.
      split; auto.
      split; auto.
Qed.   

Lemma instantiate_locals__returnUpdateLocals : forall TD lc1 lc2 lc1' lc2' Result
    gl lc1'' c,
  instantiate_locals lc1 lc2 -> 
  instantiate_locals lc1' lc2' -> 
  returnUpdateLocals TD c Result lc1 lc1' gl = ret lc1'' ->
  exists lc2'', 
    returnUpdateLocals TD c Result lc2 lc2' gl = ret lc2'' /\
    instantiate_locals lc1'' lc2''. 
Proof.
  intros.
  unfold returnUpdateLocals in H1.
  remember (getOperandValue TD Result lc1 gl) as R.
  destruct R; tinv H1.
  symmetry in HeqR.
  eapply instantiate_locals__getOperandValue in HeqR; eauto.
  destruct HeqR as [gvs2 [J1 J2]].
  unfold returnUpdateLocals.
  rewrite J1. 
  destruct c; tinv H1.
  destruct n; inv H1; eauto.
  destruct t; tinv H3.
  remember (lift_op1 _ (fit_gv TD t) g t) as R.
  destruct R as [gr'|]; inv H3.
  symmetry in HeqR.
  eapply element_of__lift_op1 in HeqR; eauto.
  destruct HeqR as [ys2 [J3 J4]]. rewrite J3.
  eauto using instantiate_locals__updateAddAL.
Qed.

Lemma instantiate_locals__getIncomingValuesForBlockFromPHINodes : forall TD b
    gl lc1 lc2 (Hlc : instantiate_locals lc1 lc2) ps re1,  
  getIncomingValuesForBlockFromPHINodes TD ps b gl lc1 = Some re1 ->
  exists re2,
    getIncomingValuesForBlockFromPHINodes TD ps b gl lc2 = Some re2 /\
    instantiate_locals re1 re2.
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
    remember (getIncomingValuesForBlockFromPHINodes TD ps b gl lc1) as R1.
    destruct R1; inv H.  
    rewrite J1.
    symmetry in HeqR1.
    destruct (@IHps l1) as [re2 [J3 J4]]; auto.
    rewrite J3.
    exists ((i0, gvs2) :: re2). simpl. auto.
Qed.

Lemma instantiate_locals__updateValuesForNewBlock : forall lc1 lc2 re1 re2,
  instantiate_locals lc1 lc2 ->
  instantiate_locals re1 re2 ->
  instantiate_locals (updateValuesForNewBlock re1 lc1)
     (updateValuesForNewBlock re2 lc2).
Proof.
  induction re1; destruct re2; simpl; intros; auto.
    inv H0.
    destruct a. inv H0.
    destruct a. destruct p. destruct H0 as [eq [J1 J2]]; subst.
    apply instantiate_locals__updateAddAL; auto.    
Qed.

Lemma instantiate_locals__switchToNewBasicBlock : forall TD lc1 lc2 gl lc1' b b',
  instantiate_locals lc1 lc2 -> 
  switchToNewBasicBlock TD b' b gl lc1 = Some lc1' ->
  exists lc2', switchToNewBasicBlock TD b' b gl lc2 = Some lc2' /\
    instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold switchToNewBasicBlock in H0.
  unfold switchToNewBasicBlock.
  remember (getIncomingValuesForBlockFromPHINodes TD 
    (getPHINodesFromBlock b') b gl lc1) as R.
  destruct R; inv H0.
  symmetry in HeqR.
  eapply instantiate_locals__getIncomingValuesForBlockFromPHINodes in HeqR;eauto.
  destruct HeqR as [re2 [J1 J2]].
  rewrite J1.
  eauto using instantiate_locals__updateValuesForNewBlock.
Qed.

Lemma instantiate_locals__BOP : forall TD lc1 lc2 gl v1 v2 gvs3 bop sz,
  instantiate_locals lc1 lc2 -> 
  BOP TD lc1 gl bop sz v1 v2 = Some gvs3 ->
  exists gvs3', BOP TD lc2 gl bop sz v1 v2 = Some gvs3' /\
    element_of gvs3 gvs3'.
Proof.
  intros.
  apply BOP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold BOP.
  rewrite H1. rewrite H3.
  eauto using element_of__lift_op2.
Qed.
  
Lemma instantiate_locals__FBOP : forall TD lc1 lc2 gl v1 v2 gv3 fbop fp,
  instantiate_locals lc1 lc2 -> 
  FBOP TD lc1 gl fbop fp v1 v2 = Some gv3 ->
  exists gvs3', FBOP TD lc2 gl fbop fp v1 v2 = Some gvs3' /\
    element_of gv3 gvs3'.
Proof.
  intros.
  apply FBOP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold FBOP.
  rewrite H1. rewrite H3.
  eauto using element_of__lift_op2.
Qed.

Lemma instantiate_locals__ICMP : forall TD lc1 lc2 gl v1 v2 gv3 c t,
  instantiate_locals lc1 lc2 -> 
  ICMP TD lc1 gl c t v1 v2 = Some gv3 ->
  exists gvs3', ICMP TD lc2 gl c t v1 v2 = Some gvs3' /\
    element_of gv3 gvs3'.
Proof.
  intros.
  apply ICMP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold ICMP.
  rewrite H1. rewrite H3.
  eauto using element_of__lift_op2.
Qed.

Lemma instantiate_locals__FCMP : forall TD lc1 lc2 gl v1 v2 gv3 c t,
  instantiate_locals lc1 lc2 -> 
  FCMP TD lc1 gl c t v1 v2 = Some gv3 ->
  exists gvs3', FCMP TD lc2 gl c t v1 v2 = Some gvs3' /\
    element_of gv3 gvs3'.
Proof.
  intros.
  apply FCMP_inversion in H0.
  destruct H0 as [gv1 [gv2 [J1 [J2 J3]]]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  eapply instantiate_locals__getOperandValue in J2; eauto.
  destruct J2 as [gvs2 [H3 H4]].
  unfold FCMP.
  rewrite H1. rewrite H3.
  eauto using element_of__lift_op2.
Qed.

Definition instantiate_list_gvs(l1 : list DGVs.(GVsT))(l2 : list NDGVs.(GVsT)) :=
List.Forall2 element_of l1 l2.

Hint Unfold instantiate_list_gvs.

Lemma instantiate_locals__values2GVs : forall TD lc1 lc2 gl idxs vidxs,
  instantiate_locals lc1 lc2 -> 
  values2GVs TD idxs lc1 gl = Some vidxs ->
  exists vidxss, values2GVs TD idxs lc2 gl = Some vidxss /\
    instantiate_list_gvs vidxs vidxss.
Proof.
  induction idxs; simpl; intros.
    inv H0. exists nil. auto.

    remember (getOperandValue TD v lc1 gl) as R.
    destruct R; tinv H0.
    remember (values2GVs TD idxs lc1 gl) as R1.
    destruct R1; inv H0.
    symmetry in HeqR.
    eapply instantiate_locals__getOperandValue in HeqR; eauto.
    destruct HeqR as [gvs2 [H3 H4]].
    destruct (@IHidxs l0) as [vidxss [J1 J2]]; auto.
    rewrite H3. rewrite J1. eauto.
Qed.

Lemma in_instantiate_list_gvs : forall vidxss1 vidxss2 vidxs1
  (Hinst1 : instantiate_list_gvs vidxss1 vidxss2)
  (Hin1 : in_list_gvs vidxs1 vidxss1),
  in_list_gvs vidxs1 vidxss2.
Proof.
  intros.
  generalize dependent vidxs1.
  induction Hinst1; intros; inv Hin1; auto.
    eapply IHHinst1 in H4; eauto using element_of__incl.
Qed.

Lemma instantiate_locals__GEP : forall TD t mp1 mp1' vidxs1 vidxss1 vidxss2 
    inbounds mps2,
  instantiate_list_gvs vidxss1 vidxss2 ->
  element_of mp1 mps2 ->
  in_list_gvs vidxs1 vidxss1 ->
  GEP TD t mp1 vidxs1 inbounds = Some mp1' ->
  exists vidxs2, exists mps2', 
    in_list_gvs vidxs2 vidxss2 /\
    GEP TD t mps2 vidxs2 inbounds = Some mps2' /\ 
    element_of mp1' mps2'.
Proof.
  intros TD t mp1 mp1' vidxs1 vidxss1 vidxss2 inbounds mps2 Hinst1 Hinst2 Hin1 
    Hgep.
  inv Hgep.
  unfold GEP.
  unfold GEP in H0.
  eapply element_of__lift_op1 in H0; eauto.
  destruct H0 as [ys2 [J1 J2]].
  exists vidxs1.  
  eauto using in_instantiate_list_gvs.
Qed.

Lemma instantiate_locals__extractGenericValue : forall TD lc1 lc2 t gv2
    cidxs gv1 gvs1,
  instantiate_locals lc1 lc2 -> 
  element_of gv1 gvs1 ->
  extractGenericValue TD t gv1 cidxs = Some gv2 ->
  exists gvs2, extractGenericValue TD t gvs1 cidxs = Some gvs2 
    /\ element_of gv2 gvs2.
Proof.
  intros.
  unfold extractGenericValue in H1.
  unfold extractGenericValue.
  destruct (intConsts2Nats TD cidxs); inv H1.
  destruct (mgetoffset TD t l0) as [[]|]; inv H3.
  eauto using element_of__lift_op1.
Qed.

Lemma instantiate_locals__insertGenericValue : forall TD lc1 lc2 t1 t2 gv2 
    cidxs gv1 gvs1 gvs2 gv3,
  instantiate_locals lc1 lc2 -> 
  element_of gv1 gvs1 ->
  element_of gv2 gvs2 ->
  insertGenericValue TD t1 gv1 cidxs t2 gv2 = Some gv3 ->
  exists gvs3, insertGenericValue TD t1 gvs1 cidxs t2 gvs2 = Some gvs3
    /\ element_of gv3 gvs3.
Proof.
  intros.
  unfold insertGenericValue in H2.
  unfold insertGenericValue.
  destruct (intConsts2Nats TD cidxs); inv H2.
  destruct (mgetoffset TD t1 l0) as [[]|]; inv H4.
  eauto using element_of__lift_op2.
Qed.

Lemma instantiate_locals__CAST : forall TD lc1 lc2 gl t1 v1 t2 gv2 castop0,
  instantiate_locals lc1 lc2 -> 
  CAST TD lc1 gl castop0 t1 v1 t2 = Some gv2 ->
  exists gvs2', CAST TD lc2 gl castop0 t1 v1 t2 = Some gvs2' 
    /\ element_of gv2 gvs2'.
Proof.
  intros.
  apply CAST_inversion in H0.
  destruct H0 as [gv1 [J1 J2]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold CAST.
  rewrite H1.
  eauto using element_of__lift_op1.
Qed.

Lemma instantiate_locals__TRUNC : forall TD lc1 lc2 gl t1 v1 t2 gv2 top0,
  instantiate_locals lc1 lc2 -> 
  TRUNC TD lc1 gl top0 t1 v1 t2 = Some gv2 ->
  exists gvs2', TRUNC TD lc2 gl top0 t1 v1 t2 = Some gvs2' 
    /\ element_of gv2 gvs2'.
Proof.
  intros.
  apply TRUNC_inversion in H0.
  destruct H0 as [gv1 [J1 J2]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold TRUNC.
  rewrite H1.
  eauto using element_of__lift_op1.
Qed.

Lemma instantiate_locals__EXT : forall TD lc1 lc2 gl t1 v1 t2 gv2 top0,
  instantiate_locals lc1 lc2 -> 
  EXT TD lc1 gl top0 t1 v1 t2 = Some gv2 ->
  exists gvs2', EXT TD lc2 gl top0 t1 v1 t2 = Some gvs2' 
    /\ element_of gv2 gvs2'.
Proof.
  intros.
  apply EXT_inversion in H0.
  destruct H0 as [gv1 [J1 J2]]; subst.
  eapply instantiate_locals__getOperandValue in J1; eauto.
  destruct J1 as [gvs1 [H1 H2]].
  unfold EXT.
  rewrite H1.
  eauto using element_of__lift_op1.
Qed.

Lemma instantiate_locals__params2GVs : forall TD lc1 lc2 gl 
  (Hlc:instantiate_locals lc1 lc2) lp gvs1,
  params2GVs TD lp lc1 gl = Some gvs1 ->
  exists gvss2, params2GVs TD lp lc2 gl = Some gvss2 /\
    instantiate_list_gvs gvs1 gvss2.
Proof.
  induction lp; simpl; intros.
    inv H. eauto.

    destruct a.
    remember (getOperandValue TD v lc1 gl) as R1.
    destruct R1; tinv H.
    remember (params2GVs TD lp lc1 gl) as R2.
    destruct R2; inv H.
    symmetry in HeqR1.
    eapply instantiate_locals__getOperandValue in HeqR1; eauto.
    destruct HeqR1 as [gvs2 [H3 H4]].
    destruct (@IHlp l0) as [gvsss2 [J1 J2]]; auto.
    rewrite H3. rewrite J1. eauto.
Qed.

Lemma instantiate_locals__initializeFrameValues : forall TD lc1 lc2
  (H2: instantiate_locals lc1 lc2) la gvs1 gvs2 lc1'
  (H1 : instantiate_list_gvs gvs1 gvs2),
  _initializeFrameValues TD la gvs1 lc1 = Some lc1' ->
  exists lc2',
    _initializeFrameValues TD la gvs2 lc2 = Some lc2' /\
    instantiate_locals lc1' lc2'.
Proof.
  induction la; simpl; intros.
    inv H. eauto.

    destruct a. destruct p.
    destruct gvs1; simpl.
      destruct gvs2; inv H1.
      remember (_initializeFrameValues TD la nil lc1) as R1.
      destruct R1; tinv H.
      destruct (gundef TD t); inv H.
      symmetry in HeqR1.
      eapply IHla in HeqR1; eauto.
        destruct HeqR1 as [lc2' [J1 J2]].
        rewrite J1.
        eauto using instantiate_locals__updateAddAL, element_of__gv2gvs.

      simpl in H1.
      destruct gvs2; inv H1.
      remember (_initializeFrameValues TD la gvs1 lc1) as R1.
      destruct R1; tinv H.
      remember (lift_op1 _ (fit_gv TD t) g t) as R2.
      destruct R2; inv H.
      symmetry in HeqR1.
      eapply IHla in HeqR1; eauto.
      destruct HeqR1 as [lc2' [J1 J2]].
      rewrite J1.
      symmetry in HeqR2.
      eapply element_of__lift_op1 in HeqR2; eauto.
      destruct HeqR2 as [ys2 [J3 J4]].
      rewrite J3.
      eauto using instantiate_locals__updateAddAL.
Qed. 

Lemma instantiate_locals__initLocals : forall TD gvs1 gvss2 
  (H : instantiate_list_gvs gvs1 gvss2) la lc1,
  initLocals TD la gvs1 = Some lc1 ->
  exists lc2, 
    initLocals TD la gvss2 = Some lc2 /\
    instantiate_locals lc1 lc2.
Proof.
  unfold initLocals, initLocals.
  intros.
  eapply instantiate_locals__initializeFrameValues; eauto.
    simpl. auto.
Qed.

Lemma instantiate_list_gvs__incl : forall x y x0,
  instantiate_list_gvs x y ->
  in_list_gvs x0 x ->
  in_list_gvs x0 y.
Proof.
  intros.  
  generalize dependent x0.
  induction H; simpl; intros.
    inv H0; auto.
    inv H1; auto.
      apply IHForall2 in H6. eauto using element_of__incl.
Qed.

Lemma instantiate_locals__exCallUpdateLocals : forall TD lc1 lc2 lc1' rid oResult
    nr ft,
  instantiate_locals lc1 lc2 -> 
  exCallUpdateLocals TD ft nr rid oResult lc1 = ret lc1' ->
  exists lc2', 
    exCallUpdateLocals TD ft nr rid oResult lc2 = ret lc2' /\
    instantiate_locals lc1' lc2'. 
Proof.
  intros.
  unfold exCallUpdateLocals in H0.
  unfold exCallUpdateLocals.
  destruct nr; inv H0; eauto.
  destruct oResult; inv H2; eauto.
  destruct ft; inv H1; eauto.
  remember (fit_gv TD ft g) as R.
  destruct R; inv H2.
  eauto using instantiate_locals__updateAddAL, element_of__gv2gvs.
Qed.

Ltac simpl_nd_llvmds :=
  match goal with
  | [Hsim : instantiate_State {| ECS := _::_::_ |} ?st2 |- _ ] =>
     destruct st2 as [ECs' M'];
     destruct Hsim as [Hsim eq6]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct ECs' as [|[f2' b2' cs2' tmn2' lc2' als2'] ECs'];
       try solve [inversion Hsim2];
     destruct Hsim2 as [Hsim2 Hsim3];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 J6]]]]]; subst;
     destruct Hsim2 as [J1 [J2 [J3 [J4 [Hsim2 J6]]]]]; subst
  | [Hsim : instantiate_State {| ECS := _::_|} ?st2 |- _ ] =>
     destruct st2 as [ECs' M'];
     destruct Hsim as [Hsim eq6]; subst;
     destruct ECs' as [|[f1' b1' cs1' tmn1' lc1' als1'] ECs']; 
       try solve [inversion Hsim];
     simpl in Hsim; destruct Hsim as [Hsim1 Hsim2];
     destruct Hsim1 as [J1 [J2 [J3 [J4 [Hsim1 J6]]]]]; subst
  end.

Lemma instantiate_dsInsn : forall cfg st1 st2 st1' tr,
  instantiate_State st1 st2 ->
  sInsn cfg st1 st1' tr ->
  (exists st2', sInsn cfg st2 st2' tr /\ instantiate_State st1' st2').
Proof.
  intros cfg st1 st2 st1' tr Hsim Hop.  
  (sInsn_cases (induction Hop) Case).
Case "sReturn". simpl_nd_llvmds. 
  eapply instantiate_locals__returnUpdateLocals in H1; eauto.
  destruct H1 as [lc2'' [H1 H2]].
  exists (mkState ((mkEC f2' b2' cs' tmn2' lc2'' als2')::ECs') Mem').
  split; eauto.
    repeat (split; auto).
Case "sReturnVoid". simpl_nd_llvmds. 
  exists (mkState ((mkEC f2' b2' cs' tmn2' lc2' als2')::ECs') Mem').
  split; eauto.
    repeat (split; auto).
Case "sBranch". simpl_nd_llvmds. 
  eapply instantiate_locals__switchToNewBasicBlock in H2; eauto.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  destruct H2 as [lc2' [J3 J4]].
  exists (mkState ((mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' als1')
      ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto).
Case "sBranch_uncond". simpl_nd_llvmds. 
  eapply instantiate_locals__switchToNewBasicBlock in H0; eauto.
  destruct H0 as [lc2' [J1 J2]]. 
  exists (mkState ((mkEC f1' (block_intro l' ps' cs' tmn') cs' tmn' lc2' als1')
      ::ECs') M').
  split; eauto.
    repeat (split; auto).
Case "sBop". simpl_nd_llvmds. 
  eapply instantiate_locals__BOP in H; eauto.
  destruct H as [gvs3' [J1 J2]].
  exists (mkState ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sFBop". simpl_nd_llvmds. 
  eapply instantiate_locals__FBOP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. 
  exists (mkState ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sExtractValue". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  eapply instantiate_locals__extractGenericValue in H0; eauto.
  destruct H0 as [gvs2' [J3 J4]].
  exists (mkState ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sInsertValue". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs2' [J1' J2']].
  eapply instantiate_locals__insertGenericValue in H1; eauto.
  destruct H1 as [gvs2'' [J3 J4]].
  exists (mkState((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2'') als1')
      ::ECs') M').
  split; eauto.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sMalloc". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns2 [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 (NDGVs.(gv2gvs) (blk2GV TD mb) (typ_pointer t))) 
    als1')::ECs') Mem').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              element_of__gv2gvs).
Case "sFree". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs [J1 J2]].
  exists (mkState ((mkEC f1' b1' cs tmn1' lc1' als1')::ECs') Mem').
  split; eauto using element_of__incl.
    repeat (split; auto).
Case "sAlloca". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gns2 [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' 
      (updateAddAL _ lc1' id0 (NDGVs.(gv2gvs)  (blk2GV TD mb) (typ_pointer t))) 
    (mb::als1'))::ECs') Mem').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              element_of__gv2gvs).
Case "sLoad". simpl_nd_llvmds.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 (NDGVs.(gv2gvs) gv t))
    als1')::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL, 
                              element_of__gv2gvs).
Case "sStore". simpl_nd_llvmds.
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [mps2' [J3 J4]].
  exists (mkState ((mkEC f1' b1' cs tmn1' lc1' als1')::ECs') Mem').
  split; eauto using element_of__incl.
    repeat (split; auto).
Case "sGEP". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [mps [J1 J2]].
  eapply instantiate_locals__values2GVs in H0; eauto.
  destruct H0 as [vidxss2 [J3 J4]].
  eapply instantiate_locals__GEP in H1; eauto.
  destruct H1 as [vidxs2 [mps2' [J5 [J6 J7]]]].
  exists (mkState 
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 mps2') als1')
      ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sTrunc". simpl_nd_llvmds.
  eapply instantiate_locals__TRUNC in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sExt". simpl_nd_llvmds. 
  eapply instantiate_locals__EXT in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (mkState  
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sCast". simpl_nd_llvmds. 
  eapply instantiate_locals__CAST in H; eauto.
  destruct H as [gvs2' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs2') als1')
      ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sIcmp". simpl_nd_llvmds. 
  eapply instantiate_locals__ICMP in H; eauto.
  destruct H as [gvs3' [J1 J2]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sFcmp". simpl_nd_llvmds. 
  eapply instantiate_locals__FCMP in H; eauto.
  destruct H as [gvs3' [J1 J2]]. 
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (updateAddAL _ lc1' id0 gvs3') als1')
      ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto using instantiate_locals__updateAddAL).
Case "sSelect". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs0' [J1 J2]].
  eapply instantiate_locals__getOperandValue in H0; eauto.
  destruct H0 as [gvs1' [J3 J4]].
  eapply instantiate_locals__getOperandValue in H1; eauto.
  destruct H1 as [gvs2' [J5 J6]].
  exists (mkState
    ((mkEC f1' b1' cs tmn1' (if isGVZero TD c 
                                     then updateAddAL _ lc1' id0 gvs2' 
                                     else updateAddAL _ lc1' id0 gvs1') als1')
      ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto).
      destruct (isGVZero TD c); auto using instantiate_locals__updateAddAL.
Case "sCall". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J11 J12]].
  eapply instantiate_locals__params2GVs in H3; eauto.
  destruct H3 as [gvss2 [H11 H12]].
  eapply instantiate_locals__initLocals in H4; eauto.
  destruct H4 as [lc2' [H21 H22]].
  exists (mkState
    ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' lc2'
                       nil)::
     (mkEC f1' b1' (insn_call rid noret0 ca ft fv lp :: cs) tmn1' 
      lc1' als1') ::ECs') M').
  split; eauto using element_of__incl.
    repeat (split; auto).
Case "sExCall". simpl_nd_llvmds. 
  eapply instantiate_locals__getOperandValue in H; eauto.
  destruct H as [gvs2 [J11 J12]].
  eapply instantiate_locals__params2GVs in H2; eauto.
  destruct H2 as [gvss2 [H11 H12]].
  eapply instantiate_locals__exCallUpdateLocals in H5; eauto.
  destruct H5 as [lc2' [H21 H22]].
  exists (mkState ((mkEC f1' b1' cs tmn1' lc2' als1') ::ECs') Mem').
  split.
    eapply sExCall; eauto using element_of__incl,
                                    instantiate_list_gvs__incl.
    repeat (split; auto).
Qed.

End Sec.

Require Import dopsem.
Require Import ndopsem.

Local Transparent gv2gvs cgv2gvs lift_op1 lift_op2.

Lemma element_of__gv2gvs : forall gv t, 
  element_of (DGVs.(gv2gvs) gv t) (NDGVs.(gv2gvs) gv t).
Proof. 
  intros.
  unfold gv2gvs.
  destruct gv; try solve [intros gvs1 J; inv J; constructor].
  destruct p.
  destruct v; try solve [intros gvs1 J; inv J; constructor].
  destruct gv; try solve [intros gvs1 J; inv J; constructor].
  destruct t; simpl;
    try solve [intros gvs1 J; inv J; 
               (constructor || apply Union_introl; constructor)].
  destruct f; simpl;
    try solve [intros gvs1 J; inv J; 
               (constructor || apply Union_introl; constructor)].
Qed.

Lemma element_of__cgv2gvs : forall gv t, 
  element_of (DGVs.(cgv2gvs) gv t) (NDGVs.(cgv2gvs) gv t).
Proof. 
  intros.
  unfold cgv2gvs.
  destruct gv; try solve [intros gvs1 J; inv J; constructor].
  destruct p.
  destruct v; try solve [intros gvs1 J; inv J; constructor].
  destruct gv; try solve [intros gvs1 J; inv J; constructor].
  destruct t; simpl;
    try solve [intros gvs1 J; inv J;
               try solve [constructor |
               exists (Int.zero s); auto |
               exists Mem.nullptr; exists (Int.repr 31 0); auto]].
  destruct f; simpl;
    try solve [intros gvs1 J; inv J;
               try solve [constructor |
               exists Float.zero; auto]].
Qed.

Lemma element_of__lift_op1 : forall f xs1 xs2 t ys1,
  element_of xs1 xs2 ->
  DGVs.(lift_op1) f xs1 t = Some ys1 ->
  exists ys2, NDGVs.(lift_op1) f xs2 t = Some ys2 /\ 
    element_of ys1 ys2.
Proof.
  unfold lift_op1. simpl.
  intros. unfold MNDGVs.lift_op1. 
  exists (fun gv2 : LLVMgv.GenericValue =>
          exists gv1 : LLVMgv.GenericValue,
            exists gv2' : LLVMgv.GenericValue,
              MNDGVs.instantiate_gvs gv1 xs2 /\
              f gv1 = ret gv2' /\
              MNDGVs.instantiate_gvs gv2 (MNDGVs.gv2gvs gv2' t)).
  split; auto.
  exists xs1. exists gv1. inv H1.
  repeat (split; eauto using MNDGVs.instantiate_gv__gv2gvs).
    apply H; auto.
Qed.

Lemma element_of__lift_op2 : forall f xs1 ys1 xs2 ys2 t zxs1,
  element_of xs1 xs2 ->
  element_of ys1 ys2 ->
  DGVs.(lift_op2) f xs1 ys1 t = Some zxs1 ->
  exists zxs2, NDGVs.(lift_op2) f xs2 ys2 t = Some zxs2 /\ 
    element_of zxs1 zxs2.
Proof.
  unfold lift_op2. simpl.
  intros. unfold MNDGVs.lift_op2. 
  exists (fun gv3 : LLVMgv.GenericValue =>
          exists gv1 : LLVMgv.GenericValue,
            exists gv2 : LLVMgv.GenericValue,
              exists gv3' : LLVMgv.GenericValue,
                MNDGVs.instantiate_gvs gv1 xs2 /\
                MNDGVs.instantiate_gvs gv2 ys2 /\
                f gv1 gv2 = ret gv3' /\
                MNDGVs.instantiate_gvs gv3 (MNDGVs.gv2gvs gv3' t)).
  split; auto.
  exists xs1. exists ys1. exists zxs1. inv H2.
  repeat (split; eauto using MNDGVs.instantiate_gv__gv2gvs).
    apply H; auto. apply H0; auto.
Qed.

Lemma DOS_instantiate_NDOS : forall cfg st1 st2 st1' tr,
  @instantiate_State DGVs NDGVs st1 st2 ->
  sInsn cfg st1 st1' tr ->
  (exists st2', sInsn cfg st2 st2' tr /\ 
    instantiate_State st1' st2').
Proof.
  intros.
  eapply instantiate_dsInsn; eauto using
    element_of__gv2gvs, element_of__cgv2gvs,
    element_of__lift_op1, element_of__lift_op2.
Qed.

End OpsemInstantiation.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
