Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
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
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import AST.
Require Import Maps.
Require Import opsem.

Module OpsemProps.

Export Opsem.

Lemma sInsn__implies__sop_star : forall cfg state state' tr,
  sInsn cfg state state' tr ->
  sop_star cfg state state' tr.
Proof.
  intros cfg state state' tr HdsInsn.
  rewrite <- trace_app_nil__eq__trace.
  eauto.
Qed.

Lemma sInsn__implies__sop_plus : forall cfg state state' tr,
  sInsn cfg state state' tr ->
  sop_plus cfg state state' tr.
Proof.
  intros cfg state state' tr HdsInsn.
  rewrite <- trace_app_nil__eq__trace.
  eauto.
Qed.

Lemma sop_plus__implies__sop_star : forall cfg state state' tr,
  sop_plus cfg state state' tr ->
  sop_star cfg state state' tr.
Proof.
  intros cfg state state' tr Hdsop_plus.
  inversion Hdsop_plus; subst; eauto.
Qed.

Hint Resolve sInsn__implies__sop_star sInsn__implies__sop_plus 
  sop_plus__implies__sop_star. 

Lemma sop_star_trans : forall cfg state1 state2 state3 tr12 tr23,
  sop_star cfg state1 state2 tr12 ->
  sop_star cfg state2 state3 tr23 ->
  sop_star cfg state1 state3 (trace_app tr12 tr23).
Proof.
  intros cfg state1 state2 state3 tr12 tr23 Hdsop12 Hdsop23.
  generalize dependent state3.
  generalize dependent tr23.
  induction Hdsop12; intros; auto.
    rewrite <- trace_app_commute. eauto.
Qed.

Lemma sop_diverging_trans : forall cfg state tr1 state' tr2,
  sop_star cfg state state' tr1 ->
  sop_diverges cfg state' tr2 ->
  sop_diverges cfg state (Trace_app tr1 tr2).
Proof. 
  intros cfg state tr1 state' tr2 state_dsop_state' state'_dsop_diverges.
  generalize dependent tr2.
  (sop_star_cases (induction state_dsop_state') Case); intros; auto.
  Case "sop_star_cons".
    rewrite <- Trace_app_commute. eauto.
Qed.

Lemma eqAL_getIncomingValuesForBlockFromPHINodes : forall ps B lc lc',
  eqAL _ lc lc' ->
  getIncomingValuesForBlockFromPHINodes ps B lc = 
  getIncomingValuesForBlockFromPHINodes ps B lc'.
Proof.
  induction ps; intros; simpl; auto.
    destruct a; auto.
    destruct (getValueViaBlockFromValuels l0 B); auto.
    destruct v; simpl; erewrite IHps; eauto.
      rewrite H. auto.
Qed.
  
Lemma eqAL_updateValuesForNewBlock : forall vs lc lc',
  eqAL _ lc lc' ->
  eqAL _ (updateValuesForNewBlock vs lc)(updateValuesForNewBlock vs lc').
Proof.
  induction vs; intros; simpl; auto.
    destruct a; auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_switchToNewBasicBlock : forall B1 B2 lc lc',
  eqAL _ lc lc' ->
  match (switchToNewBasicBlock B1 B2 lc,
         switchToNewBasicBlock B1 B2 lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite eqAL_getIncomingValuesForBlockFromPHINodes; eauto.
  destruct 
    (getIncomingValuesForBlockFromPHINodes (getPHINodesFromBlock B1) B2  
    lc'); auto using eqAL_updateValuesForNewBlock.
Qed.

Lemma eqAL_switchToNewBasicBlock' : forall B1 B2 lc lc' lc1,
  eqAL _ lc lc' ->
  switchToNewBasicBlock B1 B2 lc = Some lc1 ->
  exists lc1', switchToNewBasicBlock B1 B2 lc' = Some lc1' /\
               eqAL _ lc1 lc1'.
Proof.
  intros.
  assert (J:=eqAL_switchToNewBasicBlock B1 B2 lc lc' H).
  rewrite H0 in J.
  destruct (switchToNewBasicBlock B1 B2 lc'); try solve [inversion J].
  exists g. auto.
Qed.

Lemma updateValuesForNewBlock_uniq : forall l0 lc,
  uniq lc ->
  uniq (updateValuesForNewBlock l0 lc).
Proof.
  induction l0; intros lc Uniqc; simpl; auto.
    destruct a; apply updateAddAL_uniq; auto.
Qed.

Lemma updateValuesForNewBlock_spec4 : forall rs lc id1 gv,
  lookupAL _ rs id1 = Some gv ->
  lookupAL _ (updateValuesForNewBlock rs lc) id1 = Some gv.
Proof.  
  induction rs; intros; simpl in *.   
    inversion H.

    destruct a.
    destruct (id1==a); subst.
      inversion H; subst. apply lookupAL_updateAddAL_eq; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma switchToNewBasicBlock_uniq : forall B1 B2 lc lc',
  uniq lc ->
  switchToNewBasicBlock B1 B2 lc = Some lc' ->
  uniq lc'.
Proof.
  intros B1 B2 lc lc' Uniqc H.
  unfold switchToNewBasicBlock in H.
  destruct (getIncomingValuesForBlockFromPHINodes (getPHINodesFromBlock B1)
    B2 lc); inversion H; subst.
  apply updateValuesForNewBlock_uniq; auto.
Qed.      

Lemma getIncomingValuesForBlockFromPHINodes_eq : 
  forall ps l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  getIncomingValuesForBlockFromPHINodes ps 
    (block_intro l1 ps1 cs1 tmn1) =
  getIncomingValuesForBlockFromPHINodes ps (block_intro l1 ps2 cs2 tmn2).
Proof.
  induction ps; intros; auto.
    simpl.
    erewrite IHps; eauto.
Qed.

Lemma switchToNewBasicBlock_eq : 
  forall B l1 ps1 cs1 tmn1 ps2 cs2 tmn2 lc,
  switchToNewBasicBlock B (block_intro l1 ps1 cs1 tmn1) lc =
  switchToNewBasicBlock B (block_intro l1 ps2 cs2 tmn2) lc.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite getIncomingValuesForBlockFromPHINodes_eq; eauto.
Qed.

Lemma updateValuesForNewBlock_spec6 : forall lc rs id1 gvs
  (Hlk : lookupAL _ (updateValuesForNewBlock rs lc) id1 = ret gvs)
  (Hin : id1 `in` (dom rs)),
  lookupAL _ rs id1 = Some gvs.
Proof.
  induction rs; simpl; intros.
    fsetdec.

    destruct a.
    assert (id1 = i0 \/ id1 `in` dom rs) as J. fsetdec.   
    destruct J as [J | J]; subst.
      rewrite lookupAL_updateAddAL_eq in Hlk; auto. inv Hlk.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0); auto.
        contradict n; auto.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 i0); 
        subst; eauto.
        rewrite lookupAL_updateAddAL_eq in Hlk; auto. 
        rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto. 
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec6 : forall b lc ps' rs id1
  (HeqR1 : ret rs = getIncomingValuesForBlockFromPHINodes ps' b lc)
  (Hin : In id1 (getPhiNodesIDs ps')),
  id1 `in` dom rs.
Proof.
  induction ps'; simpl; intros.
    inv Hin.

    destruct a. destruct b. simpl in *.
    inv_mbind. inv HeqR1.
    destruct Hin as [Hin | Hin]; subst; simpl; auto.
Qed.


Lemma getIncomingValuesForBlockFromPHINodes_spec7 : forall b lc ps' rs id1
  (HeqR1 : ret rs = getIncomingValuesForBlockFromPHINodes ps' b lc)
  (Hin : id1 `in` dom rs),
  In id1 (getPhiNodesIDs ps').
Proof.
  induction ps'; simpl; intros.
    inv HeqR1. fsetdec.

    destruct a. destruct b. simpl in *.
    inv_mbind. inv HeqR1. simpl in *.
    assert (id1 = i0 \/ id1 `in` dom g0) as J. fsetdec.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec8 : forall b lc ps' rs id1
  (HeqR1 : ret rs = getIncomingValuesForBlockFromPHINodes ps' b lc)
  (Hnotin : ~ In id1 (getPhiNodesIDs ps')),
  id1 `notin` dom rs.
Proof.
  intros.
  intro J. apply Hnotin. 
  eapply getIncomingValuesForBlockFromPHINodes_spec7 in HeqR1; eauto.
Qed.

Lemma updateValuesForNewBlock_spec7 : forall lc rs id1 gvs
  (Hlk : lookupAL GenericValue (updateValuesForNewBlock rs lc) id1 = ret gvs)
  (Hnotin : id1 `notin` (dom rs)),
  lookupAL GenericValue lc id1 = ret gvs.
Proof.
  induction rs; simpl; intros; auto.
    destruct a.

    destruct_notin.
    rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto. 
Qed.

Lemma updateValuesForNewBlock_spec6' : forall lc rs id1 
  (Hin : id1 `in` (dom rs)),
  lookupAL _ (updateValuesForNewBlock rs lc) id1 = lookupAL _ rs id1.
Proof.
  induction rs; simpl; intros.
    fsetdec.

    destruct a.
    assert (id1 = a \/ id1 `in` dom rs) as J. fsetdec.   
    destruct J as [J | J]; subst.
      rewrite lookupAL_updateAddAL_eq.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) a a); auto.
        contradict n; auto.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
        subst; eauto.
        rewrite lookupAL_updateAddAL_eq; auto. 
        rewrite <- lookupAL_updateAddAL_neq; eauto. 
Qed.

Lemma updateValuesForNewBlock_spec7' : forall lc rs id1 
  (Hin : id1 `notin` (dom rs)),
  lookupAL _ (updateValuesForNewBlock rs lc) id1 = lookupAL _ lc id1.
Proof.
  induction rs; simpl; intros; auto.
    destruct a. destruct_notin.
    rewrite <- lookupAL_updateAddAL_neq; eauto. 
Qed.

Lemma updateValuesForNewBlock_sim : forall id0 lc lc'
  (Heq : forall id' : id,
        id' <> id0 ->
        lookupAL GenericValue lc id' = lookupAL GenericValue lc' id')
  g0 g
  (EQ : forall id' : id,
       id' <> id0 ->
       lookupAL GenericValue g0 id' = lookupAL GenericValue g id'),
  forall id', id' <> id0 ->
   lookupAL GenericValue (updateValuesForNewBlock g0 lc) id' =
   lookupAL GenericValue (updateValuesForNewBlock g lc') id'.
Proof.
  intros.
  destruct (AtomSetProperties.In_dec id' (dom g0)).
    rewrite updateValuesForNewBlock_spec6'; auto.
    destruct (AtomSetProperties.In_dec id' (dom g)).
      rewrite updateValuesForNewBlock_spec6'; auto.
      
      apply notin_lookupAL_None in n.
      erewrite <- EQ in n; eauto.
      apply indom_lookupAL_Some in i0.
      destruct i0 as [gv0 i0].
      rewrite i0 in n. congruence.

    rewrite updateValuesForNewBlock_spec7'; auto.
    destruct (AtomSetProperties.In_dec id' (dom g)).
      apply notin_lookupAL_None in n.
      erewrite EQ in n; eauto.
      apply indom_lookupAL_Some in i0.
      destruct i0 as [gv0 i0].
      rewrite i0 in n. congruence.

      rewrite updateValuesForNewBlock_spec7'; auto.
Qed.

End OpsemProps.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
