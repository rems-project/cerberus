Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Maps.
Require Import opsem_props.

Definition DGVMap := @Opsem.GVsMap DGVs.

Definition value_in_scope (v0:value) (ids0:ids) : Prop :=
match v0 with
| value_const _ => True
| value_id vid => In vid ids0
end.

Definition wf_defs (v1 v2:value) F TD gl (f:fdef) (lc:DGVMap) ids0: Prop :=
F = f ->
forall gvs1 gvs2,
  value_in_scope v1 ids0 ->
  value_in_scope v2 ids0 ->
  Opsem.getOperandValue TD v1 lc gl = Some gvs1 ->
  Opsem.getOperandValue TD v2 lc gl = Some gvs2 ->
  gvs1 = gvs2.

Definition inscope_of_ec (ec:@Opsem.ExecutionContext DGVs) : option ids :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
match cs with
| nil => inscope_of_tmn f b tmn
| c::_ => inscope_of_cmd f b c
end.

Definition wf_ExecutionContext v1 v2 F TD gl (ps:list product) 
  (ec:Opsem.ExecutionContext) : Prop :=
match inscope_of_ec ec with
| Some ids0 => 
    wf_defs v1 v2 F TD gl (Opsem.CurFunction ec) (Opsem.Locals ec) ids0
| _ => False
end.

Fixpoint wf_ECStack v1 v2 F TD gl (ps:list product) (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => False
| ec::ecs' => 
    wf_ExecutionContext v1 v2 F TD gl ps ec /\ wf_ECStack v1 v2 F TD gl ps ecs'
end.

Definition wf_State v1 v2 F (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg s td ps gl _ ) := cfg in
let '(Opsem.mkState ecs _) := S in
wf_ECStack v1 v2 F td gl ps ecs.

Definition eval_rhs TD (M:mem) gl (lc:DGVMap) (c:cmd) gv : Prop :=
match c with
| insn_bop _ bop0 sz v1 v2 => BOP TD lc gl bop0 sz v1 v2 = Some gv
| insn_fbop _ fbop fp v1 v2 => FBOP TD lc gl fbop fp v1 v2  = Some gv 
| insn_extractvalue id t v idxs => 
    exists gv0, Opsem.getOperandValue TD v lc gl = Some gv0 /\
                extractGenericValue TD t gv0 idxs = Some gv
| insn_insertvalue _ t v t' v' idxs =>
    exists gv1, exists gv2, 
      Opsem.getOperandValue TD v lc gl = Some gv1 /\
      Opsem.getOperandValue TD v' lc gl = Some gv2 /\
      insertGenericValue TD t gv1 idxs t' gv2 = Some gv 
| insn_malloc _ t v aln | insn_alloca _ t v aln =>
    exists tsz, exists gns, exists gn, exists M', exists mb,
      getTypeAllocSize TD t = Some tsz /\
      Opsem.getOperandValue TD v lc gl = Some gns /\
      gn @ gns /\
      malloc TD M tsz gn aln = Some (M', mb) /\
      gv = ($ (blk2GV TD mb) # (typ_pointer t) $)
| insn_load _ t v aln =>
    exists mps, exists mp, exists gv0,
      Opsem.getOperandValue TD v lc gl = Some mps /\
      mp @ mps /\
      mload TD M mp t aln = Some gv0 /\
      gv = ($ gv0 # t$)
| insn_gep _ inbounds t v idxs =>
    exists mp, exists vidxss, exists vidxs,
      Opsem.getOperandValue TD v lc gl = Some mp /\
      values2GVs TD idxs lc gl = Some vidxss /\
      vidxs @@ vidxss /\
      GEP TD t mp vidxs inbounds = Some gv
| insn_trunc _ truncop t1 v1 t2 => TRUNC TD lc gl truncop t1 v1 t2 = Some gv
| insn_ext _ extop t1 v1 t2 => EXT TD lc gl extop t1 v1 t2 = Some gv
| insn_cast _ castop t1 v1 t2 => CAST TD lc gl castop t1 v1 t2 = Some gv
| insn_icmp _ cond0 t v1 v2 => ICMP TD lc gl cond0 t v1 v2 = Some gv
| insn_fcmp _ fcond fp v1 v2 => FCMP TD lc gl fcond fp v1 v2 = Some gv
| insn_select _ v0 t v1 v2 =>
    exists cond, exists gvs1, exists gvs2, exists c,
      Opsem.getOperandValue TD v0 lc gl = Some cond /\
      Opsem.getOperandValue TD v1 lc gl = Some gvs1 /\
      Opsem.getOperandValue TD v2 lc gl = Some gvs2 /\
      c @ cond /\
      gv = if isGVZero TD c then gvs2 else gvs1
| _ => True (* We may also consider call/excall, but ignore them so far *)
end.

Definition vev_defs (v1 v2:value) F TD M gl (f:fdef) (lc:DGVMap) c ids0: Prop :=
  F = f ->
  (value_in_scope v2 ids0 ->
   match Opsem.getOperandValue TD v2 lc gl with 
   | Some gv2 => 
       match v1 with
       | value_const _ => True
       | value_id id1 => 
           if (id1 == getCmdLoc c) then eval_rhs TD M gl lc c gv2
           else True
       end
   | _ => True
   end) /\
  (value_in_scope v1 ids0 ->
   match Opsem.getOperandValue TD v1 lc gl with 
   | Some gv1 => 
       match v2 with
       | value_const _ => True
       | value_id id2 => 
           if (id2 == getCmdLoc c) then eval_rhs TD M gl lc c gv1
           else True
       end
   | _ => True
  end).

Definition vev_ExecutionContext v1 v2 F TD M gl (ec:Opsem.ExecutionContext) 
  : Prop :=
let '(Opsem.mkEC f b cs _ lc _) := ec in
match cs with
| nil => True
| c::_ => 
    match inscope_of_cmd f b c with
    | None => True
    | Some ids0 => vev_defs v1 v2 F TD M gl f lc c ids0
    end
end.

Fixpoint vev_ECStack v1 v2 F TD M gl (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' => 
    vev_ExecutionContext v1 v2 F TD M gl ec /\ 
    vev_ECStack v1 v2 F TD M gl ecs'
end.

Definition vev_State v1 v2 F (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg s td _ gl _ ) := cfg in
let '(Opsem.mkState ecs M) := S in
vev_ECStack v1 v2 F td M gl ecs.

Ltac uniq_result :=
repeat dgvs_instantiate_inv;
repeat match goal with
| H1 : ?f ?a ?b ?c ?d = _,
  H2 : ?f ?a ?b ?c ?d = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b ?c = _,
  H2 : ?f ?a ?b ?c = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b = _,
  H2 : ?f ?a ?b = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : _ @ _ |- _ => inv H1
end.

Ltac destruct_exists :=
repeat match goal with
| H : exists _, _ |- _ => 
    let A := fresh "A" in
    let J := fresh "J" in
    destruct H as [A J]
end.

Ltac destruct_ands :=
repeat match goal with
| H : _ /\ _ |- _ => destruct H
end.

Definition sustable_cmd (c:cmd) : Prop :=
match c with
| insn_call _ _ _ _ _ _ => False
| insn_free _ _ _ => False
| insn_store _ _ _ _ _ => False
| _ => True
end.

Definition substable_value (f:fdef) (v:value) : Prop :=
match v with
| value_const _ => True
| value_id vid =>
    match lookupInsnViaIDFromFdef f vid with
    | Some (insn_cmd c) => sustable_cmd c
    | _ => False
    end
end.

Definition substable_values TD gl (f:fdef) (v1 v2:value) : Prop :=
substable_value f v1 /\ substable_value f v2 /\
match v1, v2 with
| value_const vc1, value_const vc2 => 
    @Opsem.const2GV DGVs TD gl vc1 = Opsem.const2GV TD gl vc2
| _, _ => True
end.

Lemma eval_rhs_det: forall td M gl lc c gv1 gv2,
  sustable_cmd c ->
  eval_rhs td M gl lc c gv1 -> eval_rhs td M gl lc c gv2 -> gv1 = gv2.
Proof.
  destruct c; simpl; intros; destruct_exists; destruct_ands; 
    try solve [uniq_result; auto | tauto].
Qed.

Lemma wf_defs_updateAddAL: forall v1 v2 F td Mem gl F' lc' c ids1 ids2 g0
  (Huniq: uniqFdef F') l1 ps1 cs1 tmn1
  (H : blockInFdefB (block_intro l1 ps1 cs1 tmn1) F' = true)
  (H0 : In c cs1)
  (Hvals : substable_values td gl F v1 v2)
  (Hvinscope2 : vev_defs v1 v2 F td Mem gl F' lc' c ids1)
  (Hinscope2' : wf_defs v1 v2 F td gl F' lc' ids1)
  (Heq : AtomSet.set_eq _ (getCmdLoc c::ids1) ids2)
  (Heval: eval_rhs td Mem gl lc' c g0),
  wf_defs v1 v2 F td gl F' (updateAddAL _ lc' (getCmdLoc c) g0) ids2.
Proof.
  intros.
  destruct Heq as [Hinc1 Hinc2].
  destruct Hvals as [Hval1 [Hval2 _]].
  intros EQ gvsa gvsb Hina Hinb Hgeta Hgetb; subst.
  destruct Hvinscope2 as [J1 J2]; auto.
  unfold wf_defs in Hinscope2'.
  destruct v1 as [vid1 | vc1]; simpl in *.
  Case "v1 = vid1".
    destruct v2 as [vid2 | vc2]; simpl in *.
    SCase "v2 = vid2".
      destruct (vid1 == getCmdLoc c); subst.
      SSCase "vid1 == c".
        rewrite lookupAL_updateAddAL_eq in Hgeta.
        inv Hgeta.
        destruct (vid2 == getCmdLoc c); subst.
        SSSCase "vid2 == c".
          rewrite lookupAL_updateAddAL_eq in Hgetb.
          inv Hgetb.
          eauto.

        SSSCase "vid2 <> c".
          rewrite <- lookupAL_updateAddAL_neq in Hgetb; auto.
          rewrite Hgetb in J1.
          assert (In vid2 ids1) as Hin.
            apply Hinc2 in Hinb. simpl in Hinb.
            destruct Hinb; subst; try congruence; auto.
          erewrite IngetCmdsIDs__lookupCmdViaIDFromFdef in Hval1; eauto.
          eapply eval_rhs_det; eauto.

      SSCase "vid1 <> c".
        rewrite <- lookupAL_updateAddAL_neq in Hgeta; auto.
        rewrite Hgeta in J2.
        assert (In vid1 ids1) as Hin.
          apply Hinc2 in Hina. simpl in Hina.
          destruct Hina; subst; try congruence; auto.
        destruct (vid2 == getCmdLoc c); subst.
        SSSCase "vid2 == c".
          rewrite lookupAL_updateAddAL_eq in Hgetb.
          inv Hgetb. 
          erewrite IngetCmdsIDs__lookupCmdViaIDFromFdef in Hval2; eauto.
          eapply eval_rhs_det; eauto.

        SSSCase "vid2 <> c".
          rewrite <- lookupAL_updateAddAL_neq in Hgetb; auto.
          rewrite Hgetb in J1.
          assert (In vid2 ids1) as Hin'.
            apply Hinc2 in Hinb. simpl in Hinb.
            destruct Hinb; subst; try congruence; auto.
          eauto.
      
    SCase "v2 = vc2".
      rewrite Hgetb in J1.
      destruct (vid1 == getCmdLoc c); subst.
      SSCase "vid1 == c".
        rewrite lookupAL_updateAddAL_eq in Hgeta.
        inv Hgeta. 
        erewrite IngetCmdsIDs__lookupCmdViaIDFromFdef in Hval1; eauto.
        eapply eval_rhs_det; eauto.

      SSCase "vid1 <> c".
        rewrite <- lookupAL_updateAddAL_neq in Hgeta; auto.
        assert (In vid1 ids1) as Hin.
          apply Hinc2 in Hina. simpl in Hina.
          destruct Hina; subst; try congruence; auto.
        eapply Hinscope2'; eauto.

  Case "v1 = vc1".
    rewrite Hgeta in J2.
    destruct v2 as [vid2 | vc2]; simpl in *; eauto.
    SCase "v2 = vid1".
      destruct (vid2 == getCmdLoc c); subst.
      SSCase "vid2 == c".
        rewrite lookupAL_updateAddAL_eq in Hgetb.
        inv Hgetb.
        erewrite IngetCmdsIDs__lookupCmdViaIDFromFdef in Hval2; eauto.
        eapply eval_rhs_det; eauto.

      SSCase "vid2 <> c".
        rewrite <- lookupAL_updateAddAL_neq in Hgetb; auto.
        assert (In vid2 ids1) as Hin.
          apply Hinc2 in Hinb. simpl in Hinb.
          destruct Hinb; subst; try congruence; auto.
        eapply Hinscope2'; eauto.
Qed.

Lemma wf_defs_eq : forall ids2 ids1 v1 v2 F td gl F' lc',
  AtomSet.set_eq _ ids1 ids2 ->
  wf_defs v1 v2 F td gl F' lc' ids1 ->
  wf_defs v1 v2 F td gl F' lc' ids2.
Proof.
  intros.
  intros EQ gv1 gv2 Hin1 Hin2 Hget1 Hget2; subst.
  destruct H as [J1 J2].
  eapply H0; eauto.
    destruct v1; simpl in *; eauto.
    destruct v2; simpl in *; eauto.
Qed.

Ltac destruct_ctx_return :=
match goal with
| Hwfpp : OpsemPP.wf_State _ _,
  HwfS1 : wf_State _ _ _ _ _,
  Hvev : vev_State _ _ _ _ _ |- _ =>
  destruct Hwfpp as 
    [_ [HwfSystem [HmInS [Hnempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
      [
        [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
        [HwfECs HwfCall]
      ]
      HwfCall'
     ]]
    ]]]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs;
  destruct Hvev as [Hvinscope1 [Hvinscope2 Hvev]];
  fold vev_ECStack in Hvev;
  unfold vev_ExecutionContext in Hvinscope1, Hvinscope2;
  destruct HwfS1 as [Hinscope1' [Hinscope2' HwfECs']];
  fold wf_ECStack in HwfECs';
  unfold wf_ExecutionContext in Hinscope1', Hinscope2';
  simpl in Hinscope1', Hinscope2'
end.

(* From OpsemDom, should go to Vellvm *)
Lemma isReachableFromEntry_successors : forall ifs S M f l3 ps cs tmn l' b'
  (Hreach : isReachableFromEntry f (block_intro l3 ps cs tmn))
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (HwfF : wf_fdef ifs S M f) (Huniq : uniqFdef f)
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

(* OpsemPP, and OpsemDom should also reuse the lemma. *)
Lemma inscope_tmn_to_tmn : forall (f : fnattrs) (t : typ) (i0 : id) (a : args)
  (v : varg) (bs : blocks) (l3 : l) (ps : phinodes) (cs : cmds) 
  (tmn : terminator) (ids0 : list atom) (l' : l) (ps' : phinodes)
  (HuniqF : uniqFdef (fdef_intro (fheader_intro f t i0 a v) bs))
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn)
            (fdef_intro (fheader_intro f t i0 a v) bs) = true)
  (contents3 : set atom)
  (Hinscope : ret ids0 =
             fold_left
               (inscope_of_block (fdef_intro (fheader_intro f t i0 a v) bs)
                  l3) contents3
               (ret (getPhiNodesIDs ps ++ getCmdsIDs cs ++ getArgsIDs a)))
  (contents' : set atom)
  (Hsub : incl contents' (l3 :: contents3))
  (r : list atom)
  (J1 : fold_left
         (inscope_of_block (fdef_intro (fheader_intro f t i0 a v) bs) l')
         contents'
         (ret (getPhiNodesIDs ps' ++ getCmdsIDs nil ++ getArgsIDs a)) = 
       ret r),
  incl (set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0.
Proof.
  intros.
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
              clear - J9 HBinF HuniqF. apply uniqF__uniqBlocks in HuniqF.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs a).
            apply in_or_app; auto.
      
            apply J5 in J9; auto.
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.
Qed.

(* From OpsemDom *)
Definition getArgsIDsFromFdef (f:fdef) : list atom :=
let '(fdef_intro (fheader_intro _ _ _ la _) _) := f in
getArgsIDs la.

Lemma substable_value_isnt_phi: forall F l' ps' cs' tmn' vid1
  (HuniqF: uniqFdef F)
  (Hlk: Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hvals : substable_value F (value_id vid1)),
  ~ In vid1 (getPhiNodesIDs ps').
Proof.
  intros.
  symmetry_ctx.
  apply lookupBlockViaLabelFromFdef_inv in Hlk; auto.
  destruct Hlk as [_ HBinF].
  intro J.
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in J; eauto.
  destruct_exists. destruct_ands.
  unfold substable_value in Hvals.
  rewrite H in Hvals. auto.
Qed.

Lemma substable_value_isnt_arg: forall fa rt fid la va lb vid
  (HuniqF: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hvals : substable_value (fdef_intro (fheader_intro fa rt fid la va) lb) 
             (value_id vid)),
  ~ In vid (getArgsIDs la).
Proof.
  intros.
  symmetry_ctx.
  intro J.
  eapply IngetArgsIDs__lookupCmdViaIDFromFdef in J; eauto.
  unfold substable_value in Hvals.
  rewrite J in Hvals. auto.
Qed.

Lemma wf_defs_br_aux : forall v1 v2 F0 TD gl ifs S M lc l' ps' cs' lc' F tmn' b
  (Hreach : isReachableFromEntry F b) 
  (Hreach': isReachableFromEntry F (block_intro l' ps' cs' tmn'))
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') b gl lc
               = ret lc')
  (t : list atom)
  (Hvals : substable_values TD gl F0 v1 v2)
  (Hwfdfs : wf_defs v1 v2 F0 TD gl F lc t)
  (ids0' : list atom)
  (HwfF : wf_fdef ifs S M F) (HuniqF: uniqFdef F)
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef F))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = (dom_analyze F) !! l')
  (Hinscope : (fold_left (inscope_of_block F l') contents' 
    (ret (getPhiNodesIDs ps' ++ getArgsIDsFromFdef F)) = ret ids0'))
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs v1 v2 F0 TD gl F lc' ids0'.
Proof.
  intros. destruct Hvals as [Hval1 [Hval2 _]].
  unfold Opsem.switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  intros EQ gvs1 gvs2 Hin1 Hin2 Hget1 Hget2; subst.
  remember (Opsem.getIncomingValuesForBlockFromPHINodes TD ps' b gl lc) as R1.
  destruct R1 as [rs|]; inv Hswitch.
  destruct v1 as [vid1 | vc1]; simpl in *. 
  Case "v1 = vid1".
    assert (~ In vid1 (getPhiNodesIDs ps')) as Hnotin1.
      eapply substable_value_isnt_phi; eauto.
    assert (Hnotin1' := Hnotin1).
    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) 
      in Hnotin1; auto.
    apply Hinc in Hnotin1. assert (HeqR1':=HeqR1).
    eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1; 
      eauto.
    eapply OpsemProps.updateValuesForNewBlock_spec7 in Hget1; eauto.

    destruct v2 as [vid2 | vc2]; simpl in *; eauto.
    SCase "v2 = vid2".
      assert (~ In vid2 (getPhiNodesIDs ps')) as Hnotin2.
        eapply substable_value_isnt_phi; eauto.
      assert (Hnotin2' := Hnotin2).
      apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) 
        in Hnotin2; auto.
      apply Hinc in Hnotin2. assert (HeqR1'':=HeqR1').
      eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1'; 
        eauto.
      eapply OpsemProps.updateValuesForNewBlock_spec7 in Hget2; eauto.
  
  Case "v1 = vc1".
    destruct v2 as [vid2 | vc2]; simpl in *; eauto.
    SCase "v2 = vid2".
      assert (~ In vid2 (getPhiNodesIDs ps')) as Hnotin.
        eapply substable_value_isnt_phi; eauto.
      assert (Hnotin' := Hnotin).
      apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) 
        in Hnotin; auto.
      apply Hinc in Hnotin. assert (HeqR1':=HeqR1).
      eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1; 
        eauto.
      eapply OpsemProps.updateValuesForNewBlock_spec7 in Hget2; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall ifs S M F l3 ps cs tmn ids0 l' ps' cs' tmn'
  l0 lc lc' gl TD (Hreach : isReachableFromEntry F (block_intro l3 ps cs tmn)) 
  v1 v2 F0 (Hvals : substable_values TD gl F0 v1 v2),
wf_fdef ifs S M F -> 
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) gl lc = Some lc' ->
wf_defs v1 v2 F0 TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs v1 v2 F0 TD gl F lc' ids0'.
Proof.
  intros ifs S M F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 lc lc' gl TD Hreach v1 v2
    F0 Hvals HwfF HuniqF HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd, inscope_of_id.
  destruct F as [fh bs].
  remember (dom_analyze (fdef_intro fh bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms HuniqF HwfF.
    apply uniqF__uniqBlocks in HuniqF.
    simpl in HuniqF.
    eapply dom_successors; eauto.

  assert (isReachableFromEntry (fdef_intro fh bs) (block_intro l' ps' nil tmn')) 
    as Hreach'.
    eapply isReachableFromEntry_successors in Hlkup; eauto.

  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound'). destruct fh as [f t i0 a v].
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil ++ getArgsIDs a)(bs:=bs)(l0:=l')
      (fh:=fheader_intro f t i0 a v) in J1; auto.
    destruct J1 as [r J1].
    exists r. split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF HuniqF.
      eapply inscope_tmn_to_tmn; eauto.

    split; auto.
      subst. simpl in J1. simpl_env in J1.   
      eapply wf_defs_br_aux in Hswitch; eauto.
        
  Case "cs'<>nil".
    assert (J1:=inbound').
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n]; 
      try solve [contradict n; auto].
    simpl_env.  destruct fh.
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil ++ getArgsIDs a)(bs:=bs)
      (fh:=fheader_intro f t i0 a v)(l0:=l') in J1.
    destruct J1 as [r J1].
    exists r. split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0) 
      as Jinc.
      clear - Hinscope J1 Hsub HBinF HuniqF.
      eapply inscope_tmn_to_tmn; eauto.

    split; auto.
      subst. eapply wf_defs_br_aux in Hswitch; eauto.
Qed.

Lemma inscope_of_tmn_br_uncond : forall v1 v2 F0 ifs S M F l3 ps cs ids0 l' ps' 
  cs' tmn' l0 lc lc' bid TD gl (Hvals : substable_values TD gl F0 v1 v2),
isReachableFromEntry F (block_intro l3 ps cs (insn_br_uncond bid l0)) ->
wf_fdef ifs S M F -> uniqFdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) gl lc = Some lc' ->
wf_defs v1 v2 F0 TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs v1 v2 F0 TD gl F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall v1 v2 F0 ifs S M F l0 ps cs bid l1 l2 ids0 l' 
  ps' cs' tmn' Cond c lc lc' gl TD (Hvals : substable_values TD gl F0 v1 v2),
isReachableFromEntry F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) ->
wf_fdef ifs S M F -> uniqFdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) gl lc = Some lc' ->
wf_defs v1 v2 F0 TD gl F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs v1 v2 F0 TD gl F lc' ids0'.
Proof.
  intros.
  remember (isGVZero TD c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| Hwfpp : OpsemPP.wf_State _ _,
  HwfS1 : wf_State _ _ _ _ _,
  Hvev : vev_State _ _ _ _ _ |- _ =>
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [Hnempty [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1' [ps1' [cs1' Heq1]]]]]]]] 
     [HwfECs HwfCall]]
    ]]]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs;
  destruct Hvev as [Hvinscope1 Hvev];
  fold vev_ECStack in Hvev;
  unfold vev_ExecutionContext in Hvinscope1;
  destruct HwfS1 as [Hinscope1' HwfECs'];
  fold wf_ECStack in HwfECs';
  unfold wf_ExecutionContext in Hinscope1';
  simpl in Hinscope1'
end.

Lemma preservation_cmd_updated_case : forall
  (F : fdef)
  (B : block)
  lc gv3
  (cs : list cmd)
  (tmn : terminator)
  id0 c0 los nts gl Mem0 Mem1 als EC fs Ps S
  (Hid : Some id0 = getCmdID c0) v1 v2 
  (Hvals : substable_values (los,nts) gl F v1 v2) Cfg St
  (Hvev : vev_State v1 v2 F Cfg St)
  (Hwfpp : OpsemPP.wf_State Cfg St)
  (Heval: eval_rhs (los,nts) Mem0 gl lc c0 gv3)
  (EQ1 : Cfg = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := (los, nts);
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |}) F0
  (EQ2 : St = {| Opsem.ECS := {| 
                           Opsem.CurFunction := F0;
                           Opsem.CurBB := B;
                           Opsem.CurCmds := c0 :: cs;
                           Opsem.Terminator := tmn;
                           Opsem.Locals := lc;
                           Opsem.Allocas := als |} :: EC;
                 Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State v1 v2 F Cfg St) als',
  wf_State v1 v2 F Cfg
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F0;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := updateAddAL _ lc id0 gv3;
            Opsem.Allocas := als' |} :: EC;
     Opsem.Mem := Mem1 |}.
Proof.
Local Opaque inscope_of_cmd inscope_of_tmn.
  intros. subst.
  destruct_ctx_other.
  split; auto.
    unfold wf_ExecutionContext. simpl.
    remember (inscope_of_cmd F0 (block_intro l1' ps1' (cs1' ++ c0 :: cs) tmn) c0)
      as R1. 
    assert (HeqR1':=HeqR1).
    assert (uniqFdef F0) as HuniqF.
      eapply wf_system__uniqFdef; eauto.
    destruct R1; try solve [inversion Hinscope1].
      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
      subst.
      assert (cmdInBlockB c0 (block_intro l1' ps1' (cs1' ++ c0 :: cs) tmn) 
               = true) as Hin.
        simpl. apply In_InCmdsB. apply in_middle.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs1')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F0) in HwfSystem; eauto.        
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
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.

      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F0) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.
Transparent inscope_of_cmd inscope_of_tmn.
Qed.

Lemma preservation_cmd_non_updated_case : forall
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (F : fdef)
  (B : block)
  lc (gl : GVMap)
  (fs : GVMap) EC
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 Mem1: mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None) v1 v2
  (Hvals : substable_values (los,nts) gl F v1 v2) Cfg St
  (Hvev : vev_State v1 v2 F Cfg St)
  (Hwfpp : OpsemPP.wf_State Cfg St)
  (EQ1 : Cfg = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := (los, nts);
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |}) F0
  (EQ2 : St = {| Opsem.ECS := {| 
                           Opsem.CurFunction := F0;
                           Opsem.CurBB := B;
                           Opsem.CurCmds := c0 :: cs;
                           Opsem.Terminator := tmn;
                           Opsem.Locals := lc;
                           Opsem.Allocas := als |} :: EC;
                 Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State v1 v2 F Cfg St),
  wf_State v1 v2 F Cfg
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F0;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := lc;
            Opsem.Allocas := als |} :: EC;
     Opsem.Mem := Mem1 |}.
Proof.
Local Opaque inscope_of_cmd inscope_of_tmn.
  intros. subst.
  destruct_ctx_other.
  split; auto.
    remember (inscope_of_cmd F0 (block_intro l1' ps1' (cs1' ++ c0 :: cs) tmn) c0)
      as R1. 
    destruct R1; try solve [inversion Hinscope1].
    unfold wf_ExecutionContext. simpl.
    destruct cs; simpl_env in *.
    Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs1')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F0) in HwfSystem; eauto.        
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
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq; eauto.
        
    Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F0) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq ; eauto.
Transparent inscope_of_cmd inscope_of_tmn.
Qed.

Lemma preservation_dbCall_case : forall fid fa rt la va lb td lc gl
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  v1 v2 F (Hvals : substable_values td gl F v1 v2),
  wf_defs v1 v2 F td gl 
    (fdef_intro (fheader_intro fa rt fid la va) lb) lc (getArgsIDs la).
Proof.
  intros. destruct Hvals as [Hval1 [Hval2 Hcst]].
  assert (incl nil (bound_blocks lb)) as J.
    intros x J. inv J.
  intros EQ gvs1 gvs2 Hin1 Hin2 Hget1 Hget2; subst.
  destruct v1 as [vid1 | vc1].
    eapply substable_value_isnt_arg in Hval1; eauto.
    simpl in Hin1. congruence.
  destruct v2 as [vid2 | vc2].
    eapply substable_value_isnt_arg in Hval2; eauto.
    simpl in Hin2. congruence.

    simpl in *. rewrite Hget1 in Hcst. rewrite Hget2 in Hcst. congruence.
Qed.

Lemma preservation : forall v1 v2 F cfg S1 S2 tr
  (Hvals : substable_values (OpsemAux.CurTargetData cfg) (OpsemAux.Globals cfg) 
             F v1 v2) (Hvev: vev_State v1 v2 F cfg S1)
  (Hwfpp: OpsemPP.wf_State cfg S1) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State v1 v2 F cfg S1), wf_State v1 v2 F cfg S2.
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

Case "sReturn". 
Focus.

  destruct_ctx_return.

  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F0
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
    assert (uniqFdef F') as HuniqF.
      eapply wf_system__uniqFdef; eauto.

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
        assert (HeqR2':=HeqR2).
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold Opsem.returnUpdateLocals in H1. simpl in H1.
        remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          destruct t; tinv H1.
          remember (lift_op1 DGVs (fit_gv (los, nts) t) g t) as R2.
          destruct R2; inv H1.
          change i0 with 
            (getCmdLoc (insn_call i0 false c (typ_function t l4 v0) v p)); auto.
          eapply wf_defs_updateAddAL; eauto.
            simpl. apply in_middle.

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
        assert (HeqR2':=HeqR2).
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].
        rewrite <- J1.
        unfold Opsem.returnUpdateLocals in H1. simpl in H1.
        remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR.
          destruct t; tinv H1.
          remember (lift_op1 DGVs (fit_gv (los, nts) t) g t) as R2.
          destruct R2; inv H1.
          change i0 with 
            (getCmdLoc (insn_call i0 false c (typ_function t l4 v0) v p)); auto.
          eapply wf_defs_updateAddAL; eauto.
            simpl. apply in_middle.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto. 

Unfocus.

Case "sReturnVoid". 
Focus.

  destruct_ctx_return.

  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F0
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
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
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1 Hinscope2'.
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
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnodup H1 Hinscope2'.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 

Unfocus.

Case "sBranch".
Focus.

  destruct_ctx_other.
  remember (inscope_of_tmn F0
             (block_intro l1' ps1' (cs1' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F0) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F0) in HuniqF; eauto.
    eapply inscope_of_tmn_br in HeqR1; eauto.
    destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
    destruct cs'; rewrite <- HeqR1; auto.
Unfocus.

Case "sBranch_uncond".
Focus.

  destruct_ctx_other.
  remember (inscope_of_tmn F0
             (block_intro l1' ps1' (cs1' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
    unfold wf_ExecutionContext. simpl.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F0) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F0) in HuniqF; eauto.
    eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
      (tmn':=tmn') in HeqR1; eauto.
    destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
    destruct cs'; rewrite <- HeqR1; auto.
Unfocus.

Case "sBop". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sFBop". 
  abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sExtractValue". 
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto).
Case "sInsertValue". 
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto).
Case "sMalloc". 
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto 10).
Case "sFree". 
  abstract (eapply preservation_cmd_non_updated_case; eauto; simpl; auto).
Case "sAlloca". 
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto 10).
Case "sLoad". 
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto 7).
Case "sStore". 
  abstract (eapply preservation_cmd_non_updated_case; eauto; simpl; auto).
Case "sGEP". 
  abstract (eapply preservation_cmd_updated_case; eauto; simpl; eauto 7).
Case "sTrunc". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sExt". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sCast". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sIcmp". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sFcmp". abstract (eapply preservation_cmd_updated_case; eauto; auto).
Case "sSelect". 
  abstract (
  assert (eval_rhs (los, nts) Mem gl lc (insn_select id0 v0 t v3 v4) 
           (if isGVZero (los, nts) c then gvs2 else gvs1)) as J; 
    try solve [simpl; eauto 9];
  try solve [
    destruct (isGVZero (los, nts) c); 
      eapply preservation_cmd_updated_case; eauto; auto
  ]).

Case "sCall".
Focus.
  destruct_ctx_other.

  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply OpsemAux.lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.

  repeat (split; auto).
    assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) 
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    unfold wf_ExecutionContext. simpl.
    assert (ps'=nil) as EQ.
      eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.
    subst.
    apply dom_entrypoint in H2. 

Transparent inscope_of_tmn inscope_of_cmd.

    destruct cs'.
      unfold inscope_of_tmn.
      remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
        !! l') as R.
      destruct R. simpl in H2. subst. simpl.
      eapply preservation_dbCall_case; eauto.

      unfold inscope_of_cmd, inscope_of_id.
      remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
        !! l') as R.
      destruct R. simpl. simpl in H2. subst. simpl.
      destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
        try solve [contradict n; auto]. 
      eapply preservation_dbCall_case; eauto.
Unfocus.

Case "sExCall". 
  abstract (
  unfold Opsem.exCallUpdateLocals in H5;
  destruct noret0; try solve [
    inv H5; eapply preservation_cmd_non_updated_case in HwfS1; eauto; auto |
    destruct oresult; inv H5;
    destruct ft; tinv H7;
    remember (fit_gv (los, nts) ft g) as R;
    destruct R; inv H7;
    eapply preservation_cmd_updated_case with (Mem1:=Mem') in HwfS1; 
      simpl; eauto; simpl; auto]
  ).
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
