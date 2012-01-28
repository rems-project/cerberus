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
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import mem2reg.
Require Import memory_props.

Definition fdef_simulation (pinfo: PhiInfo) f1 f2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    elim_dead_st_fdef f1 (PI_id pinfo) = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (f1:fdef) cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    elim_dead_st_cmds cs1 (PI_id pinfo) = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (f1:fdef) b1 b2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    elim_dead_st_block (PI_id pinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) Ps1 Ps2 : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) S1 S2 : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo Ps1 Ps1
   end) S1 S2.

Definition EC_simulation (pinfo: PhiInfo) (EC1 EC2:@Opsem.ExecutionContext DGVs)
  : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\
       als1 = als2 /\
       block_simulation pinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (ECs1 ECs2:@Opsem.ECStack DGVs) 
  : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo EC1 EC2 /\ ECs_simulation pinfo ECs1' ECs2'
| _, _ => False
end.

Definition no_alias_head_in_tail (pinfo:PhiInfo) ptr
  (ec0:@Opsem.ExecutionContext DGVs) : Prop :=
forall gvsa (Heq: Opsem.CurFunction ec0 = PI_f pinfo)
  (Hlkup: lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) = Some gvsa),
  MemProps.no_alias ptr gvsa.

Definition no_alias_head_tail (pinfo:PhiInfo) ptr 
  (ecs':list Opsem.ExecutionContext) : Prop :=
  forall ec0 (Hin: In ec0 ecs'), no_alias_head_in_tail pinfo ptr ec0.

Definition Mem_simulation (pinfo:PhiInfo) TD (ecs1:list Opsem.ExecutionContext) 
  Mem1 Mem2 : Prop :=
forall ptr ty al gvs1 gvs2 
  (Hnalias: no_alias_head_tail pinfo ptr ecs1)
  (Hld1: mload TD Mem1 ptr ty al = Some gvs1)
  (Hld2: mload TD Mem2 ptr ty al = Some gvs2),
  gvs1 = gvs2.

Definition State_simulation (pinfo: PhiInfo)
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo Ps1 Ps2 /\
    ECs_simulation pinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ Mem_simulation pinfo TD1 ECs1 M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b 
      (insn_store sid _ _ (value_id qid) _ :: cs) 
      tmn lc als::_) _ => 
    if (fdef_dec (PI_f pinfo) f) then 
      if (id_dec (PI_id pinfo) qid) then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall pinfo St,
  removable_State pinfo St \/ ~ removable_State pinfo St.
Proof.
  destruct St. 
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  destruct c; auto.
  destruct v0; auto.
  simpl.
  destruct (fdef_dec (PI_f pinfo) CurFunction); auto.
  destruct (id_dec (PI_id pinfo) i1); auto.
Qed.

Lemma cmds_simulation_elim_cons_inv: forall (pinfo : PhiInfo) (i0 : id) (t : typ)
  (v : value) (a : align) (cs1 : list cmd) (cs2 : cmds)
  (Hcssim2 : cmds_simulation pinfo (PI_f pinfo)
              (insn_store i0 t v (value_id (PI_id pinfo)) a :: cs1) cs2),
  cmds_simulation pinfo (PI_f pinfo) cs1 cs2.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  simpl in *.
  destruct (id_dec (PI_id pinfo) (PI_id pinfo)); congruence.
Qed.

(* copied from id_rhs_val.v *)
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

Lemma no_alias_head_tail_prop1 : 
  forall pinfo ptr F B1 cs1 tmn1 lc als1 ECs B2 cs2 tmn2 als2,
  no_alias_head_tail pinfo ptr
              ({|
               Opsem.CurFunction := F;
               Opsem.CurBB := B1;
               Opsem.CurCmds := cs1;
               Opsem.Terminator := tmn1;
               Opsem.Locals := lc;
               Opsem.Allocas := als1 |} :: ECs) ->
  no_alias_head_tail pinfo ptr
              ({|
               Opsem.CurFunction := F;
               Opsem.CurBB := B2;
               Opsem.CurCmds := cs2;
               Opsem.Terminator := tmn2;
               Opsem.Locals := lc;
               Opsem.Allocas := als2 |} :: ECs).
Proof.
  unfold no_alias_head_tail. simpl in *.
  intros.
  intros.
  destruct Hin as [Hin | Hin]; subst; eauto.
  assert (no_alias_head_in_tail pinfo ptr
           {| Opsem.CurFunction := F;
              Opsem.CurBB := B1;
              Opsem.CurCmds := cs1;
              Opsem.Terminator := tmn1;
              Opsem.Locals := lc;
              Opsem.Allocas := als1 |}) as G. eauto.
  unfold no_alias_head_in_tail in *. simpl. auto.   
Qed.

Lemma cmds_simulation_nil_inv: forall pinfo f1 cs,
  cmds_simulation pinfo f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

(* copied from alive_store *)
Definition store_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_store _ _ _ ptr _ => used_in_value id' ptr
| _ => false
end.

Lemma cmds_simulation_nelim_cons_inv: forall pinfo F c cs2 cs',
  cmds_simulation pinfo F (c :: cs2) cs' ->
  store_in_cmd (PI_id pinfo) c = false ->
  exists cs2', 
    cs' = c :: cs2' /\ cmds_simulation pinfo F cs2 cs2'.
Proof.  
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
  destruct c; simpl in H0; eauto.
  destruct v0; simpl in H0; eauto.
  destruct (id_dec (PI_id pinfo) i1); subst; simpl; eauto.
  destruct (id_dec (PI_id pinfo) (PI_id pinfo)); simpl in *; congruence.
Qed.

(* copied from las.v *)
Ltac wfCall_inv :=
match goal with
| Heq3 : exists _,
           exists _,
             exists _,
               ?B = block_intro _ _ _ _,
  HBinF1 : blockInFdefB ?B ?F = true,
  HwfCall : OpsemPP.wf_call 
              {| 
              Opsem.CurFunction := ?F;
              Opsem.CurBB := ?B;
              Opsem.CurCmds := nil;
              Opsem.Terminator := _;
              Opsem.Locals := _;
              Opsem.Allocas := _ |} 
              ({|
               Opsem.CurFunction := _;
               Opsem.CurBB := _;
               Opsem.CurCmds := ?c' :: _;
               Opsem.Terminator := _;
               Opsem.Locals := _;
               Opsem.Allocas := _ |}  :: _) |- _ =>
  let cs3 := fresh "cs3" in
  destruct Heq3 as [l3 [ps3 [cs3 Heq3]]]; subst;
  assert (HBinF1':=HBinF1);
  apply HwfCall in HBinF1';
  destruct c'; tinv HBinF1'; clear HBinF1'
end.

Ltac destruct_ctx_return :=
match goal with
| Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [ _ HwfCall'
     ]]
    ]]]]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  destruct ECs2 as [|[F3 B3 cs3 tmn3 lc3 als3] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim' Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hecsim' as 
      [Hfsim2' [Htsim2' [Heq2' [Hbsim2' 
        [Heq3' [Heq4' [Hlcsim2' Hcssim2']]]]]]]; subst;
  destruct Hnoalias as 
    [
      [[Hinscope1' _] [[[Hinscope2' _] [HwfECs' _]] _]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs';
  apply cmds_simulation_nil_inv in Hcssim2; subst;
  wfCall_inv;
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; auto;
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result
end.

Lemma no_alias_head_tail_and_app: forall pinfo ptr ECs1 ECs2,
  no_alias_head_tail pinfo ptr ECs1 ->
  no_alias_head_tail pinfo ptr ECs2 ->
  no_alias_head_tail pinfo ptr (ECs1 ++ ECs2).
Proof.
  intros.
  unfold no_alias_head_tail in *.
  intros.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin]; eauto.
Qed.

Lemma no_alias_head_tail_and_cons: forall pinfo ptr EC ECs,
  no_alias_head_in_tail pinfo ptr EC ->
  no_alias_head_tail pinfo ptr ECs ->
  no_alias_head_tail pinfo ptr (EC :: ECs).
Proof.
  intros.
  simpl_env.
  apply no_alias_head_tail_and_app; auto.
  unfold no_alias_head_tail.  
  intros. 
  simpl in Hin. 
  destruct Hin as [Hin | Hin]; subst; auto.
    inv Hin.
Qed.

Lemma dse_is_sim : forall maxb pinfo Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hnld: load_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo St1) St1' tr1 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil) /\
  (forall (Hnrem: ~removable_State pinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  split; intros.
Case "removable state".
  
  destruct Cfg1 as [S1 [los nts] Ps1 gl1 fs1].
  destruct St1 as [ECs1 M1].
  destruct ECs1 as [|[F1 B1 [|[] cs1] tmn1 lc1 als1] ECs1]; tinv Hrem.
  simpl in Hrem.
  destruct v0 as [qid | vc]; tinv Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec (PI_id pinfo) qid); subst; tinv Hrem.
  
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [HwfECs Hwfcall]]
    ]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs.

  destruct Hnoalias as 
    [
      [[Hinscope' _] [HwfECs' HwfHT]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals.
  fold Promotability.wf_ECStack in HwfECs'.

  inv Hop1.

  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2].
  destruct St2 as [ECs2 M2].

  simpl in Hsim.
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst.
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim.
  destruct Hstksim as [Hecsim Hstksim].
  unfold EC_simulation in Hecsim.
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst.

  repeat (split; eauto 2 using cmds_at_block_tail_next).
    eapply cmds_simulation_elim_cons_inv; eauto.

    uniq_result.
    clear - Hmsim H23 H20.
    unfold Mem_simulation in *.
    intros. 
    eapply Hmsim; eauto using no_alias_head_tail_prop1.
    eapply MemProps.mstore_preserves_mload_inv'; eauto.
    assert (no_alias_head_in_tail pinfo ptr 
          {| Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |}) as J.
      apply Hnalias; simpl; auto.
    apply MemProps.no_alias_sym.
    unfold no_alias_head_in_tail in J; eauto.

Case "unremovable state".
  clear Hnrem.
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
  destruct_ctx_return.
  repeat (split; eauto 2 using cmds_at_block_tail_next).

    clear - H26 Hmsim H0 H1 Hinscope1'.
    unfold Mem_simulation in *.
    intros.
    eapply Hmsim with (ptr:=ptr)(ty:=ty)(al:=al);
      eauto using MemProps.free_allocas_preserves_mload_inv.
      
      clear Hmsim.
      apply no_alias_head_tail_and_cons; simpl.
        
  unfold no_alias_head_in_tail. simpl. intros. subst.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  
Admitted.

(*
admit.
eapply no_alias_head_tail_prop1; eauto.

      admit.

eapply ; eauto.

        


admit.


Case "sReturnVoid".
  destruct_ctx_return.

  assert (tmn2 = insn_return_void rid) as Hreturn.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Htsim2; auto.
  subst.

  inv Hop2.

  match goal with
  | H0 : free_allocas ?td ?M ?las = _,
    H26 : free_allocas ?td ?M ?las = _ |- _ =>
      rewrite H0 in H26; inv H26
  end.
  wfCall_inv.
  repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sBranch".
Focus.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.

  assert (exists Cond2,
    tmn2 = insn_br bid Cond2 l1 l2 /\ 
    value_simulation pinfo lasinfo F Cond Cond2) as Hbr.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Htsim2; eauto.
  destruct Hbr as [Cond2 [EQ Hvsim2]]; subst.

  inv Hop2.
  uniq_result.
  remember (inscope_of_tmn F (block_intro l3 ps3 (cs31 ++ nil) 
             (insn_br bid Cond l1 l2)) (insn_br bid Cond l1 l2)) as R.
  destruct R; tinv Hinscope1'.

  assert (uniqFdef F) as HuniqF.
    eauto using wf_system__uniqFdef.
  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.
  assert (c = c0)as Heq.
    eapply getOperandValue_inTmnOperands_sim with (v:=Cond)(v':=Cond2); 
      try solve [eauto | simpl; auto].
  subst.
  assert (block_simulation pinfo lasinfo F 
           (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H22 H1 Hfsim2.
    destruct (isGVZero (los, nts) c0); eauto using fdef_sim__block_sim.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq [Hpsim' [Hcssim' Htsim']]]; subst.

  assert (isReachableFromEntry F (block_intro l'0 ps' cs' tmn') /\
    In l'0 (successors_terminator (insn_br bid Cond l1 l2)) /\
    blockInFdefB (block_intro l'0 ps' cs' tmn') F = true) as J.
    symmetry in H1.
    destruct (isGVZero (los,nts) c0);
      assert (J:=H1);
      apply lookupBlockViaLabelFromFdef_inv in J; eauto;
      destruct J as [J H13']; subst;
      (repeat split; simpl; auto); try solve [
        auto | eapply reachable_successors; (eauto || simpl; auto)].
  destruct J as [Hreach' [Hsucc' HBinF1']].

  assert (lc' = lc'0) as Heq.
    eapply switchToNewBasicBlock_sim in Hbsim; eauto.
  subst.
  repeat (split; auto).
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

Unfocus.

Case "sBranch_uncond".
Focus.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.

  assert (tmn2 = insn_br_uncond bid l0) as Hbr.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Htsim2; eauto.
  subst.

  inv Hop2.
  uniq_result.
  remember (inscope_of_tmn F (block_intro l3 ps3 (cs31 ++ nil) 
             (insn_br_uncond bid l0)) (insn_br_uncond bid l0)) as R.
  destruct R; tinv Hinscope1'.

  assert (uniqFdef F) as HuniqF.
    eauto using wf_system__uniqFdef.
  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  assert (block_simulation pinfo lasinfo F 
           (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    clear - H H16 Hfsim2.
    eauto using fdef_sim__block_sim.
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq [Hpsim' [Hcssim' Htsim']]]; subst.

  assert (isReachableFromEntry F (block_intro l'0 ps' cs' tmn') /\
    In l'0 (successors_terminator (insn_br_uncond bid l0)) /\
    blockInFdefB (block_intro l'0 ps' cs' tmn') F = true) as J.
    symmetry in H;
    assert (J:=H);
    apply lookupBlockViaLabelFromFdef_inv in J; eauto;
    destruct J as [J H13']; subst;
    (repeat split; simpl; auto); try solve [
      auto | eapply reachable_successors; (eauto || simpl; auto)].
  destruct J as [Hreach' [Hsucc' HBinF1']].

  assert (lc' = lc'0) as Heq.
    eapply switchToNewBasicBlock_sim in Hbsim; eauto.
  subst.
  repeat (split; auto).
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

Unfocus.

Case "sBop".

  destruct_ctx_other.
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists v1', exists v2',
    c1' = insn_bop id0 bop0 sz0 v1' v2' /\ 
    value_simulation pinfo lasinfo F v1 v1' /\
    value_simulation pinfo lasinfo F v2 v2') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Hcsim2; eauto.
  destruct Hcmd as [v1' [v2' [Heq [Hvsim1 Hvsim2]]]]; subst.
  inv Hop2.

  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  assert (gvs0 = gvs3) as Heq.
    unfold Opsem.BOP in *.
    inv_mbind'; inv_mfalse; app_inv; symmetry_ctx.

    match goal with
    | HeqR : Opsem.getOperandValue _ ?v1 _ _ = ret _, 
      HeqR' : Opsem.getOperandValue _ ?v1' _ _ = ret _, 
      HeqR0 : Opsem.getOperandValue _ ?v2 _ _ = ret _,
      HeqR0' : Opsem.getOperandValue _ ?v2' _ _ = ret _,
      Hvsim1 : value_simulation _ _ _ ?v1 ?v1',
      Hvsim2 : value_simulation _ _ _ ?v2 ?v2' |- _ => 
      eapply getOperandValue_inCmdOperands_sim with (v':=v1') in HeqR; 
        try (eauto || simpl; auto);
      eapply getOperandValue_inCmdOperands_sim with (v':=v2') in HeqR0; 
        try (eauto || simpl; auto);
      subst; uniq_result; auto
    end.

  subst.

  repeat (split; eauto 2 using cmds_at_block_tail_next').

Case "sFBop". admit.
Case "sExtractValue". admit.
Case "sInsertValue". admit.
Case "sMalloc". 

  destruct_ctx_other.
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists v',
    c1' = insn_malloc id0 t v' align0 /\ 
    value_simulation pinfo lasinfo F v v') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Hcsim2; eauto.
  destruct Hcmd as [v' [Heq Hvsim]]; subst.
  inv Hop2.

  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  assert (gns = gns0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=v') in H0; 
      try (eauto || simpl; auto).
  subst.
  uniq_result.
  repeat (split; eauto 2 using cmds_at_block_tail_next').

Case "sFree". admit.
Case "sAlloca". admit.
Case "sLoad". admit.
Case "sStore". admit.
Case "sGEP". admit.
Case "sTrunc". admit.
Case "sExt". admit.
Case "sCast". admit.
Case "sIcmp". admit.
Case "sFcmp". admit.
Case "sSelect". admit.
Case "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists fv', exists lp',
    c1' = insn_call rid noret0 ca ft fv' lp' /\ 
    value_simulation pinfo lasinfo F fv fv' /\
    pars_simulation pinfo lasinfo F lp lp') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation, pars_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Hcsim2; eauto.
  destruct Hcmd as [fv' [lp' [Heq [Hvsim Hpasim]]]]; subst.

  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  inv Hop2.

  SCase "SCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H; 
      try (eauto || simpl; auto).
  subst. clear H.

  assert (Hfsim1:=Hpsim).
  eapply lookupFdefViaPtr__simulation in Hfsim1; eauto.

  assert (Hbsim1:=Hfsim1).
  eapply fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  repeat (split; eauto 4).
    exists l'0. exists ps'. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    assert (gvs = gvs0) as EQ.
      inv_mfalse; symmetry_ctx.
      eapply params2GVs_sim; eauto.
    subst.
    clear - H4 H31 Hfsim1.
    apply fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Heq _]. inv Heq. uniq_result.
    auto.

  SCase "sExCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H; 
      try (eauto || simpl; auto).
  subst. clear H.
  clear - H28 H1 Hpsim.

  eapply lookupFdefViaPtr__simulation_l2r in H1; eauto.
  destruct H1 as [f2 [H1 H2]].
  apply OpsemAux.lookupExFdecViaPtr_inversion in H28.
  apply OpsemAux.lookupFdefViaPtr_inversion in H1.
  destruct H28 as [fn [J1 [J2 J3]]].
  destruct H1 as [fn' [J4 J5]].
  uniq_result.   

Case "sExCall". 

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_cons_inv in Hcssim2.
  destruct Hcssim2 as [c1' [cs3' [Heq [Hcsim2 Hcssim2]]]]; subst.

  assert (exists fv', exists lp',
    c1' = insn_call rid noret0 ca ft fv' lp' /\ 
    value_simulation pinfo lasinfo F fv fv' /\
    pars_simulation pinfo lasinfo F lp lp') as Hcmd.
    clear - Hcsim2.
    unfold value_simulation, cmd_simulation, pars_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Hcsim2; eauto.
  destruct Hcmd as [fv' [lp' [Heq [Hvsim Hpasim]]]]; subst.

  assert (wf_fdef nil S (module_intro los nts Ps) F) as HwfF.
    eauto using wf_system__wf_fdef.

  inv Hop2.

  SCase "SCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H; 
      try (eauto || simpl; auto).
  subst. clear H.
  clear - H29 H1 Hpsim.

  eapply lookupExFdecViaPtr__simulation_l2r in H1; eauto.
  apply OpsemAux.lookupExFdecViaPtr_inversion in H1.
  apply OpsemAux.lookupFdefViaPtr_inversion in H29.
  destruct H1 as [fn [J1 [J2 J3]]].
  destruct H29 as [fn' [J4 J5]].
  uniq_result.   

  SCase "sExCall".

  uniq_result.

  assert (fptr = fptr0) as Heq.
    inv_mfalse; symmetry_ctx.
    eapply getOperandValue_inCmdOperands_sim with (v':=fv') in H; 
      try (eauto || simpl; auto).
  subst. clear H.

  assert (Hlkdec:=Hpsim).
  eapply lookupExFdecViaPtr__simulation_l2r in Hlkdec; eauto.

  assert (gvss = gvss0) as EQ.
    inv_mfalse; symmetry_ctx.
    eapply params2GVs_sim; eauto.
  subst.
  uniq_result.

  repeat (split; eauto 2 using cmds_at_block_tail_next').

Transparent inscope_of_tmn inscope_of_cmd.

Qed.

*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
