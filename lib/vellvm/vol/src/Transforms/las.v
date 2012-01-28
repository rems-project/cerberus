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
Require Import alive_store.
Require Import id_rhs_val.
Require Import palloca_props.

(* We define a special las used by mem2reg that only considers local commands.
   In general, it should be extended to the las defined w.r.t domination and
   memory dependency (which we are aiming in the future work)

   The current mem2reg also does SAS eliminations before all loads are removed.
   For example,
     st v1 p; ...; st v2 p; ...
   if there are no other lds in the first ..., the first ``st v1 p'' can be 
   removed.

   In practice, such a code after phiplacement may exist if the original code 
   also does store to the promotable alloca. 

   An alternative approach is that we only consider such elimination after all
   possible removed loads are removed, as what the paper presents. mem2reg does
   not check if there are any unremoved loads in unreachable blocks. If so,
   some stores cannot be removed. We need to let mem2reg ignore the loads of
   unreachable blocks to remove what SAS can eliminate.

   For this reason, here, we give the abstract properties that las needs to hold.
   The properties do not depend on the concrete design in mem2reg, such as
   find_init_stld, find_next_stld, ... So the proofs can still work if we change
   mem2reg. We should prove that the design in mem2reg satisfy the properties.
 *)

Definition las (lid sid: id) (v:value) (cs2:cmds) (b:block) (pinfo:PhiInfo)
  : Prop :=
blockInFdefB b (PI_f pinfo) = true /\
store_in_cmds (PI_id pinfo) cs2 = false /\
let '(block_intro _ _ cs _) := b in
exists cs1, exists cs3,
  cs = 
  cs1 ++ 
  insn_store sid (PI_typ pinfo) v (value_id (PI_id pinfo)) (PI_align pinfo) :: 
  cs2 ++ 
  insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) (PI_align pinfo) :: 
  cs3.

Record LASInfo (pinfo: PhiInfo) := mkLASInfo {
  LAS_lid : id;
  LAS_sid : id;
  LAS_value : value;
  LAS_tail : cmds;
  LAS_block : block;
  LAS_prop : las LAS_lid LAS_sid LAS_value LAS_tail LAS_block pinfo
}.

Lemma LAS_substable_values : forall td gl pinfo lasinfo 
  (Huniq: uniqFdef (PI_f pinfo)),
  substable_values td gl (PI_f pinfo) (value_id (LAS_lid pinfo lasinfo))  
    (LAS_value pinfo lasinfo).
Admitted.

Lemma store_in_cmds_merge: forall i0 cs1 cs2,
  store_in_cmds i0 cs1 = false /\ store_in_cmds i0 cs2 = false ->
  store_in_cmds i0 (cs1++cs2) = false.
Admitted.

Lemma las__alive_store: forall lid sid v cs2 b pinfo,
  las lid sid v cs2 b pinfo ->
  alive_store sid v (cs2 ++
    [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) (PI_align pinfo)]) 
    b pinfo.
Proof.
  unfold las. unfold alive_store.
  intros. destruct b.
  destruct H as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
  split; auto.
  split.
    apply store_in_cmds_merge.
    split; auto.
     
    exists cs1. exists cs3. simpl_env. auto.
Qed.

Lemma lasinfo__stinfo: forall pinfo (lasinfo: LASInfo pinfo),
  { stinfo: StoreInfo pinfo |
    SI_id pinfo stinfo = LAS_sid pinfo lasinfo /\
    SI_value pinfo stinfo = LAS_value pinfo lasinfo /\
    SI_block pinfo stinfo = LAS_block pinfo lasinfo /\
    SI_tail pinfo stinfo = 
      LAS_tail pinfo lasinfo ++ 
      [insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo) (value_id (PI_id pinfo)) 
        (PI_align pinfo)] }.
Proof.
  intros.
  destruct lasinfo. simpl.
  apply las__alive_store in LAS_prop0.
  exists (mkStoreInfo 
    pinfo LAS_sid0 LAS_value0 
    (LAS_tail0 ++
     [insn_load LAS_lid0 (PI_typ pinfo) (value_id (PI_id pinfo))
        (PI_align pinfo)]) LAS_block0 LAS_prop0).
  auto.
Defined.

Lemma las__alive_store__vev_EC: forall pinfo lasinfo los nts M gl ps ec ifs s 
  (Hwfs: wf_system ifs s) 
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true)
  (Hwfpp: OpsemPP.wf_ExecutionContext (los,nts) ps ec) stinfo Hp
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo),
  alive_store.wf_ExecutionContext pinfo stinfo (los,nts) M gl ec -> 
  vev_ExecutionContext (value_id (LAS_lid pinfo lasinfo)) 
    (LAS_value pinfo lasinfo) (PI_f pinfo) (los,nts) M gl ec.
Proof.
  intros. clear Hlas2st.
  destruct Hp as [J1 [J2 [J3 J4]]].
  intros.
  destruct ec. simpl in *.
  destruct CurCmds; auto.

  destruct Hwfpp as 
    [Hreach [HbInF [HfInPs [_ [Hinscope [l' [ps' [cs' EQ]]]]]]]]; subst.

  remember (inscope_of_cmd CurFunction
                 (block_intro l' ps' (cs' ++ c :: CurCmds) Terminator) c) as R.
  destruct R; auto.

  assert (uniqFdef CurFunction) as Huniq.
    eapply wf_system__uniqFdef; eauto.

  assert (Hnodup:=HbInF).
  apply uniqFdef__blockInFdefB__nodup_cmds in Hnodup; auto.

  intros G1; subst.
  split; intro G1.
  Case "LAS_value is in scope".

  remember (Opsem.getOperandValue (los,nts) (LAS_value pinfo lasinfo) 
      Locals gl) as R.
  destruct R; auto.
  destruct (LAS_lid pinfo lasinfo == getCmdLoc c); auto.

  assert (c = insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
             (value_id (PI_id pinfo)) (PI_align pinfo)) as EQ.
      eapply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=c) in HbInF; eauto
        using in_middle.
      destruct stinfo. simpl in *. subst.
      destruct (LAS_block pinfo lasinfo).
      assert (SI_alive':=SI_alive).
      destruct SI_alive' as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
      rewrite_env (
        (cs1 ++ [insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
                            (LAS_value pinfo lasinfo) (value_id (PI_id pinfo))
                            (PI_align pinfo)] ++
         LAS_tail pinfo lasinfo) ++
         insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
           (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3) in J1.
      eapply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=
        insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo) 
          (value_id (PI_id pinfo)) (PI_align pinfo)) in J1; 
        eauto using in_middle.
      simpl in J1. rewrite <- e in HbInF. 
      rewrite HbInF in J1. inv J1. auto.

  subst.

  assert (block_intro l' ps' 
              (cs' ++ insn_load (LAS_lid pinfo lasinfo) 
                            (PI_typ pinfo) (value_id (PI_id pinfo))
                            (PI_align pinfo) :: CurCmds) Terminator = 
              SI_block pinfo stinfo) as Heq.
      clear H Hinscope HeqR Hreach.
      assert (In 
        (LAS_lid pinfo lasinfo)
        (getBlockIDs
          (block_intro l' ps'
            (cs' ++
              insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
              (value_id (PI_id pinfo)) (PI_align pinfo) :: CurCmds)
            Terminator))) as Hin.
        simpl.
        rewrite getCmdsIDs_app.
        simpl. 
        rewrite_env ((getPhiNodesIDs ps' ++ getCmdsIDs cs') ++ 
                      LAS_lid pinfo lasinfo :: getCmdsIDs CurCmds).
        apply in_middle.

      apply inGetBlockIDs__lookupBlockViaIDFromFdef with 
        (id1:=LAS_lid pinfo lasinfo) in HbInF; auto.
      clear Hin.

      destruct stinfo. simpl in *. subst.
      destruct (LAS_block pinfo lasinfo).
      assert (SI_alive':=SI_alive).
      destruct SI_alive' as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
      assert (In (LAS_lid pinfo lasinfo)
        (getBlockIDs
          (block_intro l1 p
             (cs1 ++
              insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
                (LAS_value pinfo lasinfo) (value_id (PI_id pinfo))
                (PI_align pinfo)
              :: (LAS_tail pinfo lasinfo ++
                  [insn_load (LAS_lid pinfo lasinfo) 
                     (PI_typ pinfo) (value_id (PI_id pinfo)) 
                     (PI_align pinfo)]) ++ cs3) t))) as Hin.
        simpl.
        apply in_or_app. right.
        rewrite getCmdsIDs_app.
        apply in_or_app. right.
        simpl. rewrite getCmdsIDs_app.
        apply in_or_app. left.
        rewrite getCmdsIDs_app. simpl.
        apply in_middle.

      apply inGetBlockIDs__lookupBlockViaIDFromFdef with 
        (id1:=LAS_lid pinfo lasinfo) in J1; auto.
      clear Hin.

      rewrite HbInF in J1. inv J1. auto.

  assert (alive_store.wf_defs pinfo stinfo (los,nts) M gl Locals) as G.
    clear Hinscope Hreach.
    apply H; auto.
      clear H.
      destruct stinfo. simpl in *. subst.
      destruct (LAS_block pinfo lasinfo).
      assert (SI_alive':=SI_alive).
      destruct SI_alive' as [J1 [J2 [cs1 [cs3 J3]]]]; subst.
      inv Heq.
      assert (
          cs' = cs1 ++
                insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
                  (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
                  (PI_align pinfo) :: (LAS_tail pinfo lasinfo) /\
          CurCmds = cs3
          ) as EQ.
        clear - H2 Hnodup.
        rewrite_env (
          (cs1 ++
          insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
            (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
            (PI_align pinfo)
          :: LAS_tail pinfo lasinfo) ++
          insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
              (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3) in H2.
        apply NoDup_cmds_split_middle in H2; auto.

      destruct EQ; subst. clear H2.
      unfold follow_alive_store. simpl.
      intros.
      assert (cs1 = cs0 /\ cs3 = cs2) as EQ.
        clear - H Hnodup.  
        rewrite_env (
          (cs1 ++
          insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
            (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
            (PI_align pinfo)
          :: LAS_tail pinfo lasinfo) ++
          insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
              (value_id (PI_id pinfo)) (PI_align pinfo) :: cs3) in H.
        rewrite_env (
          (cs0 ++
          insn_store (LAS_sid pinfo lasinfo) (PI_typ pinfo)
            (LAS_value pinfo lasinfo) (value_id (PI_id pinfo)) 
            (PI_align pinfo)
          :: LAS_tail pinfo lasinfo) ++
          insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
              (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2) in H.
        apply NoDup_cmds_split_middle in H; auto.
        destruct H as [H1 H2].
        split; auto.
          apply app_inv_tail in H1; auto.

      destruct EQ; subst. clear H.
      exists (LAS_tail pinfo lasinfo).
      exists ([insn_load (LAS_lid pinfo lasinfo) (PI_typ pinfo)
                   (value_id (PI_id pinfo)) (PI_align pinfo)]).
      auto.

  simpl.
  unfold alive_store.wf_defs in G.
  assert (exists gvsa, exists gvsv,
    lookupAL (GVsT DGVs) Locals (PI_id pinfo) = ret gvsa /\
    Opsem.getOperandValue (los,nts) (SI_value pinfo stinfo) Locals gl =
      ret gvsv) as G2.
    admit. (* wf domination *)
  destruct G2 as [gvsa [gvsv [G3 G2]]].
  exists gvsa. exists gvsa. exists gvsv.
  split; auto.
  split; auto.
    rewrite <- J2 in HeqR0.
    rewrite G2 in HeqR0. inv HeqR0.
    eapply G in G2; eauto.

  Case "LAS_lid >> LAS_value".
    simpl.
    remember (lookupAL (GVsT DGVs) Locals (LAS_lid pinfo lasinfo)) as R.
    destruct R; auto.
    remember (LAS_value pinfo lasinfo) as R.
    destruct R; auto.
    destruct (i0 == getCmdLoc c); subst; auto.
    admit. (* LAS_value >> LAS_lid, cyclic! *)   
Qed.

Lemma las__alive_store__vev_ECStack: forall pinfo lasinfo los nts M gl ifs ps s
  (Hwfs: wf_system ifs s) stinfo Hp 
  (HmInS: moduleInSystemB (module_intro los nts ps) s = true)
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo)
  ECs (Hwfpp: OpsemPP.wf_ECStack (los,nts) ps ECs),
  alive_store.wf_ECStack pinfo stinfo (los,nts) M gl ECs -> 
  vev_ECStack (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo) 
    (PI_f pinfo) (los,nts) M gl ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct H as [J1 J2].
    destruct Hwfpp as [HwfEC [HwfStk Hwfcall]].
    split; eauto.
      eapply las__alive_store__vev_EC; eauto.
Qed.

Lemma las__alive_store__vev: forall pinfo lasinfo cfg S 
  (Hwfpp: OpsemPP.wf_State cfg S) stinfo Hp
  (Hlas2st : exist _ stinfo Hp = lasinfo__stinfo pinfo lasinfo),
  alive_store.wf_State pinfo stinfo cfg S -> 
  vev_State (value_id (LAS_lid pinfo lasinfo)) (LAS_value pinfo lasinfo) 
    (PI_f pinfo) cfg S.
Proof.
  intros.
  destruct cfg, S.
  destruct CurTargetData as [los nts].
  destruct Hwfpp as [Hwfg [Hwfs [HmInS [Hnempty Hstks]]]].
  unfold alive_store.wf_State in H.
  simpl in H. simpl.
  eapply las__alive_store__vev_ECStack; eauto.
Qed.

Definition fdef_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) f1 f2
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    subst_fdef (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    List.map (subst_cmd (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo)) cs1 
      = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) f1 b1 b2
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
    subst_block (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) Ps1 Ps2
  : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo lasinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) S1 S2
  : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo lasinfo Ps1 Ps1
   end) S1 S2.

Definition phis_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  ps1 ps2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    List.map (subst_phi (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo)) ps1 
      = ps2
  else ps1 = ps2.

Definition tmn_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  t t': Prop :=
if (fdef_dec (PI_f pinfo) f1) then 
  subst_tmn (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) t = t'
else t = t'.

Definition EC_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) 
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo lasinfo f1 f2 /\
       tmn_simulation pinfo lasinfo f1 tmn1 tmn2 /\
       als1 = als2 /\
       block_simulation pinfo lasinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo lasinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) 
  (ECs1 ECs2:@Opsem.ECStack DGVs) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo lasinfo EC1 EC2 /\ 
    ECs_simulation pinfo lasinfo ECs1' ECs2'
| _, _ => False
end.

Definition State_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo lasinfo Ps1 Ps2 /\
    ECs_simulation pinfo lasinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

Lemma cmds_simulation_nil_inv: forall pinfo lasinfo f1 cs,
  cmds_simulation pinfo lasinfo f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

Definition cmd_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  c c': Prop :=
if (fdef_dec (PI_f pinfo) f1) then 
  subst_cmd (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) c = c'
else c = c'.

Lemma cmds_simulation_cons_inv: forall pinfo lasinfo F c1 cs2 cs',
  cmds_simulation pinfo lasinfo F (c1 :: cs2) cs' ->
  exists c1', exists cs2', 
    cs' = c1' :: cs2' /\
    cmd_simulation pinfo lasinfo F c1 c1' /\
    cmds_simulation pinfo lasinfo F cs2 cs2'.
Proof.  
  intros.
  unfold cmds_simulation, cmd_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
Qed.

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
  HwfS1 : wf_State _ _ _ _ _,
  Hsim : State_simulation _ _ _ _ ?Cfg2 ?St2 ,
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
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 EQ4]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  destruct ECs2 as [|[F3 B3 cs3 tmn3 lc3 als3] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim' Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Htsim2 [Heq2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hecsim' as 
      [Hfsim2' [Htsim2' [Heq2' [Hbsim2' 
        [Heq3' [Heq4' [Hlcsim2' Hcssim2']]]]]]]; subst;
  destruct HwfS1 as [Hinscope1' [Hinscope2' HwfECs']];
  fold wf_ECStack in HwfECs';
  unfold wf_ExecutionContext in Hinscope1', Hinscope2';
  simpl in Hinscope1', Hinscope2';
  apply cmds_simulation_nil_inv in Hcssim2; subst;
  apply cmds_simulation_cons_inv in Hcssim2'; 
  destruct Hcssim2' as [c1' [cs3' [Heq [Hcsim2' Hcssim2']]]]; subst
end.

Lemma fdef_sim__block_sim : forall pinfo lasinfo f1 f2 b1 b2 l0,
  fdef_simulation pinfo lasinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  block_simulation pinfo lasinfo f1 b1 b2.
Admitted.

Lemma block_simulation_inv : forall pinfo lasinfo F l1 ps1 cs1 tmn1 l2 ps2 cs2
  tmn2,
  block_simulation pinfo lasinfo F (block_intro l1 ps1 cs1 tmn1)
    (block_intro l2 ps2 cs2 tmn2) ->
  l1 = l2 /\ 
  phis_simulation pinfo lasinfo F ps1 ps2 /\ 
  cmds_simulation pinfo lasinfo F cs1 cs2 /\ 
  tmn_simulation pinfo lasinfo F tmn1 tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation, phis_simulation, tmn_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); inv H; auto.
Qed.

Definition value_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  v v': Prop :=
if (fdef_dec (PI_f pinfo) f1) then 
  subst_value (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) v = v'
else v = v'.

Lemma getOperandValue_inTmnOperands_sim : forall los nts ifs s ps gl pinfo 
  lasinfo (f : fdef) (Hwfg : wf_global (los,nts) s gl) 
  (HwfF: wf_fdef ifs s (module_intro los nts ps) f)
  (tmn : terminator)
  (lc : GVMap)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (Hinscope : id_rhs_val.wf_defs (value_id (LAS_lid pinfo lasinfo))
                     (LAS_value pinfo lasinfo) (PI_f pinfo) 
                     (los, nts) gl f lc l0)
  (v v' : value)
  (Hvincs : valueInTmnOperands v tmn) gv gv'
  (Hget' : getOperandValue (los, nts) v' lc gl = Some gv')
  (Hvsim : value_simulation pinfo lasinfo f v v')
  (Hget : getOperandValue (los, nts) v lc gl = Some gv),
  gv = gv'.
Proof.
  intros.
  unfold value_simulation in Hvsim.
  unfold wf_defs in Hinscope.
  destruct (fdef_dec (PI_f pinfo) f); subst; try solve [uniq_result; auto].
  destruct v; subst; simpl in Hget', Hget, Hinscope;
    try solve [uniq_result; auto].
  destruct (id_dec i0 (LAS_lid pinfo lasinfo)); simpl in Hget'; subst;
    try solve [uniq_result; auto].  
  eapply Hinscope in Hget; eauto.
    admit. (* wf *)
    admit. (* wf + v >> lid *)
Qed.

Lemma getOperandValue_inCmdOperands_sim : forall los nts ifs s gl pinfo lasinfo
  ps (f : fdef) (Hwfg : wf_global (los,nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts ps) f)
  (tmn : terminator)
  (lc : GVMap)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 cs : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : id_rhs_val.wf_defs (value_id (LAS_lid pinfo lasinfo))
                     (LAS_value pinfo lasinfo) (PI_f pinfo) 
                     (los, nts) gl f lc l0)
  (v v' : value)
  (Hvincs : valueInCmdOperands v c) gv gv'
  (Hget' : getOperandValue (los, nts) v' lc gl = Some gv')
  (Hvsim : value_simulation pinfo lasinfo f v v')
  (Hget : getOperandValue (los, nts) v lc gl = Some gv),
  gv = gv'.
Proof.
  intros.
  unfold value_simulation in Hvsim.
  unfold wf_defs in Hinscope.
  destruct (fdef_dec (PI_f pinfo) f); subst; try solve [uniq_result; auto].
  destruct v; subst; simpl in Hget', Hget, Hinscope;
    try solve [uniq_result; auto].
  destruct (id_dec i0 (LAS_lid pinfo lasinfo)); simpl in Hget'; subst;
    try solve [uniq_result; auto].  
  eapply Hinscope in Hget; eauto.
    admit. (* wf *)
    admit. (* wf + v >> lid *)
Qed.

Lemma phis_simulation_nil_inv: forall pinfo lasinfo f1 ps,
  phis_simulation pinfo lasinfo f1 nil ps -> ps = nil.
Proof.
  unfold phis_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

Definition phi_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  p1 p2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    subst_phi (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) p1 = p2
  else p1 = p2.

Lemma phis_simulation_cons_inv: forall pinfo lasinfo F p1 ps2 ps',
  phis_simulation pinfo lasinfo F (p1 :: ps2) ps' ->
  exists p1', exists ps2', 
    ps' = p1' :: ps2' /\
    phi_simulation pinfo lasinfo F p1 p1' /\
    phis_simulation pinfo lasinfo F ps2 ps2'.
Proof.  
  intros.
  unfold phis_simulation, phi_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
Qed.

Definition list_value_l_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) 
  (f1:fdef) vls vls': Prop :=
if (fdef_dec (PI_f pinfo) f1) then 
  subst_list_value_l (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) vls = vls'
else vls = vls'.

Lemma phi_simulation_inv: forall pinfo lasinfo f1 i1 t1 vls1 i2 t2 vls2,
  phi_simulation pinfo lasinfo f1 (insn_phi i1 t1 vls1) (insn_phi i2 t2 vls2) ->
  i1 = i2 /\ t1 = t2 /\ list_value_l_simulation pinfo lasinfo f1 vls1 vls2.
Proof.
  unfold phi_simulation, list_value_l_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f1); inv H; auto.
Qed.

Lemma getValueViaLabelFromValuels_sim : forall l1 pinfo lasinfo f1 vls1 vls2 v 
  v' (Hsim: list_value_l_simulation pinfo lasinfo f1 vls1 vls2)
  (HeqR0 : ret v = getValueViaLabelFromValuels vls1 l1)
  (HeqR' : ret v' = getValueViaLabelFromValuels vls2 l1),
  value_simulation pinfo lasinfo f1 v v'.
Proof.
  induction vls1; simpl; intros; try congruence.
    unfold list_value_l_simulation, value_simulation in *.
    destruct (fdef_dec (PI_f pinfo) f1); subst.
      simpl in HeqR'.
      destruct (l0 == l1); subst; eauto.
        congruence.

    simpl in HeqR'.
    destruct (l0 == l1); subst; try (congruence || eauto).
Qed.

Lemma getValueViaLabelFromValuels_getOperandValue_sim : forall
  los nts ifs s gl pinfo lasinfo
  ps (f : fdef) (Hwfg : wf_global (los,nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts ps) f) (HuniqF: uniqFdef f)
  (l0 : l) (lc : GVMap) (t : list atom) (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator) 
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : id_rhs_val.wf_defs (value_id (LAS_lid pinfo lasinfo))
                     (LAS_value pinfo lasinfo) (PI_f pinfo) 
                     (los, nts) gl f lc t)
  (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (i0 : id) (l2 : list_value_l) (ps2 : list phinode)
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (Hreach' : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (v0 v0': value)
  (HeqR3 : ret v0 = getValueViaLabelFromValuels l2 l1)
  (g1 : GenericValue) 
  (HeqR4 : ret g1 = getOperandValue (los,nts) v0 lc gl)
  (g2 : GVMap) (g : GenericValue) (g0 : GVMap) t1
  (H1 : wf_value_list
         (make_list_system_module_fdef_value_typ
            (map_list_value_l
               (fun (value_ : value) (_ : l) =>
                (s, module_intro los nts ps, f, value_, t1)) l2)))
  (H7 : wf_phinode f (block_intro l0 ps' cs' tmn') (insn_phi i0 t1 l2))
  (Hvsim: value_simulation pinfo lasinfo f v0 v0')
  (HeqR1 : ret g = getOperandValue (los,nts) v0' lc gl),
  g1 = g.
Proof.
  intros. symmetry_ctx.
  unfold value_simulation in Hvsim.
  destruct (fdef_dec (PI_f pinfo) f); subst; try solve [uniq_result; auto].
  destruct v0 as [vid | vc]; simpl in HeqR1, HeqR4; try congruence.
  destruct (id_dec vid (LAS_lid pinfo lasinfo)); subst; simpl in HeqR1; 
    try congruence.
  destruct H7 as [Hwfops Hwfvls].
  assert (Hnth:=HeqR3).
  eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
  destruct Hnth as [n Hnth].
  assert (HwfV:=HeqR3).
  eapply wf_value_list__getValueViaLabelFromValuels__wf_value in HwfV; eauto.
  eapply wf_phi_operands__elim in Hwfops; eauto.
  destruct Hwfops as [vb [b1 [Hlkvb [Hlkb1 Hdom]]]].
  assert (b1 = block_intro l1 ps1 cs1 tmn1) as EQ.
    clear - Hlkb1 HbInF HwfF HuniqF.
    apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
    rewrite HbInF in Hlkb1. inv Hlkb1; auto.
  subst.
  clear Hwfvls HwfV Hnth.
  destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
  clear Hreach.
  unfold blockDominates in J3.         
  destruct vb. assert (HeqR':=HeqR).
  unfold inscope_of_tmn in HeqR.
  destruct (PI_f pinfo) as [[f t2 i1 a v] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t2 i1 a v) bs)) !! l1) 
    as R1.
  destruct R1.
  apply fold_left__spec in HeqR.
  destruct (eq_atom_dec l3 l1); subst.
  Case "l3=l1".
    destruct HeqR as [HeqR _].
    assert (In (LAS_lid pinfo lasinfo) t) as Hid2InScope.
      clear - HeqR3 HeqR Hlkb1 J3 Hlkvb HbInF HwfF HuniqF.
      assert (J':=Hlkvb).
      apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
      apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto. 
      destruct Hlkb1 as [J1 J2].
      eapply blockInFdefB_uniq in J2; eauto.
      destruct J2 as [J2 [J4 J5]]; subst.
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
      simpl in J'.
      apply HeqR; auto.
      admit. (* lid cannot be in args *)
    eapply Hinscope in HeqR1; eauto.
      admit. (* v >> lid *)
  
  Case "l3<>l1".
    assert (In l3 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as G.
      destruct J3 as [J3 | J3]; subst; try congruence.
      apply ListSet.set_diff_intro; auto.
        simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
    assert (
      lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t2 i1 a v) bs) l3 
        = ret block_intro l3 p c t0) as J1.
      clear - Hlkvb HwfF HuniqF.
      apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
      apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkvb; auto.
    destruct HeqR as [_ [HeqR _]].
    apply HeqR in J1; auto.
    assert (In (LAS_lid pinfo lasinfo) t) as Hid2InScope.
      clear - J1 HeqR Hlkb1 J3 Hlkvb HbInF HwfF HuniqF.
      apply J1.
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
    eapply Hinscope in HeqR1; eauto.
      admit. (* v >> lid *)
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall
  los nts ifs s gl pinfo lasinfo
  ps (f : fdef) (Hwfg : wf_global (los,nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts ps) f) (HuniqF: uniqFdef f)
  l0
  (lc : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1 
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : id_rhs_val.wf_defs (value_id (LAS_lid pinfo lasinfo))
                     (LAS_value pinfo lasinfo) (PI_f pinfo) 
                     (los, nts) gl f lc t)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (Hreach' : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block ifs s (module_intro los nts ps) f 
            (block_intro l1 ps1 cs1 tmn1))
  B1' 
  (Hbsim1: block_simulation pinfo lasinfo f (block_intro l1 ps1 cs1 tmn1) B1')  
  ps2
  (H8 : wf_phinodes ifs s (module_intro los nts ps) f 
          (block_intro l0 ps' cs' tmn') ps2)
  (Hin: exists ps1, ps' = ps1 ++ ps2) RVs RVs' ps2'
  (Hpsim2: phis_simulation pinfo lasinfo f ps2 ps2')
  (Hget : @Opsem.getIncomingValuesForBlockFromPHINodes DGVs (los,nts) ps2 
           (block_intro l1 ps1 cs1 tmn1) gl lc = ret RVs)
  (Hget' : @Opsem.getIncomingValuesForBlockFromPHINodes DGVs (los,nts)
             ps2' B1' gl lc = ret RVs'),
  RVs = RVs'.
Proof.
  induction ps2 as [|[]]; intros; simpl in Hget, Hget'.
    apply phis_simulation_nil_inv in Hpsim2.
    subst. simpl in Hget'. congruence.    

    apply phis_simulation_cons_inv in Hpsim2.
    destruct Hpsim2 as [p1' [ps2'0 [Heq [Hpsim1 Hpsim2]]]]; subst.
    simpl in Hget'. destruct p1'. 
    apply phi_simulation_inv in Hpsim1.
    destruct Hpsim1 as [Heq1 [Heq2 Hvlsim1]]; subst.
    inv_mbind'. 
    destruct B1'. simpl in HeqR0.
    apply block_simulation_inv in Hbsim1.
    destruct Hbsim1 as [Heq [Hpsim1 [Hcssim1 Htsim1]]]; subst.
    simpl in HeqR3.
    eapply getValueViaLabelFromValuels_sim in Hvlsim1; eauto.
    inv H8. 
    assert (g = g0) as Heq.
      inv H6.
      eapply getValueViaLabelFromValuels_getOperandValue_sim with (l0:=l0); 
        eauto.
    subst. 
    eapply IHps2 with (RVs:=l4) in H7; eauto.
      congruence.

      destruct Hin as [ps3 Hin]. subst.
      exists (ps3++[insn_phi i1 t1 l2]).
      simpl_env. auto.
Qed.

Lemma switchToNewBasicBlock_sim : forall
  los nts ifs s gl pinfo lasinfo
  ps (f : fdef) (Hwfg : wf_global (los,nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts ps) f) (HuniqF: uniqFdef f)
  l2 (lc : GVMap) (t : list atom) l1 ps1 cs1 tmn1
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : id_rhs_val.wf_defs (value_id (LAS_lid pinfo lasinfo))
                     (LAS_value pinfo lasinfo) (PI_f pinfo) 
                     (los, nts) gl f lc t)
  (ps2 : phinodes) (cs2 : cmds) (tmn2 : terminator)
  (Hsucc : In l2 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (block_intro l2 ps2 cs2 tmn2))
  (Hreach' : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (HbInF' : blockInFdefB (block_intro l2 ps2 cs2 tmn2) f = true)
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  lc0 lc0'
  (Hget : @Opsem.switchToNewBasicBlock DGVs (los,nts) 
    (block_intro l2 ps2 cs2 tmn2) 
    (block_intro l1 ps1 cs1 tmn1) gl lc = ret lc0) B1' B2'
  (Hbsim1: block_simulation pinfo lasinfo f (block_intro l1 ps1 cs1 tmn1) B1')  
  (Hbsim2: block_simulation pinfo lasinfo f (block_intro l2 ps2 cs2 tmn2) B2')
  (Hget' : @Opsem.switchToNewBasicBlock DGVs (los,nts) B2' B1' gl lc = ret lc0'),
  lc0 = lc0'.
Proof.
  intros.
  assert (HwfB : wf_block ifs s (module_intro los nts ps) f 
           (block_intro l1 ps1 cs1 tmn1)).
    apply wf_fdef__blockInFdefB__wf_block; auto.
  assert (H8 : wf_phinodes ifs s (module_intro los nts ps) f 
                 (block_intro l2 ps2 cs2 tmn2) ps2).
    apply wf_fdef__wf_phinodes; auto.
  unfold Opsem.switchToNewBasicBlock in *.
  inv_mbind'. app_inv. symmetry_ctx.
  assert (l3 = l0) as EQ.
    destruct B2'.
    apply block_simulation_inv in Hbsim2.
    destruct Hbsim2 as [J1 [J2 [J3 J4]]]; subst.
    eapply getIncomingValuesForBlockFromPHINodes_sim; eauto.
      exists nil. auto.
  subst. auto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  HwfS1 : wf_State _ _ _ _ _,
  Hsim : State_simulation _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [HwfECs Hwfcall]]
    ]]]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 EQ4]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Htsim2 [Heq2 [Hbsim2 
        [[l3 [ps3 [cs31 Heq3]]]
        [[l4 [ps4 [cs41 Heq4]]] [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct HwfS1 as [Hinscope1' HwfECs'];
  fold wf_ECStack in HwfECs';
  unfold wf_ExecutionContext in Hinscope1';
  simpl in Hinscope1'
end.

Lemma cmds_at_block_tail_next': forall l3 ps3 cs31 c cs tmn,
  exists l1, exists ps1, exists cs11,
         block_intro l3 ps3 (cs31 ++ c :: cs) tmn =
         block_intro l1 ps1 (cs11 ++ cs) tmn.
Proof.
  intros.
  exists l3. exists ps3. exists (cs31++[c]). simpl_env. auto.
Qed.

Definition pars_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  (ps1 ps2:params) : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    (List.map 
      (fun p => 
       let '(t, v):=p in 
       (t, subst_value (LAS_lid pinfo lasinfo) (LAS_value pinfo lasinfo) v)) ps1)
    = ps2
  else ps1 = ps2.

Lemma products_simulation__fdef_simulation : forall pinfo lasinfo Ps1 Ps2 fid f1 
  f2,
  lookupFdefViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  products_simulation pinfo lasinfo Ps1 Ps2 ->
  fdef_simulation pinfo lasinfo f1 f2.
Admitted.

Lemma lookupFdefViaPtr__simulation : forall pinfo lasinfo Ps1 Ps2 fptr f1 f2 fs,
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 ->
  products_simulation pinfo lasinfo Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  fdef_simulation pinfo lasinfo f1 f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; inv H1. simpl in H.
  eapply products_simulation__fdef_simulation in H0; eauto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall pinfo lasinfo F1 F2 B1 B2,
  fdef_simulation pinfo lasinfo F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation pinfo lasinfo F1 B1 B2.
Admitted.

Lemma fdef_simulation_inv: forall pinfo lasinfo fh1 fh2 bs1 bs2,
  fdef_simulation pinfo lasinfo (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\ 
  List.Forall2 
    (fun b1 b2 => block_simulation pinfo lasinfo (fdef_intro fh1 bs1) b1 b2) 
    bs1 bs2.
Admitted.

Lemma pars_simulation_nil_inv: forall pinfo lasinfo f1 ps,
  pars_simulation pinfo lasinfo f1 nil ps -> ps = nil.
Proof.
  unfold pars_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

Definition par_simulation (pinfo: PhiInfo) (lasinfo: LASInfo pinfo) (f1:fdef)
  (p p':typ * attributes * value) : Prop :=
if (fdef_dec (PI_f pinfo) f1) then 
  let '(t, v) := p in
  (t, v {[LAS_value pinfo lasinfo // LAS_lid pinfo lasinfo]}) = p'
else p = p'.

Lemma pars_simulation_cons_inv: forall pinfo lasinfo F p1 ps2 ps',
  pars_simulation pinfo lasinfo F (p1 :: ps2) ps' ->
  exists p1', exists ps2', 
    ps' = p1' :: ps2' /\
    par_simulation pinfo lasinfo F p1 p1' /\
    pars_simulation pinfo lasinfo F ps2 ps2'.
Proof.  
  intros.
  unfold pars_simulation, par_simulation in *.
  destruct p1.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
Qed.

Lemma par_simulation__value_simulation: forall pinfo lasinfo F t1 v1 t2 v2,
  par_simulation pinfo lasinfo F (t1,v1) (t2,v2) ->
  value_simulation pinfo lasinfo F v1 v2.
Proof.
  unfold par_simulation, value_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); inv H; auto.
Qed.

Lemma params2GVs_sim_aux : forall
  (s : system) pinfo lasinfo 
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  n c t v p2
  (cs : list cmd)
  (tmn : terminator)
  lc (gl : GVMap) ifs
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts ps) f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn)
           (insn_call i0 n c t v p2))
  (Hinscope : id_rhs_val.wf_defs (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) (los, nts) gl f lc l0)
  p22 p22' gvs gvs'
  (Hex : exists p21, p2 = p21 ++ p22)
  (Hp2gv : Opsem.params2GVs (los, nts) p22 lc gl = Some gvs)
  (Hp2gv' : Opsem.params2GVs (los, nts) p22' lc gl = Some gvs')
  (Hpasim : pars_simulation pinfo lasinfo f p22 p22'),
  gvs = gvs'.
Proof.
  induction p22; simpl; intros; eauto.
    apply pars_simulation_nil_inv in Hpasim. subst.
    simpl in *. congruence.

    destruct a as [[t0 attr0] v0].
    destruct Hex as [p21 Hex]; subst. 
    apply pars_simulation_cons_inv in Hpasim. 
    destruct Hpasim as [p1' [ps2' [EQ [Hpsim' Hpasim']]]]; subst.
    simpl in *. destruct p1'.
    inv_mbind'.
    
    assert (g0 = g) as Heq.
      apply par_simulation__value_simulation in Hpsim'.
      eapply getOperandValue_inCmdOperands_sim in Hpsim'; eauto.
        simpl. unfold valueInParams. right. 
        assert (J:=@in_split_r _ _ (p21 ++ (t0, attr0, v0) :: p22) 
          (t0, attr0, v0)).
        remember (split (p21 ++ (t0, attr0, v0) :: p22)) as R.
        destruct R.
        simpl in J. apply J.
        apply In_middle.
    subst.
    erewrite <- IHp22 with (gvs':=l2); eauto.
      exists (p21 ++ [(t0, attr0,v0)]). simpl_env. auto.
Qed.

Lemma params2GVs_sim : forall
  (s : system) pinfo lasinfo 
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  n c t v p2
  (cs : list cmd)
  (tmn : terminator)
  lc (gl : GVMap) ifs
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts ps) f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn)
           (insn_call i0 n c t v p2))
  (Hinscope : id_rhs_val.wf_defs (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) (los, nts) gl f lc l0)
  p2' gvs gvs'
  (Hp2gv : Opsem.params2GVs (los, nts) p2 lc gl = Some gvs)
  (Hp2gv' : Opsem.params2GVs (los, nts) p2' lc gl = Some gvs')
  (Hpasim : pars_simulation pinfo lasinfo f p2 p2'),
  gvs = gvs'.
Proof.
  intros.
  eapply params2GVs_sim_aux; eauto.
    exists nil. auto.
Qed.

Lemma lookupFdefViaPtr__simulation_l2r : forall pinfo lasinfo Ps1 Ps2 fptr f1 fs,
  products_simulation pinfo lasinfo Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  exists f2, 
    OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 /\
    fdef_simulation pinfo lasinfo f1 f2.
Admitted.

Lemma lookupExFdecViaPtr__simulation_l2r : forall pinfo lasinfo Ps1 Ps2 fptr f fs,
  products_simulation pinfo lasinfo Ps1 Ps2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs fptr = Some f ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs fptr = Some f.
Admitted.

Lemma las_is_sim : forall pinfo lasinfo Cfg1 St1 Cfg2 St2 St2' tr2 tr1 St1'
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (HwfS1: id_rhs_val.wf_State (value_id (LAS_lid pinfo lasinfo)) 
           (LAS_value pinfo lasinfo) (PI_f pinfo) Cfg1 St1)
  (Hsim: State_simulation pinfo lasinfo Cfg1 St1 Cfg2 St2)
  (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
  (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
  State_simulation pinfo lasinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2.
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  (sInsn_cases (destruct Hop1) Case).

Case "sReturn".

  destruct_ctx_return.

  assert (exists Result2,
    tmn2 = insn_return rid RetTy Result2 /\ 
    value_simulation pinfo lasinfo F Result Result2) as Hreturn.
    clear - Htsim2.
    unfold value_simulation, tmn_simulation in *.
    destruct (fdef_dec (PI_f pinfo) F); inv Htsim2; eauto.
  destruct Hreturn as [Result2 [EQ Hvsim2]]; subst.

  inv Hop2.

  match goal with
  | H0 : free_allocas ?td ?M ?las = _,
    H26 : free_allocas ?td ?M ?las = _ |- _ =>
      rewrite H0 in H26; inv H26
  end.
  wfCall_inv.

  assert (lc'' = lc''0) as EQ.
    clear - H27 H1 Hcsim2' Hvsim2 Hinscope1' HwfSystem HmInS Hreach1 HBinF1 
      HFinPs1 Hwfg.
    unfold Opsem.returnUpdateLocals in H1, H27.
    inv_mbind'.
    destruct c1'; tinv H0.
    assert (i0 = i1 /\ n = n0 /\ t0 = t) as EQ.
      unfold cmd_simulation in Hcsim2';
      destruct (fdef_dec (PI_f pinfo) F'); inv Hcsim2'; auto.
    destruct EQ as [Heq1 [Heq2 Heq3]]; subst.
    destruct n0; try solve [inv H0; inv H2; auto].
    destruct t; tinv H0.
    inv_mbind'.
    remember (inscope_of_tmn F
                   (block_intro l3 ps3 (cs3 ++ nil)
                      (insn_return rid RetTy Result))
                   (insn_return rid RetTy Result)) as R.
    destruct R; tinv Hinscope1'.
    symmetry_ctx.
    eapply getOperandValue_inTmnOperands_sim in HeqR0; eauto
      using wf_system__wf_fdef; simpl; auto.
    subst. uniq_result. auto.
    
  subst.
  repeat (split; eauto 2 using cmds_at_block_tail_next).

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


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
