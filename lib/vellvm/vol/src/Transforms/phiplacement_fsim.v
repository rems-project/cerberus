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
Require Import dtree.
Require Import primitives.
Require Import Maps.
Require Import mem2reg.
Require Import opsem_props.
Require Import promotable_props.
Require Import palloca_props.

Ltac zauto := auto with zarith.
Ltac zeauto := eauto with zarith.

Import Promotability.

(* Simulation *)

Definition DGVMap := @Opsem.GVsMap DGVs.

Definition reg_simulation (F:fdef) (lc1 lc2:DGVMap) : Prop :=
(forall i0 gv, 
  lookupAL _ lc1 i0 = Some gv -> lookupAL _ lc2 i0 = Some gv
) /\
(forall i0 gv1, lookupAL _ lc1 i0 = Some gv1 -> In i0 (getFdefLocs F)).

(* Copied from SB *)
Definition label_of_block (b:block) : l :=
match b with
| block_intro l1 _ _ _ => l1
end.

Definition fdef_simulation (pinfo: PhiInfo) f1 f2: Prop :=
  let '(mkPhiInfo f rd succs preds pid ty al _) := pinfo in
  if (fdef_dec f1 f) then 
    phinodes_placement f1 rd pid ty al succs preds = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (f1:fdef) (l1:l) cs1 cs2: Prop :=
  let '(mkPhiInfo f rd succs preds pid ty al newids) := pinfo in
  if (fdef_dec f1 f) then
     match ATree.get l1 (successors f1) with
     | Some (_::_) => 
        match ATree.get l1 newids with
        | Some (lid, _, _) => cs1 ++ [insn_load lid ty (value_id pid) al] = cs2
        | None => cs1 = cs2
        end
     | _ => cs1 = cs2
     end 
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) f1 b1 b2: Prop :=
  let '(mkPhiInfo f _ succs preds pid ty al newids) := pinfo in
  if (fdef_dec f1 f) then
     phinodes_placement_block pid ty al newids succs preds b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) Ps1 Ps2: Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) S1 S2: Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo Ps1 Ps1
   end) S1 S2.

Definition EC_simulation_head (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (EC1 EC2:Opsem.ExecutionContext) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(los, nts) := TD in
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\ als1 = als2 /\
       (label_of_block b1 = label_of_block b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       reg_simulation f1 lc1 lc2 /\
       cmds_simulation pinfo f1 (label_of_block b1) cs1 cs2
  end.

Definition EC_simulation_tail (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (EC1 EC2:Opsem.ExecutionContext) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 ((insn_call _ _ _ _ _ _ as c1)::cs1) tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(los, nts) := TD in
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\ als1 = als2 /\
       (label_of_block b1 = label_of_block b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++c1::cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       reg_simulation f1 lc1 lc2 /\
       cmds_simulation pinfo f1 (label_of_block b1) (c1::cs1) cs2
  | _ => False
  end.

Fixpoint ECs_simulation_tail (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (ECs1 ECs2:Opsem.ECStack) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation_tail TD Ps1 pinfo EC1 EC2 /\ 
    ECs_simulation_tail TD Ps1 pinfo ECs1' ECs2'
| _, _ => False
end.

Fixpoint ECs_simulation (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (ECs1 ECs2:Opsem.ECStack) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation_head TD Ps1 pinfo EC1 EC2 /\ 
    ECs_simulation_tail TD Ps1 pinfo ECs1' ECs2'
| _, _ => False
end.

Definition State_simulation (pinfo: PhiInfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    let '(los, nts) := TD1 in
    wf_system nil S1 /\
    moduleInSystemB (module_intro los nts Ps1) S1 = true /\
    system_simulation pinfo S1 S2 /\ 
    TD1 = TD2 /\ 
    products_simulation pinfo Ps1 Ps2 /\
    ECs_simulation TD1 Ps1 pinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

Lemma cmds_simulation_nil_ret_inv: forall B F tmn pinfo cs2
  (HBinF : blockInFdefB B F = true)
  (Heq: exists l1, exists ps1, exists cs11,
          B = block_intro l1 ps1 (cs11 ++ nil) tmn)
  (Hsucc: successors_terminator tmn = nil)
  (Htcmds: cmds_simulation pinfo F (label_of_block B) nil cs2),
  cs2 = nil.
Admitted.

Lemma cmds_simulation_nil_br_inv: forall B F tmn pinfo cs2
  (HBinF : blockInFdefB B F = true)
  (Heq: exists l1, exists ps1, exists cs11,
          B = block_intro l1 ps1 (cs11 ++ nil) tmn)
  (Hsucc: successors_terminator tmn <> nil)
  (Htcmds: cmds_simulation pinfo F (label_of_block B) nil cs2),
  if fdef_dec F pinfo.(PI_f) then   
    match ATree.get (label_of_block B) pinfo.(PI_newids) with
    | None => cs2 = nil
    | Some (lid', _, _) =>
        cs2 = [insn_load lid' pinfo.(PI_typ) (value_id pinfo.(PI_id)) 
                pinfo.(PI_align)]
    end
  else
    cs2 = nil.
Admitted.

Lemma cmds_simulation_cons_inv: forall B F pinfo c cs1 cs2
  (Htcmds: cmds_simulation pinfo F (label_of_block B) (c::cs1) cs2),
  exists cs2', 
    cs2 = c::cs2' /\   
    cmds_simulation pinfo F (label_of_block B) cs1 cs2'.
Admitted.

Lemma lookup_fdef_sim__block_sim : forall pinfo f1 f2 l0 b1,
  fdef_simulation pinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  exists b2,
    lookupBlockViaLabelFromFdef f2 l0 = Some b2 /\
    block_simulation pinfo f1 b1 b2.
Admitted.

Lemma simulation__getOperandValue: forall TD v lc gl2 lc2 g F
  (HeqR : Opsem.getOperandValue TD v lc gl2 = ret g)
  (Hrsim : reg_simulation F lc lc2),
  Opsem.getOperandValue TD v lc2 gl2 = ret g.
Proof.
  intros.
  destruct Hrsim as [J1 _].
  destruct v; auto.
    apply J1 in HeqR; auto.
Qed.

Lemma returnUpdateLocals_rsim : forall TD i0 n c t v p Result lc lc' gl2 
  lc'' F F' lc2' lc2
  (H1 : Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc
         lc' gl2 = ret lc'')
  (Hrsim : reg_simulation F lc lc2)
  (Hrsim' : reg_simulation F' lc' lc2'),
  exists lc2'',
    Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc2 lc2' gl2 
      = ret lc2'' /\ reg_simulation F' lc'' lc2''.
Proof.
  unfold Opsem.returnUpdateLocals in *.
  intros.
  remember (Opsem.getOperandValue TD Result lc gl2) as R.
  destruct R; inv H1.
    destruct n; inv H0.
    erewrite simulation__getOperandValue; eauto. 

    destruct t; tinv H1.
    erewrite simulation__getOperandValue; eauto. 
    destruct (lift_op1 DGVs (fit_gv TD t) g t); inv H1.
    exists (updateAddAL (GVsT DGVs) lc2' i0 g0).
    split; auto.
      destruct Hrsim' as [J1 J2].
      split; intros.
        destruct (id_dec i0 i1); subst.
          rewrite lookupAL_updateAddAL_eq.
          rewrite lookupAL_updateAddAL_eq in H; auto.

          rewrite <- lookupAL_updateAddAL_neq; auto.
          rewrite <- lookupAL_updateAddAL_neq in H; auto.

        admit.
Qed.

(* copied from SB *)
Lemma cmds_at_block_tail_next : forall B c cs tmn2,
  (exists l1, exists ps1, exists cs11, B = 
    block_intro l1 ps1 (cs11 ++ c :: cs) tmn2) ->
  exists l1, exists ps1, exists cs11, B = block_intro l1 ps1 (cs11 ++ cs) tmn2.
Proof.
  intros.
  destruct H as [l1 [ps1 [cs11 H]]]; subst.
  exists l1. exists ps1. exists (cs11 ++ [c]). simpl_env. auto.
Qed.

Ltac destruct_ctx_br :=
match goal with
| [Hsim : State_simulation _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           Opsem.ECS := {|
                          Opsem.CurFunction := ?F;
                          Opsem.CurBB := _;
                          Opsem.CurCmds := nil;
                          Opsem.Terminator := _;
                          Opsem.Locals := _;
                          Opsem.Allocas := _ |} :: _;
           Opsem.Mem := _ |} ?Cfg2 ?St2 |- _] =>
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hnth [Heqb1 [Heqb2     
    [Hrsim Htcmds]]]]]]]]]; subst
end.

Ltac destruct_ctx_return :=
match goal with
| [Hsim : State_simulation _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           Opsem.ECS := {|
                          Opsem.CurFunction := ?F;
                          Opsem.CurBB := _;
                          Opsem.CurCmds := nil;
                          Opsem.Terminator := _;
                          Opsem.Locals := _;
                          Opsem.Allocas := _ |}
                          :: {|
                             Opsem.CurFunction := ?F';
                             Opsem.CurBB := _;
                             Opsem.CurCmds := ?c' :: _;
                             Opsem.Terminator := _;
                             Opsem.Locals := _;
                             Opsem.Allocas := _ |} :: _;
           Opsem.Mem := _ |} ?Cfg2 ?St2 |- _] =>
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct ECs2 as [|[F2' B2' cs2' tmn2' lc2' als2'] ECs2];
    try solve [inversion HsimECs];
  destruct HsimECs as [HsimEC' HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hnth [Heqb1 [Heqb2     
    [Hrsim Htcmds]]]]]]]]]; subst;
  destruct c'; try solve [inversion HsimEC'];
  destruct HsimEC' as [HBinF' [HFinPs' [Htfdef' [Heq0' [Heq1' [Hnth' 
    [Heqb1' [Heqb2' [Hrsim' Htcmds']]]]]]]]]; subst
end.

Notation "$ gv # t $" := (DGVs.(gv2gvs) gv t) (at level 41).

Definition noalias_EC (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (ec:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
if (fdef_dec (PI_f pinfo) f) then wf_defs maxb pinfo TD M lc als else True.

Lemma phinodes_placement_is_correct__sBranch: forall 
  (pinfo : PhiInfo) (Cfg2 : OpsemAux.Config) (St2 : Opsem.State)
  (S : system) (TD : TargetData) (Ps : list product) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (bid : id) (Cond : value)
  (l1 : l) (l2 : l) (ECs : list Opsem.ExecutionContext) (Mem : mem) 
  (als : list mblock) maxb EC1 Cfg1 (Hwfpi: WF_PhiInfo pinfo)
  (Heq1: Cfg1 = {| OpsemAux.CurSystem := S;
                   OpsemAux.CurTargetData := TD;
                   OpsemAux.CurProducts := Ps;
                   OpsemAux.Globals := gl;
                   OpsemAux.FunTable := fs |})
  (Hnoalias: noalias_EC maxb pinfo TD Mem EC1)
  (Heq2: EC1 = {| Opsem.CurFunction := F;
                  Opsem.CurBB := B;
                  Opsem.CurCmds := nil;
                  Opsem.Terminator := insn_br bid Cond l1 l2;
                  Opsem.Locals := lc;
                  Opsem.Allocas := als |})
  (Hsim : State_simulation pinfo Cfg1
            {| Opsem.ECS := EC1 :: ECs;
               Opsem.Mem := Mem |} Cfg2 St2)
  (conds : GVsT DGVs) (c : GenericValue) (l' : l) (ps' : phinodes)
  (cs' : cmds) (tmn' : terminator) (lc' : Opsem.GVsMap)
  (H : Opsem.getOperandValue TD Cond lc gl = ret conds)
  (H0 : c @ conds)
  (H1 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (H2 : Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc =
       ret lc'),
  exists St2' : Opsem.State,
     Opsem.sop_plus Cfg2 St2 St2' trace_nil /\
     State_simulation pinfo Cfg1
     {|Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := (block_intro l' ps' cs' tmn');
                       Opsem.CurCmds := cs';
                       Opsem.Terminator := tmn';
                       Opsem.Locals := lc';
                       Opsem.Allocas := als |} :: ECs;
       Opsem.Mem := Mem |} Cfg2 St2'.
Proof.
  intros. subst.
  destruct_ctx_br.
  assert (exists b2,
    (if isGVZero (los, nts) c
     then lookupBlockViaLabelFromFdef F2 l2
     else lookupBlockViaLabelFromFdef F2 l1) = Some b2 /\
    block_simulation pinfo F (block_intro l' ps' cs' tmn') b2) as Hfind.
    symmetry in H1.
    destruct (isGVZero (los, nts) c); 
      eapply lookup_fdef_sim__block_sim in H1; eauto.
  destruct Hfind as [b2 [Hfind Htblock]].
  eapply cmds_simulation_nil_br_inv in Htcmds; 
    try solve [eauto | simpl; congruence].
  destruct (fdef_dec F (PI_f pinfo)) as [ e | n]; subst.
  SCase "F is tranformed".
    assert (phinodes_placement_block (PI_id pinfo)
      (PI_typ pinfo) (PI_align pinfo) (PI_newids pinfo) (PI_succs pinfo) 
      (PI_preds pinfo) (block_intro l' ps' cs' tmn') = b2) as EQ.
      clear - Htblock. destruct pinfo. simpl in *.
      destruct (fdef_dec PI_f PI_f); auto.
        congruence.
    subst. clear Htblock. simpl in Hfind.
    assert ((PI_newids pinfo) ! l' <> None) as Hreach'.
      admit. (* reachable *)
    remember ((PI_newids pinfo) ! l') as R1.
    destruct R1 as [[[lid' pid'] sid']|]; try congruence.
    assert (exists prd, exists prds, (PI_preds pinfo) ! l' = Some (prd::prds)) 
      as R2.
      admit. (* must be of at most one pred *)
    destruct R2 as [prd [prds Heq]].
    rewrite Heq in Hfind.
    assert ((PI_newids pinfo) ! (label_of_block B) <> None) as Hreach.
      admit. (* reachable *)
    remember ((PI_newids pinfo) ! (label_of_block B)) as R.
    destruct R as [[[lid pid] sid]|]; subst; try congruence.
    assert (exists mp, exists gv,
      getOperandValue (los, nts) (value_id (PI_id pinfo)) lc gl2 = Some mp /\
      mload (los, nts) M2 mp (PI_typ pinfo) (PI_align pinfo) = Some gv) as Halc.
      clear - Hnoalias.
      (* By promotablity *)
      unfold noalias_EC in Hnoalias.
      destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
      assert (exists gvsa, lookupAL _ lc (PI_id pinfo) = Some gvsa) 
        as Hlkup.
        (* WF ssa isnt stuck by accessing undefined variables *)
        admit.
      destruct Hlkup as [gvsa Hlkup]. simpl. 
      change (GVsT DGVs) with GenericValue in Hlkup.
      rewrite Hlkup.
      apply Hnoalias in Hlkup; auto.
      destruct Hlkup as [[J1 [J2 [gv J3]]] _].
      exists gvsa. exists gv. auto.
    destruct Halc as [mp [gv [Hget Hld]]].
    assert (reg_simulation (PI_f pinfo) lc 
             (updateAddAL _ lc2 lid ($ gv # PI_typ pinfo $))) as Hrsim'.
      admit. (* Hrsim HeqR *)
    remember (cs' ++ 
              match (PI_succs pinfo) ! l' with
              | ret nil => nil
              | ret (_ :: _) =>
                  [insn_load lid' (PI_typ pinfo)
                    (value_id (PI_id pinfo)) (PI_align pinfo)]
              | merror => nil
              end) as cs2'.
    remember (block_intro l'
                (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo)
                   (prd :: prds) :: ps')
                (insn_store sid' (PI_typ pinfo) (value_id pid')
                   (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2') tmn') 
             as b2.
    assert (exists lc2', 
      Opsem.switchToNewBasicBlock (los, nts) b2 B2 gl2 
        (updateAddAL _ lc2 lid ($ gv # PI_typ pinfo $)) = ret lc2' /\
      reg_simulation (PI_f pinfo) lc' lc2' /\ 
      lookupAL _ lc2' pid' = Some gv) as Hswitch.
      admit. (* switch *)
    destruct Hswitch as [lc2' [Hswitch [Hrsim'' Hlk]]].
    assert (mstore (los,nts) M2 mp (PI_typ pinfo) gv (PI_align pinfo) 
      = Some M2) as Hst.
      clear - Hld. admit. (* By MemModel *)
    exists (Opsem.mkState ((Opsem.mkEC F2 b2 cs2' tmn' lc2' als2)::ECs2) M2).
    split.
    SSCase "opsem".
      rewrite <- (@trace_app_nil__eq__trace trace_nil).
      apply Opsem.sop_plus_cons with (state2:=
         Opsem.mkState 
           ((Opsem.mkEC F2 B2 nil (insn_br bid Cond l1 l2) 
             (updateAddAL _ lc2 lid ($ gv # (PI_typ pinfo) $)) als2)::ECs2) M2).
        eapply simulation__getOperandValue with (lc2:=lc2) in Hget; eauto.
        econstructor; eauto.

      rewrite <- (@trace_app_nil__eq__trace trace_nil).
      apply Opsem.sop_star_cons with (state2:=
         Opsem.mkState 
           ((Opsem.mkEC F2 b2 
             (insn_store sid' (PI_typ pinfo) (value_id pid')
               (value_id (PI_id pinfo)) (PI_align pinfo) :: cs2') 
             tmn' lc2' als2)::ECs2) M2).
        subst.
        eapply simulation__getOperandValue with 
          (lc2:=updateAddAL _ lc2 lid ($ gv # (PI_typ pinfo) $)) in H; eauto.

      apply OpsemProps.sInsn__implies__sop_star.
      clear c H0 H1 Hfind.
      econstructor; eauto.
        eapply simulation__getOperandValue with (lc:=lc'); eauto.
          clear - Hget H2.
          admit. (* By WF promotablity *)
    SSCase "sim".
      assert (blockInFdefB (block_intro l' ps' cs' tmn') (PI_f pinfo))as HBinF'.
        assert (HuniqF:=HFinPs).
        eapply wf_system__uniqFdef in HuniqF; eauto.
        destruct (PI_f pinfo) as [[] bs].
        destruct HuniqF as [HuniqBlocks HuniqArgs].
        symmetry in H1.
        destruct (isGVZero (los,nts) c);
          apply genLabel2Block_blocks_inv with (f:=fheader_intro f t i0 a v) 
            in H1; auto; destruct H1; eauto.
      subst.
      repeat (split; eauto 2 using cmds_at_block_tail_next).
        exists l'. exists ps'. exists nil. auto.

        exists l'. 
        exists (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo) (prd :: prds)
          :: ps').
        exists [insn_store sid' (PI_typ pinfo) (value_id pid')
                 (value_id (PI_id pinfo)) (PI_align pinfo)].
        simpl_env. auto.

        destruct pinfo. simpl in *.
        destruct (fdef_dec PI_f PI_f); try congruence.
          admit. (* WF_PhiInfo *)

  SCase "F isnt tranformed".
    admit. (* simpl case *)
Qed.

Lemma noalias_State__noalias_EC: forall maxb pinfo Cfg EC ECs Mem,
  Promotability.wf_State maxb pinfo Cfg 
    {| Opsem.ECS := EC :: ECs; Opsem.Mem := Mem |} ->
  noalias_EC maxb pinfo (OpsemAux.CurTargetData Cfg) Mem EC.
Proof.
  intros. destruct Cfg.
  destruct H as [[J1 _] _].
  destruct EC. destruct J1 as [J1 _].
  simpl. auto.
Qed.

Lemma phinodes_placement_is_correct : forall maxb pinfo Cfg1 St1 Cfg2 St2 St1' tr
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2)
  (Hop: Opsem.sInsn Cfg1 St1 St1' tr), 
  exists St2',
    Opsem.sop_plus Cfg2 St2 St2' tr /\    
    State_simulation pinfo Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  (sInsn_cases (induction Hop) Case); 
    try apply noalias_State__noalias_EC in Hnoalias.

Case "sReturn".  
  destruct_ctx_return.
  eapply cmds_simulation_nil_ret_inv in Htcmds; eauto. subst.
  apply cmds_simulation_cons_inv in Htcmds'.
  destruct Htcmds' as [cs2'0 [EQ Htcmds']]; subst.
  eapply returnUpdateLocals_rsim in H1; eauto.
  destruct H1 as [lc2'' [H1 Hrsim'']].
  exists 
    (Opsem.mkState ((Opsem.mkEC F2' B2' cs2'0 tmn2' lc2'' als2')::ECs2) Mem').
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply OpsemProps.sInsn__implies__sop_plus.
    constructor; auto.
  
    repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sReturnVoid".
  destruct_ctx_return.
  eapply cmds_simulation_nil_ret_inv in Htcmds; eauto. subst.
  apply cmds_simulation_cons_inv in Htcmds'.
  destruct Htcmds' as [cs2'0 [EQ Htcmds']]; subst.
  exists 
    (Opsem.mkState ((Opsem.mkEC F2' B2' cs2'0 tmn2' lc2' als2')::ECs2) Mem').
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply OpsemProps.sInsn__implies__sop_plus.
    constructor; auto.
  
    repeat (split; eauto 2 using cmds_at_block_tail_next).

Case "sBranch". eapply phinodes_placement_is_correct__sBranch; eauto.
Case "sBranch_uncond". admit.
  (* eapply SBpass_is_correct__dsBranch_uncond; eauto. *)
Case "sBop". 

Admitted.
(*
eapply SBpass_is_correct__dsBop; eauto.

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
*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
