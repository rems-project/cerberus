Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vminus.
Require Import imperative.

(************** Specification of SSA construction *****************************)

Definition renaming := list (id*id).

Inductive sp_inssa_value (rm:renaming) : value -> value -> Prop :=
| sp_inssa_value_id: forall vid1 vid2, 
    In (vid1, vid2) rm -> 
    sp_inssa_value rm (value_id vid1) (value_id vid2)
| sp_inssa_value_const: forall c,
    sp_inssa_value rm (value_const c) (value_const c)
.

Inductive sp_inssa_cmd (rm:renaming) : cmd -> cmd -> Prop :=
| sp_inssa_bop : forall bop0 id0 v1 v2 id0' v1' v2',
    sp_inssa_value rm v1 v1' -> sp_inssa_value rm v2 v2' ->
    In (id0, id0') rm -> 
    sp_inssa_cmd rm (insn_bop id0 bop0 v1 v2) (insn_bop id0' bop0 v1' v2')
| sp_inssa_icmp : forall cond0 id0 v1 v2 id0' v1' v2',
    sp_inssa_value rm v1 v1' -> sp_inssa_value rm v2 v2' ->
    In (id0, id0') rm -> 
    sp_inssa_cmd rm (insn_icmp id0 cond0 v1 v2) (insn_icmp id0' cond0 v1' v2').

Inductive sp_inssa_tmn (rm:renaming) : terminator -> terminator -> Prop :=
| sp_inssa_br : forall id0 v v' l1 l2,
    sp_inssa_value rm v v' -> 
    sp_inssa_tmn rm (insn_br id0 v l1 l2) (insn_br id0 v' l1 l2)
| sp_inssa_br_uncond : forall id0 l0,
    sp_inssa_tmn rm (insn_br_uncond id0 l0) (insn_br_uncond id0 l0)
| sp_inssa_ret : forall id0 v v',
    sp_inssa_value rm v v' -> 
    sp_inssa_tmn rm (insn_return id0 v) (insn_return id0 v')
.

Definition sp_inssa_phinode (rm:renaming) (pn:phinode) : Prop :=
let '(insn_phi id0 vls0) := pn in
exists vid, In (vid, id0) rm /\
List.Forall (fun vl1 => 
             match vl1 with
             | (value_id vid1, _) => In (vid, vid1) rm 
             | (value_const (const_int c), _) => c = 0%Z
             end) (unmake_list_value_l vls0).

Inductive sp_inssa_block (rm:renaming) : block -> block -> Prop :=
| sp_inssa_block_intro: forall l0 ps0 cs1 cs2 t1 t2, 
  List.Forall (sp_inssa_phinode rm) ps0 ->
  List.Forall2 (sp_inssa_cmd rm) cs1 cs2 ->
  sp_inssa_tmn rm t1 t2 ->
  sp_inssa_block rm (block_intro l0 nil cs1 t1) (block_intro l0 ps0 cs2 t2)
.

Inductive sp_inssa_fdef (rm:renaming) : fdef -> fdef -> Prop :=
| sp_inssa_fdef_intro: forall bs1 bs2, 
  List.Forall2 (sp_inssa_block rm) bs1 bs2 ->
  sp_inssa_fdef rm (fdef_intro bs1) (fdef_intro bs2)
.

Hint Constructors sp_inssa_cmd sp_inssa_tmn sp_inssa_block sp_inssa_fdef.

Definition wf_renaming (rm:renaming) : Prop :=
(forall id1 id2 id1' id2',
   In (id1, id1') rm -> In (id2, id2') rm -> id1 <> id2 -> id1' <> id2') /\
(forall id1 id1' id2, In (id1, id1') rm -> In (id2, id1') rm -> id1 = id2).

(************** Typing prop *****************************)

Export VMitypings.

Lemma wfi_fdef__wfi_tmn: forall (l1 : l) (ps1 : phinodes) (cs1 : cmds) 
  (tmn1 : terminator) (f : fdef),
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  wfi_fdef f ->
  wfi_insn f (insn_terminator tmn1).
Admitted.

Lemma wfi_blocks__wfi_block : forall f bs b,
  wfi_blocks f bs -> 
  InBlocksB b bs = true ->
  wfi_block f b.
Proof.
  induction bs; intros b Hwfbs Hbinbs.
    inv Hbinbs.

    inv Hwfbs.
    simpl in Hbinbs.
    apply orb_prop in Hbinbs.
    inv Hbinbs; eauto.
      apply blockEqB_inv in H.
      subst. auto.
Qed.

Lemma wfi_fdef__blockInFdefB__wfi_block : forall b f,
  blockInFdefB b f = true -> 
  wfi_fdef f ->
  wfi_block f b.
Proof.
  intros.
  inv H0.  
  eapply wfi_blocks__wfi_block; eauto.
Qed.

Lemma wfi_fdef__lookup__wfi_block : forall b f l0,
  Some b = lookupBlockViaLabelFromFdef f l0 ->
  wfi_fdef f ->
  wfi_block f b.
Proof.
  intros.
  eapply wfi_fdef__blockInFdefB__wfi_block; eauto.
    symmetry in H. destruct b.
(*
    assert (uniqFdef f) as J. eapply wf_fdef__uniqFdef; eauto.
    eapply lookupBlockViaLabelFromFdef_inv in H; eauto.
    destruct H; auto.
*)
Admitted.

(************** Opsem *****************************)

Definition igetOperandValue (v:value) (locals:GVMap) : GenericValue := 
match v with
| value_id id => 
    match lookupAL _ locals id with
    | Some gv => gv
    | None => Int.zero 31
    end
| value_const c => const2GV c
end.

Definition iBOP (lc:GVMap) (op:bop) (v1 v2:value) : GenericValue :=
match (igetOperandValue v1 lc, igetOperandValue v2 lc) with
| (gv1, gv2) => mbop op gv1 gv2
end.

Definition iICMP (lc:GVMap) (c:cond) (v1 v2:value) : GenericValue :=
match (igetOperandValue v1 lc, igetOperandValue v2 lc) with
| (gv1, gv2) => micmp c gv1 gv2
end.

Export Opsem.

Inductive siInsn : fdef -> ExecutionContext -> ExecutionContext -> trace -> Prop :=
| siBranch : forall F B lc bid Cond l1 l2 c l' ps' cs' tmn',   
  igetOperandValue Cond lc = c ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  siInsn F
    (mkEC B nil (insn_br bid Cond l1 l2) lc)
    (mkEC (block_intro l' ps' cs' tmn') cs' tmn' lc)
    trace_nil

| siBranch_uncond : forall F B lc bid l l' ps' cs' tmn',   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  siInsn F
    (mkEC B nil (insn_br_uncond bid l) lc)
    (mkEC (block_intro l' ps' cs' tmn') cs' tmn' lc)
    trace_nil 

| siBop: forall F B lc id bop v1 v2 gvs3 cs tmn,
  iBOP lc bop v1 v2 = gvs3 ->
  siInsn F
    (mkEC B ((insn_bop id bop v1 v2)::cs) tmn lc) 
    (mkEC B cs tmn (updateAddAL _ lc id gvs3))
    trace_nil 

| siIcmp : forall F B lc id cond v1 v2 gvs3 cs tmn,
  iICMP lc cond v1 v2 = gvs3 ->
  siInsn F  
    (mkEC B ((insn_icmp id cond v1 v2)::cs) tmn lc) 
    (mkEC B cs tmn (updateAddAL _ lc id gvs3))
    trace_nil
.

Hint Constructors siInsn.

Definition wf_ExecutionContext (f:fdef) (ec:ExecutionContext) : Prop :=
let '(mkEC b cs tmn lc) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
wfi_fdef f /\
exists l1, exists cs', b = block_intro l1 nil (cs'++cs) tmn.

Lemma iprogress: forall f S1, wf_ExecutionContext f S1 ->
  s_isFinialState S1 = true \/ 
  (exists S2, exists tr, siInsn f S1 S2 tr).
Proof.
  intros f S1 HwfS1.
  destruct S1 as [b cs tmn lc].
  destruct HwfS1 as [Hreach [HbInF [HwfF [l1 [cs1 Heq]]]]].
  subst b.
  destruct cs.
  Case "cs=nil".
    destruct tmn.
    SCase "tmn=ret". simpl. auto.
    SCase "tmn=br". 
      right.
      assert (Hwfc := HbInF).
      eapply wfi_fdef__wfi_tmn in Hwfc; eauto.
      assert (exists l', exists cs', exists tmn',
              Some (block_intro l' nil cs' tmn') = 
              (if isGVZero (igetOperandValue v lc)
                 then lookupBlockViaLabelFromFdef f l2
                 else lookupBlockViaLabelFromFdef f l0)) as HlkB.
        inv Hwfc. 
        destruct block1 as [l2' ps2 cs2 tmn2].
        destruct block2 as [l3' ps3 cs3 tmn3].
        destruct (isGVZero (igetOperandValue v lc)).
          exists l3'. exists cs3. exists tmn3.
          rewrite H5. symmetry in H5.
          apply wfi_fdef__lookup__wfi_block in H5; auto.
          inv H5. auto.

          exists l2'. exists cs2. exists tmn2.
          rewrite H3. symmetry in H3.
          apply wfi_fdef__lookup__wfi_block in H3; auto.
          inv H3. auto.

      destruct HlkB as [l' [cs' [tmn' HlkB]]].
      exists (mkEC (block_intro l' nil cs' tmn') cs' tmn' lc).
      exists trace_nil. eauto.

    SCase "tmn=br_uncond". 
      right.
      assert (exists cs', exists tmn',
        Some (block_intro l0 nil cs' tmn') = lookupBlockViaLabelFromFdef f l0) 
          as HlkB.
        assert (Hwfc:=HbInF).
        eapply wfi_fdef__wfi_tmn in Hwfc; eauto.
        inv Hwfc.        
        exists (cs1++nil). exists (insn_br_uncond i0 l0).
        rewrite H1. 
(*
        apply lookupBlockViaLabelFromFdef_inv in H3; auto.
        destruct H3 as [H3 _]; subst. auto.
*)
        admit.
      destruct HlkB as [cs' [tmn' HlkB]].
      exists (mkEC (block_intro l0 nil cs' tmn') cs' tmn' lc).
      exists trace_nil. eauto.

  Case "cs<>nil".
    right.
    destruct c.
  SCase "c=bop".
    exists {|
                CurBB := block_intro l1 nil
                           (cs1 ++ insn_bop i0 b v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 (iBOP lc b v v0))
           |}.
    exists trace_nil. eauto.

  SCase "icmp". 
    exists {|
                CurBB := block_intro l1 nil
                           (cs1 ++ insn_icmp i0 c v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 (iICMP lc c v v0))
            |}.
     exists trace_nil. eauto.
Qed.

(************** Bisimulation *****************************)

Require Import Lattice.
Require Import Maps.
Import AtomSet.

Definition wf_GVs (rm:renaming)(lc1:GVMap)(id2:id)(gvs2:GenericValue) 
  : Prop :=
forall id1, 
  In (id1,id2) rm ->
  lookupAL _ lc1 id1 = Some gvs2 \/
  (lookupAL _ lc1 id1 = None /\ gvs2 = Int.zero 31).

Definition wf_defs (rm:renaming)(lc1 lc2:GVMap)(ids2:list atom) 
  : Prop :=
forall id2 gvs2, 
  In id2 ids2 -> 
  lookupAL _ lc2 id2 = Some gvs2 -> 
  wf_GVs rm lc1 id2 gvs2.

Definition related_ECs (rm:renaming) (f2:fdef) 
  (ec1 ec2:ExecutionContext) : Prop :=
let '(mkEC b1 cs1 tmn1 lc1) := ec1 in
let '(mkEC b2 cs2 tmn2 lc2) := ec2 in
isReachableFromEntry f2 b2 /\
blockInFdefB b2 f2 = true /\
sp_inssa_block rm b1 b2 /\
List.Forall2 (sp_inssa_cmd rm) cs1 cs2 /\
match cs2 with
| nil => 
    match inscope_of_tmn f2 b2 tmn2 with
    | Some ids2 => wf_defs rm lc1 lc2 ids2
    | None => False
    end
| c2::_ =>
    match inscope_of_cmd f2 b2 c2 with
    | Some ids2 => wf_defs rm lc1 lc2 ids2
    | None => False
    end
end /\
(exists l1, exists cs1', exists ps2, exists cs2',
b1 = block_intro l1 nil (cs1'++cs1) tmn1 /\
b2 = block_intro l1 ps2 (cs2'++cs2) tmn2).

Lemma wf_defs_eq : forall rm lc1 lc2 ids2 ids2',
  set_eq _ ids2 ids2' ->
  wf_defs rm lc1 lc2 ids2 ->
  wf_defs rm lc1 lc2 ids2'.
Proof.
  intros.
  intros id2 gvs2 Hin Hlk.
  destruct H as [J1 J2]. eauto.
Qed.

Lemma state_tmn_typing : forall f l1 ps1 cs1 tmn1 defs id2 lc1 lc2 gv2 rm,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs rm lc1 lc2 defs ->
  wf_fdef f ->
  In id2 (getInsnOperands (insn_terminator tmn1)) ->
  lookupAL _ lc2 id2 = Some gv2 ->
  wf_GVs rm lc1 id2 gv2.
Proof.
  intros f l1 ps1 cs1 tmn1 defs id2 lc1 lc2 gv2 rm Hreach HwfInstr Hinscope 
    HwfDefs HuniqF HinOps Hlkup.
  apply wf_insn__wf_insn_base in HwfInstr; 
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  
 
  assert (
     In (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id2)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id_))
              id_list)))
    ) as G.
    rewrite H1 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=block_intro l1 ps1 cs1 tmn1)
    (insn1:=insn_terminator tmn1)(id1:=id2) in H2; auto.

  inv H2.
  apply HwfDefs; auto.
    unfold inscope_of_tmn in Hinscope.
    destruct f.
    remember ((dom_analyze (fdef_intro b)) !! l1) as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H7 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      destruct J' as [J' _].
      destruct J' as [[cs2 [c1 [cs3 [J1 J2]]]] | [ps2 [p1 [ps3 [J1 J2]]]]]; 
        subst.
        rewrite getCmdsIDs_app. simpl. rewrite J2.
        apply in_or_app. right.
        apply in_or_app. right. simpl. auto.
    
        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
      unfold blockStrictDominates in J'. 
      rewrite <- HeqR in J'.
      destruct block'. 
      assert (In l0 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as J.       
        simpl in Hreach.
        apply insnInFdefBlockB__blockInFdefB in H.
        eapply sdom_isnt_refl with (l':=l0) in Hreach; eauto.
          apply ListSet.set_diff_intro; auto.
            simpl. intro J. destruct J as [J | J]; auto.
          rewrite <- HeqR. simpl. auto.
      destruct Hinscope as [_ [Hinscope _]].
      assert (
        lookupBlockViaLabelFromFdef (fdef_intro b) l0 =
        ret block_intro l0 p c t) as J1.
        apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
          eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
      apply Hinscope with (b1:=block_intro l0 p c t) in J; auto.
        apply J.
        eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma state_cmd_typing : forall f b c defs id2 lc1 lc2 gv2 rm,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs rm lc1 lc2 defs ->
  wf_fdef f ->
  In id2 (getInsnOperands (insn_cmd c)) ->
  lookupAL _ lc2 id2 = Some gv2 ->
  wf_GVs rm lc1 id2 gv2.
Proof.
  intros f b c defs id2 lc1 lc2 gv2 rm Hnodup Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps Hlkup.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  

  assert (
     In (f, b, insn_cmd c, id2)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, b, insn_cmd c, id_))
              id_list)))
    ) as G.
    rewrite H1 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=b)(insn1:=insn_cmd c)(id1:=id2) 
    in H2; auto.

  inv H2. 
  apply HwfDefs; auto.
    unfold inscope_of_cmd, inscope_of_id in Hinscope.
    destruct b. destruct f.
    remember ((dom_analyze (fdef_intro b)) !! l0) as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H7 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      simpl in J'.
      destruct J' as [[ps2 [p1 [ps3 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]];
        subst.

        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
        clear - J2 Hnodup.
        apply in_or_app. right.
          simpl in Hnodup. apply NoDup_inv in Hnodup.
          destruct Hnodup as [_ Hnodup].
          apply NoDup_inv in Hnodup.
          destruct Hnodup as [Hnodup _].
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3).
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3) in Hnodup.
          apply NoDup__In_cmds_dominates_cmd; auto.
            rewrite getCmdsIDs_app.
            apply in_or_app. right. simpl. rewrite J2. simpl. auto.
    
      clear H0 HwfDefs. 
      unfold blockStrictDominates in J'.
      rewrite <- HeqR in J'.
      destruct block'.
      assert (In l1 (ListSet.set_diff eq_atom_dec bs_contents [l0])) as J.       
        simpl in Hreach.
        apply insnInFdefBlockB__blockInFdefB in H.
        eapply sdom_isnt_refl with (l':=l1) in Hreach; eauto.
          apply ListSet.set_diff_intro; auto.
            simpl. intro J. destruct J as [J | J]; auto.
          rewrite <- HeqR. simpl. auto.
      destruct Hinscope as [_ [Hinscope _]].
      assert (
        lookupBlockViaLabelFromFdef (fdef_intro b) l1
          = ret block_intro l1 p0 c1 t0) as J1.
        apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
          eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
      apply Hinscope with (b1:=block_intro l1 p0 c1 t0) in J; auto.
        apply J.
        eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma getOperandValue_inTmnOperans_sim : forall
  (f : fdef)
  (tmn : terminator)
  (lc lc': GVMap)
  (HwfSys1 : wf_fdef f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn) f = true)
  (l0 : list atom) rm
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (Hinscope : wf_defs rm lc lc' l0)
  (v v': value)
  (Hvincs : valueInTmnOperands v' tmn) gv gv'
  (Hval : sp_inssa_value rm v v')
  (Hget' : getOperandValue v' lc' = Some gv')
  (Hget : igetOperandValue v lc = gv),
  gv = gv'.
Proof.
  intros.
  destruct v' as [vid' | vc']; inv Hval; simpl in *; try congruence.
  assert (HwfInstr:=HbInF).
  eapply wf_fdef__wf_tmn in HwfInstr; eauto.
  assert (wf_GVs rm lc vid' gv') as Hlkup.
    eapply state_tmn_typing; eauto. 
    apply valueInTmnOperands__InOps; auto.
  destruct (@Hlkup vid1) as [Hlkup1 | [Hlkup1 Heq]]; 
    try solve [auto | rewrite Hlkup1; auto].
Qed.

Lemma getOperandValue_inCmdOps_sim : forall
  (f : fdef)
  (cs : list cmd)
  (tmn : terminator)
  (lc lc': GVMap)
  (HwfSys1 : wf_fdef f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom) rm
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : wf_defs rm lc lc' l0)
  (v v': value)
  (Hval : sp_inssa_value rm v v')
  (Hvincs : valueInCmdOperands v' c) gv gv'
  (Hget' : getOperandValue v' lc' = Some gv')
  (Hget : igetOperandValue v lc = gv),
  gv = gv'.
Proof.
  intros.
  destruct v' as [vid' | vc']; inv Hval; simpl in Hget'; simpl; try congruence.
  assert (wf_GVs rm lc vid' gv') as Hlkup.
    eapply state_cmd_typing; eauto. 
    eapply wf_fdef__uniq_block; eauto.
    eapply wf_fdef__wf_cmd; eauto using In_middle.
    apply valueInCmdOperands__InOps; auto.
  destruct (@Hlkup vid1) as [Hlkup1 | [Hlkup1 Heq]]; 
    try solve [auto | rewrite Hlkup1; auto].
Qed.

Export OpsemProps.

(*
Lemma getOperandValue__wf_gvs : forall f v lc1 lc2 gvs,
  wf_defs rm lc1 lc2 ->
  getOperandValue v lc2 = Some gvs ->
  wf_GVs rm lc1 gvs.
Proof.
  intros f v lc gvs Hwflc Hwfv Hget. auto.
Qed.
*)

Lemma getIncomingValuesForBlockFromPHINodes_spec1_aux : forall f
    b lc id1 l3 cs tmn ps2 ps1 lc1 gvs rm lc',
  Some lc' = getIncomingValuesForBlockFromPHINodes ps2 b lc ->
  List.In id1 (getPhiNodesIDs ps2) ->
  uniqFdef f ->
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_phinodes f (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  lookupAL _ lc' id1 = Some gvs ->
  wf_GVs rm lc1 id1 gvs.
Proof.    
  intros f b lc id1 l3 cs tmn ps2 ps1 lc1 gvs rm lc' H H0 Huniq Hbinf Hwfps Hlk.
  assert (Huniq':=Hbinf).
  apply uniqFdef__uniqBlockLocs in Huniq'; auto.
  simpl in Huniq'. 
  apply NoDup_split in Huniq'.
  destruct Huniq' as [Huniq' _].
  assert (In id1 (getPhiNodesIDs (ps1++ps2))) as Hin.
    rewrite getPhiNodesIDs_app.
    apply in_app_iff; auto.
  generalize dependent lc'.
  generalize dependent ps1.
  induction ps2; simpl in *; intros.
    inversion H0.

    assert (J:=Hbinf).
    destruct a.
    simpl in H0.
    inv Hwfps. inv H5.
    destruct H0 as [H0 | H0]; subst.
      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].
        eapply wf_value_list__getValueViaBlockFromValuels__wf_value in H3; eauto.
        remember (getOperandValue v lc) as R.
        destruct R as [g|]; tinv H.
        symmetry in HeqR. 
        destruct (getIncomingValuesForBlockFromPHINodes ps2 b lc); inv H.
        simpl in Hlk.
        destruct (id1 == id1) as [e' | n]; try solve [contradict n; auto].
          inv Hlk.
Admitted.
(*
          eapply getOperandValue__wf_gvs in HeqR; eauto.

      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].   
        remember (getOperandValue v lc) as R.
        destruct R; tinv H. 
        remember (getIncomingValuesForBlockFromPHINodes ps2 b lc) 
          as R.
        destruct R; inversion H; subst.         
        simpl.
        destruct (id1==i0); subst.
          clear - Huniq' H0.
          rewrite getPhiNodesIDs_app in Huniq'.
          apply NoDup_split in Huniq'.
          destruct Huniq' as [_ Huniq'].
          inv Huniq'. congruence.
      
          eapply IHps2 with (ps1:=ps1 ++ [insn_phi i0 l0]); simpl_env; eauto.
Qed.
*)

Hint Resolve wf_fdef__uniqFdef.

Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall f b 
    lc id1 l3 cs tmn ps lc' gvs lc1 rm,
  Some lc' = getIncomingValuesForBlockFromPHINodes ps b lc ->
  In id1 (getPhiNodesIDs ps) ->
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_fdef f ->
  lookupAL _ lc' id1 = Some gvs ->
  wf_GVs rm lc1 id1 gvs.
Admitted.
(*
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H2.
    apply lookupBlockViaLabelFromFdef_inv in H2; auto.
    destruct H2; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec1_aux with (ps1:=nil); 
    eauto using wf_fdef__wf_phinodes.
Qed.
*)

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' b lc1 rm
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock (block_intro l' ps' cs' tmn') b lc = ret lc')
  (t : list atom)
  (Hwfdfs : wf_defs rm lc1 lc t)
  (ids0' : list atom)
  (HwfF : wf_fdef F)
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef F))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = (dom_analyze F) !! l')
  (Hinscope : (fold_left (inscope_of_block F l') contents' 
    (ret (getPhiNodesIDs ps')) = ret ids0'))
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs rm lc1 lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  intros id2 gvs Hid2 Hlk.
  remember (getIncomingValuesForBlockFromPHINodes ps' b lc) as R1.
  destruct R1 as [rs|]; inv Hswitch.
  destruct (In_dec eq_atom_dec id2 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    apply updateValuesForNewBlock_spec6 in Hlk; auto.
    eapply getIncomingValuesForBlockFromPHINodes_spec1 with (gvs:=gvs) in HeqR1;
      eauto.
      eapply getIncomingValuesForBlockFromPHINodes_spec6 in HeqR1; eauto.

    assert (Hnotin' := Hnotin).
    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin. assert (HeqR1':=HeqR1).
    eapply getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1; eauto.
    eapply updateValuesForNewBlock_spec7 in Hlk; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 
  lc1 lc2 lc2' rm,
wf_fdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) lc2 = Some lc2' ->
wf_defs rm lc1 lc2 ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs rm lc1 lc2' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 lc1 lc2 lc2' rm
    HwfF HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  assert (uniqFdef F) as Huniq. auto.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd, inscope_of_id.
  destruct F as [bs].
  remember (dom_analyze (fdef_intro bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms Huniq HwfF.
    simpl in Huniq.
    eapply dom_successors; eauto.

  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound').
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil)(bs:=bs)(l0:=l') in J1.
    destruct J1 as [r J1].
    exists r. split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
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

      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4; auto.
      
            apply J5 in J9; auto.
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      subst. simpl in J1. simpl_env in J1.   
      eapply wf_defs_br_aux; eauto.

  Case "cs'<>nil".
    assert (J1:=inbound').
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n]; 
      try solve [contradict n; auto].
    simpl_env.
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps')(bs:=bs)
      (l0:=l') in J1.
    destruct J1 as [r J1].
    exists r.  split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
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
        contradict J; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4; auto.
      
            apply J5 in J9; auto. 
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      subst. eapply wf_defs_br_aux; eauto.
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs ids0 l' ps' cs' tmn' l0 
  lc1 lc2 lc2' bid rm,
wf_fdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) lc2 = Some lc2' ->
wf_defs rm lc1 lc2 ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs rm lc1 lc2' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c lc1 lc2 lc2' rm,
wf_fdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) lc2 = Some lc2' ->
wf_defs rm lc1 lc2 ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs rm lc1 lc2' ids0'.
Proof.
  intros.
  remember (isGVZero c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Lemma sp_inssa_fdef__lookupBlockViaLabelFromFdef : forall rm F F' l0 b b',
  sp_inssa_fdef rm F F' ->
  lookupBlockViaLabelFromFdef F l0 = Some b ->
  lookupBlockViaLabelFromFdef F' l0 = Some b' ->
  sp_inssa_block rm b b'.
Proof.
Admitted.

Lemma sp_inssa_cmd__spec1 : forall rm c1 c2,
  sp_inssa_cmd rm c1 c2 -> In (getCmdLoc c1, getCmdLoc c2) rm.
Proof. intros. inv H; auto. Qed.
       
Lemma wf_defs_updateAddAL : forall rm lc1 lc2 ids1 ids2 i1 i2 gv,
  wf_renaming rm ->
  wf_defs rm lc1 lc2 ids1 ->
  set_eq _ (i2::ids1) ids2 -> In (i1,i2) rm ->
  wf_defs rm (updateAddAL _ lc1 i1 gv) (updateAddAL _ lc2 i2 gv) ids2.
Proof.
  intros rm lc1 lc2 ids1 ids2 i1 i2 gv Hwfm HwfDefs Heq Hin.
  intros i' gv' Hin' Hlk'. intros id1 Hin1.
  destruct Hwfm as [Hwfm1 Hwfm2].
  destruct (id_dec i2 i'); subst.
    rewrite lookupAL_updateAddAL_eq in Hlk'. inv Hlk'. 
    eapply Hwfm2 in Hin1; eauto. subst.
    rewrite lookupAL_updateAddAL_eq. auto.

    rewrite <- lookupAL_updateAddAL_neq in Hlk'; auto.
    destruct Heq as [Hinc1 Hinc2].
    apply Hinc2 in Hin'. simpl in Hin'.
    destruct Hin' as [Eq | Hin']; subst; try solve [contradict n; auto].
    destruct (id_dec i1 id1); subst.
      rewrite lookupAL_updateAddAL_eq.
      (* BUG: We should only consider the latest renaming that dominates the 
              current pc *)
      admit.

      rewrite <- lookupAL_updateAddAL_neq; auto. 
      apply HwfDefs in Hlk'; auto.
Qed.

Lemma bisimulation_cmd_updated_case : forall 
  (F2 F1 : fdef) (B2 : block) (lc2 : GVMap) (gv : GenericValue)
  (cs2 : list cmd) (tmn2 : terminator)
  id1 c1 id2 c2 B1 cs1 tmn1 lc1 rm (Hwfm: wf_renaming rm)
  (Hid1 : Some id1 = getCmdID c1)
  (Hid2 : Some id2 = getCmdID c2)
  (HwfF1 : wfi_fdef F1) (HwfF2 : wf_fdef F2)
  (Hctrans : sp_inssa_cmd rm c1 c2)
  (Htrans : sp_inssa_fdef rm F1 F2)
  (Hrel : related_ECs rm F2
            {| CurBB := B1;
               CurCmds := c1 :: cs1;
               Terminator := tmn1;
               Locals := lc1
            |}
            {| CurBB := B2;
               CurCmds := c2 :: cs2;
               Terminator := tmn2;
               Locals := lc2
            |}),
  related_ECs rm F2
     {| CurBB := B1;
        CurCmds := cs1;
        Terminator := tmn1;
        Locals := updateAddAL _ lc1 id1 gv
     |}
     {| CurBB := B2;
        CurCmds := cs2;
        Terminator := tmn2;
        Locals := updateAddAL _ lc2 id2 gv
     |}.
Proof.
  intros.
  destruct Hrel as
    [Hreach2 [HBinF2 [Hbtrans [Hcstrans [Hinscope2 
      [l3 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]; subst.
  inv Hcstrans. 
  remember (inscope_of_cmd F2 (block_intro l3 ps2 (cs2' ++ c2 :: cs2) tmn2) c2) 
    as R1. 
  assert (uniqFdef F2) as HuniqF2. auto.
  destruct R1; try solve [inversion Hinscope2].
  repeat (split; try solve [auto]).
      assert (Hid2' := Hid2).
      symmetry in Hid1, Hid2.
      apply getCmdLoc_getCmdID in Hid1.
      apply getCmdLoc_getCmdID in Hid2.
      subst.
      destruct cs2; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c2) (getCmdsLocs cs2')) as Hnotin.
          eapply wf_fdef__uniq_block with (f:=F2) in HwfF2; eauto.        
          simpl in HwfF2.
          apply NoDup_inv in HwfF2.
          destruct HwfF2 as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c2 (cs2' ++ [c2])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF2).
        eapply wf_fdef__wf_cmd with (c:=c2) in Hwfc; 
          eauto.
        rewrite <- Hid2' in J2.
        eapply wf_defs_updateAddAL; eauto using sp_inssa_cmd__spec1.

      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [c2] ++ [c] ++ cs2))) as Hnodup.
          eapply wf_fdef__uniq_block with (f:=F2) in HwfF2; eauto.        
          simpl in HwfF2.
          apply NoDup_inv in HwfF2.
          destruct HwfF2 as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c2 (cs2' ++ [c2] ++ [c] ++ cs2)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF2).
        eapply wf_fdef__wf_cmd with (c:=c2) in Hwfc; 
          eauto.
        rewrite <- Hid2' in J2.
        eapply wf_defs_updateAddAL; eauto using sp_inssa_cmd__spec1.

  exists l3. exists (cs1'++[c1]). exists ps2. exists (cs2'++[c2]). 
  simpl_env. auto.
Qed.

Ltac bisimulation_cmd :=
match goal with
| H : _ ?lc _ ?v1 ?v2 = ret ?gvs3,
  Hrel : related_ECs _ _ _ _ |-
  context [?f ?lc1 ?bop0 ?v0 ?v3] =>
  assert (f lc1 bop0 v0 v3 = gvs3) as Heq;
    try solve [unfold ICMP, BOP in *;
    inv_mbind'; inv_mfalse; app_inv; symmetry_ctx;
    match goal with
    | HeqR : getOperandValue ?v _ = ret _, 
      HeqR0 : getOperandValue ?v0 _ = ret _ |- _ => 
      eapply getOperandValue_inCmdOps_sim in HeqR; try (eauto || simpl; auto);
      eapply getOperandValue_inCmdOps_sim in HeqR0; try (eauto || simpl; auto);
      subst; auto
    end];
  subst;
  split; try solve [auto |
      eapply bisimulation_cmd_updated_case in Hrel; try solve [simpl; eauto]]
end.

Lemma bisimulation : forall rm F1 F2 S1 S2 S1' S2' tr1 tr2,
  wf_renaming rm ->
  wfi_fdef F1 ->
  wf_fdef F2 ->
  sp_inssa_fdef rm F1 F2 ->
  related_ECs rm F2 S1 S2 ->
  siInsn F1 S1 S1' tr1 ->
  sInsn F2 S2 S2' tr2 ->
  related_ECs rm F2 S1' S2' /\ tr1 = tr2.
Proof.
  intros rm F1 F2 S1 S2 S1' S2' tr1 tr2 Hwfm HwfF1 HwfF2 Htrans Hrel HsInsn1
    HsInsn2.
  (sInsn_cases (destruct HsInsn2) Case).
Focus.
Case "sBranch".
  destruct S1 as [b1 cs1 tmn1 lc1];
  assert (J:=Hrel); simpl in J;
  destruct J as
    [Hreach2 [HBinF2 [Hbtrans [Hcstrans [Hinscope2
      [l3 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]; subst.
  inv Hcstrans.
  inv Hbtrans. inv H10.
  inv HsInsn1.
  remember (inscope_of_tmn F
                  (block_intro l3 ps2 (cs2' ++ nil) (insn_br bid Cond l1 l2))
                  (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; tinv Hinscope2.
  assert (igetOperandValue v lc1 = c) as Heq.
    eapply getOperandValue_inTmnOperans_sim; try solve [eauto | simpl; auto].
  subst.
  assert (sp_inssa_block rm (block_intro l'0 ps'0 cs'0 tmn'0) 
    (block_intro l' ps' cs' tmn')) as Hbtrans.
    destruct (isGVZero (igetOperandValue v lc1));
      eapply sp_inssa_fdef__lookupBlockViaLabelFromFdef; eauto.
  inv Hbtrans.
  assert (isReachableFromEntry F (block_intro l' ps' cs' tmn') /\
    In l' (successors_terminator (insn_br bid v l1 l2)) /\
    blockInFdefB (block_intro l' ps' cs' tmn') F = true /\
    wf_phinodes F (block_intro l' ps' cs' tmn') ps') as J.
    symmetry in H0.
    destruct (isGVZero (igetOperandValue v lc1));
      assert (J:=H0);
      apply lookupBlockViaLabelFromFdef_inv in J; eauto;
      destruct J as [J H0']; subst;
      symmetry in H0; eapply wf_fdef__lookup__wf_block in H0; eauto;
      (repeat split; simpl; auto); try solve
        [eapply reachable_successors; (eauto || simpl; auto) |
         inv H0; auto].
  destruct J as [Hreach' [Hsucc' [HBinF1' HwfPNs]]].
  repeat split; auto.
      clear - HeqR1 H0 H1 Hinscope2 HBinF2 HwfF2.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists nil. exists ps'. exists nil. auto.
Unfocus.

Focus.
Case "sBranch_uncond". 
  destruct S1 as [b1 cs1 tmn1 lc1];
  assert (J:=Hrel); simpl in J;
  destruct J as
    [Hreach2 [HBinF2 [Hbtrans [Hcstrans [Hinscope2
      [l3 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]; subst.
  inv Hcstrans.
  inv Hbtrans. inv H9.
  inv HsInsn1.
  remember (inscope_of_tmn F
                  (block_intro l3 ps2 (cs2' ++ nil) (insn_br_uncond bid l0))
                  (insn_br_uncond bid l0)) as R1. 
  destruct R1; tinv Hinscope2.
  assert (sp_inssa_block rm (block_intro l'0 ps'0 cs'0 tmn'0) 
    (block_intro l' ps' cs' tmn')) as Hbtrans.
    eapply sp_inssa_fdef__lookupBlockViaLabelFromFdef; eauto.
  inv Hbtrans.
  assert (isReachableFromEntry F (block_intro l' ps' cs' tmn') /\
    In l' (successors_terminator (insn_br_uncond bid l0)) /\
    blockInFdefB (block_intro l' ps' cs' tmn') F = true /\
    wf_phinodes F (block_intro l' ps' cs' tmn') ps') as J.
    symmetry in H.
    assert (J:=H).
    apply lookupBlockViaLabelFromFdef_inv in J; eauto.
    destruct J as [J H']; subst.
    symmetry in H; eapply wf_fdef__lookup__wf_block in H; eauto.
    (repeat split; simpl; auto); try solve
        [eapply reachable_successors; (eauto || simpl; auto) |
         inv H; auto].
  destruct J as [Hreach' [Hsucc' [HBinF1' HwfPNs]]].
  repeat split; auto.
      clear - HeqR1 H H0 Hinscope2 HBinF2 HwfF2.
      eapply inscope_of_tmn_br_uncond in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists nil. exists ps'. exists nil. auto.
Unfocus.

Case "sBop". 
  destruct S1 as [b1 cs1 tmn1 lc1];
  assert (J:=Hrel); simpl in J;
  destruct J as
    [Hreach2 [HBinF2 [Hbtrans [Hcstrans [Hinscope2
      [l3 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]; subst.
  inv Hcstrans. inv H3.
  inv Hbtrans. inv HsInsn1.
  remember (inscope_of_cmd F
                  (block_intro l3 ps2 (cs2' ++ insn_bop id0 bop0 v1 v2 :: cs)
                     tmn) (insn_bop id0 bop0 v1 v2)) as R1. 
  destruct R1; tinv Hinscope2.
  abstract bisimulation_cmd.

Case "sIcmp". 
  destruct S1 as [b1 cs1 tmn1 lc1];
  assert (J:=Hrel); simpl in J;
  destruct J as
    [Hreach2 [HBinF2 [Hbtrans [Hcstrans [Hinscope2
      [l3 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]; subst.
  inv Hcstrans. inv H3.
  inv Hbtrans. inv HsInsn1.
  remember (inscope_of_cmd F
                  (block_intro l3 ps2 (cs2' ++ insn_icmp id0 cond0 v1 v2 :: cs)
                     tmn) (insn_icmp id0 cond0 v1 v2)) as R1. 
  destruct R1; tinv Hinscope2.
  abstract bisimulation_cmd.
Qed.

Lemma related_finalstate_is_stuck : forall rm F2 S1 S2 S2' tr2
  (Hrel : related_ECs rm F2 S1 S2)
  (Hfinal1 : s_isFinialState S1 = true)
  (HsInsn2 : sInsn F2 S2 S2' tr2),
  False.
Proof.
  intros.
  destruct S1. destruct CurCmds0; tinv Hfinal1. 
  destruct Terminator0; inv Hfinal1. destruct S2. 
  destruct Hrel as 
    [J1 [J2 [J3 [J4 [J5 [l1 [cs1' [ps2 [cs2' [J7 J8]]]]]]]]]]; 
    subst.
  inv J4. inv J3. inv H7. inv HsInsn2.
Qed.

Lemma backsimulation : forall rm F1 F2 S1 S2 S2' tr2,
  wf_renaming rm ->
  wfi_fdef F1 -> wf_fdef F2 ->
  wf_ExecutionContext F1 S1 ->
  sp_inssa_fdef rm F1 F2 ->
  related_ECs rm F2 S1 S2 ->
  sInsn F2 S2 S2' tr2 ->
  exists S1', exists tr1,
    siInsn F1 S1 S1' tr1 /\ related_ECs rm F2 S1' S2' /\ tr1 = tr2.
Proof.
  intros rm F1 F2 S1 S2 S2' tr2 Hwfm HwfF1 HwfF2 HwfEC1 Htrans Hrel HsInsn2.
  apply iprogress in HwfEC1; auto.
  destruct HwfEC1 as [Hfinal1 | [S1' [tr1 HsiInsn1]]].
    eapply related_finalstate_is_stuck in Hrel; eauto. inv Hrel.
    exists S1'. exists tr1. split; eauto using bisimulation.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
