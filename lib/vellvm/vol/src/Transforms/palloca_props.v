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

Record PhiInfo := mkPhiInfo {
  PI_f: fdef;
  PI_rd: list l;
  PI_succs: ATree.t (list l);
  PI_preds: ATree.t (list l);
  PI_id: id;
  PI_typ: typ;
  PI_align: align;
  PI_newids: ATree.t (id*id*id)  
}.

Definition promotable_alloca (f:fdef) (pid:id) (ty:typ) (al:align) : Prop :=
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    find_promotable_alloca f cs nil = Some (pid, ty, al)
| _ => False
end.

Definition WF_PhiInfo (pinfo: PhiInfo) : Prop :=
promotable_alloca (PI_f pinfo) (PI_id pinfo) (PI_typ pinfo) (PI_align pinfo) /\
reachablity_analysis (PI_f pinfo) = Some (PI_rd pinfo) /\
(PI_succs pinfo) = successors (PI_f pinfo) /\
(PI_preds pinfo) = make_predecessors (PI_succs pinfo) /\
(PI_newids pinfo) = fst (gen_fresh_ids (PI_rd pinfo) (getFdefLocs (PI_f pinfo))).

Lemma find_promotable_alloca_spec: forall f cs nids pid ptyp pal,
  find_promotable_alloca f cs nids = Some (pid, ptyp, pal) ->
  exists pv, In (insn_alloca pid ptyp pv pal) cs /\
             is_promotable f pid.
Proof.
  induction cs; simpl; intros.
    congruence.

    destruct a; try solve [apply IHcs in H; destruct H as [pv [H1 H2]]; eauto].
    remember (is_promotable f i0 && negb (in_dec id_dec i0 nids)) as R.
    destruct R; try solve [apply IHcs in H; destruct H as [pv [H1 H2]]; eauto].
    inv H. 
    symmetry in HeqR. apply andb_true_iff in HeqR. destruct HeqR.
    eauto.
Qed.

Ltac simpl_WF_PhiInfo :=
match goal with
| H : WF_PhiInfo ?pinfo |- _ =>
  destruct H as [H _];
  unfold promotable_alloca in H;
  match goal with
  | H : match getEntryBlock ?PI_f0 with
        | Some _ => _
        | None => _
        end |- _ =>
    remember (getEntryBlock PI_f0) as R;
    destruct R as [[]|]; tinv H;
    apply find_promotable_alloca_spec in H
  end
end.

Lemma WF_PhiInfo_spec1: forall pinfo, 
  WF_PhiInfo pinfo -> 
  uniqFdef (PI_f pinfo) ->
  exists v, 
    lookupInsnViaIDFromFdef (PI_f pinfo) (PI_id pinfo) = 
      Some (insn_cmd 
             (insn_alloca (PI_id pinfo) (PI_typ pinfo) v (PI_align pinfo))).
Proof.
  intros. 
  simpl_WF_PhiInfo.
  destruct H as [v [H _]].
  exists v. 
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in HeqR; eauto.
  simpl in HeqR. auto.
Qed.

Definition is_promotable_fun pid := 
  (fun acc b => 
     let '(block_intro _ ps cs tmn) := b in
     if (List.fold_left (fun re p => re || used_in_phi pid p) ps 
          (used_in_tmn pid tmn)) then false
     else
       fold_left 
         (fun acc0 c =>
          if used_in_cmd pid c then
            match c with
            | insn_load _ _ _ _ => acc0
            | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
            | _ => false
            end
          else acc0) cs acc
  ). 

Lemma used_in_phi_fun_spec: forall pid (a0 : bool) (b : phinode),
  a0 || used_in_phi pid b = false -> a0 = false.
Proof.
  intros. apply orb_false_iff in H. destruct H; auto.
Qed.

Lemma unused_in_phis__unused_in_phi: forall (pid id0 : id) (ps : phinodes)
  (p0 : phinode) (J1 : ret p0 = lookupPhiNodeViaIDFromPhiNodes ps id0)
  (J2 : fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p) 
          ps false = false),
  used_in_phi pid p0 = false.
Proof.
  induction ps; simpl; intros.
    congruence.

    assert (fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
              ps false = false /\ used_in_phi pid a = false) as J3.
      apply fold_left_or_false; auto.
        apply used_in_phi_fun_spec.

    destruct J3 as [J3 J4].
    destruct (getPhiNodeID a == id0); subst; eauto.
      inv J1. auto.
Qed.

Lemma unused_in_value__neg_valueEqB: forall pid v,
  used_in_value pid v = false ->
  negb (valueEqB v (value_id pid)).
Proof.
  intros.
  unfold valueEqB. 
  destruct v; inv H; simpl.
    destruct (value_dec (value_id i0) (value_id pid)); simpl.
      inversion e. subst.
      destruct (id_dec pid pid); subst; inv H1; try congruence.
         
      reflexivity.

    destruct (value_dec (value_const c) (value_id pid)); simpl.
      congruence.
      reflexivity.
Qed.

Lemma used_in_cmd_fun_spec:
  forall pid acc0 c,
  (if used_in_cmd pid c then
    match c with
    | insn_load _ _ _ _ => acc0
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
    | _ => false
    end
  else acc0) = true -> acc0 = true.
Proof.
  intros. clear - H.
  destruct acc0; auto.
  destruct (used_in_cmd pid c); auto.
  destruct c; auto.
  apply andb_true_iff in H. destruct H; auto.
Qed.

Lemma unused_in_cmds__unused_in_cmd: forall (pid id0 : id) (cs : cmds)
  (c0 : cmd) (J1 : ret c0 = lookupCmdViaIDFromCmds cs id0)
  (J2 : fold_left 
          (fun acc0 c =>
           if used_in_cmd pid c then
             match c with
             | insn_load _ _ _ _ => acc0
             | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
             | _ => false
             end
           else acc0) cs true = true),
  match c0 with
  | insn_load _ _ _ _ => True
  | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) 
  | _ => used_in_cmd pid c0 = false
  end.
Proof.
  induction cs; simpl; intros.
    congruence.

    assert (
      fold_left 
        (fun acc0 c =>
         if used_in_cmd pid c then
           match c with
           | insn_load _ _ _ _ => acc0
           | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
           | _ => false
           end
         else acc0) cs true = true /\
      (if used_in_cmd pid a then
         match a with
         | insn_load _ _ _ _ => true
         | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && true
         | _ => false
         end
       else true) = true) as J3.
      apply fold_left_and_true; auto.
        apply used_in_cmd_fun_spec.

    destruct J3 as [J3 J4]. clear J2.
    destruct (eq_atom_dec id0 (getCmdLoc a)); subst.
      inv J1. clear IHcs J3.
      remember (used_in_cmd pid a) as R.
      destruct R.    
        destruct a; auto.
          apply andb_true_iff in J4. 
          destruct J4; auto.
        destruct a; auto.
          simpl in *.
          symmetry in HeqR.
          apply orb_false_iff in HeqR. 
           destruct HeqR. 
           apply unused_in_value__neg_valueEqB; auto.

      clear J4.
      eapply IHcs in J3; eauto.
Qed.

Lemma is_promotable_fun_spec: forall pid (a0: bool) (b: block)
  (H1: is_promotable_fun pid a0 b = true), a0 = true.
Proof.
  intros. clear - H1.
  destruct a0; auto.
  unfold is_promotable_fun in H1.
  destruct b.
  destruct (fold_left
    (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
    (used_in_tmn pid t)); auto.
  apply fold_left_and_true in H1.
  destruct H1 as [_ H1]; auto.
  apply used_in_cmd_fun_spec.
Qed.

Lemma is_promotable_spec: forall pid id0 instr bs,
  fold_left (is_promotable_fun pid) bs true = true ->
  lookupInsnViaIDFromBlocks bs id0 = ret instr ->
  match instr with
  | insn_cmd c0 =>
    match c0 with
    | insn_load _ _ _ _ => True
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) 
    | _ => used_in_cmd pid c0 = false
    end
  | _ => used_in_insn pid instr = false
  end.
Proof.
  induction bs; simpl; intros.
    congruence.

    assert (fold_left (is_promotable_fun pid) bs true = true /\ 
            is_promotable_fun pid true a = true) as J.
      apply fold_left_and_true; auto.
        apply is_promotable_fun_spec.

    destruct J as [J1 J2].
    remember (lookupInsnViaIDFromBlock a id0) as R.
    destruct R.
      inv H0.
      clear - J2 HeqR.
      destruct a; simpl in *.
      remember (fold_left
                 (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
                 (used_in_tmn pid t)) as R.
      destruct R; tinv J2.
      assert (fold_left 
               (fun (re : bool) (p : phinode) => re || used_in_phi pid p) 
                 p false = false /\
              used_in_tmn pid t = false) as J.
        apply fold_left_or_false; auto.
          apply used_in_phi_fun_spec.        

      destruct J as [J3 J4]. clear HeqR0.
      remember (lookupPhiNodeViaIDFromPhiNodes p id0) as R1.
      remember (lookupCmdViaIDFromCmds c id0) as R2.
      destruct R1.
        inv HeqR.
        clear - J3 HeqR1. simpl.
        eapply unused_in_phis__unused_in_phi in J3; eauto.

        destruct R2; inv HeqR.
        clear - J2 HeqR2. simpl.
        eapply unused_in_cmds__unused_in_cmd in J2; eauto.

      apply IHbs in H0; auto.
Qed.

Lemma WF_PhiInfo_spec3: forall pinfo, 
  WF_PhiInfo pinfo -> 
  forall instr id0, 
    lookupInsnViaIDFromFdef (PI_f pinfo) id0 = Some instr ->
    match instr with
    | insn_cmd c0 =>
      match c0 with
      | insn_load _ _ _ _ => True
      | insn_store _ _ v _ _ => negb (valueEqB v (value_id (PI_id pinfo))) 
      | _ => used_in_cmd (PI_id pinfo) c0 = false
      end
    | _ => used_in_insn (PI_id pinfo) instr = false
    end.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [v [_ H]].
  destruct (PI_f pinfo). simpl in *.
  eapply is_promotable_spec in H0; eauto.
Qed.

Definition wf_use_at_head (pinfo:PhiInfo) (v:value) :=
used_in_value (PI_id pinfo) v = false.

Lemma used_in_phi__wf_use_at_head: forall pinfo v0 (p : phinode)
  (H0 : used_in_phi (PI_id pinfo) p = false)
  (H1 : valueInInsnOperands v0 (insn_phinode p)),
  wf_use_at_head pinfo v0.
Proof.
  intros.
  unfold wf_use_at_head.
  destruct p; simpl in *.
  induction l0; tinv H1.
    simpl in *.
    apply orb_false_iff in H0.
    destruct H0 as [J1 J2].
    destruct H1 as [H1 | H1]; subst; auto.
Qed.

Lemma neg_valueEqB__unused_in_value: forall pid v,
  negb (valueEqB v (value_id pid)) ->
  used_in_value pid v = false.
Proof.
  intros.
  unfold valueEqB in H.  
  destruct v; auto.
  destruct (value_dec (value_id i0) (value_id pid)); simpl in *.
    congruence.

    destruct (id_dec i0 pid); subst; auto.
      congruence.
Qed.

Lemma unused_in_list_value__unused_in_value: forall pid v0 l0,
  used_in_list_value pid l0 = false ->
  valueInListValue v0 l0 ->
  used_in_value pid v0 = false.
Proof.
  induction l0; simpl; intros.
    inv H0.
     
    apply orb_false_iff in H.
    destruct H as [J1 J2].
    inv H0; auto.
Qed.

Lemma unused_in_params__used_in_value: forall pid v0 ps
  (H1: fold_left
         (fun (acc : bool) (p : typ * attributes * value) =>
          let '(_, v) := p in used_in_value pid v || acc) ps false = false)
  (H2 : valueInParams v0 ps),
  used_in_value pid v0 = false.
Proof.
  induction ps as [|[]]; simpl; intros.
    inv H2.

    assert (forall (a : bool) (b : typ * attributes * value),
      (let '(_, v1) := b in used_in_value pid v1 || a) = false -> a = false).
      intros. destruct b.
      apply orb_false_iff in H.
      destruct H; auto.
    apply fold_left_or_false in H1; auto.
    destruct H1 as [J1 J2]. clear H.
    apply orb_false_iff in J2.
    destruct J2.
    unfold valueInParams in *.
    simpl in H2.
    remember (split ps) as R.
    destruct R.
    simpl in H2.
    destruct H2 as [H2 | H2]; subst; auto.
Qed.   

Lemma WF_PhiInfo_spec4: forall pinfo, 
  WF_PhiInfo pinfo -> 
  forall instr id0 v0, 
    lookupInsnViaIDFromFdef (PI_f pinfo) id0 = Some instr ->
    match instr with
    | insn_cmd c0 =>
      match c0 with
      | insn_load _ _ _ _ => False
      | insn_store _ _ v _ _ => v = v0 
      | _ => valueInCmdOperands v0 c0
      end
    | _ => valueInInsnOperands v0 instr
    end ->
    wf_use_at_head pinfo v0.
Proof.
  intros.
  apply WF_PhiInfo_spec3 in H0; auto.
  destruct instr.
    simpl in H0. 
    eapply used_in_phi__wf_use_at_head in H1; eauto.

    unfold wf_use_at_head.
    destruct c; tinv H1; simpl in *;
      try solve [
        subst; auto |
        match goal with
        | H0 : used_in_value _ ?v1 || used_in_value _ ?v2 = false,
          H1 : ?v0 = ?v1 \/ ?v0 = ?v2 |- _ =>
            apply orb_false_iff in H0;
            destruct H0 as [J1 J2];
            destruct H1; subst; auto
        end
      ].

      subst. 
      apply neg_valueEqB__unused_in_value; auto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      destruct H1 as [H1 | H1]; subst; auto.
      eapply unused_in_list_value__unused_in_value in J2; eauto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      apply orb_false_iff in J1.
      destruct J1 as [J1 J3].
      destruct H1 as [H1 | [H1 | H1]]; subst; auto.

      apply orb_false_iff in H0.
      destruct H0 as [J1 J2].
      destruct H1 as [H1 | H1]; subst;   
        eauto using unused_in_params__used_in_value.

    unfold wf_use_at_head.
    destruct t; simpl in *; subst; 
      try solve [auto | match goal with
                        | H1: False |- _ => inv H1
                        end].
Qed.

Lemma unused_in_phis__unused_in_phi': forall (pid: id) (ps: phinodes) 
  (p0 : phinode) (J1 : InPhiNodesB p0 ps)
  (J2 : fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p) 
          ps false = false),
  used_in_phi pid p0 = false.
Proof.
  induction ps; simpl; intros.
    congruence.

    assert (fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
              ps false = false /\ used_in_phi pid a = false) as J3.
      apply fold_left_or_false; auto.
        apply used_in_phi_fun_spec.        

    destruct J3 as [J3 J4].
    apply orb_true_iff in J1.
    destruct J1 as [J1 | J1]; auto.
      apply phinodeEqB_inv in J1. subst. auto.
Qed.

Lemma unused_in_cmds__unused_in_cmd': forall (pid id0 : id) (cs : cmds)
  (c0 : cmd) (J1 : InCmdsB c0 cs)
  (J2 : fold_left 
          (fun acc0 c =>
           if used_in_cmd pid c then
             match c with
             | insn_load _ _ _ _ => acc0
             | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
             | _ => false
             end
           else acc0) cs true = true),
  match c0 with
  | insn_load _ _ _ _ => True
  | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) 
  | _ => used_in_cmd pid c0 = false
  end.
Proof.
  induction cs; simpl; intros.
    congruence.

    assert (
      fold_left 
        (fun acc0 c =>
         if used_in_cmd pid c then
           match c with
           | insn_load _ _ _ _ => acc0
           | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
           | _ => false
           end
         else acc0) cs true = true /\
      (if used_in_cmd pid a then
         match a with
         | insn_load _ _ _ _ => true
         | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && true
         | _ => false
         end
       else true) = true) as J3.
      apply fold_left_and_true; auto.
        apply used_in_cmd_fun_spec.

    destruct J3 as [J3 J4]. clear J2.
    apply orb_true_iff in J1.
    destruct J1 as [J1 | J1].
      clear IHcs J3.
      apply cmdEqB_inv in J1. subst.
      remember (used_in_cmd pid a) as R.
      destruct R.    
        destruct a; auto.
          apply andb_true_iff in J4. 
          destruct J4; auto.

        destruct a; auto.
          simpl in *.
          symmetry in HeqR.
          apply orb_false_iff in HeqR. 
          destruct HeqR. 
          apply unused_in_value__neg_valueEqB; auto.

      clear J4.
      eapply IHcs in J3; eauto.
Qed.

Lemma is_promotable_spec': forall pid b instr bs,
  fold_left (is_promotable_fun pid) bs true = true ->
  insnInBlockB instr b ->
  InBlocksB b bs -> 
  match instr with
  | insn_cmd c0 =>
    match c0 with
    | insn_load _ _ _ _ => True
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) 
    | _ => used_in_cmd pid c0 = false
    end
  | _ => used_in_insn pid instr = false
  end.
Proof.
  induction bs; simpl; intros; try congruence.

    assert (fold_left (is_promotable_fun pid) bs true = true /\ 
            is_promotable_fun pid true a = true) as J.
      apply fold_left_and_true; auto.
        apply is_promotable_fun_spec.

    destruct J as [J1 J2]. clear H.
    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst.
      clear - J2 H0.
      destruct a; simpl in *.
      remember (fold_left
                 (fun (re : bool) (p : phinode) => re || used_in_phi pid p) p
                 (used_in_tmn pid t)) as R.
      destruct R; tinv J2.
      assert (fold_left 
               (fun (re : bool) (p : phinode) => re || used_in_phi pid p) 
                 p false = false /\
              used_in_tmn pid t = false) as J.
        apply fold_left_or_false; auto.
          apply used_in_phi_fun_spec.  

      destruct J as [J3 J4]. clear HeqR.
      destruct instr; simpl in *.
        eapply unused_in_phis__unused_in_phi' in J3; eauto.
        eapply unused_in_cmds__unused_in_cmd' in J2; eauto.
        apply terminatorEqB_inv in H0. subst. auto.

      apply IHbs in J1; auto.
Qed.

Lemma WF_PhiInfo_spec5: forall pinfo pn b, 
  WF_PhiInfo pinfo -> 
  phinodeInFdefBlockB pn (PI_f pinfo) b = true -> 
  used_in_phi (PI_id pinfo) pn = false.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [v [_ H]].
  destruct (PI_f pinfo). simpl in *.
  unfold phinodeInFdefBlockB in H0.
  apply andb_true_iff in H0.
  destruct H0.
  eapply is_promotable_spec' with (instr:=insn_phinode pn) in H1; eauto.
Qed.

Lemma WF_PhiInfo_spec6: forall pinfo l' ps' cs' tmn', 
  WF_PhiInfo pinfo -> 
  uniqFdef (PI_f pinfo) ->
  ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef (PI_f pinfo) l' 
    ->
  ~ In (PI_id pinfo) (getPhiNodesIDs ps').
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [pv [H _]].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H; eauto.
  simpl in H.

  symmetry in H1.
  apply lookupBlockViaLabelFromFdef_inv in H1; auto.
  destruct H1 as [_ H1].
  intro J. 
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in J; eauto.  
  destruct J as [p2 [J1 J2]].
  rewrite H in J1. congruence.
Qed.

Lemma PhiInfo_must_be_promotable_alloca: forall pinfo l0 ps0 cs1 c cs2 tmn0,
  WF_PhiInfo pinfo ->
  uniqFdef (PI_f pinfo) ->
  getCmdLoc c = PI_id pinfo ->
  (forall id1 typ1 v1 al1, c <> insn_alloca id1 typ1 v1 al1) ->
  blockInFdefB (block_intro l0 ps0 (cs1++c::cs2) tmn0) (PI_f pinfo) = true ->
  False. 
Proof.
  intros.
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H3; eauto using in_middle.
  apply WF_PhiInfo_spec1 in H; auto.
  destruct H as [v' H].
  simpl in H3. rewrite H1 in H3. rewrite H3 in H. inv H.
  assert (W:=@H2 (PI_id pinfo) (PI_typ pinfo) v' (PI_align pinfo)).
  auto.
Qed.

Lemma WF_PhiInfo_spec2: forall pinfo ifs S los nts Ps,
  WF_PhiInfo pinfo ->
  wf_fdef ifs S (module_intro los nts Ps) (PI_f pinfo) ->
  exists mc, flatten_typ (los, nts) (PI_typ pinfo) = Some mc.
Proof.
  intros.
  simpl_WF_PhiInfo.
  destruct H as [pv [J1 J2]].
  symmetry in HeqR.
  apply entryBlockInFdef in HeqR.
  eapply wf_fdef__wf_cmd in HeqR; eauto.
  inv HeqR.
  apply flatten_typ_total; auto.
Qed.

Lemma WF_PhiInfo__succs : forall pinfo l1 ps1 cs1 tmn1 
  (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PI_f pinfo) = true ->
  successors_terminator tmn1 <> nil ->
  exists sc, exists scs, (PI_succs pinfo) ! l1 = Some (sc::scs).
Proof.
  intros.
  destruct H as [J1 [J2 [J3 [J4 J5]]]].
  rewrite J3.
  eapply blockInFdefB__successors in H0; eauto.
  unfold ls in *.
  rewrite H0. 
  destruct (successors_terminator tmn1); try congruence. eauto.
Qed.

Lemma WF_PhiInfo__preds : forall pinfo l1 ps1 cs1 tmn1 l0 
  (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) (PI_f pinfo) = true ->
  In l0 (successors_terminator tmn1) ->
  exists prd, exists prds, (PI_preds pinfo) ! l0 = Some (prd::prds).
Proof.
  intros.
  destruct H as [J1 [J2 [J3 [J4 J5]]]].
  rewrite J4.
  eapply blockInFdefB__successors in H0; eauto.
  rewrite J3.
  assert (In l0 (successors (PI_f pinfo))!!!l1) as Hin.
    unfold successors_list.
    unfold ls, l in *.
    rewrite H0. auto.
  apply make_predecessors_correct in Hin.
  unfold successors_list in Hin.
  unfold ls, l in *.
  destruct ((make_predecessors (successors (PI_f pinfo))) ! l0); tinv Hin. 
  destruct l2; tinv Hin.
  eauto.
Qed.

Definition is_temporary i0 (newids : ATree.t (id * id * id)) : Prop :=
exists l0,
  match ATree.get l0 newids with
  | Some (lid, pid, sid) => i0 == lid \/ i0 == pid \/ i0 == sid
  | None => False
  end.

Definition gen_fresh_ids_fun :=
  (fun (acc : ATree.t (atom * atom * atom) * list atom) (l0 : atom) =>
    let '(nids', ex_ids') := acc in
    let 'exist lid' _ := atom_fresh_for_list ex_ids' in
    let 'exist pid' _ := atom_fresh_for_list (lid' :: ex_ids') in
    let 'exist sid' _ := atom_fresh_for_list (pid' :: lid' :: ex_ids') in
    (ATree.set l0 (lid', pid', sid') nids',
     sid' :: pid' :: lid' :: ex_ids')).

Lemma gen_fresh_ids__spec_aux: forall i0 ex_ids0 rds nids ex_ids,
  (forall j0, In j0 ex_ids0 -> In j0 ex_ids) ->
  (forall j0, is_temporary j0 nids -> ~ In j0 ex_ids0) ->
  is_temporary i0 (fst (fold_left gen_fresh_ids_fun rds (nids, ex_ids))) -> 
  ~ In i0 ex_ids0.
Proof.
  induction rds; simpl; intros; auto.
  remember (atom_fresh_for_list ex_ids) as R1.
  destruct R1 as [lid' Jlid'].
  remember (atom_fresh_for_list (lid'::ex_ids)) as R2.
  destruct R2 as [pid' Jpid'].
  remember (atom_fresh_for_list (pid'::lid'::ex_ids)) as R3.
  destruct R3 as [sid' Jsid'].
  apply IHrds in H1; auto.
    intros j0 Hin. simpl. auto.

    intros j0 Histmp.
    destruct Histmp as [l0 Histmp].
    remember (
      @ATree.get (prod (prod id id) id) l0
               (@ATree.set (prod (prod atom atom) atom) a
                  (@pair (prod atom atom) atom (@pair atom atom lid' pid')
                     sid') nids)
      ) as R.
    destruct R as [[[]]|]; tinv Histmp.
    destruct (a == l0); subst.
      intro J. apply H in J.
      rewrite ATree.gss in HeqR.
      inv HeqR.
      destruct Histmp as [EQ | [EQ | EQ]]; subst.
        destruct (j0 == lid'); subst; simpl in EQ; try congruence; auto.
        destruct (j0 == pid'); subst; simpl in EQ; try congruence.
          apply Jpid'. simpl. auto.
        destruct (j0 == sid'); subst; simpl in EQ; try congruence; auto.
          apply Jsid'. simpl. auto.

      rewrite ATree.gso in HeqR; auto.
      apply H0.
      exists l0. unfold id. rewrite <- HeqR. auto.
Qed.

Lemma gen_fresh_ids__spec: forall i0 rds ex_ids,
  is_temporary i0 (fst (gen_fresh_ids rds ex_ids)) -> ~ In i0 ex_ids.
Proof.
  unfold gen_fresh_ids.
  intros.
  fold gen_fresh_ids_fun in H.
  eapply gen_fresh_ids__spec_aux in H; eauto.
    intros j0 J.
    destruct J as [l0 J].
    rewrite ATree.gempty in J. inv J.
Qed.

(* There are some other getFdefLocs lemmas in sb_ds_trans_lib.v. 
   We should merge them. *)
Lemma getCmdLoc_in_getFdefLocs : forall f1 c cs tmn2 id0 l1 ps1 cs11
  (HBinF : blockInFdefB (block_intro l1 ps1 (cs11 ++ c :: cs) tmn2) f1 = true)
  (Hget : getCmdLoc c = id0),
  In id0 (getFdefLocs f1).
Proof.
  intros. subst.
  destruct f1. destruct f. simpl.
  destruct (split a).
  apply in_or_app. right.
  eapply in_getBlockLocs__in_getBlocksLocs in HBinF; eauto.
  simpl. 
  apply in_or_app. right.
  apply in_or_app. left.
  apply getCmdLoc_in_getCmdsLocs with (c:=c); auto.
  apply in_middle.
Qed.

Lemma temporary_must_be_fresh: forall l0 ps0 cs0 c cs2 tmn0 pinfo i0
  (Hin : blockInFdefB (block_intro l0 ps0 (cs0 ++ c :: cs2) tmn0) 
           (PI_f pinfo) = true)
  (Hld : is_temporary i0 
           (fst (gen_fresh_ids (PI_rd pinfo) (getFdefLocs (PI_f pinfo)))))
  (Heq : getCmdLoc c = i0),
  False.
Proof.
  intros.
  eapply getCmdLoc_in_getFdefLocs in Hin; eauto.
  apply gen_fresh_ids__spec in Hld; auto.
Qed.

Lemma WF_PhiInfo_fresh: forall pinfo lid pid sid l0 (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  ret (lid, pid, sid) = (PI_newids pinfo) ! l0 ->
  PI_id pinfo <> lid /\ PI_id pinfo <> pid /\ PI_id pinfo <> sid.
Proof.
  intros.
  apply WF_PhiInfo_spec1 in Huniq; auto.
  destruct Huniq as [v Huniq].
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB in Huniq.
  destruct Huniq as [b1 HbInF].
  simpl in HbInF.  
  apply andb_true_iff in HbInF.
  destruct HbInF as [J1 J2].
  destruct b1. simpl in J1.
  apply InCmdsB_in in J1.
  apply in_split in J1.
  destruct J1 as [cs1 [cs2 J1]]; subst.
  destruct H as [J1 [J6 [J3 [J4 J5]]]].
  destruct (PI_id pinfo == lid); subst.
    eapply temporary_must_be_fresh in J2; eauto.
    simpl. rewrite <- J5. exists l0. rewrite <- H0. 
    destruct (PI_id pinfo == PI_id pinfo); try congruence.
      simpl. left. reflexivity.
  destruct (PI_id pinfo == pid); subst.
    eapply temporary_must_be_fresh in J2; eauto.
    simpl. rewrite <- J5. exists l0. rewrite <- H0. 
    destruct (PI_id pinfo == PI_id pinfo); try congruence.
      simpl. right. left. reflexivity.
  destruct (PI_id pinfo == sid); subst; auto.
    eapply temporary_must_be_fresh in J2; eauto.
    simpl. rewrite <- J5. exists l0. rewrite <- H0. 
    destruct (PI_id pinfo == PI_id pinfo); try congruence.
      simpl. right. right. reflexivity.
Qed.

Lemma WF_PhiInfo_spec9: forall pinfo l0 l3 ps3 cs3 l1 ps1 cs1 tmn1 bid
  (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  lookupBlockViaLabelFromFdef (PI_f pinfo) l0 =
    ret block_intro l1 ps1 cs1 tmn1 ->
  blockInFdefB (block_intro l3 ps3 cs3 (insn_br_uncond bid l0)) (PI_f pinfo) ->
  exists succs, (PI_succs pinfo) ! l3 = Some succs /\ In l1 succs.
Proof.
  intros.
  apply blockInFdefB__successors in H1; auto.
  simpl in H1.
  destruct H as [J1 [J2 [J3 [J4 J5]]]].
  rewrite J3. 
  unfold ls, l in *.
  rewrite H1.
  exists (l0::nil).
  split; auto.
  apply lookupBlockViaLabelFromFdef_inv in H0; auto.
  destruct H0 as [EQ _]; subst; simpl; auto.
Qed.

Lemma WF_PhiInfo_spec8: forall pinfo td c l1 l2 l3 ps3 cs3 l0 ps0 cs0 tmn0 bid 
  Cond (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  (if isGVZero td c
   then lookupBlockViaLabelFromFdef (PI_f pinfo) l2
   else lookupBlockViaLabelFromFdef (PI_f pinfo) l1) =
  ret block_intro l0 ps0 cs0 tmn0 ->
  blockInFdefB (block_intro l3 ps3 cs3 (insn_br bid Cond l1 l2)) (PI_f pinfo) ->
  exists succs, (PI_succs pinfo) ! l3 = Some succs /\ In l0 succs.
Proof.
  intros.
  apply blockInFdefB__successors in H1; auto.
  simpl in H1.
  destruct H as [J1 [J2 [J3 [J4 J5]]]].
  rewrite J3. 
  unfold ls, l in *.
  rewrite H1.
  exists (l1::l2::nil).
  split; auto.
  destruct (isGVZero td c).
    apply lookupBlockViaLabelFromFdef_inv in H0; auto.
    destruct H0 as [EQ _]; subst; simpl; auto.

    apply lookupBlockViaLabelFromFdef_inv in H0; auto.
    destruct H0 as [EQ _]; subst; simpl; auto.
Qed.

Lemma gen_fresh_ids__spec3_aux: forall rds nids ex_ids i0 a b c,
  (forall a b c j0, nids ! j0 = Some (a, b, c) -> a <> b /\ a <> c /\ b <> c) ->
  (fst (fold_left gen_fresh_ids_fun rds (nids, ex_ids))) ! i0 
    = Some (a, b, c) -> 
  a <> b /\ a <> c /\ b <> c.
Proof.
  induction rds; simpl; intros; eauto.
  remember (atom_fresh_for_list ex_ids) as R1.
  destruct R1 as [lid' Jlid'].
  remember (atom_fresh_for_list (lid'::ex_ids)) as R2.
  destruct R2 as [pid' Jpid'].
  remember (atom_fresh_for_list (pid'::lid'::ex_ids)) as R3.
  destruct R3 as [sid' Jsid'].
  apply IHrds in H0; auto.
    intros a1 b1 c1 j1 J.
    destruct (a == j1); subst.
      rewrite ATree.gss in J.
      inv J.
      destruct (a1 == b1); subst; auto.
      contradiction Jpid'; simpl; auto.

      destruct (a1 == c1); subst; auto.
      contradiction Jsid'; simpl; auto.

      destruct (b1 == c1); subst; auto.
      contradiction Jsid'; simpl; auto.

      rewrite ATree.gso in J; eauto.
Qed.

Lemma gen_fresh_ids__spec3: forall rds ex_ids l0 lib pid sid,
  Some (lib, pid, sid) = (fst (gen_fresh_ids rds ex_ids)) ! l0 -> 
  lib <> pid /\ lib <> sid /\ pid <> sid.
Proof.
  unfold gen_fresh_ids.
  intros.
  fold gen_fresh_ids_fun in H. 
  symmetry in H.
  eapply gen_fresh_ids__spec3_aux in H; eauto.
    intros a b c j0 J.
    rewrite ATree.gempty in J. inv J.
Qed.

Lemma gen_fresh_ids__spec5_aux: forall rds nids' nids ex_ids ex_ids',
  (forall i0, is_temporary i0 nids -> In i0 ex_ids) ->
  (nids', ex_ids') = (fold_left gen_fresh_ids_fun rds (nids, ex_ids)) -> 
  (forall i0, is_temporary i0 nids' -> In i0 ex_ids').
Proof.
  induction rds; simpl; intros.
    inv H0. auto.

    remember (atom_fresh_for_list ex_ids) as R1.
    destruct R1 as [lid' Jlid'].
    remember (atom_fresh_for_list (lid'::ex_ids)) as R2.
    destruct R2 as [pid' Jpid'].
    remember (atom_fresh_for_list (pid'::lid'::ex_ids)) as R3.
    destruct R3 as [sid' Jsid'].
    eapply IHrds in H0; eauto.
    intros.
    destruct H2 as [l0 H2].
    unfold id in *.
    remember ((ATree.set a (lid', pid', sid') nids) ! l0) as R.
    destruct R as [[[]]|]; tinv H2.
    destruct (a == l0); subst.
      rewrite ATree.gss in HeqR.
      inv HeqR.
      simpl.
      destruct H2 as [H2 | [H2 | H2]].
        destruct (i1 == lid'); simpl in H2; try congruence; auto.
        destruct (i1 == pid'); simpl in H2; try congruence; auto.
        destruct (i1 == sid'); simpl in H2; try congruence; auto.

      simpl. right. right. right.
      rewrite ATree.gso in HeqR; auto.
      apply H.
      exists l0. unfold id in *. rewrite <- HeqR. auto.
Qed.

Lemma gen_fresh_ids__spec4_aux: forall rds nids' nids ex_ids
  (Hp: forall i0, is_temporary i0 nids -> In i0 ex_ids),
  (forall (l1 l2 : atom) (a1 b1 c1 a2 b2 c2 : id),
  l1 <> l2 ->
  ret (a1, b1, c1) = nids ! l1 ->
  ret (a2, b2, c2) = nids ! l2 ->
  a1 <> a2 /\
  a1 <> b2 /\
  a1 <> c2 /\
  b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\ c1 <> a2 /\ c1 <> b2 /\ c1 <> c2) ->
  nids' = fst (fold_left gen_fresh_ids_fun rds (nids, ex_ids)) -> 
  forall (l1 l2 : atom) (a1 b1 c1 a2 b2 c2 : id),
  l1 <> l2 ->
  ret (a1, b1, c1) = nids' ! l1 ->
  ret (a2, b2, c2) = nids' ! l2 ->
  a1 <> a2 /\
  a1 <> b2 /\
  a1 <> c2 /\
  b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\ c1 <> a2 /\ c1 <> b2 /\ c1 <> c2.
Proof.
  induction rds; simpl; intros; subst; try solve [eapply H; eauto].
  remember (atom_fresh_for_list ex_ids) as R1.
  destruct R1 as [lid' Jlid'].
  remember (atom_fresh_for_list (lid'::ex_ids)) as R2.
  destruct R2 as [pid' Jpid'].
  remember (atom_fresh_for_list (pid'::lid'::ex_ids)) as R3.
  destruct R3 as [sid' Jsid'].
  apply IHrds with (l1:=l1)(l2:=l2)(nids:=ATree.set a (lid', pid', sid') nids)
    (ex_ids:=sid' :: pid' :: lid' :: ex_ids)(a2:=a2)(b2:=b2)(c2:=c2) in H2; 
    auto.
    clear IHrds.

    intros.
    destruct H0 as [l0 H0].
    unfold id in *.
    remember ((ATree.set a (lid', pid', sid') nids) ! l0) as R.
    destruct R as [[[]]|]; tinv H0.
    destruct (a == l0); subst.
      rewrite ATree.gss in HeqR.
      inv HeqR.
      simpl.
      destruct H0 as [H0 | [H0 | H0]].
        destruct (i0 == lid'); simpl in H0; try congruence; auto.
        destruct (i0 == pid'); simpl in H0; try congruence; auto.
        destruct (i0 == sid'); simpl in H0; try congruence; auto.

      simpl. right. right. right.
      rewrite ATree.gso in HeqR; auto.
      apply Hp.
      exists l0. unfold id in *. rewrite <- HeqR. auto.

  clear IHrds.
  intros.
  destruct (a == l0); subst.
    rewrite ATree.gss in H4.
    inv H4.
    destruct (l0 == l3); subst; try congruence.
    rewrite ATree.gso in H5; auto. 
      assert (In a3 ex_ids) as Hina.
        apply Hp. exists l3. unfold id. rewrite <- H5. 
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) a3 a3); simpl.
          left. reflexivity. congruence.
      assert (In b3 ex_ids) as Hinb.
        apply Hp. exists l3. unfold id. rewrite <- H5. 
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) b3 b3); simpl.
          right. left. reflexivity. congruence.
      assert (In c3 ex_ids) as Hinc.
        apply Hp. exists l3. unfold id. rewrite <- H5. 
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) c3 c3); simpl.
          right. right. reflexivity. congruence.
      clear - Hina Hinb Hinc Jlid' Jpid' Jsid'. 
      simpl in *.
      repeat split; try intro J; subst; auto.

    rewrite ATree.gso in H4; auto.
    destruct (a == l3); subst.
      rewrite ATree.gss in H5.
      inv H5. 
      assert (In a0 ex_ids) as Hina.
        apply Hp. exists l0. unfold id. rewrite <- H4. 
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) a0 a0); simpl.
          left. reflexivity. congruence.
      assert (In b0 ex_ids) as Hinb.
        apply Hp. exists l0. unfold id. rewrite <- H4. 
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) b0 b0); simpl.
          right. left. reflexivity. congruence.
      assert (In c0 ex_ids) as Hinc.
        apply Hp. exists l0. unfold id. rewrite <- H4. 
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) c0 c0); simpl.
          right. right. reflexivity. congruence.
      clear - Hina Hinb Hinc Jlid' Jpid' Jsid'. 
      simpl in *.
      repeat split; try intro J; subst; auto.

      rewrite ATree.gso in H5; eauto.
Qed.

Lemma gen_fresh_ids__spec4: forall nids rds ex_ids,
  nids = fst (gen_fresh_ids rds ex_ids) ->
  forall (l1 l2 : atom) (a1 b1 c1 a2 b2 c2 : id),
  l1 <> l2 ->
  ret (a1, b1, c1) = nids ! l1 ->
  ret (a2, b2, c2) = nids ! l2 ->
  a1 <> a2 /\
  a1 <> b2 /\
  a1 <> c2 /\
  b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\ c1 <> a2 /\ c1 <> b2 /\ c1 <> c2.
Proof.
  unfold gen_fresh_ids.
  fold gen_fresh_ids_fun.
  intros.
  eapply gen_fresh_ids__spec4_aux; eauto.
    intros. destruct H3 as [l3 H3]. rewrite ATree.gempty in H3. inv H3.
    intros. rewrite ATree.gempty in H4. congruence.
Qed.

Lemma gen_fresh_ids__spec2_aux: forall l1 rds newids nids exids, 
  fst (fold_left gen_fresh_ids_fun rds (nids, exids)) = newids ->
  In l1 rds \/ nids ! l1 <> None ->
  newids ! l1 <> None.
Proof.
  induction rds; simpl; intros.
    subst.
    destruct H0 as [H0 | H0]; auto.
    
    remember (atom_fresh_for_list exids) as R1.
    destruct R1 as [lid' Jlid'].
    remember (atom_fresh_for_list (lid'::exids)) as R2.
    destruct R2 as [pid' Jpid'].
    remember (atom_fresh_for_list (pid'::lid'::exids)) as R3.
    destruct R3 as [sid' Jsid'].
    apply IHrds in H; auto.
    destruct H0 as [[H0 | H0]| H0]; subst; auto.
      right. 
      rewrite ATree.gss. congruence.

      right. 
      destruct (l1 == a); subst.
        rewrite ATree.gss. congruence.
        rewrite ATree.gso; auto. 
Qed.

Lemma gen_fresh_ids__spec2: forall l1 newids rds exids,
  fst (gen_fresh_ids rds exids) = newids ->
  In l1 rds ->
  newids ! l1 <> None.
Proof.
  unfold gen_fresh_ids.
  fold gen_fresh_ids_fun.
  intros.
  eapply gen_fresh_ids__spec2_aux in H; eauto.
Qed.

Lemma reachable__reachablity_analysis: forall f rd a,
  reachable f a -> reachablity_analysis f = Some rd -> In a rd.
Admitted.

Lemma reachable_blk_has_newids : forall pinfo l1,
  WF_PhiInfo pinfo ->
  reachable (PI_f pinfo) l1 ->
  (PI_newids pinfo) ! l1 <> merror.
Proof.
  intros.
  destruct H as [H1 [H2 [H3 [H4 H5]]]].
  eapply reachable__reachablity_analysis in H2; eauto.
  clear - H5 H2.
  eapply gen_fresh_ids__spec2; eauto.
Qed.

Definition gen_phinode_fun (nids:ATree.t (id * id * id)) ty :=
  (fun (acc : list_value_l) (p : atom) =>
      Cons_list_value_l
        match nids ! p with
        | ret (lid0, _, _) => value_id lid0
        | merror => value_const (const_undef ty)
        end p acc).

Lemma WF_PhiInfo__getValueViaLabelFromValuels_aux: forall 
  (nids:ATree.t (id * id * id)) l3 lid pid sid ty
  (J:ret (lid, pid, sid) = nids ! l3) pds v ps,
  (ret v = getValueViaLabelFromValuels ps l3 -> v = value_id lid) ->
  ret v = getValueViaLabelFromValuels 
   (fold_left (gen_phinode_fun nids ty) pds ps) l3 ->
  v = value_id lid.
Proof.
  induction pds; simpl; intros; auto.
    apply IHpds in H0; auto.
      intro J1.
      simpl in J1.
      destruct (@eq_dec l (EqDec_eq_of_EqDec l EqDec_atom) a l3); subst; auto.
        rewrite <- J in J1. inv J1. auto.
Qed.

Lemma WF_PhiInfo__getValueViaLabelFromValuels: forall 
  (nids:ATree.t (id * id * id)) l3 lid pid sid ty
  (J:ret (lid, pid, sid) = nids ! l3) pds v,
  ret v = getValueViaLabelFromValuels 
   (fold_left (gen_phinode_fun nids ty) pds Nil_list_value_l) l3 ->
  v = value_id lid.
Proof.
  intros.
  eapply WF_PhiInfo__getValueViaLabelFromValuels_aux in H; eauto.
    simpl. intros. congruence.
Qed.

Lemma WF_PhiInfo_br_succs_preds: forall pinfo l0 l3 (Hwfpi : WF_PhiInfo pinfo)
  succs (Hsucc : (PI_succs pinfo) ! l3 = ret succs) (Hin : In l0 succs)
  prds (Heq' : (PI_preds pinfo) ! l0 = ret prds),
  In l3 prds.
Proof.
  intros.
  destruct Hwfpi as [J1 [J2 [J3 [J4 J5]]]].
  rewrite J3 in Hsucc.
  rewrite J4 in Heq'.
  assert (In l0 (successors (PI_f pinfo))!!!l3) as Hin'.
    unfold successors_list.
    unfold ls, l in *.
    rewrite Hsucc. auto.
  apply make_predecessors_correct in Hin'.
  unfold successors_list in Hin'.
  unfold ls, l in *.
  rewrite J3 in Heq'.
  rewrite Heq' in Hin'. auto.
Qed.

Lemma WF_PhiInfo__getIncomingValuesForBlockFromPHINodes_neq_PI_id: 
  forall pinfo l0 ps0 cs0 tmn0 B gl lc l5 td (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) ->
  Some l5 = @Opsem.getIncomingValuesForBlockFromPHINodes DGVs 
              td ps0 B gl lc ->
  PI_id pinfo `notin` dom l5.
Proof.
  intros.
  apply blockInFdefB_lookupBlockViaLabelFromFdef in H0; auto.
  eapply WF_PhiInfo_spec6 in H; eauto.
  eapply OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8 in H1; eauto.
Qed.

Lemma WF_PhiInfo__getIncomingValuesForBlockFromPHINodes: forall pinfo l0 ps0 cs0
  tmn0 B gl lc gvsa l5 td (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo) ->
  Some l5 = Opsem.getIncomingValuesForBlockFromPHINodes td ps0 B gl lc ->
  lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa ->
  lookupAL (GVsT DGVs) (Opsem.updateValuesForNewBlock l5 lc) (PI_id pinfo) 
    = ret gvsa.
Proof.
  intros.
  eapply WF_PhiInfo__getIncomingValuesForBlockFromPHINodes_neq_PI_id in H1; 
    eauto.
  clear H H0 ps0 l0 cs0 tmn0 B td.
  rewrite OpsemProps.updateValuesForNewBlock_spec7'; auto.
Qed.

Ltac inv_mbind' :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; inv H
         | H : Some _ = match ?e with
               | Some _ => _
               | None => None
               end |- _ => remember e as R; destruct R as [|]; inv H
         | H :  ret _ = match ?p with
                        | (_, _) => _
                        end |- _ => destruct p
         end.

Lemma WF_PhiInfo__switchToNewBasicBlock: forall (pinfo : PhiInfo) 
  (lc : Opsem.GVsMap) (gl : GVMap) (Huniq: uniqFdef (PI_f pinfo))
  (Hwfpi : WF_PhiInfo pinfo) (lc' : Opsem.GVsMap) los nts
  (l0 : l) (ps0 : phinodes) (cs0 : cmds) (tmn0 : terminator) 
  (lid' : id) (pid' : id) (sid' : id)
  (HeqR1 : ret (lid', pid', sid') = (PI_newids pinfo) ! l0)
  (prds : list l) (l3 : l) (ps3 : phinodes) (cs11 : list cmd)
  (lid : id) (pid : id) (sid : id)
  (HeqR : ret (lid, pid, sid) = (PI_newids pinfo) ! l3)
  tmn3
  succs (Hsucc : (PI_succs pinfo) ! l3 = ret succs) (Hin : In l0 succs)
  (HBinF : blockInFdefB
            (block_intro l3 ps3 (cs11 ++ nil) tmn3)
            (PI_f pinfo) = true)
  (HuniqF : uniqFdef (PI_f pinfo))
  (HBinF' : blockInFdefB (block_intro l0 ps0 cs0 tmn0) (PI_f pinfo))
  (gvsa : GVsT DGVs) (gv : GenericValue)
  (Hlkp1 : lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa)
  (Hlk2 : lookupAL (GVsT DGVs) lc lid = ret gv)
  (Heq' : (PI_preds pinfo) ! l0 = ret prds)
  (ps3' : phinodes) (cs3' : list cmd)
  (H2 : Opsem.switchToNewBasicBlock (los, nts)
         (block_intro l0
            (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo) prds
             :: ps0)
            (insn_store sid' (PI_typ pinfo) (value_id pid')
               (value_id (PI_id pinfo)) (PI_align pinfo)
             :: cs0 ++
                match (PI_succs pinfo) ! l0 with
                | ret nil => nil
                | ret (_ :: _) =>
                    [insn_load lid' (PI_typ pinfo) 
                       (value_id (PI_id pinfo)) (PI_align pinfo)]
                | merror => nil
                end) tmn0)
         (block_intro l3 ps3'
            (cs3' ++
             [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo))
                (PI_align pinfo)]) tmn3) gl lc = 
       ret lc'),
  lookupAL (GVsT DGVs) lc' pid' = ret gv /\
  lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in H2.
  simpl in H2.
  inv_mbind'.
  assert (v = value_id lid) as EQ'.      
    eapply WF_PhiInfo__getValueViaLabelFromValuels in HeqR2; eauto.
    eapply WF_PhiInfo_br_succs_preds in Hsucc; eauto.
  
  subst v.
  simpl in HeqR0. rewrite Hlk2 in HeqR0. inv HeqR0.
  
  simpl.
  split.
    rewrite lookupAL_updateAddAL_eq; auto.
  
    assert (PI_id pinfo <> pid') as Hneq_pid.
      clear - Hwfpi HeqR1 Huniq. 
      apply WF_PhiInfo_fresh in HeqR1; auto.
    rewrite <- lookupAL_updateAddAL_neq; auto.
  
    eapply WF_PhiInfo__getIncomingValuesForBlockFromPHINodes in Hlkp1; eauto.
Qed.

Definition not_temporaries (i0 : id) (newids : ATree.t (id * id * id)) : Prop :=
forall l0,
  match ATree.get l0 newids with
  | Some (lid, pid, sid) => i0 <> lid /\ i0 <> pid /\ i0 <> sid
  | None => True
  end.

Lemma is_temporary_dec : forall id0 newids,
  is_temporary id0 newids \/ not_temporaries id0 newids.
Proof.
  intros.
  assert (not_temporaries id0 newids \/ ~ not_temporaries id0 newids) as J.
    tauto.
  destruct J; auto.
  left.
  unfold is_temporary, not_temporaries in *.
  apply Coq.Logic.Classical_Pred_Type.not_all_ex_not in H.
  destruct H as [n H].
  exists n.
  destruct (newids ! n) as [[[]]|]; auto.
    destruct (id0 == i0); subst; simpl.
      left. reflexivity.
    destruct (id0 == i1); subst; simpl.
      right. left. reflexivity.
    destruct (id0 == i2); subst; simpl.
      right. right. reflexivity.
    contradict H; auto.
Qed.

Lemma temporaries_exclusive: forall i0 newids0
  (H1: not_temporaries i0 newids0) (H0: is_temporary i0 newids0), False.
Proof.
  intros.
  unfold not_temporaries in H1.
  unfold is_temporary in H0.
  destruct H0 as [l0 H0].
  assert (J:=@H1 l0).
  destruct newids0 ! l0 as [[[]]|].
    destruct J as [J1 [J2 J3]].
    destruct H0 as [H0 | [H0 | H0]].
      contradict J1; auto. 
      destruct (i0 == i1); auto.
        simpl in H0. congruence.
      contradict J2; auto. 
      destruct (i0 == i2); auto.
        simpl in H0. congruence.
      contradict J3; auto. 
      destruct (i0 == i3); auto.
        simpl in H0. congruence.
    inv H0.
Qed.

Definition value_has_no_tmps (pinfo:PhiInfo) (v:value) : Prop :=
match v with
| value_const _ => True
| value_id vid => not_temporaries vid (PI_newids pinfo)
end.

Lemma params_has_no_tmps__intro_aux: forall pinfo lp (init:Prop),
  init ->
  (forall v, valueInParams v lp -> value_has_no_tmps pinfo v) -> 
  fold_left
      (fun (acc : Prop) (p : typ * attributes * value) =>
       let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp init.
Proof.
  induction lp as [|[]]; simpl; intros; auto.
    apply IHlp.
    split; auto.
      apply H0. 
      unfold valueInParams. simpl.
      destruct (split lp). simpl. auto.

      intros.
      apply H0. 
      unfold valueInParams in *. simpl in *.
      destruct (split lp). simpl. auto.
Qed.

Lemma params_has_no_tmps__intro: forall pinfo lp,
  (forall v, valueInParams v lp -> value_has_no_tmps pinfo v) -> 
  fold_left
      (fun (acc : Prop) (p : typ * attributes * value) =>
       let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp True.
Proof.
  intros.
  apply params_has_no_tmps__intro_aux; auto.
Qed.

(* from sb_ds_trans *)
Definition getValueIDs (v:value) : atoms :=
match v with
| value_id id => {{id}}
| value_const _ => {}
end.

(* from sb_ds_trans *)
Definition id_fresh_in_value v1 i2 : Prop :=
match v1 with
| value_id i1 => i1 <> i2
| _ => True
end.

(* from sb_ds_trans *)
Fixpoint ids2atoms (ids0:ids) : atoms :=
match ids0 with
| nil => {}
| id0::ids0' => {{id0}} `union` ids2atoms ids0'
end.

(* from sb_ds_trans_lib *)
Lemma getPhiNodeID_in_getFdefLocs : forall f1 l0 ps p cs tmn,
  blockInFdefB (block_intro l0 ps cs tmn) f1 = true ->
  In p ps ->
  In (getPhiNodeID p) (getFdefLocs f1).
Proof.
  intros.
  destruct f1. destruct f. simpl.
  apply in_or_app. right.
  eapply in_getBlockLocs__in_getBlocksLocs in H; eauto.
  simpl. 
  apply in_or_app. left.
  apply in_getPhiNodeID__in_getPhiNodesIDs; auto.
Qed.  

(* from sb_ds_trans_lib *)
Lemma in_singleton : forall a d, singleton a [<=] d <-> a `in` d.
Proof.
  intros.
  unfold AtomSetImpl.Subset.
  split; intros; eauto.
    assert (a0 = a) as EQ. fsetdec.
    subst. auto.
Qed.      

(* from sb_ds_trans_lib *)
Lemma ids2atoms__in : forall a d, In a d <-> singleton a [<=] (ids2atoms d).
Proof. 
  induction d; simpl.
    split; intros. 
      inv H.

      apply in_singleton in H. 
      fsetdec.
    destruct IHd as [J1 J2].
    split; intros. 
      destruct H as [H | H]; subst. 
        fsetdec.        
        apply J1 in H. fsetdec.
        assert (a = a0 \/ a `in` (ids2atoms d)) as J.
          fsetdec.
        destruct J as [J | J]; subst; auto.
          apply in_singleton in J. eauto.
Qed.

(* from sb_ds_trans_lib *)
Lemma ids2atoms__notin : forall a d, ~ In a d <-> a `notin` (ids2atoms d).
Proof. 
  split; intros.  
    destruct (AtomSetProperties.In_dec a (ids2atoms d)); auto.
      apply in_singleton in i0.
      apply ids2atoms__in in i0. congruence.
    destruct (in_dec eq_atom_dec a d); auto.
      apply ids2atoms__in in i0.
      apply in_singleton in i0. congruence.
Qed.

(* from sb_ds_trans_lib *)
Lemma wf_value_id__in_getFdefLocs : forall S m f v t,
  wf_value S m f v t -> getValueIDs v[<=]ids2atoms (getFdefLocs f).
Proof.
  intros.
  inv H; simpl.
    clear. fsetdec.

    destruct f. destruct f. simpl in *.
    remember (lookupTypViaIDFromArgs a id5) as R.
    apply ids2atoms__in.
    destruct R; inv H2.
      symmetry in HeqR.
      destruct (In_dec eq_atom_dec id5 (getArgsIDs a)) as [Hin | Hnotin].
        apply in_or_app. auto.

        apply NotInArgsIDs_lookupTypViaIDFromArgs in Hnotin.
        rewrite HeqR in Hnotin. inv Hnotin.
      destruct (In_dec eq_atom_dec id5 (getBlocksLocs b)) as [Hin | Hnotin].
        apply in_or_app. auto.
        
        apply notInBlocks__lookupTypViaIDFromBlocks in Hnotin.
        rewrite H3 in Hnotin. inv Hnotin.
Qed.

Lemma wf_value_id__in_getFdefLocs' : forall S m f v t,
  wf_value S m f v t -> 
  match v with
  | value_id vid => In vid (getFdefLocs f)
  | _ => True
  end.
Proof.
  intros.
  destruct v; auto.
  apply wf_value_id__in_getFdefLocs in H.
  simpl in H.
  apply ids2atoms__in in H; auto.
Qed.

Lemma original_values_arent_tmps: forall ifs S m pinfo F B v instr
  (HwfF: wf_fdef ifs S m F)
  (Hwfpi: WF_PhiInfo pinfo) 
  (HBinF : insnInFdefBlockB instr F B = true)
  (HvInOps : valueInInsnOperands v instr),
  if fdef_dec (PI_f pinfo) F then value_has_no_tmps pinfo v else True.
Proof.
  intros.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  destruct v; simpl; auto.
  destruct Hwfpi as [_ [_ [_ [_ Hfresh]]]].
  intros l0.
  rewrite Hfresh.
  remember ((fst (gen_fresh_ids (PI_rd pinfo) (getFdefLocs (PI_f pinfo)))) ! l0)
    as R.
  destruct R as [[[]]|]; auto.
  eapply wf_fdef__wf_insn in HBinF; eauto.
  eapply wf_insn__wf_value in HvInOps; eauto.
  destruct HvInOps as [t HvInOps].
  apply wf_value_id__in_getFdefLocs' in HvInOps.
  destruct (i0 == i1); subst.
    assert (is_temporary i1 
             (fst (gen_fresh_ids 
                  (PI_rd pinfo) (getFdefLocs (PI_f pinfo))))) as Histmp.
      exists l0. rewrite <- HeqR. auto.
      destruct (i1 == i1); simpl; try congruence.
      left. reflexivity.
   apply gen_fresh_ids__spec in Histmp; auto.
  split; auto.
  destruct (i0 == i2); subst.
    assert (is_temporary i2 
             (fst (gen_fresh_ids 
                  (PI_rd pinfo) (getFdefLocs (PI_f pinfo))))) as Histmp.
      exists l0. rewrite <- HeqR. auto.
      destruct (i2 == i2); simpl; try congruence.
      right. left. reflexivity.
   apply gen_fresh_ids__spec in Histmp; auto.
  split; auto.
  destruct (i0 == i3); subst; auto.
    assert (is_temporary i3 
             (fst (gen_fresh_ids 
                  (PI_rd pinfo) (getFdefLocs (PI_f pinfo))))) as Histmp.
      exists l0. rewrite <- HeqR. auto.
      destruct (i3 == i3); simpl; try congruence.
      right. right. reflexivity.
   apply gen_fresh_ids__spec in Histmp; auto.
Qed.

Lemma original_values_in_cmd_arent_tmps: forall (pinfo : PhiInfo) 
  (Hwfpi : WF_PhiInfo pinfo) (l1 : l) (ps1 : phinodes) (cs11 cs1' : list cmd)
  v c (Hin : valueInCmdOperands v c) tmn ifs S m F1
  (HwfF: wf_fdef ifs S m F1)
  (HBinF : blockInFdefB
            (block_intro l1 ps1 (cs11 ++ c :: cs1')
               tmn) F1 = true),
   if fdef_dec (PI_f pinfo) F1
   then value_has_no_tmps pinfo v
   else True.
Proof.
  intros.
  eapply original_values_arent_tmps with
    (B:=block_intro l1 ps1 (cs11 ++ c :: cs1') tmn) (instr:=insn_cmd c); 
    simpl; eauto.
  apply andb_true_iff.
  split; auto.
    apply In_InCmdsB. apply in_middle.
Qed.

Lemma original_ids_in_phi_arent_temporaries: forall pinfo l1 ps1 cs1 tmn l3 vid
  vls pid typ ifs S m (HwfF: wf_fdef ifs S m (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn) (PI_f pinfo) = true ->
  In (insn_phi pid typ vls) ps1 ->
  Some (value_id vid) = getValueViaLabelFromValuels vls l3 ->
  not_temporaries vid (PI_newids pinfo).
Proof.
  intros.
  assert (insnInFdefBlockB 
           (insn_phinode (insn_phi pid typ0 vls)) (PI_f pinfo)
           (block_intro l1 ps1 cs1 tmn)) as Hin. 
    apply andb_true_iff.
    split; auto.
      simpl.
      apply In_InPhiNodesB. auto.
  eapply original_values_arent_tmps with (v:=value_id vid) in Hin; simpl; eauto.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl in Hin. auto.

    symmetry in H2.
    eapply getValueViaLabelFromValuels__In_list_prj1; eauto.
Qed.

Lemma original_indxs_arent_tmps: forall pinfo F1 l1 ps1 cs11 id0 inbounds0 t v
  idxs cs1' tmn (Hwfpi: WF_PhiInfo pinfo) ifs S m (HwfF: wf_fdef ifs S m F1)
  (HBinF : blockInFdefB
            (block_intro l1 ps1
               (cs11 ++ insn_gep id0 inbounds0 t v idxs :: cs1') tmn) F1 =
            true),
  if fdef_dec (PI_f pinfo) F1 then
    forall nth sz0 v0,
      nth_list_sz_value nth idxs = Some (sz0, v0) ->
      value_has_no_tmps pinfo v0
  else True.
Proof.
  intros.
  destruct (fdef_dec (PI_f pinfo) F1); subst; auto.
  intros.
  eapply original_values_in_cmd_arent_tmps with (v:=v0) in HBinF; eauto.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl.
    right. apply nth_list_sz_value__valueInListValue in H; auto.
Qed.

Lemma WF_PhiInfo_spec12: forall pinfo l1 ps1 cs1 rid noret0 ca ft fv lp cs2 tmn
  F1 ifs S m (HwfF: wf_fdef ifs S m F1),
  WF_PhiInfo pinfo ->
  blockInFdefB 
    (block_intro l1 ps1 (cs1 ++ insn_call rid noret0 ca ft fv lp :: cs2) tmn) 
    F1 = true ->
  if fdef_dec (PI_f pinfo) F1 then
    fold_left
      (fun (acc : Prop) (p : typ * attributes * value) =>
       let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp True
  else True.  
Proof.
  intros.
  destruct (fdef_dec (PI_f pinfo) F1); subst; auto.
  apply params_has_no_tmps__intro.
  intros.
  eapply original_values_in_cmd_arent_tmps with (v:=v) in H0; eauto.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl. auto.
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

Ltac solve_in_prefix :=
repeat match goal with
| G: In ?i (?prefix ++ _) |- In ?i (?prefix ++ _) =>
  apply in_or_app;
  apply in_app_or in G;
  destruct G as [G | G]; auto;
  right
end.

Lemma phinodes_placement_blocks__disjoint_tmps: forall l0 i1 i2 i3 i0
  pid t al nids succs preds 
  (Hdisj: forall l1 l2 a1 b1 c1 a2 b2 c2, 
    l1 <> l2 ->
    ret (a1, b1, c1) = nids ! l1 ->
    ret (a2, b2, c2) = nids ! l2 ->
    a1 <> a2 /\ a1 <> b2 /\ a1 <> c2 /\
    b1 <> a2 /\ b1 <> b2 /\ b1 <> c2 /\
    c1 <> a2 /\ c1 <> b2 /\ c1 <> c2) 
  (J1: ret (i1, i2, i3) = nids ! l0)
  (J2: i0 = i1 \/ i0 = i2 \/ i0 = i3) bs,
  ~ In l0 (getBlocksLabels bs) ->
  In i0 (getBlocksLocs
           (phinodes_placement_blocks bs pid t al nids succs preds)) ->
  In i0 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros; auto.
    destruct a. simpl in *.
    assert (l1 <> l0 /\ ~ In l0 (getBlocksLabels bs)) as J.
      split.
        intro J. subst. auto.
        intro J. contradict H; auto.
    destruct J as [J3 J4].
    apply in_app_or in H0.
    destruct H0 as [H0 | H0].

Ltac solve_in_head := 
match goal with
| H0 : In _ ([_] ++ _),
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
| H0 : In _ (_:: _),
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
| H0 : _ = _ \/ In _ _,
  J2 : _ \/ _ \/ _ |- _ =>
    simpl in H0;
    destruct H0 as [H0 | H0]; subst; try solve [
      destruct J2 as [J2 | [J2 | J2]]; subst;
        repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end; congruence]
end.

    remember (nids ! l1) as R1.
    remember (preds ! l1) as R2.
    remember (succs ! l1) as R3.
    simpl_env.
    destruct R1 as [[[]]|]; auto.
      eapply Hdisj in J1; eauto.
      clear Hdisj. 
      destruct R2 as [[]|].
        destruct R3 as [[]|]; simpl in H0; simpl_env in H0.
          solve_in_prefix.
          apply in_or_app. auto.

          repeat rewrite getCmdsLocs_app in H0; simpl in H0; simpl_env in H0.     
          solve_in_prefix.
          solve_in_head.
          apply in_or_app. simpl. 
          destruct H0 as [H0 | H0]; auto.

          solve_in_prefix.
          apply in_or_app. auto.

        destruct R3 as [[]|]; simpl in H0; simpl_env in H0.
          solve_in_head.
          solve_in_prefix.
          solve_in_head.
          solve_in_prefix.
          apply in_or_app. auto.

          repeat rewrite getCmdsLocs_app in H0; simpl in H0; simpl_env in H0.     
          solve_in_head.
          solve_in_prefix.
          solve_in_head.
          solve_in_prefix.
          solve_in_head.
          apply in_or_app. auto.

          solve_in_head.
          solve_in_prefix.
          solve_in_head.
          solve_in_prefix.
          apply in_or_app. auto.

        destruct R3 as [[]|]; simpl in H0; simpl_env in H0.
          solve_in_prefix.
          apply in_or_app. auto.

          repeat rewrite getCmdsLocs_app in H0; simpl in H0; simpl_env in H0.     
          solve_in_prefix.
          solve_in_head.
          apply in_or_app. simpl. 
          destruct H0 as [H0 | H0]; auto.

          solve_in_prefix.
          apply in_or_app. auto.

      simpl in H0. simpl_env in H0.
      solve_in_prefix.
      apply in_or_app. auto.

    apply IHbs in H0; auto.
    apply in_or_app. auto.
Qed.

Lemma WF_PhiInfo_spec10: forall pinfo l1 ps1 cs1 c cs2 tmn 
  (Huniq: uniqFdef (PI_f pinfo)),
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs2) tmn) (PI_f pinfo) = true
    ->
  match c with
  | insn_alloca _ _ _ _ => False 
  | _ => True
  end ->
  PI_id pinfo <> getCmdLoc c.  
Proof.
  intros.
  apply WF_PhiInfo_spec1 in H; auto.
  destruct H as [v H].
  eapply IngetCmdsIDs__lookupCmdViaIDFromFdef in H0; eauto using in_middle.
  destruct (PI_id pinfo == getCmdLoc c); subst; auto.
  rewrite e in H.
  rewrite H in H0. clear e.
  inversion H0. rewrite <- H3 in H1. inv H1.
Qed.

Lemma WF_PhiInfo_spec11: forall pinfo l1 ps1 cs1 c cs2 tmn,
  WF_PhiInfo pinfo ->
  blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs2) tmn) (PI_f pinfo) = true
    ->
  match c with
  | insn_alloca _ _ _ _ => False 
  | _ => True
  end ->
  not_temporaries (getCmdLoc c) (PI_newids pinfo).  
Proof.
  intros.
  eapply getCmdLoc_in_getFdefLocs in H0; eauto.
  destruct (is_temporary_dec (getCmdLoc c) (PI_newids pinfo)); auto.
  destruct H as [J1 [J2 [J3 [J4 J5]]]].
  rewrite J5 in H2.
  apply gen_fresh_ids__spec in H2; auto.
  contradict H0; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
*)

