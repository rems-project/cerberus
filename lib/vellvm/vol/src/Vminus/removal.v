Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vminus.

Definition remove_phinodes (id':id) (ps:phinodes) : phinodes := 
  (List.filter (fun p => negb (id_dec (getPhiNodeID p) id')) ps).
 
Definition remove_cmds (id':id) (cs:cmds) : cmds := 
  (List.filter (fun c => negb (id_dec (getCmdLoc c) id')) cs).

Definition remove_block (id':id) (b:block) : block := 
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro l0 (remove_phinodes id' ps0) (remove_cmds id' cs0) tmn0
end.

Definition remove_fdef (id':id) (f:fdef) : fdef := 
match f with
| fdef_intro bs => fdef_intro (List.map (remove_block id') bs) 
end.

Definition used_in_value (id0:id) (v:value) : bool :=
match v with
| value_id id1 => id_dec id1 id0
| _ => false
end.

Definition used_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_bop _ _ v1 v2 | insn_icmp _ _ v1 v2 => 
  used_in_value id' v1 || used_in_value id' v2
end.

Definition used_in_tmn (id':id) (tmn:terminator) : bool :=
match tmn with
| insn_br _ v0 _ _ | insn_return _ v0 => used_in_value id' v0
| _ => false
end.

Fixpoint used_in_list_value_l (id':id) (l0:list_value_l) : bool :=
match l0 with
| Nil_list_value_l => false
| Cons_list_value_l v0 _ tl => 
    used_in_value id' v0 || used_in_list_value_l id' tl
end.

Definition used_in_phi (id':id) (pn:phinode) : bool :=
match pn with
| insn_phi _ vls => used_in_list_value_l id' vls
end.

Definition used_in_insn (id':id) (instr:insn) : bool :=
match instr with
| insn_cmd c => used_in_cmd id' c
| insn_phinode p => used_in_phi id' p
| insn_terminator tmn => used_in_tmn id' tmn
end.

Definition used_in_block (id':id) (b:block) : bool := 
match b with
| block_intro _ ps0 cs0 tmn0 =>
  (List.fold_left (fun re p => re || used_in_phi id' p) ps0 false) ||
  (List.fold_left (fun re c => re || used_in_cmd id' c) cs0 false) ||
  (used_in_tmn id' tmn0)
end.

Definition used_in_fdef (id':id) (f:fdef) : bool := 
match f with
| fdef_intro bs => 
  List.fold_left (fun re b => re || used_in_block id' b) bs false
end.

(************** Preserving wellformedness **************************************)

Lemma remove_getEntryBlock : forall f id0 b
  (Hentry : getEntryBlock f = Some b),
  getEntryBlock (remove_fdef id0 f) = Some (remove_block id0 b).
Proof.
  intros. destruct f. simpl in *.
  destruct b0; inv Hentry; auto.
Qed.

Lemma remove_getEntryBlock_None : forall f id0
  (Hentry : getEntryBlock f = None),
  getEntryBlock (remove_fdef id0 f) = None.
Proof.
  intros. destruct f. simpl in *.
  destruct b; inv Hentry; auto.
Qed.

Lemma remove_genBlockUseDef_block : forall id0 b ud,
  genBlockUseDef_block b ud = 
  genBlockUseDef_block (remove_block id0 b) ud.
Proof.
  intros. destruct b; simpl.
  destruct t; auto.
Qed.

Lemma remove_genBlockUseDef_blocks : forall id0 bs ud,
  genBlockUseDef_blocks bs ud = 
  genBlockUseDef_blocks (List.map (remove_block id0) bs) ud.
Proof.
  induction bs; simpl; intros; auto.
    rewrite <- IHbs.
    rewrite <- remove_genBlockUseDef_block; auto.
Qed.

Lemma remove_hasNonePredecessor : forall f id0 b
  (Hnpred : hasNonePredecessor b (genBlockUseDef_fdef f) = true),
  hasNonePredecessor (remove_block id0 b) 
    (genBlockUseDef_fdef (remove_fdef id0 f)) = true.
Proof.
  intros. destruct f. simpl in *.
  rewrite <- remove_genBlockUseDef_blocks.
  destruct b; auto.
Qed.

Lemma remove_InBlocksLabels : forall (id0 : id) l0 (bs : blocks)
  (Hin : In l0 (getBlocksLabels (List.map (remove_block id0) bs))),
  In l0 (getBlocksLabels bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl. intro.
    destruct Hin as [Hin | Hin]; auto.
Qed.

Lemma remove_uniqBlocksLabels : forall (id0 : id) (bs : blocks)
  (HuniqBs : NoDup (getBlocksLabels bs)),
  NoDup (getBlocksLabels (List.map (remove_block id0) bs)).
Proof.
  induction bs; simpl; intros; auto.
    destruct a. simpl.
    inv HuniqBs.
    apply NoDup_cons; eauto using remove_InBlocksLabels.
Qed.

Hint Constructors sublist NoDup.

Hint Resolve sublist_refl sublist_weaken sublist_app : ssa_remove.

Lemma remove_getPhiNodesIDs : forall id0 ps,
  sublist _ (getPhiNodesIDs (remove_phinodes id0 ps)) (getPhiNodesIDs ps).
Proof.
  induction ps; simpl; auto.
    destruct a. simpl in *. 
    destruct (id_dec i0 id0); subst; simpl; auto.
Qed.

Lemma remove_getCmdsLocs : forall id0 cs,
  sublist _ (getCmdsLocs (remove_cmds id0 cs)) (getCmdsLocs cs).
Proof.
  induction cs; simpl; auto.
    destruct a; simpl in *; destruct (id_dec i0 id0); subst; simpl; auto.
Qed.

Hint Resolve remove_getPhiNodesIDs remove_getCmdsLocs : ssa_remove.

Lemma remove_blocksLocs : forall (id0 : id) (bs : blocks),
  sublist _ (getBlocksLocs (List.map (remove_block id0) bs)) (getBlocksLocs bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl. simpl_env. auto with ssa_remove.
Qed.

Hint Resolve remove_blocksLocs : ssa_remove.

Lemma remove_uniqBlocksLocs : forall (id0 : id) (bs : blocks)
  (HuniqBs : NoDup (getBlocksLocs bs)),
  NoDup (getBlocksLocs (List.map (remove_block id0) bs)).
Proof. intros. eapply sublist_NoDup; eauto with ssa_remove. Qed.

Hint Resolve remove_uniqBlocksLabels remove_uniqBlocksLocs : ssa_remove.

Lemma remove_uniqBlocks : forall (id0 : id) (bs : blocks)
  (HuniqBs : uniqBlocks bs),
  uniqBlocks (List.map (remove_block id0) bs).
Proof.
  intros.
  destruct HuniqBs as [J1 J2].
  split; auto with ssa_remove.
Qed. 

Lemma remove_uniqFdef : forall f id0 (HuniqF : uniqFdef f),
  uniqFdef (remove_fdef id0 f).
Proof.
  intros.
  destruct f. simpl in *. apply remove_uniqBlocks; auto.
Qed.

Lemma remove_InBlocksB : forall id0 b bs
  (Hin : InBlocksB b bs = true),
  InBlocksB (remove_block id0 b) (List.map (remove_block id0) bs) = true.
Proof.
  induction bs; simpl; intros; auto.
    apply orb_prop in Hin.
    apply orb_true_intro. 
    destruct Hin as [Hin | Hin]; auto.
      left.
      destruct b. destruct a. unfold blockEqB in *.
      apply eq_sumbool2bool_true. 
      apply sumbool2bool_true in Hin.
      inv Hin. auto.
Qed.

Hint Resolve remove_InBlocksB: ssa_remove.

Lemma remove_blockInFdefB : forall f id0 b
  (Hin : blockInFdefB b f = true),
  blockInFdefB (remove_block id0 b) (remove_fdef id0 f) = true.
Proof.
  intros. destruct f. simpl in *.
  auto with ssa_remove.
Qed.

Hint Resolve remove_blockInFdefB: ssa_remove.

Lemma remove_InPhiNodesB : forall id0 p ps, 
  getPhiNodeID p <> id0 ->
  InPhiNodesB p ps = true ->
  InPhiNodesB p (remove_phinodes id0 ps) = true.
Proof.
  induction ps; simpl; intros.
    congruence.

    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0].
      apply phinodeEqB_inv in H0; subst;
      destruct (id_dec (getPhiNodeID a) id0); subst; simpl; 
        try solve [auto | apply orb_true_iff; left; apply phinodeEqB_refl].
      destruct (id_dec (getPhiNodeID a) id0); subst; simpl; 
        try solve [auto | apply orb_true_iff; right; auto].
Qed.

Hint Resolve remove_InPhiNodesB: ssa_remove.

Lemma remove_phinodeInBlockB : forall id0 p b
  (Heq : getPhiNodeID p <> id0)
  (Hin : phinodeInBlockB p b = true),
  phinodeInBlockB p (remove_block id0 b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_remove.
Qed. 

Hint Resolve remove_phinodeInBlockB: ssa_remove.

Lemma remove_InCmdsB : forall id0 c cs, 
  getCmdLoc c <> id0 ->
  InCmdsB c cs = true ->
  InCmdsB c (remove_cmds id0 cs) = true.
Proof.
  induction cs; simpl; intros; auto.
    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0]; auto.
      apply cmdEqB_inv in H0; subst;
      destruct (id_dec (getCmdLoc a) id0); subst; simpl; 
        try solve [auto | apply orb_true_iff; left; apply cmdEqB_refl].
      destruct (id_dec (getCmdLoc a) id0); subst; simpl; 
        try solve [auto | apply orb_true_iff; right; auto].
Qed.

Hint Resolve remove_InCmdsB: ssa_remove.

Lemma remove_cmdInBlockB : forall id0 c b
  (Heq : getCmdLoc c <> id0)
  (Hin : cmdInBlockB c b = true),
  cmdInBlockB c (remove_block id0 b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_remove.
Qed. 

Hint Resolve remove_cmdInBlockB: ssa_remove.

Lemma remove_terminatorInBlockB : forall id0 t b
  (Hin : terminatorInBlockB t b = true),
  terminatorInBlockB t (remove_block id0 b) = true.
Proof.
  destruct b. simpl. intro. 
  apply terminatorEqB_inv in Hin. subst.
  apply terminatorEqB_refl.
Qed. 

Hint Resolve remove_terminatorInBlockB: ssa_remove.

Definition unremovable (id':id) (instr : insn) : Prop :=
match instr with
| insn_cmd c => getCmdLoc c <> id'
| insn_phinode p => getPhiNodeID p <> id'
| _ => True
end.

Lemma remove_insnInFdefBlockB : forall f id0 b instr
  (Hneq : unremovable id0 instr)
  (Hin : insnInFdefBlockB instr f b = true),
  insnInFdefBlockB instr (remove_fdef id0 f) (remove_block id0 b) = true.
Proof.
  unfold insnInFdefBlockB.
  intros.
  destruct instr; simpl in *;
    apply andb_true_iff in Hin; inv Hin;
    apply andb_true_iff; auto with ssa_remove.
Qed.

Hint Resolve remove_insnInFdefBlockB: ssa_remove.

Lemma remove_getCmdsIDs : forall id0 cs,
  sublist _ (getCmdsIDs (remove_cmds id0 cs)) (getCmdsIDs cs).
Proof.
  induction cs; simpl; intros; auto.
    destruct a; simpl in *; destruct (id_dec i0 id0); subst; simpl; auto.
Qed.

Lemma remove_In_getPhiNodesIDs1 : forall id5 id' ps,
  id5 <> id' ->
  In id5 (getPhiNodesIDs ps) ->
  In id5 (getPhiNodesIDs (remove_phinodes id' ps)).
Proof.
  induction ps; simpl; intros. auto.
    destruct H0 as [H0 | H0]; subst.
      destruct (id_dec (getPhiNodeID a) id'); subst; simpl; auto.
        congruence.
      destruct (id_dec (getPhiNodeID a) id'); subst; simpl; auto.
Qed.

Lemma remove_In_getPhiNodesIDs2 : forall id5 id' ps,
  id5 <> id' ->
  In id5 (getPhiNodesIDs (remove_phinodes id' ps)) ->
  In id5 (getPhiNodesIDs ps).
Proof.
  induction ps; simpl; intros; auto.
    destruct (id_dec (getPhiNodeID a) id'); subst; simpl in *; auto.
    destruct H0 as [H0 | H0]; subst; auto.
Qed.

Lemma remove_In_getCmdsIDs1 : forall id5 id' cs,
  id5 <> id' ->
  In id5 (getCmdsIDs cs) ->
  In id5 (getCmdsIDs (remove_cmds id' cs)).
Proof.
  induction cs; simpl; intros. auto.
    destruct a; simpl in *;
      destruct H0 as [H0 | H0]; subst; try solve [
        destruct (id_dec id5 id'); subst; simpl; try solve [auto | congruence] |
        destruct (id_dec i0 id'); subst; simpl; auto].
Qed.

Lemma remove_In_getCmdsIDs2 : forall id5 id' cs,
  id5 <> id' ->
  In id5 (getCmdsIDs (remove_cmds id' cs)) ->
  In id5 (getCmdsIDs cs).
Proof.
  induction cs; simpl; intros. auto.
    destruct a; simpl in *;
      destruct (id_dec i0 id'); subst; simpl in *; 
        try solve [auto | destruct H0 as [H0 | H0]; subst; auto].
Qed.

Hint Resolve remove_In_getPhiNodesIDs1 remove_In_getCmdsIDs1
             remove_In_getPhiNodesIDs2 remove_In_getCmdsIDs2 : ssa_remove.

Lemma remove_lookupBlockViaIDFromBlocks : forall id5 id' bs b,
  id5 <> id' ->
  lookupBlockViaIDFromBlocks bs id5 = ret b ->
  lookupBlockViaIDFromBlocks (List.map (remove_block id') bs) id5 = 
    ret (remove_block id' b).
Proof.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    destruct (in_dec eq_dec id5 (getPhiNodesIDs p ++ getCmdsIDs c)).
      inv H0.
      destruct(in_dec eq_dec id5
         (getPhiNodesIDs (remove_phinodes id' p) ++
          getCmdsIDs (remove_cmds id' c))); auto.
        contradict n.
        apply in_or_app.
        apply in_app_or in i0.
        destruct i0 as [i0 | i0]; auto with ssa_remove.

      destruct(in_dec eq_dec id5
         (getPhiNodesIDs (remove_phinodes id' p) ++
          getCmdsIDs (remove_cmds id' c))); auto.
        contradict n.
        apply in_or_app.
        apply in_app_or in i0.
        destruct i0 as [i0 | i0]; eauto with ssa_remove.
Qed.

Hint Resolve remove_lookupBlockViaIDFromBlocks : ssa_remove.

Lemma remove_lookupBlockViaIDFromFdef : forall f id5 b id',
  id5 <> id' ->
  lookupBlockViaIDFromFdef f id5 = ret b ->
  lookupBlockViaIDFromFdef (remove_fdef id' f) id5 = ret (remove_block id' b).
Proof.
  destruct f. simpl; intros. auto with ssa_remove.
Qed.

Hint Resolve remove_lookupBlockViaIDFromFdef: ssa_remove.

Lemma remove_successors_blocks : forall id' bs,
  successors_blocks bs = successors_blocks (List.map (remove_block id') bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl.
    rewrite IHbs.
    destruct t; auto.
Qed.

Hint Resolve remove_successors_blocks: ssa_remove.

Lemma remove_successors : forall f id',
  successors f = successors (remove_fdef id' f).
Proof.
  intros. destruct f. simpl. auto with ssa_remove.
Qed.

Lemma remove_bound_blocks : forall id' bs,
  bound_blocks bs = bound_blocks (List.map (remove_block id') bs).
Proof.
  induction bs; simpl; auto.
    destruct a; simpl. rewrite IHbs. auto.
Qed.

Hint Resolve remove_bound_blocks.

Lemma remove_vertexes_fdef: forall f id',
  vertexes_fdef f = vertexes_fdef (remove_fdef id' f).
Proof.
  unfold vertexes_fdef.
  destruct f. simpl. intro.
  rewrite <- remove_bound_blocks. auto.
Qed.

Lemma remove_arcs_fdef: forall f id',
  arcs_fdef f = arcs_fdef (remove_fdef id' f).
Proof.
  unfold arcs_fdef.
  destruct f. simpl. intro.
  rewrite <- remove_successors_blocks. auto.
Qed.

Lemma remove_reachable : forall f id',
  reachable f = reachable (remove_fdef id' f).
Proof.
  intros.
  unfold reachable.
  case_eq (getEntryBlock f).
    intros b Hentry. 
    apply remove_getEntryBlock with (id0:=id') in Hentry; eauto.
    rewrite Hentry.
    destruct b. simpl.
    rewrite <- remove_vertexes_fdef.
    rewrite <- remove_arcs_fdef. auto.

    intro Hentry.
    apply remove_getEntryBlock_None with (id0:=id') in Hentry; eauto.
    rewrite Hentry. auto.
Qed.

Lemma remove_isReachableFromEntry : forall f b id',
  isReachableFromEntry f b = 
    isReachableFromEntry (remove_fdef id' f) (remove_block id' b).
Proof.
  unfold isReachableFromEntry. intros.
  destruct b. simpl. rewrite <- remove_reachable; auto.
Qed.

Lemma remove_blockDominates : forall f b1 b2 id',
  blockDominates f b1 b2 <->
    blockDominates (remove_fdef id' f) (remove_block id' b1)
      (remove_block id' b2).
Proof.
  intros.
  unfold blockDominates. destruct b1. destruct b2. simpl.
  unfold dom_analyze. destruct f. simpl.
  rewrite <- remove_successors_blocks.
  remember (entry_dom b) as R1.
  remember (entry_dom (List.map (remove_block id') b)) as R2.
  destruct R1 as [x1 Hx1]. 
  destruct R2 as [x2 Hx2]. 
  destruct x1 as [x1|]. 
  Case "1".
    destruct x1 as [le1 start1].
    destruct start1.
    destruct bs_contents as [|l2 bs_contents]; tinv Hx1.
    destruct x2 as [x2|]. 
    SCase "1.1".
      destruct x2 as [le2 start2].
      destruct start2.
      destruct bs_contents as [|l3 bs_contents]; tinv Hx2.
      destruct b; tinv HeqR1.
      destruct b. 
      inv HeqR1. inv HeqR2. 
      eapply blockDominates_iff; eauto.
    SCase "1.2".
      destruct b; simpl in *; tinv HeqR1.
        inv Hx2.
  Case "2".
    subst. simpl in *. inv HeqR2. split; intro; auto.
Qed.

Hint Resolve not_id_dec__neq : ssa_remove.

Lemma noused_values2ids : forall id' l0 
  (H2 : used_in_list_value_l id' l0 = false),
  ~ In id' (values2ids (list_prj1 value l (unmake_list_value_l l0))).
Proof.
  induction l0; simpl; intros; auto.
    destruct v; simpl in *; auto.
    binvf H2 as H1 H2; subst; auto.
    apply IHl0 in H2. 
    intro J. 
    destruct J as [J | J]; subst; auto.
      apply not_id_dec__neq in H1; auto.
Qed.     

Hint Resolve noused_values2ids : ssa_remove.

Lemma noused_getPhiNodeOperands : forall id' p
  (H2 :used_in_phi id' p = false),
  ~ In id' (getPhiNodeOperands p).
Proof.
  destruct p; simpl; intros. auto with ssa_remove.
Qed.

Lemma noused_getCmdOperands_helper : forall id' v v0
  (n : used_in_value id' v || used_in_value id' v0 = false),
  ~ In id' (getValueIDs v ++ getValueIDs v0).
Proof.
  intros.
  binvf n as H1 H2.
  destruct v; simpl in *.
    apply not_id_dec__neq in H1.
    destruct v0; simpl in *.
      apply not_id_dec__neq in H2.
      intro J. destruct J as [J | [J | J]]; auto.

      intro J. destruct J as [J | J]; auto.

    destruct v0; simpl in *; auto.
      apply not_id_dec__neq in H2.
      intro J. destruct J as [J | J]; auto.
Qed.

Hint Resolve noused_getCmdOperands_helper: ssa_remove.

Lemma noused_getCmdOperands : forall id' c
  (H2 : used_in_cmd id' c = false),
  ~ In id' (getCmdOperands c).
Proof.
  destruct c; simpl; intros; auto with ssa_remove.
Qed.

Lemma noused_getTerminatorOperands : forall id' t
  (H2 : used_in_tmn id' t = false),
  ~ In id' (getTerminatorOperands t).
Proof.
  destruct t; simpl; intros; auto.
    destruct v; simpl in *; auto.
      apply not_id_dec__neq in H2.
      intro J. destruct J as [J | J]; auto.
    destruct v; simpl in *; auto.
      apply not_id_dec__neq in H2.
      intro J. destruct J as [J | J]; auto.
Qed.

Hint Resolve noused_getCmdOperands noused_getPhiNodeOperands
  noused_getTerminatorOperands: ssa_remove.

Lemma noused_getInsnOperands : forall id' instr 
  (H2 : used_in_insn id' instr = false),
  ~ In id' (getInsnOperands instr).
Proof.
  destruct instr; simpl; auto with ssa_remove.
Qed.

Lemma remove_phinodes_neq : forall p1 ps2 id' ps1,
  getPhiNodeID p1 <> id' ->
  exists ps0, exists ps3,
    remove_phinodes id' (ps1 ++ p1 :: ps2) = ps0 ++ p1 :: ps3 /\
    remove_phinodes id' ps1 = ps0 /\
    remove_phinodes id' ps2 = ps3.
Proof.
  induction ps1; intros; simpl.
    destruct (id_dec (getPhiNodeID p1) id'); subst; simpl.
      congruence.
      exists nil. exists (remove_phinodes id' ps2). auto.
    destruct (id_dec (getPhiNodeID a) id'); subst; simpl; auto.
      apply IHps1 in H. destruct H as [ps0 [ps3 [H [J1 J2]]]].
      exists (a::ps0). exists ps3. rewrite H. rewrite J1. rewrite J2. auto.
Qed.

Lemma remove_cmds_neq : forall id' cs2 c1 cs1
  (Hneq1 : getCmdLoc c1 <> id'),
   exists cs0 : list cmd,
     exists cs4 : list cmd,
       remove_cmds id' (cs1 ++ c1 :: cs2) = cs0 ++ c1 :: cs4 /\
       remove_cmds id' cs1 = cs0 /\
       remove_cmds id' cs2 = cs4.
Proof.
  induction cs1; simpl in *; intros.
    destruct (id_dec (getCmdLoc c1) id'); subst.
      congruence.
      exists nil. exists (remove_cmds id' cs2). auto.
    destruct (id_dec (getCmdLoc a) id'); subst; simpl; auto.
      apply IHcs1 in Hneq1. destruct Hneq1 as [cs0 [cs3 [Hneq1 [J1 J2]]]].
      exists (a::cs0). exists cs3. rewrite Hneq1. rewrite J1. rewrite J2. auto.
Qed.

Lemma remove_phinodes_neq_inv : forall id' ps p1 ps3 ps0,
  getPhiNodeID p1 <> id' ->
  remove_phinodes id' ps  = ps0 ++ p1 :: ps3 ->
  exists ps1, exists ps2,
    ps = ps1 ++ p1 :: ps2 /\
    remove_phinodes id' ps1 = ps0 /\
    remove_phinodes id' ps2 = ps3.
Proof.
  induction ps; simpl; intros.
    inv H0. symmetry in H2. contradict H2. apply app_cons_not_nil; auto.

    destruct (id_dec (getPhiNodeID a) id'); subst; simpl in *.
      apply IHps in H0; auto.
      destruct H0 as [ps1 [ps2 [H0 [J1 J2]]]]; subst.
      exists (a::ps1). exists ps2. simpl.
      destruct (id_dec (getPhiNodeID a) (getPhiNodeID a)); simpl; auto.
        congruence.

      destruct ps0; inv H0. 
        exists nil. exists ps. auto.

        apply IHps in H3; auto.
        destruct H3 as [ps1 [ps2 [H3 [J1 J2]]]]; subst.
        exists (p::ps1). exists ps2. simpl.
        destruct (id_dec (getPhiNodeID p) id'); subst; simpl; auto.
          congruence.
Qed.

Lemma remove_cmds_neq_inv : forall id' cs c1 cs3 cs0,
  getCmdLoc c1 <> id' ->
  remove_cmds id' cs  = cs0 ++ c1 :: cs3 ->
  exists cs1, exists cs2,
    cs = cs1 ++ c1 :: cs2 /\
    remove_cmds id' cs1 = cs0 /\
    remove_cmds id' cs2 = cs3.
Proof.
  induction cs; simpl; intros.
    inv H0. symmetry in H2. contradict H2. apply app_cons_not_nil; auto.

    destruct (id_dec (getCmdLoc a) id'); subst; simpl in *.
      apply IHcs in H0; auto.
      destruct H0 as [cs1 [cs2 [H0 [J1 J2]]]]; subst.
      exists (a::cs1). exists cs2. simpl.
      destruct (id_dec (getCmdLoc a) (getCmdLoc a)); simpl; auto.
        congruence.

      destruct cs0; inv H0. 
        exists nil. exists cs. auto.

        apply IHcs in H3; auto.
        destruct H3 as [cs1 [cs2 [H3 [J1 J2]]]]; subst.
        exists (c::cs1). exists cs2. simpl.
        destruct (id_dec (getCmdLoc c) id'); subst; simpl; auto.
          congruence.
Qed.

Lemma remove_insnDominates : forall i0 instr id' b, 
  NoDup (getBlockLocs b) ->
  unremovable id' instr ->
  i0 <> id' ->
  insnInBlockB instr b = true ->
  (insnDominates i0 instr b <->
  insnDominates i0 instr (remove_block id' b)).
Proof.
 intros i0 instr id' b Hnodup Hneq1 Hneq2 HiInB. destruct b. simpl.
 destruct instr; simpl; split; intro J; auto.
   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]]; 
     subst.
     left.
     apply remove_phinodes_neq with (ps1:=ps1)(ps2:=ps2) in Hneq2; eauto.
     destruct Hneq2 as [ps0 [ps3 [Heq2 [J5 J6]]]].
     rewrite Heq2. eauto.

     right. simpl in Hneq1.
     apply getCmdLoc_getCmdID in J2. subst.
     apply remove_cmds_neq with (cs1:=cs1)(cs2:=cs2 ++ c0 :: cs3) in Hneq2; eauto.
     destruct Hneq2 as [cs0 [cs3' [Heq2 [J5 J6]]]].
     rewrite Heq2. exists cs0. exists c1. rewrite <- J6.
     apply remove_cmds_neq with (cs1:=cs2)(cs2:=cs3) in Hneq1; eauto.
     destruct Hneq1 as [cs4 [cs5 [Hneq1 [J7 J8]]]].
     rewrite Hneq1. exists cs4. exists cs5. split; auto.
     destruct c1; auto.

   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]]; 
     subst.
     left.
     apply remove_phinodes_neq_inv in J1; auto.
     destruct J1 as [ps3 [ps4 [J1 [J2 J3]]]]; subst.
     eauto.

     right.
     apply getCmdLoc_getCmdID in J2. subst.
     apply remove_cmds_neq_inv in J1; auto.
     destruct J1 as [cs4 [cs5 [J1 [J2 J3]]]]; subst.
     simpl in Hneq1.
     apply remove_cmds_neq_inv in J3; auto.
     destruct J3 as [cs1 [cs6 [J3 [J4 J5]]]]; subst.
     exists cs4. exists c1. exists cs1. exists cs6. split; auto.
     destruct c1; auto.
 
   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq]; 
     subst; split; auto.
     left.
     apply getCmdLoc_getCmdID in J2. subst.
     apply remove_cmds_neq with (cs1:=cs1)(cs2:=cs2) in Hneq2; eauto.
     destruct Hneq2 as [cs0 [cs3' [Heq2 [J5 J6]]]].
     rewrite Heq2. exists cs0. exists c1. exists cs3'. split; auto.
     destruct c1; auto.

     right.
     apply remove_phinodes_neq with (ps1:=ps1)(ps2:=ps2) in Hneq2; eauto.
     destruct Hneq2 as [ps0 [ps3 [Heq2 [J5 J6]]]].
     rewrite Heq2. eauto.

   simpl in *. apply terminatorEqB_inv in HiInB. subst.
   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq]; 
     subst; split; auto.
     left.
     apply getCmdLoc_getCmdID in J2. subst.
     apply remove_cmds_neq_inv in J1; auto.
     destruct J1 as [cs4 [cs5 [J1 [J2 J3]]]]; subst.
     exists cs4. exists c1. exists cs5. split; auto.
     destruct c1; auto.
 
     right.
     apply remove_phinodes_neq_inv in J1; auto.
     destruct J1 as [ps3 [ps4 [J1 [J2 J3]]]]; subst.
     eauto.
Qed.

Lemma remove_blockStrictDominates : forall f b1 b2 id',
  blockStrictDominates f b1 b2 <->
    blockStrictDominates (remove_fdef id' f) (remove_block id' b1)
      (remove_block id' b2).
Proof.
  intros.
  unfold blockStrictDominates. destruct b1. destruct b2. simpl.
  unfold dom_analyze. destruct f. simpl.
  rewrite <- remove_successors_blocks.
  remember (entry_dom b) as R1.
  remember (entry_dom (List.map (remove_block id') b)) as R2.
  destruct R1 as [x1 Hx1]. 
  destruct R2 as [x2 Hx2]. 
  destruct x1 as [x1|]. 
  Case "1".
    destruct x1 as [le1 start1].
    destruct start1.
    destruct bs_contents as [|l2 bs_contents]; tinv Hx1.
    destruct x2 as [x2|]. 
    SCase "1.1".
      destruct x2 as [le2 start2].
      destruct start2.
      destruct bs_contents as [|l3 bs_contents]; tinv Hx2.
      destruct b; tinv HeqR1.
      destruct b. 
      inv HeqR1. inv HeqR2. 
      eapply blockStrictDominates_iff; eauto.
    SCase "1.2".
      destruct b; simpl in *; tinv HeqR1.
        inv Hx2.
  Case "2".
    subst. simpl in *. inv HeqR2. split; intro; auto.
Qed.

Lemma remove_wf_operand : forall instr id' f b i0
  (Huniq : NoDup (getBlockLocs b))
  (H1 : wf_operand f b instr i0)
  (Hneq : unremovable id' instr)
  (n : i0 <> id'),
  wf_operand (remove_fdef id' f) (remove_block id' b) instr i0.
Proof.
  intros.
  inv H1.
  eapply wf_operand_intro; try solve [eauto with ssa_remove].   
    rewrite <- remove_insnDominates; eauto using insnInFdefBlockB__insnInBlockB.
    rewrite <- remove_blockStrictDominates.
    rewrite <- remove_isReachableFromEntry; auto.
Qed.

Hint Resolve remove_wf_operand: ssa_remove.

Hint Constructors wf_operand_list.

Lemma remove_wf_operand_list : forall instr id' f b id_list0
  (Huniq : NoDup (getBlockLocs b))
  (Hneq : unremovable id' instr)
  (Hnotin : ~ In id' (unmake_list_id id_list0))
  (H2 : wf_operand_list
         (make_list_fdef_block_insn_id
            (map_list_id (fun id_ : id => (f, b, instr, id_)) id_list0))),
  wf_operand_list
   (make_list_fdef_block_insn_id
      (map_list_id
         (fun id_ : id =>
          (remove_fdef id' f, remove_block id' b,
          instr, id_)) id_list0)).
Proof.
  induction id_list0; simpl; intros; auto.
    inv H2.
    assert (i0 <> id' /\ ~ In id' (unmake_list_id id_list0)) as J.
      destruct (id_dec i0 id'); subst;
        destruct (In_dec id_dec id' (unmake_list_id id_list0)); subst; auto.
    destruct J as [J1 J2].
    destruct (id_dec i0 id'); subst; simpl; auto with ssa_remove.
Qed.

Hint Resolve remove_wf_operand_list: ssa_remove.

Lemma remove_wf_insn_base : forall f b id0 instr 
  (Huniq : NoDup (getBlockLocs b))
  (Hneq : unremovable id0 instr)
  (Hnouse : used_in_insn id0 instr = false)
  (HwfI: wf_insn_base f b instr),
  wf_insn_base (remove_fdef id0 f) (remove_block id0 b) instr.
Proof.
  intros.
  inv HwfI.
  eapply remove_insnInFdefBlockB in H; eauto.
  apply noused_getInsnOperands in Hnouse; auto. rewrite H1 in Hnouse.
  eapply wf_insn_base_intro; eauto with ssa_remove.
Qed.

Hint Constructors wf_insn wf_value.

Lemma remove_lookupBlockViaLabelFromBlocks : forall l5 id' bs b,
  lookupBlockViaLabelFromBlocks bs l5 = ret b ->
  lookupBlockViaLabelFromBlocks (List.map (remove_block id') bs) l5 = 
    ret (remove_block id' b).
Proof.
  unfold lookupBlockViaLabelFromBlocks.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l5 l0); 
      subst; inv H; auto.
Qed.

Hint Resolve remove_lookupBlockViaLabelFromBlocks : ssa_remove.

Lemma remove_lookupBlockViaLabelFromFdef : forall f l5 b id',
  lookupBlockViaLabelFromFdef f l5 = ret b ->
  lookupBlockViaLabelFromFdef (remove_fdef id' f) l5 = ret (remove_block id' b).
Proof.
  destruct f. simpl. intros. apply remove_lookupBlockViaLabelFromBlocks; auto.
Qed.

Lemma remove_lookupIDFromPhiNodes : forall id5 id' ps,
  id5 <> id' -> 
  lookupIDFromPhiNodes ps id5 = 
    lookupIDFromPhiNodes (remove_phinodes id' ps) id5.
Proof.
  induction ps; simpl; intros; auto.
    rewrite IHps; auto.
    unfold lookupIDFromPhiNode in *.
    destruct a. simpl in *.
    destruct (id_dec i0 id'); subst; simpl; auto.
      destruct (id5 == id'); subst; auto. congruence.
Qed.
 
Lemma remove_lookupIDFromCmds : forall id5 id' cs,
  id5 <> id' -> 
  lookupIDFromCmds cs id5 = lookupIDFromCmds (remove_cmds id' cs) id5. 
Proof.
  induction cs; simpl; intros; auto.
    rewrite IHcs; auto.
    unfold lookupIDFromCmd in *.
    destruct a; simpl in *;
      destruct (id_dec i0 id'); subst; simpl; 
      try solve [auto | 
                 destruct (id5 == id'); subst; try solve [auto | congruence]].
Qed.

Lemma remove_lookupIDFromBlocks : forall id5 id' bs,
  id5 <> id' -> 
  lookupIDFromBlocks bs id5 = 
    lookupIDFromBlocks (List.map (remove_block id') bs) id5.
Proof.
  induction bs; simpl; intros; auto.
    destruct a. simpl in *.
    rewrite IHbs; auto.
    rewrite <- remove_lookupIDFromPhiNodes; auto.
    rewrite <- remove_lookupIDFromCmds; auto.
Qed.

Lemma remove_lookupIDFromFdef : forall f id5 id',
  id5 <> id' -> 
  lookupIDFromFdef f id5 = lookupIDFromFdef (remove_fdef id' f) id5.
Proof.
  destruct f. simpl. intros. rewrite <- remove_lookupIDFromBlocks; auto.
Qed.

Lemma remove_wf_value : forall f id0 v (Hwfv: wf_value f v) 
  (Hnouse : used_in_value id0 v = false),
  wf_value (remove_fdef id0 f) v.
Proof.
  intros.
  inv Hwfv; try constructor.
    rewrite <- remove_lookupIDFromFdef; auto with ssa_remove.
Qed.

Hint Constructors wf_phi_operands.

Lemma remove_wf_phi_operands : forall f b id0 id' vls
  (Hnouse : used_in_list_value_l id0 vls = false)
  (Hwf_pnops: wf_phi_operands f b id' vls),
  wf_phi_operands (remove_fdef id0 f) (remove_block id0 b) id' vls.
Proof.
  intros.
  induction Hwf_pnops; simpl in *; auto.
    binvf Hnouse as J1 J2.
    eapply wf_phi_operands_cons_vid; eauto.
      eapply remove_lookupBlockViaIDFromFdef in H; eauto with ssa_remove.
      eapply remove_lookupBlockViaLabelFromFdef in H0; eauto.
      destruct H1 as [H1 | H1].
        rewrite <- remove_blockDominates; auto.
        rewrite <- remove_isReachableFromEntry; auto.
Qed.
     
Lemma remove_predOfBlock : forall id0 b,
  predOfBlock b = predOfBlock (remove_block id0 b).
Proof.
  destruct b; simpl; auto.
Qed.

Lemma remove_check_list_value_l : forall f b id0 vls
  (Hcl: check_list_value_l f b vls),
  check_list_value_l (remove_fdef id0 f) (remove_block id0 b) vls.
Proof.
  unfold check_list_value_l. destruct f as [bs]. simpl. intros until vls.
  repeat rewrite <- remove_genBlockUseDef_blocks.
  repeat rewrite <- remove_predOfBlock. auto.
Qed.

Hint Resolve remove_wf_phi_operands remove_check_list_value_l: ssa_remove.

Lemma remove_wf_phinode : forall f b id0 PN (HwfPN: wf_phinode f b PN)
  (Hnouse: used_in_phi id0 PN = false),
  wf_phinode (remove_fdef id0 f) (remove_block id0 b) PN.
Proof.
  intros. destruct PN as [id' vls].
  unfold wf_phinode in *. simpl.
  destruct HwfPN as [Hwf_pnops Hcl].
  split; auto with ssa_remove.
Qed.

Hint Resolve remove_wf_value : ssa_remove.

Lemma remove_wf_value_list : forall
  (id0 : id)
  (fdef5 : fdef)
  (block5 : block)
  (value_l_list : list_value_l)
  (Hnouse : used_in_list_value_l id0 value_l_list = false)
  (H : wf_value_list
        (make_list_fdef_value
           (map_list_value_l
              (fun (value_ : value) (_ : l) => (fdef5, value_)) value_l_list))),
   wf_value_list
     (make_list_fdef_value
        (map_list_value_l
           (fun (value_ : value) (_ : l) =>
            (remove_fdef id0 fdef5, value_)) value_l_list)).
Proof.
  induction value_l_list; simpl; intros; auto.
    inv H. binvf Hnouse as J1 J2.
    apply Cons_wf_value_list; auto with ssa_remove.
Qed.

Hint Resolve remove_wf_value_list: ssa_remove.

Lemma remove_wf_insn : forall f b id0 instr (HwfI: wf_insn f b instr)
  (Huniq : NoDup (getBlockLocs b)) (Hnouse : used_in_insn id0 instr = false) 
  (Hnr : unremovable id0 instr),
  wf_insn (remove_fdef id0 f) (remove_block id0 b) instr.
Proof.
  intros.

  Ltac DONE := 
  eauto with ssa_remove; try match goal with
  | H : wf_insn_base _ _ _ |- wf_insn_base _ _ _ => 
    eapply remove_wf_insn_base in H; eauto
  | H : wf_value _ ?v |- wf_value _ ?v => 
    eapply remove_wf_value in H; eauto
  | H : lookupBlockViaLabelFromFdef _ ?l = Some _ |- 
        lookupBlockViaLabelFromFdef _ ?l = Some _  =>
    eapply remove_lookupBlockViaLabelFromFdef in H; eauto
  | H : insnInFdefBlockB _ _ _ = _ |- insnInFdefBlockB _ _ _ = _ =>
    eapply remove_insnInFdefBlockB in H; eauto
  | H : wf_phinode _ _ _ |- wf_phinode _ _ _ =>
    eapply remove_wf_phinode in H; eauto
  | H : used_in_insn _ _ = false |- used_in_value _ _ = false =>
    apply orb_false_iff in H; destruct H; auto
  end.
  
  destruct HwfI; simpl;
  match goal with
  | |- wf_insn _ _ _ => 
      try solve [eapply wf_insn_return; DONE |
           eapply wf_insn_br; DONE |
           eapply wf_insn_br_uncond; DONE |
           eapply wf_insn_bop; DONE; DONE |
           eapply wf_insn_icmp; DONE; DONE |
           eapply wf_insn_phi; DONE]
  end.
Qed.

Hint Resolve remove_wf_insn : ssa_remove.

Hint Constructors wf_phinodes.

Lemma used_in_phinodes_cons_inv : forall phinodes5 id0 phinode5,
  fold_left (fun (re : bool) (p : phinode) => re || used_in_phi id0 p)
    phinodes5 (used_in_phi id0 phinode5) = false ->
  used_in_phi id0 phinode5 = false /\
    fold_left (fun (re : bool) (p : phinode) => re || used_in_phi id0 p)
      phinodes5 false = false.
Proof.
  intros.
  destruct (used_in_phi id0 phinode5); auto.
    apply fold_left_eq in H.
      congruence.
      intros. binvf H0 as J1 J2; auto.  
Qed.

Lemma remove_wf_phinodes : forall f b id0 PNs (HwfPNs: wf_phinodes f b PNs)
  (Hnouse : List.fold_left (fun re p => re || used_in_phi id0 p) PNs false = false) 
  (Huniq : NoDup (getBlockLocs b)),
  wf_phinodes (remove_fdef id0 f) (remove_block id0 b) (remove_phinodes id0 PNs).
Proof.
  intros. 
  induction HwfPNs; simpl in *; auto.
    apply used_in_phinodes_cons_inv in Hnouse. destruct Hnouse. 
    destruct (id_dec (getPhiNodeID phinode5) id0); subst; simpl; eauto.
      eapply remove_wf_insn in H; eauto.
Qed.

Hint Constructors wf_cmds.

Lemma used_in_cmds_cons_inv : forall cs5 id0 c5
  (Hnouse : List.fold_left (fun re c => re || used_in_cmd id0 c) cs5 
    (used_in_cmd id0 c5) = false),
  used_in_cmd id0 c5 = false /\
    fold_left (fun (re : bool) c => re || used_in_cmd id0 c) cs5 false = false.
Proof.
  intros.
  destruct (used_in_cmd id0 c5); auto.
    apply fold_left_eq in Hnouse.
      congruence.
      intros. binvf H as J1 J2; auto.  
Qed.

Lemma remove_wf_cmds : forall f b id0 Cs (HwfCs: wf_cmds f b Cs)
  (Hnouse : List.fold_left (fun re c => re || used_in_cmd id0 c) Cs false = false) 
  (Huniq : NoDup (getBlockLocs b)),
  wf_cmds (remove_fdef id0 f) (remove_block id0 b) (remove_cmds id0 Cs).
Proof.
  intros. 
  induction HwfCs; simpl in *; auto.
    apply used_in_cmds_cons_inv in Hnouse. destruct Hnouse.
    destruct (id_dec (getCmdLoc cmd5) id0); subst; simpl; eauto.
      eapply remove_wf_insn in H; eauto.
Qed.

Lemma remove_wf_block : forall f b id0 (HwfB : wf_block f b)
  (Hnouse : used_in_block id0 b = false)
  (Huniq : NoDup (getBlockLocs b)),
  wf_block (remove_fdef id0 f) (remove_block id0 b).
Proof.
  intros.
  inv_wf_block HwfB; subst.
  binvf Hnouse as J1 J2; binvf J1 as J1 J3.
  match goal with
  | HBinF : blockInFdefB _ _ = _,
    HwfPNs : wf_phinodes _ _ _,
    HwfCs : wf_cmds _ _ _,
    Hwftmn : wf_insn _ _ _ |- _ =>
     eapply remove_blockInFdefB in HBinF; eauto;
     eapply remove_wf_phinodes in HwfPNs; eauto;
     eapply remove_wf_cmds in HwfCs; eauto;
     eapply remove_wf_insn in Hwftmn; simpl; eauto
  end.
  apply wf_block_intro; eauto.
Qed.

Hint Resolve remove_wf_block : ssa_remove.

Hint Constructors wf_blocks.

Lemma remove_wf_blocks : forall f bs id0 (HwfBs : wf_blocks f bs)
  (Hnouse : List.fold_left (fun re b => re || used_in_block id0 b) bs false = false)
  (Huniq : uniqBlocks bs),
  wf_blocks (remove_fdef id0 f) (List.map (remove_block id0) bs).
Proof.
  intros.
  induction HwfBs; simpl; auto.
    simpl_env in Huniq. apply uniqBlocks_inv in Huniq. inv Huniq.
    inv H0. simpl in *. simpl_env in H3.
    assert (used_in_block id0 block5 = false /\
            fold_left
              (fun (re : bool) b => re || used_in_block id0 b)
                blocks5 false = false) as J.
      destruct (used_in_block id0 block5); auto.
        apply fold_left_eq in Hnouse.
          congruence.
          intros. binvf H0 as J1 J2; auto.  
    destruct J.
    apply wf_blocks_cons; eauto with ssa_remove.
Qed.

Hint Resolve remove_getEntryBlock remove_hasNonePredecessor remove_uniqFdef 
  remove_wf_blocks : ssa_remove.

Lemma remove_wf_fdef : forall f id0 (HwfF: wf_fdef f) 
  (Hnouse : used_in_fdef id0 f = false), 
  wf_fdef (remove_fdef id0 f).
Proof.
  intros.
  inv_wf_fdef HwfF.
  simpl in Hnouse.
  match goal with
  | Hentry : getEntryBlock _ = _,
    HuniqF : uniqFdef _,
    Hnpred : hasNonePredecessor _ _ = _,
    HwfBs : wf_blocks _ _ |- _ =>
     eapply remove_getEntryBlock in Hentry; eauto;
     eapply remove_hasNonePredecessor in Hnpred; eauto;
     eapply remove_wf_blocks in HwfBs; eauto;
     eapply remove_uniqFdef in HuniqF; eauto
  end.
  eapply wf_fdef_intro; eauto.
Qed.

(************** Bisimulation for constant substituion **************************)

Export Opsem.

Definition related_ECs id0 (f1:fdef) (ec1 ec2:ExecutionContext) : Prop :=
let '(mkEC b1 cs1 tmn1 lc1) := ec1 in
let '(mkEC b2 cs2 tmn2 lc2) := ec2 in
isReachableFromEntry f1 b1 /\
blockInFdefB b1 f1 = true /\
(forall id', id' <> id0 -> lookupAL _ lc1 id' = lookupAL _ lc2 id') /\
remove_block id0 b1 = b2 /\
remove_cmds id0 cs1 = cs2 /\
(exists l1, exists ps1, exists cs1', exists ps2, exists cs2',
b1 = block_intro l1 ps1 (cs1'++cs1) tmn1 /\
b2 = block_intro l1 ps2 (cs2'++cs2) tmn2).

Lemma remove_block__lookupAL_genLabel2Block_block : forall 
    id0 l0 bs b b',
  lookupAL _ (genLabel2Block_blocks bs) l0 = Some b ->
  lookupAL _ (genLabel2Block_blocks (List.map (remove_block id0) bs)) l0 
    = Some b' ->
  remove_block id0 b = b'.
Proof.
  induction bs; simpl; intros.
    congruence.   

    destruct a. simpl in *.
    destruct (l0 == l1); subst; eauto.
      inv H. inv H0. auto.
Qed.

Lemma remove_fdef__lookupBlockViaLabelFromFdef : forall id0 F l0 b b',
  lookupBlockViaLabelFromFdef F l0 = Some b ->
  lookupBlockViaLabelFromFdef (remove_fdef id0 F) l0 = Some b' ->
  remove_block id0 b = b'.
Proof.
  destruct F. simpl in *. intros. 
  eauto using remove_block__lookupAL_genLabel2Block_block.
Qed.

Lemma getOperandValue_sim : forall
  (lc lc' : GVMap) id0 
  (v : value) (Hnouse: used_in_value id0 v = false)
  (Heq: forall id', id' <> id0 -> lookupAL _ lc id' = lookupAL _ lc' id'),
  getOperandValue v lc = getOperandValue v lc'.
Proof.
  intros.
  destruct v as [vid | vc]; simpl in *; try congruence.
    auto with ssa_remove.
Qed.

Lemma used_in_getValueViaLabelFromValuels : forall l1 id0 l2 v
  (Hnouse : used_in_list_value_l id0 l2 = false)
  (HeqR0 : ret v = getValueViaLabelFromValuels l2 l1),
  used_in_value id0 v = false.
Proof.
  induction l2; simpl; intros; try congruence.
    binvf Hnouse as J1 J2.
    destruct (l0 == l1); subst; inv HeqR0; auto.
Qed.

Lemma getValueViaLabelFromValuels_getOperandValue_sim : forall
  (lc : GVMap) (l1 : l) (id0 : id) (l2 : list_value_l)
  (v0 : value) (Hnouse : used_in_list_value_l id0 l2 = false)
  (HeqR3 : ret v0 = getValueViaLabelFromValuels l2 l1) lc'
  (Heq: forall id', id' <> id0 -> lookupAL _ lc id' = lookupAL _ lc' id'),
  getOperandValue v0 lc = getOperandValue v0 lc'.
Proof.
  intros.
  destruct v0 as [vid | vc]; simpl in *; try congruence.
    eapply used_in_getValueViaLabelFromValuels in HeqR3; eauto with ssa_remove.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall
  (lc lc': GVMap) b1 id0 
  (Heq: forall id', id' <> id0 -> lookupAL _ lc id' = lookupAL _ lc' id')
  ps2 RVs RVs'
  (Hnouse : List.fold_left (fun re p => re || used_in_phi id0 p) ps2 false = false)
  (Hget : getIncomingValuesForBlockFromPHINodes ps2 b1 lc = Some RVs)
  (Hget' : getIncomingValuesForBlockFromPHINodes 
    (remove_phinodes id0 ps2) (remove_block id0 b1) lc' = ret RVs'),
  forall id', id' <> id0 -> lookupAL _ RVs id' = lookupAL _ RVs' id'.
Proof.
  induction ps2; intros; simpl in Hget, Hget'; try congruence.
    simpl in *.
    apply used_in_phinodes_cons_inv in Hnouse. destruct Hnouse as [J1 J2].
    destruct a. simpl in *.
    destruct (id_dec i0 id0); subst; simpl in *.
      inv_mbind'. app_inv. destruct b1. simpl in *.
      eapply used_in_getValueViaLabelFromValuels in HeqR; eauto.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id' id0); subst;
        try congruence; auto with ssa_remove.

      inv_mbind'. app_inv. destruct b1. simpl in *.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id' i0); subst; eauto.
        rewrite <- HeqR2 in HeqR. inv HeqR.
      eapply used_in_getValueViaLabelFromValuels in HeqR2; eauto.
        rewrite HeqR3. rewrite HeqR0.
        eapply getOperandValue_sim; eauto.        
Qed.

Export OpsemProps.

Lemma switchToNewBasicBlock_sim : forall
  (lc lc': GVMap) id0 b1 b2
  lc0 lc0' (Hnouse : used_in_block id0 b2 = false)
  (Heq: forall id', id' <> id0 -> lookupAL _ lc id' = lookupAL _ lc' id')
  (Hget : switchToNewBasicBlock b2 b1 lc = ret lc0)
  (Hget' : switchToNewBasicBlock 
    (remove_block id0 b2) (remove_block id0 b1) lc' = ret lc0'),
  forall id', id' <> id0 -> lookupAL _ lc0 id' = lookupAL _ lc0' id'.
Proof.
  intros.
  unfold switchToNewBasicBlock in *.
  inv_mbind'. app_inv. symmetry_ctx. destruct b1, b2. simpl in *.
  binvf Hnouse as J1 J2. binvf J1 as J1 J3.  
  assert (forall id', id' <> id0 -> lookupAL _ g0 id' = lookupAL _ g id') as EQ.
    eapply getIncomingValuesForBlockFromPHINodes_sim with (ps2:=p0); eauto.
  eapply updateValuesForNewBlock_sim; eauto.
Qed.

Lemma used_in_blocks_cons_inv : forall bs5 id0 b5,
  fold_left (fun (re : bool) b => re || used_in_block id0 b) 
    bs5 (used_in_block id0 b5) = false ->
  used_in_block id0 b5 = false /\
    fold_left (fun (re : bool) b => re || used_in_block id0 b) bs5 false 
      = false.
Proof.
  intros.
  destruct (used_in_block id0 b5); auto.
    apply fold_left_eq in H.
      congruence.
      intros. binvf H0 as J1 J2; auto.  
Qed.

Lemma used_in_blocks__used_in_block : forall id0 b bs,
  fold_left (fun (re : bool) (b0 : block) => re || used_in_block id0 b0) bs
    false = false ->
  InBlocksB b bs = true -> 
  used_in_block id0 b = false.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply used_in_blocks_cons_inv in H. destruct H.
    binvt H0 as J1 J2; auto.
      apply blockEqB_inv in J1. subst. auto.
Qed.      

Lemma used_in_cmds__used_in_cmd : forall id0 c cs,
  fold_left (fun (re : bool) c => re || used_in_cmd id0 c) cs
    false = false ->
  In c cs -> 
  used_in_cmd id0 c = false.
Proof.
  induction cs; simpl; intros.
    inv H0.

    apply used_in_cmds_cons_inv in H. destruct H.
    destruct H0 as [H0 | H0]; subst; auto.
Qed.      

Lemma used_in_cmd__used_in_value : forall id0 v c,
  used_in_cmd id0 c = false ->
  valueInCmdOperands v c -> 
  used_in_value id0 v = false.
Proof.
  induction c; simpl; intros;
    binvf H as J3 J4; destruct H0 as [H0 | H0]; subst; auto.
Qed.

Lemma used_in_fdef__used_in_cmd_value : forall id0 l3 ps1 cs c v tmn1 F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true ->
  valueInCmdOperands v c -> In c cs ->
  used_in_value id0 v = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
  binvf H0 as J3 J4. binvf J3 as J1 J2.
  eapply used_in_cmds__used_in_cmd in J2; eauto.
  eapply used_in_cmd__used_in_value in H1; eauto.
Qed.

Lemma used_in_tmn__used_in_value : forall id0 v tmn,
  used_in_tmn id0 tmn = false ->
  valueInTmnOperands v tmn -> 
  used_in_value id0 v = false.
Proof.
  destruct tmn; simpl; intros; try solve [inv H0 | subst; auto].
Qed.

Lemma used_in_fdef__used_in_tmn_value : forall id0 l3 ps1 cs v tmn1 F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true ->
  valueInTmnOperands v tmn1 ->
  used_in_value id0 v = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
  binvf H0 as J3 J4. binvf J3 as J1 J2.
  eapply used_in_tmn__used_in_value in H1; eauto.
Qed.

Lemma used_in_fdef__used_in_block : forall id0 b F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB b F1 = true ->
  used_in_block id0 b = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
Qed.
 
Definition removable_EC id0 (ec1:ExecutionContext) : Prop :=
match ec1 with
| mkEC b1 (c::cs) tmn1 lc1 => getCmdLoc c = id0
| _ => False
end.

Lemma removable_EC_dec : forall id0 ec1,
  removable_EC id0 ec1 \/ ~ removable_EC id0 ec1.
Proof.
  destruct ec1. 
  destruct CurCmds0; simpl; auto.
  destruct (id_dec (getCmdLoc c) id0); auto.
Qed.

Lemma bisimulation_cmd_case1 : forall c F B cs tmn lc S2 gvs3
  (HnouseF1 : used_in_fdef (getCmdLoc c) F = false)
  (Hrel : related_ECs (getCmdLoc c) F
           {|
           CurBB := B;
           CurCmds := c :: cs;
           Terminator := tmn;
           Locals := lc |} S2),
  related_ECs (getCmdLoc c) F
    {|
    CurBB := B;
    CurCmds := cs;
    Terminator := tmn;
    Locals := updateAddAL GenericValue lc (getCmdLoc c) gvs3 |} S2 /\
  trace_nil = trace_nil.
Proof.
  intros.
    destruct S2 as [b2 cs2 tmn2 lc2].
    assert (J:=Hrel); simpl in J.
    destruct J as
      [Hreach1 [HBinF1 [Heq1 [Hbtrans [Hcstrans
        [l3 [ps1 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]]; subst.
    destruct (id_dec (getCmdLoc c) (getCmdLoc c)); subst; simpl in Heq3; 
      simpl; try congruence.
    repeat split; auto.
      intros id' Hneq.
      rewrite <- lookupAL_updateAddAL_neq; auto. 

      exists l3. exists ps1. exists (cs1' ++ [c]).
      exists (remove_phinodes (getCmdLoc c) ps1). exists cs2'. 
      inv Heq3. simpl_env in *. 
      rewrite H1. split; auto.
Qed.

Lemma getOperandValue_sim' : forall
  (lc lc' : GVMap) id0 c F1 tmn1 cs1' cs1 ps1 l3
  (v : value) (Hnouse: used_in_fdef id0 F1 = false)
  (HBinF1 : blockInFdefB
             (block_intro l3 ps1 (cs1' ++ c :: cs1)
                tmn1) F1 = true)
  (Heq: forall id', id' <> id0 -> lookupAL _ lc id' = lookupAL _ lc' id')
  gv gv',
  valueInCmdOperands v c ->
  getOperandValue v lc = Some gv ->
  getOperandValue v lc' = Some gv' ->
  gv = gv'.
Proof.
  intros.
  eapply used_in_fdef__used_in_cmd_value with (c:=c)(v:=v) in HBinF1; 
    simpl; eauto using in_middle.
  eapply getOperandValue_sim in Heq; eauto.
  rewrite H0 in Heq. rewrite H1 in Heq. inv Heq. auto.
Qed.

Ltac destruct_ctx :=
match goal with
| Hrel : related_ECs ?id0 _ ?S1 _,
  HsInsn1 : sInsn _ ?S1 _ _,
  Hrem : ~ removable_EC ?id0 ?S1 |- _ =>
  destruct S1 as [b1 cs1 tmn1 lc1];
  assert (J:=Hrel); simpl in J;
  destruct J as
    [Hreach1 [HBinF1 [Heq1 [Hbtrans [Hcstrans
      [l3 [ps1 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]]; subst;
  match goal with
  | Hcstrans : remove_cmds ?id0 ?cs1 = nil |- _ =>
    assert (cs1 = nil) as Heq; (try
    match goal with 
    | |- cs1 = nil =>
      destruct cs1 as [|c' cs1]; simpl in *; auto;
      destruct (id_dec (getCmdLoc c') id0); subst; simpl in *; 
        tinv Hcstrans; congruence
    end);
    subst; clear Hcstrans; inv Heq3
  | |- _ =>
    destruct cs1 as [|c cs1]; tinv Hcstrans;
    simpl in Hcstrans;
    destruct (id_dec (getCmdLoc c) id0); subst; simpl in Hcstrans;
      try solve [simpl in Hrem; congruence];
    inv Hcstrans; clear Hrem
  end;
  inv HsInsn1
end.

Ltac op_sim :=
match goal with
| H : _ ?lc _ ?v1 ?v2 = Some ?gvs3,
  H' : _ ?lc1 _ ?v1 ?v2 = Some ?gvs0 |- ?gv0 = ?gv3 =>
    unfold ICMP, BOP in *;
    inv_mbind'; inv_mfalse; app_inv; symmetry_ctx;
    match goal with
    | H1 : getOperandValue ?v1 ?lc1 = Some ?g1,
      H2 : getOperandValue ?v1 ?lc = Some ?g,
      H3 : getOperandValue ?v2 ?lc1 = Some ?g2,
      H4 : getOperandValue ?v2 ?lc = Some ?g0 |- _ =>
    assert (g = g1) as EQ; try solve 
      [eapply getOperandValue_sim' with (v:=v1); try solve [eauto | simpl; auto]];
    subst;
    assert (g0 = g2) as EQ; try solve 
      [eapply getOperandValue_sim' with (v:=v2); try solve [eauto | simpl; auto]];
    subst; auto
    end
end.

Lemma bisimulation : forall id0 F1 F2 S1 S2,
  wf_fdef F1 ->
  used_in_fdef id0 F1 = false ->
  remove_fdef id0 F1 = F2 ->
  related_ECs id0 F1 S1 S2 ->
  (removable_EC id0 S1 ->
   forall S1' tr1, 
    sInsn F1 S1 S1' tr1 ->
    related_ECs id0 F1 S1' S2 /\ tr1 = trace_nil) /\
  (~removable_EC id0 S1 ->
   forall S1' S2' tr1 tr2,
    sInsn F1 S1 S1' tr1 ->
    sInsn F2 S2 S2' tr2 ->
    related_ECs id0 F1 S1' S2' /\ tr1 = tr2).
Proof.
  intros id0 F1 F2 S1 S2 HwfF1 HnouseF1 Htrans Hrel.
  split; intro Hrem.
Case "removable state".
  intros S1' tr1 HsInsn1.
  (sInsn_cases (destruct HsInsn1) SCase); inv Hrem. 
  SCase "sBop". apply bisimulation_cmd_case1; auto.
  SCase "sIcmp". apply bisimulation_cmd_case1; auto.

Case "unremovable state".
  intros S1' S2' tr1 tr2 HsInsn1 HsInsn2.
  (sInsn_cases (destruct HsInsn2) SCase); destruct_ctx.
Focus.
  SCase "sBranch". 
  assert (c0 = c) as Heq.
    clear - Heq1 H12 H HBinF1 HnouseF1.
    eapply used_in_fdef__used_in_tmn_value with (v:=Cond) in HBinF1; 
      simpl; eauto.
    apply getOperandValue_sim with(v:=Cond) in Heq1; eauto.
    rewrite H in Heq1. rewrite H12 in Heq1. inv Heq1. auto.
  subst.
  assert (remove_block id0 (block_intro l'0 ps'0 cs'0 tmn'0) 
    = block_intro l' ps' cs' tmn') as Hbtrans.
    destruct (isGVZero c); 
      eapply remove_fdef__lookupBlockViaLabelFromFdef; eauto.
  inv Hbtrans.
  assert (isReachableFromEntry F1 (block_intro l' ps'0 cs'0 tmn') /\
    In l' (successors_terminator (insn_br bid Cond l1 l2)) /\
    blockInFdefB (block_intro l' ps'0 cs'0 tmn') F1 = true /\
    wf_phinodes F1 (block_intro l' ps'0 cs'0 tmn') ps'0) as J.
    symmetry in H13.
    destruct (isGVZero c);
      assert (J:=H13);
      apply lookupBlockViaLabelFromFdef_inv in J; eauto;
      destruct J as [J H13']; subst;
      symmetry in H13; eapply wf_fdef__lookup__wf_block in H13; eauto;
      (repeat split; simpl; auto); try solve
        [eapply reachable_successors; (eauto || simpl; auto) |
         inv H13; auto].
  destruct J as [Hreach' [Hsucc' [HBinF1' HwfPNs]]].
  assert (forall id', id' <> id0 ->
    lookupAL GenericValue lc'0 id' = lookupAL GenericValue lc' id') as Heq.
    eapply used_in_fdef__used_in_block in HBinF1'; eauto.
    eapply switchToNewBasicBlock_sim; eauto.
  repeat split; auto.
    exists l'. exists ps'0. exists nil. exists (remove_phinodes id0 ps'0). 
    exists nil. auto.
Unfocus.

Focus.
  SCase "sBranch_uncond". 
  assert (remove_block id0 (block_intro l'0 ps'0 cs'0 tmn'0) 
    = block_intro l' ps' cs' tmn') as Hbtrans.
    eapply remove_fdef__lookupBlockViaLabelFromFdef; eauto.
  inv Hbtrans.
  assert (isReachableFromEntry F1 (block_intro l' ps'0 cs'0 tmn') /\
    In l' (successors_terminator (insn_br_uncond bid l0)) /\
    blockInFdefB (block_intro l' ps'0 cs'0 tmn') F1 = true /\
    wf_phinodes F1 (block_intro l' ps'0 cs'0 tmn') ps'0) as J.
    symmetry in H9.
    assert (J:=H9);
      apply lookupBlockViaLabelFromFdef_inv in J; eauto;
      destruct J as [J H9']; subst;
      symmetry in H9; eapply wf_fdef__lookup__wf_block in H9; eauto;
      (repeat split; simpl; auto); try solve
        [eapply reachable_successors; (eauto || simpl; auto) |
         inv H9; auto].
  destruct J as [Hreach' [Hsucc' [HBinF1' HwfPNs]]].
  assert (forall id', id' <> id0 ->
    lookupAL GenericValue lc'0 id' = lookupAL GenericValue lc' id') as Heq.
    eapply used_in_fdef__used_in_block in HBinF1'; eauto.
    eapply switchToNewBasicBlock_sim; eauto.
  repeat split; auto.
    exists l'. exists ps'0. exists nil. exists (remove_phinodes id0 ps'0). 
    exists nil. auto.
Unfocus.

  SCase "sBop".
  assert (gvs0 = gvs3) as Heq; try op_sim.
  subst.
  repeat split; auto.
    intros id' Hneq. apply Heq1 in Hneq.
    destruct (id_dec id1 id'); subst; try solve [
      repeat rewrite lookupAL_updateAddAL_eq; auto |
      repeat rewrite <- lookupAL_updateAddAL_neq; auto].

      exists l3. exists ps1. exists (cs1' ++ [insn_bop id1 bop0 v1 v2]).
      exists (remove_phinodes id0 ps1).
      exists (cs2'++ [insn_bop id1 bop0 v1 v2]). inv Heq3.
      simpl. simpl_env in *. rewrite H2. split; auto.

  SCase "sIcmp".
  assert (gvs0 = gvs3) as Heq; try op_sim.
  subst.
  repeat split; auto.
    intros id' Hneq. apply Heq1 in Hneq.
    destruct (id_dec id1 id'); subst.
      repeat rewrite lookupAL_updateAddAL_eq; auto.
      repeat rewrite <- lookupAL_updateAddAL_neq; auto.

      exists l3. exists ps1. exists (cs1' ++ [insn_icmp id1 cond0 v1 v2]).
      exists (remove_phinodes id0 ps1). 
      exists (cs2'++ [insn_icmp id1 cond0 v1 v2]). inv Heq3. 
      simpl. simpl_env in *. rewrite H2. split; auto.
Qed.

Lemma related_finalstate_is_stuck : forall id0 F1 F2 S1 S2 S2' tr2
  (Hrel : related_ECs id0 F1 S1 S2)
  (Hfinal1 : s_isFinialState S1 = true)
  (HsInsn2 : sInsn F2 S2 S2' tr2),
  False.
Proof.
  intros.
  destruct S1. destruct CurCmds0; tinv Hfinal1. 
  destruct Terminator0; inv Hfinal1. destruct S2. 
  destruct Hrel as 
    [J1 [J2 [J3 [J4 [J5 [l1 [ps1 [cs1' [ps2 [cs2' [J7 J8]]]]]]]]]]]; 
    subst.
  inv J8. inv HsInsn2.
Qed.

Lemma finalstate_isnt_removable : forall id0 S1
  (Hfinal1 : s_isFinialState S1 = true)
  (Hrmst : removable_EC id0 S1),
  False.
Proof.
  intros. destruct S1. simpl in *.
  destruct CurCmds0; auto. congruence.
Qed.

Lemma backsimulation : forall id0 F1 F2 S1 S2,
  wf_fdef F1 ->
  used_in_fdef id0 F1 = false ->
  remove_fdef id0 F1 = F2 ->
  related_ECs id0 F1 S1 S2 ->
  OpsemPP.wf_ExecutionContext F1 S1 -> 
  (removable_EC id0 S1 ->
   exists S1',
    sInsn F1 S1 S1' trace_nil /\ related_ECs id0 F1 S1' S2) /\
  (~removable_EC id0 S1 ->
   forall S2' tr,
    sInsn F2 S2 S2' tr ->
    exists S1', 
    sInsn F1 S1 S1' tr /\ related_ECs id0 F1 S1' S2' ).
Proof.
  intros id0 F1 F2 S1 S2 HwfF1 Hnouse Htrans Hrel HwfEC1.
  apply OpsemPP.progress in HwfEC1; auto.
  assert (J:=Hrel).
  eapply bisimulation in J; eauto.
  destruct J as [J1 J2].
  split; intro Hrem.
    destruct HwfEC1 as [Hfinal1 | [S1' [tr1 HsInsn1]]].
      eapply finalstate_isnt_removable in Hrem; eauto. inv Hrem.
      exists S1'. eapply J1 in Hrem; eauto. destruct Hrem; subst; auto.
    intros S2' tr2 HsInsn2.
    destruct HwfEC1 as [Hfinal1 | [S1' [tr1 HsInsn1]]].
      eapply related_finalstate_is_stuck in Hrel; eauto. inv Hrel.
      exists S1'. eapply J2 in Hrem; eauto. destruct Hrem; subst; auto.
Qed.

(************** More props  **************************************)

Lemma used_in_insn__getInsnOperands: forall id2 instr
  (G4 : used_in_insn id2 instr = true),
  In id2 (getInsnOperands instr).
Proof.
  destruct instr; simpl; intros.
    destruct p; simpl in *.
      induction l0; simpl in *.
        inv G4.
        destruct v; simpl in *; auto.
        apply orb_true_iff in G4.
        destruct G4 as [G4 | G4]; auto.
        destruct (id_dec i1 id2); simpl in *; auto.
          congruence.
  
    destruct c; simpl in *.
      destruct v; destruct v0; simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto.
        destruct (id_dec i2 id2); simpl in *; auto. congruence.
        destruct (id_dec i1 id2); simpl in *; auto. congruence. 
        destruct (id_dec i1 id2); simpl in *; auto. congruence. congruence.
      destruct v; destruct v0; simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto.
        destruct (id_dec i2 id2); simpl in *; auto. congruence.
        destruct (id_dec i1 id2); simpl in *; auto. congruence. 
        destruct (id_dec i1 id2); simpl in *; auto. congruence. congruence.

    destruct t; simpl in *; auto.
      destruct v; simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto. congruence. congruence.
      destruct v; simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto. congruence. congruence.
      congruence.
Qed.

Lemma notin_unused_in_value: forall id1 v1,
  ~ In id1 (getValueIDs v1) -> used_in_value id1 v1 = false.
Proof.
  destruct v1; simpl; intros; auto.
    destruct (id_dec i0 id1); subst; simpl; auto.
      contradict H; auto.
Qed.

Lemma remove_notin_getPhiNodesIDs: forall id1 ps,
  ~ In id1 (getPhiNodesIDs (remove_phinodes id1 ps)).
Proof. 
  induction ps; simpl; intros; auto.
    destruct (id_dec (getPhiNodeID a) id1); subst; simpl; auto.
      intro J. 
      destruct J as [J | J]; subst; auto.
Qed.

Lemma remove_notin_getCmdsLocs: forall id1 cs,
  ~ In id1 (getCmdsLocs (remove_cmds id1 cs)).
Proof.
  induction cs; simpl; intros; auto.
    destruct (id_dec (getCmdLoc a) id1); subst; simpl; auto.
      intro J. 
      destruct J as [J | J]; subst; auto.
Qed.

Lemma remove_notin_getBlockLocs: forall id1 b
  (H: forall t, insnInBlockB (insn_terminator t) b -> getTerminatorID t <> id1),
  ~ In id1 (getBlockLocs (remove_block id1 b)).
Proof.
  destruct b. simpl. intros.
  apply notin_app.
    apply remove_notin_getPhiNodesIDs.
  apply notin_app.
    apply remove_notin_getCmdsLocs.
    intro J. simpl in J. 
    destruct J as [Heq | J]; subst; auto.
      apply (@H t); auto.
      apply terminatorEqB_refl.
Qed.     

Lemma remove_notin_getBlocksLocs: forall id1 bs
  (H: forall b t, insnInFdefBlockB (insn_terminator t) (fdef_intro bs) b -> 
      getTerminatorID t <> id1),
  ~ In id1 (getBlocksLocs (List.map (remove_block id1) bs)).
Proof.
  induction bs; simpl; intros; auto.
    apply notin_app.
      apply remove_notin_getBlockLocs.
        intros. apply H with (b:=a).
        apply andb_true_iff.
        split; auto.
          apply orb_true_iff. left. apply blockEqB_refl.
          apply IHbs. intros. apply H with (b:=b).
          apply andb_true_iff in H0. 
          apply andb_true_iff. destruct H0.
          split; auto. apply orb_true_iff. auto.
Qed.




(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)

