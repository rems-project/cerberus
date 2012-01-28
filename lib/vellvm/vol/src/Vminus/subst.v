Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vminus.
Require Import Lattice.
Import AtomSet.

Definition subst_value (id0:id) (v':value) (v:value) : value :=
match v with
| value_id id1 => if id_dec id1 id0 then v' else v
| _ => v
end.

Notation "v {[ v' // id0 ]}" := 
  ( subst_value id0 v' v ) (at level 42, no associativity).

Definition subst_cmd (id':id) (v':value) (c:cmd) : cmd :=
match c with
| insn_bop id0 bop0 v1 v2 => 
    insn_bop id0 bop0 (v1{[v'//id']}) (v2{[v'//id']})
| insn_icmp id0 cond0 v1 v2 => 
    insn_icmp id0 cond0 (v1{[v'//id']}) (v2{[v'//id']})
end.

Definition subst_tmn (id':id) (v':value) (tmn:terminator) : terminator :=
match tmn with
| insn_br id0 v0 l1 l2 => insn_br id0 (v0{[v'//id']}) l1 l2
| insn_return id0 v0 => insn_return id0 (v0{[v'//id']})
| _ => tmn
end.

Fixpoint subst_list_value_l (id':id) (v':value ) (l0:list_value_l)
  : list_value_l :=
match l0 with
| Nil_list_value_l => Nil_list_value_l
| Cons_list_value_l v0 l0 tl => 
   Cons_list_value_l (v0{[v'//id']}) l0 (subst_list_value_l id' v' tl)
end.

Definition subst_phi (id':id) (v':value) (pn:phinode) : phinode :=
match pn with
| insn_phi id0 vls => insn_phi id0 (subst_list_value_l id' v' vls) 
end.

Definition subst_insn (id':id) (v':value) (instr:insn) : insn :=
match instr with
| insn_phinode pn => insn_phinode (subst_phi id' v' pn)
| insn_cmd c => insn_cmd (subst_cmd id' v' c)
| insn_terminator tmn => insn_terminator (subst_tmn id' v' tmn)
end.

Definition subst_block (id':id) (v':value) (b:block) : block := 
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro l0 (List.map (subst_phi id' v') ps0) 
    (List.map (subst_cmd id' v') cs0) (subst_tmn id' v' tmn0) 
end.

Definition subst_fdef (id':id) (v':value) (f:fdef) : fdef := 
match f with
| fdef_intro bs => fdef_intro (List.map (subst_block id' v') bs) 
end.

Definition csubst_fdef (id':id) (cst':const) : fdef -> fdef := 
subst_fdef id' (value_const cst').

Definition csubst_block (id':id) (cst':const) : block -> block := 
subst_block id' (value_const cst').

Definition csubst_phi (id':id) (cst':const) : phinode -> phinode := 
subst_phi id' (value_const cst').

Definition csubst_cmd (id':id) (cst':const) : cmd -> cmd := 
subst_cmd id' (value_const cst').

Definition csubst_tmn (id':id) (cst':const) : terminator -> terminator := 
subst_tmn id' (value_const cst').

Definition csubst_insn (id':id) (cst':const) : insn -> insn := 
subst_insn id' (value_const cst').

Definition csubst_value (id':id) (cst':const) : value -> value := 
subst_value id' (value_const cst').

(************** Preserving wellformedness **************************************)

Lemma subst_getEntryBlock : forall f v0 id0 b
  (Hentry : getEntryBlock f = Some b),
  getEntryBlock (subst_fdef id0 v0 f) = Some (subst_block id0 v0 b).
Proof.
  intros. destruct f. simpl in *.
  destruct b0; inv Hentry; auto.
Qed.

Lemma subst_getEntryBlock_None : forall f v0 id0
  (Hentry : getEntryBlock f = None),
  getEntryBlock (subst_fdef id0 v0 f) = None.
Proof.
  intros. destruct f. simpl in *.
  destruct b; inv Hentry; auto.
Qed.

Lemma subst_genBlockUseDef_block : forall id0 v0 b ud,
  genBlockUseDef_block b ud = 
  genBlockUseDef_block (subst_block id0 v0 b) ud.
Proof.
  intros. destruct b; simpl.
  destruct t; auto.
Qed.

Lemma subst_genBlockUseDef_blocks : forall id0 v0 bs ud,
  genBlockUseDef_blocks bs ud = 
  genBlockUseDef_blocks (List.map (subst_block id0 v0) bs) ud.
Proof.
  induction bs; simpl; intros; auto.
    rewrite <- IHbs.
    rewrite <- subst_genBlockUseDef_block; auto.
Qed.

Lemma subst_hasNonePredecessor : forall f v0 id0 b
  (Hnpred : hasNonePredecessor b (genBlockUseDef_fdef f) = true),
  hasNonePredecessor (subst_block id0 v0 b) 
    (genBlockUseDef_fdef (subst_fdef id0 v0 f)) = true.
Proof.
  intros. destruct f. simpl in *.
  rewrite <- subst_genBlockUseDef_blocks.
  destruct b; auto.
Qed.

Lemma subst_InBlocksLabels : forall (v0 : value) (id0 : id) l0 (bs : blocks)
  (Hin : In l0 (getBlocksLabels (List.map (subst_block id0 v0) bs))),
  In l0 (getBlocksLabels bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl. intro.
    destruct Hin as [Hin | Hin]; auto.
Qed.

Lemma subst_uniqBlocksLabels : forall (v0 : value) (id0 : id) (bs : blocks)
  (HuniqBs : NoDup (getBlocksLabels bs)),
  NoDup (getBlocksLabels (List.map (subst_block id0 v0) bs)).
Proof.
  induction bs; simpl; intros; auto.
    destruct a. simpl.
    inv HuniqBs.
    apply NoDup_cons; eauto using subst_InBlocksLabels.
Qed.

Lemma subst_getPhiNodesIDs : forall v0 id0 ps,
  getPhiNodesIDs (List.map (subst_phi id0 v0) ps) = getPhiNodesIDs ps.
Proof.
  induction ps; simpl; intros; auto.
    destruct a. simpl in *. rewrite IHps; auto.
Qed.

Lemma subst_getCmdsLocs : forall v0 id0 cs,
  getCmdsLocs (List.map (subst_cmd id0 v0) cs) = getCmdsLocs cs.
Proof.
  induction cs; simpl; intros; auto.
    destruct a; simpl in *; rewrite IHcs; auto.
Qed.

Lemma subst_blocksLocs : forall (v0 : value) (id0 : id) (bs : blocks),
  getBlocksLocs (List.map (subst_block id0 v0) bs) = getBlocksLocs bs.
Proof.
  induction bs; simpl; auto.
    destruct a. simpl. 
    rewrite subst_getPhiNodesIDs.
    rewrite subst_getCmdsLocs.
    rewrite IHbs.
    destruct t; auto.
Qed.

Lemma subst_uniqBlocksLocs : forall (v0 : value) (id0 : id) (bs : blocks)
  (HuniqBs : NoDup (getBlocksLocs bs)),
  NoDup (getBlocksLocs (List.map (subst_block id0 v0) bs)).
Proof.
  intros. rewrite subst_blocksLocs. auto.
Qed.

Hint Resolve subst_uniqBlocksLabels subst_uniqBlocksLocs : ssa_subst.

Lemma subst_uniqBlocks : forall (v0 : value) (id0 : id) (bs : blocks)
  (HuniqBs : uniqBlocks bs),
  uniqBlocks (List.map (subst_block id0 v0) bs).
Proof.
  intros.
  destruct HuniqBs as [J1 J2].
  split; auto with ssa_subst.
Qed. 

Lemma subst_uniqFdef : forall f v0 id0 (HuniqF : uniqFdef f),
  uniqFdef (subst_fdef id0 v0 f).
Proof.
  intros.
  destruct f. simpl in *. apply subst_uniqBlocks; auto.
Qed.

Lemma subst_InBlocksB : forall v0 id0 b bs
  (Hin : InBlocksB b bs = true),
  InBlocksB (subst_block id0 v0 b) (List.map (subst_block id0 v0) bs) = true.
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

Hint Resolve subst_InBlocksB: ssa_subst.

Lemma subst_blockInFdefB : forall f v0 id0 b
  (Hin : blockInFdefB b f = true),
  blockInFdefB (subst_block id0 v0 b) (subst_fdef id0 v0 f) = true.
Proof.
  intros. destruct f. simpl in *.
  auto with ssa_subst.
Qed.

Hint Resolve subst_blockInFdefB: ssa_subst.

Lemma subst_InPhiNodesB : forall id0 v0 p ps, 
  InPhiNodesB p ps = true ->
  InPhiNodesB (subst_phi id0 v0 p) (List.map (subst_phi id0 v0) ps) = true.
Proof.
  induction ps; simpl; intros.
    congruence.
    apply orb_true_iff in H.
    apply orb_true_iff.
    destruct H as [H | H]; auto.
    apply phinodeEqB_inv in H; subst. 
    left. apply phinodeEqB_refl.
Qed.

Hint Resolve subst_InPhiNodesB: ssa_subst.

Lemma subst_phinodeInBlockB : forall v0 id0 p b
  (Hin : phinodeInBlockB p b = true),
  phinodeInBlockB (subst_phi id0 v0 p) (subst_block id0 v0 b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_subst.
Qed. 

Hint Resolve subst_phinodeInBlockB: ssa_subst.

Lemma subst_InCmdsB : forall id0 v0 c cs, 
  InCmdsB c cs = true ->
  InCmdsB (subst_cmd id0 v0 c) (List.map (subst_cmd id0 v0) cs) = true.
Proof.
  induction cs; simpl; intros.
    congruence.
    apply orb_true_iff in H.
    apply orb_true_iff.
    destruct H as [H | H]; auto.
    apply cmdEqB_inv in H; subst. 
    left. apply cmdEqB_refl.
Qed.

Hint Resolve subst_InCmdsB: ssa_subst.

Lemma subst_cmdInBlockB : forall v0 id0 c b
  (Hin : cmdInBlockB c b = true),
  cmdInBlockB (subst_cmd id0 v0 c) (subst_block id0 v0 b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_subst.
Qed. 

Hint Resolve subst_cmdInBlockB: ssa_subst.

Lemma subst_terminatorInBlockB : forall v0 id0 t b
  (Hin : terminatorInBlockB t b = true),
  terminatorInBlockB (subst_tmn id0 v0 t) (subst_block id0 v0 b) = true.
Proof.
  destruct b. simpl. intro. 
  apply terminatorEqB_inv in Hin. subst.
  apply terminatorEqB_refl.
Qed. 

Hint Resolve subst_terminatorInBlockB: ssa_subst.

Lemma subst_insnInFdefBlockB : forall f v0 id0 b instr
  (Hin : insnInFdefBlockB instr f b = true),
  insnInFdefBlockB (subst_insn id0 v0 instr) (subst_fdef id0 v0 f) 
    (subst_block id0 v0 b) = true.
Proof.
  unfold insnInFdefBlockB.
  intros.
  destruct instr; simpl;
    apply andb_true_iff in Hin; inv Hin;
    apply andb_true_iff; auto with ssa_subst.
Qed.

Hint Resolve subst_insnInFdefBlockB: ssa_subst.

Fixpoint remove_from_list_id (id':id) (l0:list_id) : list_id :=
match l0 with
| Nil_list_id => Nil_list_id
| Cons_list_id id0 tl => 
    if id_dec id0 id'  
    then remove_from_list_id id' tl 
    else Cons_list_id id0 (remove_from_list_id id' tl)
end.

Lemma csubst_values2ids : forall id' cst' l0 id_list0,
  values2ids (list_prj1 value l (unmake_list_value_l l0)) =
    unmake_list_id id_list0 ->
  values2ids
     (list_prj1 value l
        (unmake_list_value_l (subst_list_value_l id' (value_const cst') l0))) =
    unmake_list_id (remove_from_list_id id' id_list0).
Proof.
  induction l0; simpl; intros.
    destruct id_list0; inv H; auto.

    destruct v; simpl in *; auto.
      destruct (id_dec i0 id'); subst; destruct id_list0; inv H; simpl.
        destruct (id_dec i0 i0); try congruence; auto.
        destruct (id_dec i1 id'); simpl; try congruence; f_equal; auto.
Qed.     

Hint Resolve csubst_values2ids : ssa_subst.

Lemma csubst_getPhiNodeOperands : forall id' cst' p id_list0,
  getPhiNodeOperands p = unmake_list_id id_list0 ->
  getPhiNodeOperands (subst_phi id' (value_const cst') p) =
    unmake_list_id (remove_from_list_id id' id_list0).
Proof.
  destruct p; simpl; intros; auto with ssa_subst.
Qed.

Lemma csubst_getCmdOperands_helper : forall id' cst' v v0 id_list0
  (H : getValueIDs v ++ getValueIDs v0 = unmake_list_id id_list0),
  getValueIDs (v {[value_const cst' // id']}) ++
  getValueIDs (v0 {[value_const cst' // id']}) =
   unmake_list_id (remove_from_list_id id' id_list0).
Proof.
  intros.
  destruct v; simpl in *.
    destruct id_list0; inv H.
    destruct v0; simpl in *.
      destruct id_list0; inv H2.
      destruct id_list0; inv H1; simpl.
      destruct (id_dec i1 id'); destruct (id_dec i2 id'); subst; auto. 
  
      destruct id_list0; inv H2.
      destruct (id_dec i1 id'); subst; auto.
    destruct v0; simpl in *.
      destruct id_list0; inv H.
      destruct id_list0; inv H2; simpl.
      destruct (id_dec i1 id'); subst; auto. 
  
      destruct id_list0; inv H; auto.
Qed.

Hint Resolve csubst_getCmdOperands_helper: ssa_subst.

Lemma csubst_getCmdOperands : forall id' cst' c id_list0,
 getCmdOperands c = unmake_list_id id_list0 ->
 getCmdOperands (subst_cmd id' (value_const cst') c) =
   unmake_list_id (remove_from_list_id id' id_list0).
Proof.
  destruct c; simpl; intros; auto with ssa_subst.
Qed.

Lemma csubst_getTerminatorOperands : forall id' cst' t id_list0,
 getTerminatorOperands t = unmake_list_id id_list0 ->
 getTerminatorOperands (subst_tmn id' (value_const cst') t) =
   unmake_list_id (remove_from_list_id id' id_list0).
Proof.
  destruct t; simpl; intros; try solve [destruct id_list0; inv H; simpl; auto].
    destruct v; simpl in *.
      destruct id_list0; inv H.
      destruct id_list0; inv H2; simpl.
      destruct (id_dec i2 id'); subst; auto. 
  
      destruct id_list0; inv H; auto.
    destruct v; simpl in *.
      destruct id_list0; inv H.
      destruct id_list0; inv H2; simpl.
      destruct (id_dec i2 id'); subst; auto. 
  
      destruct id_list0; inv H; auto.
Qed.

Hint Resolve csubst_getCmdOperands csubst_getPhiNodeOperands
  csubst_getTerminatorOperands: ssa_subst.

Lemma csubst_getInsnOperands : forall id' cst' instr id_list0,
  getInsnOperands instr = unmake_list_id id_list0 ->
  getInsnOperands (csubst_insn id' cst' instr) =
    unmake_list_id (remove_from_list_id id' id_list0).
Proof.
  destruct instr; simpl; intros; auto with ssa_subst.
Qed.

Lemma subst_getCmdsIDs : forall v0 id0 cs,
  getCmdsIDs (List.map (subst_cmd id0 v0) cs) = getCmdsIDs cs.
Proof.
  induction cs; simpl; intros; auto.
    destruct a; simpl in *; rewrite IHcs; auto.
Qed.

Lemma subst_lookupBlockViaIDFromBlocks : forall id5 id' v' bs b,
  lookupBlockViaIDFromBlocks bs id5 = ret b ->
  lookupBlockViaIDFromBlocks (List.map (subst_block id' v') bs) id5 = 
    ret (subst_block id' v' b).
Proof.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    rewrite subst_getPhiNodesIDs.
    rewrite subst_getCmdsIDs.
    destruct (in_dec eq_dec id5 (getPhiNodesIDs p ++ getCmdsIDs c)); auto.
      inv H. auto.
Qed.

Hint Resolve subst_lookupBlockViaIDFromBlocks : ssa_subst.

Lemma subst_lookupBlockViaIDFromFdef : forall f id5 b id' v',
  lookupBlockViaIDFromFdef f id5 = ret b ->
  lookupBlockViaIDFromFdef (subst_fdef id' v' f) id5 = 
    ret (subst_block id' v' b).
Proof.
  destruct f. simpl; intros. auto with ssa_subst.
Qed.

Hint Resolve subst_lookupBlockViaIDFromFdef: ssa_subst.

Lemma subst_successors_blocks : forall id' v' bs,
  successors_blocks bs = successors_blocks (List.map (subst_block id' v') bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl.
    rewrite IHbs.
    destruct t; auto.
Qed.

Hint Resolve subst_successors_blocks: ssa_subst.

Lemma subst_successors : forall f id' v',
  successors f = successors (subst_fdef id' v' f).
Proof.
  intros. destruct f. simpl. auto with ssa_subst.
Qed.

Lemma subst_bound_blocks : forall id' v' bs,
  bound_blocks bs = bound_blocks (List.map (subst_block id' v') bs).
Proof.
  induction bs; simpl; auto.
    destruct a; simpl. rewrite IHbs. auto.
Qed.

Hint Resolve subst_bound_blocks.

Lemma subst_vertexes_fdef: forall f id' v',
  vertexes_fdef f = vertexes_fdef (subst_fdef id' v' f).
Proof.
  unfold vertexes_fdef.
  destruct f. simpl. intros.
  rewrite <- subst_bound_blocks. auto.
Qed.

Lemma subst_arcs_fdef: forall f id' v',
  arcs_fdef f = arcs_fdef (subst_fdef id' v' f).
Proof.
  unfold arcs_fdef.
  destruct f. simpl. intros.
  rewrite <- subst_successors_blocks. auto.
Qed.

Lemma subst_reachable : forall f id' v',
  reachable f = reachable (subst_fdef id' v' f).
Proof.
  intros.
  unfold reachable.
  case_eq (getEntryBlock f).
    intros b Hentry. 
    apply subst_getEntryBlock with (id0:=id')(v0:=v') in Hentry; eauto.
    rewrite Hentry.
    destruct b. simpl. 
    rewrite <- subst_vertexes_fdef.
    rewrite <- subst_arcs_fdef. auto.

    intro Hentry.
    apply subst_getEntryBlock_None with (id0:=id')(v0:=v') in Hentry; eauto.
    rewrite Hentry. auto.
Qed.

Lemma subst_isReachableFromEntry : forall f b id' v',
  isReachableFromEntry f b = 
    isReachableFromEntry (subst_fdef id' v' f) (subst_block id' v' b).
Proof.
  unfold isReachableFromEntry. intros.
  destruct b. simpl. rewrite <- subst_reachable; auto.
Qed.

Lemma subst_blockStrictDominates : forall f b1 b2 id' v',
  blockStrictDominates f b1 b2 <->
    blockStrictDominates (subst_fdef id' v' f) (subst_block id' v' b1)
      (subst_block id' v' b2).
Proof.
  intros.
  unfold blockStrictDominates. destruct b1. destruct b2. simpl.
  unfold dom_analyze. destruct f. simpl.
  rewrite <- subst_successors_blocks.
  remember (entry_dom b) as R1.
  remember (entry_dom (List.map (subst_block id' v') b)) as R2.
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

Lemma subst_blockDominates : forall f b1 b2 id' v',
  blockDominates f b1 b2 <->
    blockDominates (subst_fdef id' v' f) (subst_block id' v' b1)
      (subst_block id' v' b2).
Proof.
  intros.
  unfold blockDominates. destruct b1. destruct b2. simpl.
  unfold dom_analyze. destruct f. simpl.
  rewrite <- subst_successors_blocks.
  remember (entry_dom b) as R1.
  remember (entry_dom (List.map (subst_block id' v') b)) as R2.
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

Hint Unfold csubst_fdef csubst_block csubst_insn.

Lemma csubst_In_values2ids : forall id' cst' i0 l0 
  (n : i0 <> id')
  (H2 : ListSet.set_In i0 
    (values2ids (list_prj1 value l (unmake_list_value_l l0)))),
  ListSet.set_In i0
    (values2ids
      (list_prj1 value l
        (unmake_list_value_l (subst_list_value_l id' (value_const cst') l0)))).
Proof.
  induction l0; simpl; intros; auto.
    destruct v; simpl in *; auto.
    destruct H2 as [H2 | H2]; subst.
      destruct (id_dec i0 id'); try congruence; simpl; auto.
      destruct (id_dec i1 id'); subst; simpl; auto.
Qed.     

Hint Resolve csubst_In_values2ids : ssa_subst.

Lemma csubst_In_getPhiNodeOperands : forall id' cst' i0 p
  (n : i0 <> id')
  (H2 : ListSet.set_In i0 (getPhiNodeOperands p)),
  ListSet.set_In i0 (getPhiNodeOperands (subst_phi id' (value_const cst') p)).
Proof.
  destruct p; simpl; intros; auto with ssa_subst.
Qed.

Lemma csubst_In_getCmdOperands_helper : forall id' cst' v v0 i3
  (n : i3 <> id')
  (H2 : ListSet.set_In i3 (getValueIDs v ++ getValueIDs v0)),
  ListSet.set_In i3 (getValueIDs (v {[value_const cst' // id']}) ++
                     getValueIDs (v0 {[value_const cst' // id']})).
Proof.
  intros.
  destruct v; simpl in *.
    destruct H2 as [H2 | H2]; subst.
      destruct v0; simpl in *;
        destruct (id_dec i3 id'); try congruence; simpl; auto.
  
      destruct v0; simpl in *; try solve [inversion H2].
        destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
        destruct (id_dec i3 id'); try congruence; simpl; auto.
          destruct (id_dec i0 id'); simpl; auto.

    destruct v0; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      destruct (id_dec i3 id'); try congruence; simpl; auto.
Qed.

Hint Resolve csubst_In_getCmdOperands_helper: ssa_subst.

Lemma csubst_In_getCmdOperands : forall id' cst' c i3
  (n : i3 <> id')
  (H2 : ListSet.set_In i3 (getCmdOperands c)),
  ListSet.set_In i3 (getCmdOperands (subst_cmd id' (value_const cst') c)).
Proof.
  destruct c; simpl; intros; auto with ssa_subst.
Qed.

Lemma csubst_In_getTerminatorOperands : forall id' cst' t i3
  (n : i3 <> id')
  (H2 : ListSet.set_In i3 (getTerminatorOperands t)),
  ListSet.set_In i3 (getTerminatorOperands(subst_tmn id' (value_const cst') t)).
Proof.
  destruct t; simpl; intros; auto.
    destruct v; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      destruct (id_dec i3 id'); try congruence; simpl; auto.
    destruct v; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      destruct (id_dec i3 id'); try congruence; simpl; auto.
Qed.

Hint Resolve csubst_In_getCmdOperands csubst_In_getPhiNodeOperands
  csubst_In_getTerminatorOperands: ssa_subst.

Lemma csubst_In_getInsnOperands : forall i0 id' instr cst'
  (n : i0 <> id')
  (H2 : ListSet.set_In i0 (getInsnOperands instr)),
  ListSet.set_In i0
     (getInsnOperands (csubst_insn id' cst' instr)).
Proof.
  destruct instr; simpl; auto with ssa_subst.
Qed.

Lemma subst_isPhiNode : forall instr id' v',
  isPhiNode instr = isPhiNode (subst_insn id' v' instr).
Proof.
  destruct instr; auto.
Qed.

Lemma subst_insnDominates : forall i0 instr id' v' b, 
 NoDup (getBlockLocs b) ->
 insnInBlockB instr b = true ->
 (insnDominates i0 instr b <->
 insnDominates i0 (subst_insn id' v' instr) (subst_block id' v' b)).
Proof.
 intros i0 instr id' v' b Hnodup HiInB. destruct b. simpl.
 destruct instr; simpl; split; intro J; auto.
   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]]; 
     subst.
     left.
     exists (List.map (subst_phi id' v') ps1).
     exists (subst_phi id' v' p1).
     exists (List.map (subst_phi id' v') ps2).
     repeat rewrite List.map_app. 
     destruct p1. simpl. auto. 

     right.
     exists (List.map (subst_cmd id' v') cs1).
     exists (subst_cmd id' v' c1).
     exists (List.map (subst_cmd id' v') cs2).
     exists (List.map (subst_cmd id' v') cs3).
     simpl_env.
     repeat rewrite List.map_app. 
     destruct c1; simpl in *; inv J2; auto. 

   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]]; 
     subst.
     left.
     apply map_app_inv in J1. destruct J1 as [ps1' [ps2' [J1 [J2 J3]]]]; subst.
     destruct ps2'; inv J3.
     exists ps1'. exists p. exists ps2'.
     destruct p. simpl. auto. 
       
     right.
     apply map_app_inv in J1. destruct J1 as [cs1' [cs2' [J1 [J3 J4]]]]. subst.
     destruct cs2'; inv J4.
     apply map_app_inv in H1. destruct H1 as [cs3' [cs4' [J1 [J3 J4]]]]; subst.
     destruct cs4'; inv J4.
     assert (c0 = c1) as EQ.
       simpl in *.
       assert (getCmdLoc c1 = getCmdLoc c0) as EQ'.
         destruct c1; destruct c0; inv H0; auto.
       apply NoDup_inv in Hnodup. inv Hnodup.
       apply NoDup_inv in H1. inv H1.
       rewrite_env ((cs1'++c::cs3')++c1::cs4') in HiInB.
       rewrite_env ((cs1'++c::cs3')++c1::cs4') in H2.
       eapply NoDup_getCmdsLocs_prop; eauto using In_middle, InCmdsB_in.
     subst.
     exists cs1'. exists c. exists cs3'. exists cs4'.
     destruct c; simpl in *; inv J2; auto. 
 
   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq]; 
     subst; split; auto.
     left.
     exists (List.map (subst_cmd id' v') cs1).
     exists (subst_cmd id' v' c1).
     exists (List.map (subst_cmd id' v') cs2).
     simpl_env.
     repeat rewrite List.map_app. 
     destruct c1; simpl in *; inv J2; auto. 

     right.
     exists (List.map (subst_phi id' v') ps1).
     exists (subst_phi id' v' p1).
     exists (List.map (subst_phi id' v') ps2).
     repeat rewrite List.map_app. 
     destruct p1. simpl. auto. 

   simpl in *. apply terminatorEqB_inv in HiInB. subst.
   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq]; 
     subst; split; auto.
     left.
     apply map_app_inv in J1. destruct J1 as [cs1' [cs2' [J1 [J3 J4]]]]. subst.
     destruct cs2'; inv J4.
     exists cs1'. exists c. exists cs2'.
     destruct c; simpl in *; inv J2; auto. 
       
     right.
     apply map_app_inv in J1. destruct J1 as [ps1' [ps2' [J1 [J2 J3]]]]; subst.
     destruct ps2'; inv J3.
     exists ps1'. exists p. exists ps2'.
     destruct p. simpl. auto. 
Qed.

Hint Resolve csubst_In_getInsnOperands: ssa_subst.

Lemma csubst_wf_operand : forall instr id' cst' f b i0
  (Huniq : NoDup (getBlockLocs b))
  (H1 : wf_operand f b instr i0)
  (n : i0 <> id'),
   wf_operand (csubst_fdef id' cst' f) (csubst_block id' cst' b)
     (csubst_insn id' cst' instr) i0.
Proof.
  intros.
  inv H1.
  eapply wf_operand_intro; try solve 
    [eauto with ssa_subst | autounfold; eauto with ssa_subst].   

    autounfold.
    rewrite <- subst_isPhiNode; auto.

    autounfold.
    rewrite <- subst_insnDominates; eauto using insnInFdefBlockB__insnInBlockB.
    rewrite <- subst_blockStrictDominates.
    rewrite <- subst_isReachableFromEntry; auto.
Qed.

Hint Resolve csubst_wf_operand: ssa_subst.
Hint Constructors wf_operand_list.

Lemma csubst_wf_operand_list : forall instr id' cst' f b id_list0
  (Huniq : NoDup (getBlockLocs b))
  (H2 : wf_operand_list
         (make_list_fdef_block_insn_id
            (map_list_id (fun id_ : id => (f, b, instr, id_)) id_list0))),
  wf_operand_list
   (make_list_fdef_block_insn_id
      (map_list_id
         (fun id_ : id =>
          (csubst_fdef id' cst' f, csubst_block id' cst' b,
          csubst_insn id' cst' instr, id_)) (remove_from_list_id id' id_list0))).
Proof.
  induction id_list0; simpl; intros; auto.
    inv H2.
    destruct (id_dec i0 id'); subst; simpl; auto with ssa_subst.
Qed.

Hint Resolve csubst_getInsnOperands csubst_wf_operand_list: ssa_subst.

Lemma csubst_wf_insn_base : forall f b cst0 id0 instr 
  (Huniq : NoDup (getBlockLocs b))
  (HwfI: wf_insn_base f b instr),
  wf_insn_base (csubst_fdef id0 cst0 f) (csubst_block id0 cst0 b) 
    (csubst_insn id0 cst0 instr).
Proof.
  intros.
  inv HwfI.
  eapply subst_insnInFdefBlockB in H; eauto.
  eapply wf_insn_base_intro; eauto with ssa_subst.
Qed.

Hint Constructors wf_insn wf_value.

Lemma subst_lookupBlockViaLabelFromBlocks : forall l5 id' v' bs b,
  lookupBlockViaLabelFromBlocks bs l5 = ret b ->
  lookupBlockViaLabelFromBlocks (List.map (subst_block id' v') bs) l5 = 
    ret (subst_block id' v' b).
Proof.
  unfold lookupBlockViaLabelFromBlocks.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l5 l0); 
      subst; inv H; auto.
Qed.

Hint Resolve subst_lookupBlockViaLabelFromBlocks : ssa_subst.

Lemma subst_lookupBlockViaLabelFromFdef : forall f l5 b id' v',
  lookupBlockViaLabelFromFdef f l5 = ret b ->
  lookupBlockViaLabelFromFdef (subst_fdef id' v' f) l5 = 
    ret (subst_block id' v' b).
Proof.
  destruct f. simpl. intros. apply subst_lookupBlockViaLabelFromBlocks; auto.
Qed.

Lemma subst_lookupIDFromPhiNodes : forall id5 id' v' ps,
  lookupIDFromPhiNodes ps id5 = 
    lookupIDFromPhiNodes (List.map (subst_phi id' v') ps) id5.
Proof.
  induction ps; simpl; intros; auto.
    unfold lookupIDFromPhiNode in *.
    destruct a. simpl in *.
    destruct (id5 == i0); auto.
Qed.
 
Lemma subst_lookupIDFromCmds : forall id5 id' v' cs,
  lookupIDFromCmds cs id5 = 
    lookupIDFromCmds (List.map (subst_cmd id' v') cs) id5.
Proof.
  induction cs; simpl; intros; auto.
    unfold lookupIDFromCmd in *.
    destruct a; simpl in *; destruct (id5 == i0); auto.
Qed.

Lemma subst_lookupIDFromTerminator : forall id5 id' v' t,
  lookupIDFromTerminator t id5 = 
    lookupIDFromTerminator (subst_tmn id' v' t) id5.
Proof.
  destruct t; auto.
Qed.

Lemma subst_lookupIDFromBlocks : forall id5 id' v' bs,
  lookupIDFromBlocks bs id5 = 
    lookupIDFromBlocks (List.map (subst_block id' v') bs) id5.
Proof.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    rewrite IHbs.
    remember (lookupIDFromPhiNodes p id5) as R1.
    erewrite subst_lookupIDFromPhiNodes in HeqR1; eauto.
    rewrite HeqR1.
    remember (lookupIDFromCmds c id5) as R2.
    erewrite subst_lookupIDFromCmds in HeqR2; eauto.
    rewrite HeqR2.
    remember (lookupIDFromTerminator t id5) as R3.
    erewrite subst_lookupIDFromTerminator in HeqR3; eauto. 
    rewrite HeqR3; auto.
Qed.

Lemma subst_lookupIDFromFdef : forall f id5 id' v',
  lookupIDFromFdef f id5 = lookupIDFromFdef (subst_fdef id' v' f) id5.
Proof.
  destruct f. simpl. intros. rewrite <- subst_lookupIDFromBlocks; auto.
Qed.

Hint Resolve subst_lookupBlockViaLabelFromFdef: ssa_subst.

Lemma csubst_wf_value : forall f cst0 id0 v (Hwfv: wf_value f v),
  wf_value (csubst_fdef id0 cst0 f) (csubst_value id0 cst0 v).
Proof.
  intros.
  inv Hwfv; try constructor.
    simpl. destruct (id_dec id5 id0); constructor.
    autounfold. rewrite <- subst_lookupIDFromFdef; auto.
Qed.

Hint Constructors wf_phi_operands.

Lemma csubst_wf_phi_operands : forall f b cst0 id0 id' vls
  (Hwf_pnops: wf_phi_operands f b id' vls),
  wf_phi_operands (csubst_fdef id0 cst0 f) (csubst_block id0 cst0 b) id'
    (subst_list_value_l id0 (value_const cst0) vls).
Proof.
  intros.
  induction Hwf_pnops; simpl; auto.
    destruct (id_dec vid1 id0); auto.
    eapply wf_phi_operands_cons_vid; eauto.
      eapply subst_lookupBlockViaIDFromFdef in H; eauto.
      eapply subst_lookupBlockViaLabelFromFdef in H0; eauto.
      autounfold.
      destruct H1 as [H1 | H1].
        rewrite <- subst_blockDominates; auto.
        rewrite <- subst_isReachableFromEntry; auto.
Qed.
     
Lemma subst_predOfBlock : forall id0 v0 b,
  predOfBlock b = predOfBlock (subst_block id0 v0 b).
Proof.
  destruct b; simpl; auto.
Qed.

Lemma subst_list_value_l__labels : forall v0 id0 vls,
  let '(_, ls1):=split (unmake_list_value_l vls) in
  let '(_, ls2):=split (unmake_list_value_l (subst_list_value_l id0 v0 vls)) in
  ls1 = ls2.
Proof.
  induction vls; simpl; auto.
    destruct (split (unmake_list_value_l vls)).
    destruct (split (unmake_list_value_l (subst_list_value_l id0 v0 vls))).
    subst. auto.
Qed.

Lemma subst_check_list_value_l : forall f b v0 id0 vls
  (Hcl: check_list_value_l f b vls),
  check_list_value_l (subst_fdef id0 v0 f) (subst_block id0 v0 b)
    (subst_list_value_l id0 v0 vls).
Proof.
  unfold check_list_value_l. destruct f as [bs]. simpl. intros until vls.
  repeat rewrite <- subst_genBlockUseDef_blocks.
  repeat rewrite <- subst_predOfBlock. 
  assert (J:=@subst_list_value_l__labels v0 id0 vls).
  destruct (split (unmake_list_value_l vls)).
  destruct (split (unmake_list_value_l (subst_list_value_l id0 v0 vls))).
  subst. auto.
Qed.

Hint Resolve csubst_wf_phi_operands subst_check_list_value_l: ssa_subst.

Lemma csubst_wf_phinode : forall f b cst0 id0 PN (HwfPN: wf_phinode f b PN),
  wf_phinode (csubst_fdef id0 cst0 f) (csubst_block id0 cst0 b) 
    (csubst_phi id0 cst0 PN).
Proof.
  intros. destruct PN as [id' vls].
  unfold wf_phinode in *. simpl.
  destruct HwfPN as [Hwf_pnops Hcl].
  split; auto with ssa_subst.
    autounfold. auto with ssa_subst.
Qed.

Hint Resolve csubst_wf_value : ssa_subst.

Lemma csubst_wf_value_list : forall
  (cst0 : const)
  (id0 : id)
  (fdef5 : fdef)
  (block5 : block)
  (value_l_list : list_value_l)
  (H : wf_value_list
        (make_list_fdef_value
           (map_list_value_l
              (fun (value_ : value) (_ : l) => (fdef5, value_)) value_l_list))),
   wf_value_list
     (make_list_fdef_value
        (map_list_value_l
           (fun (value_ : value) (_ : l) =>
            (csubst_fdef id0 cst0 fdef5, value_))
           (subst_list_value_l id0 (value_const cst0) value_l_list))).
Proof.
  induction value_l_list; simpl; intros; auto.
    inv H.
    apply Cons_wf_value_list; auto.
    apply csubst_wf_value; auto.  
Qed.

Hint Resolve csubst_wf_value_list: ssa_subst.

Lemma csubst_wf_insn : forall f b cst0 id0 instr (HwfI: wf_insn f b instr)
  (Huniq : NoDup (getBlockLocs b)),
  wf_insn (csubst_fdef id0 cst0 f) (csubst_block id0 cst0 b) 
    (csubst_insn id0 cst0 instr).
Proof.
  intros.

  Ltac DONE := 
  eauto with ssa_subst; try match goal with
  | H : wf_insn_base _ _ _ |- wf_insn_base _ _ _ => 
    eapply csubst_wf_insn_base in H; eauto
  | H : wf_value _ ?v |- wf_value _ (?v {[ _ // _ ]}) => 
    eapply csubst_wf_value  in H; eauto
  | H : lookupBlockViaLabelFromFdef _ ?l = Some _ |- 
        lookupBlockViaLabelFromFdef _ ?l = Some _  =>
    eapply subst_lookupBlockViaLabelFromFdef in H; eauto
  | H : insnInFdefBlockB _ _ _ = _ |- insnInFdefBlockB _ _ _ = _ =>
    eapply subst_insnInFdefBlockB in H; eauto
  | H : wf_phinode _ _ _ |- wf_phinode _ _ _ =>
    eapply csubst_wf_phinode in H; eauto
  end.
  
  destruct HwfI; simpl;
  match goal with
  | |- wf_insn _ _ _ => 
      try solve [eapply wf_insn_return; DONE |
           eapply wf_insn_br; DONE |
           eapply wf_insn_br_uncond; DONE |
           eapply wf_insn_bop; DONE |
           eapply wf_insn_icmp; DONE |
           eapply wf_insn_phi; DONE]
  end.
Qed.

Hint Resolve csubst_wf_insn : ssa_subst.

Hint Constructors wf_phinodes.

Lemma csubst_wf_phinodes : forall f b cst0 id0 PNs (HwfPNs: wf_phinodes f b PNs)
  (Huniq : NoDup (getBlockLocs b)),
  wf_phinodes (csubst_fdef id0 cst0 f) (csubst_block id0 cst0 b)
    (List.map (csubst_phi id0 cst0) PNs).
Proof.
  intros. 
  induction HwfPNs; simpl; auto.
    eapply csubst_wf_insn in H; eauto.
Qed.

Hint Constructors wf_cmds.

Lemma csubst_wf_cmds : forall f b cst0 id0 Cs (HwfCs: wf_cmds f b Cs)
  (Huniq : NoDup (getBlockLocs b)),
  wf_cmds (csubst_fdef id0 cst0 f) (csubst_block id0 cst0 b)
    (List.map (csubst_cmd id0 cst0) Cs).
Proof.
  intros. 
  induction HwfCs; simpl; auto.
    eapply csubst_wf_insn in H; eauto.
Qed.

Lemma csubst_wf_block : forall f b cst0 id0 (HwfB : wf_block f b)
  (Huniq : NoDup (getBlockLocs b)),
  wf_block (csubst_fdef id0 cst0 f) (csubst_block id0 cst0 b).
Proof.
  intros.
  inv_wf_block HwfB; subst.
  match goal with
  | HBinF : blockInFdefB _ _ = _,
    HwfPNs : wf_phinodes _ _ _,
    HwfCs : wf_cmds _ _ _,
    Hwftmn : wf_insn _ _ _ |- _ =>
     eapply subst_blockInFdefB in HBinF; eauto;
     eapply csubst_wf_phinodes in HwfPNs; eauto;
     eapply csubst_wf_cmds in HwfCs; eauto;
     eapply csubst_wf_insn in Hwftmn; eauto
  end.
  apply wf_block_intro; eauto.
Qed.

Hint Resolve csubst_wf_block : ssa_subst.

Hint Constructors wf_blocks.

Lemma csubst_wf_blocks : forall f bs cst0 id0 (HwfBs : wf_blocks f bs)
  (Huniq : uniqBlocks bs),
  wf_blocks (csubst_fdef id0 cst0 f) (List.map (csubst_block id0 cst0) bs).
Proof.
  intros.
  induction HwfBs; simpl; auto.
    simpl_env in Huniq. apply uniqBlocks_inv in Huniq. inv Huniq.
    inv H0. simpl in *. simpl_env in H3.
    apply wf_blocks_cons; eauto with ssa_subst.
Qed.

Hint Resolve subst_getEntryBlock subst_hasNonePredecessor subst_uniqFdef 
  csubst_wf_blocks : ssa_subst.

Lemma csubst_wf_fdef : forall f cst0 id0 (HwfF: wf_fdef f),
  wf_fdef (csubst_fdef id0 cst0 f).
Proof.
  intros.
  inv_wf_fdef HwfF.
  match goal with
  | Hentry : getEntryBlock _ = _,
    HuniqF : uniqFdef _,
    Hnpred : hasNonePredecessor _ _ = _,
    HwfBs : wf_blocks _ _ |- _ =>
     eapply subst_getEntryBlock in Hentry; eauto;
     eapply subst_hasNonePredecessor in Hnpred; eauto;
     eapply csubst_wf_blocks in HwfBs; eauto;
     eapply subst_uniqFdef in HuniqF; eauto
  end.
  eapply wf_fdef_intro; eauto.
Qed.

(************** Bisimulation for constant substituion **************************)

Definition wf_GVs (id0:id)(cst0:const)(id1:id)(gvs:GenericValue) : Prop :=
  (id0 = id1 -> const2GV cst0 = gvs).

Definition wf_defs (id0:id)(cst0:const)(lc:GVMap)(ids1:list atom) : Prop :=
forall id1 gvs1, 
  In id1 ids1 -> 
  lookupAL _ lc id1 = Some gvs1 -> 
  wf_GVs id0 cst0 id1 gvs1.

Lemma wf_defs_eq : forall id0 cst0 ids2 ids1 lc',
  set_eq _ ids1 ids2 ->
  wf_defs id0 cst0 lc' ids1 ->
  wf_defs id0 cst0 lc' ids2.
Proof.
  intros.
  intros id1 gvs1 Hin Hlk.
  destruct H as [J1 J2]. eauto.
Qed.

Lemma wf_defs_updateAddAL : forall g1 id0 cst0 lc' ids1 ids2 i1,
  wf_defs id0 cst0 lc' ids1 ->
  set_eq _ (i1::ids1) ids2 ->
  wf_GVs id0 cst0 i1 g1 ->
  wf_defs id0 cst0 (updateAddAL _ lc' i1 g1) ids2.
Proof.
  intros g1 id0 cst0 lc' ids1 ids2 i1 HwfDefs Heq Hwfgvs.
  intros id1 gvs1 Hin Hlk.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  destruct (eq_dec i1 id1); subst.
    rewrite lookupAL_updateAddAL_eq in Hlk; auto.   
    inv Hlk. eauto.

    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
Qed.
        
Export Opsem.

Fixpoint const_in_list_value_l (cst0:const) (vls:list_value_l) : Prop :=
match vls with
| Nil_list_value_l => True
| Cons_list_value_l (value_const cst) _ vls' => 
    const2GV cst = const2GV cst0 /\ const_in_list_value_l cst0 vls'
| _ => False
end.

Definition const_in_phinodes (id0:id) (cst0:const) ps : Prop :=
match lookupPhiNodeViaIDFromPhiNodes ps id0 with
| Some (insn_phi id0' vls) =>
    id0' = id0 -> const_in_list_value_l cst0 vls
| _ => True
end.

Hint Resolve lookupPhiNodeViaIDFromPhiNodes_middle : vminus.

Lemma getOperandValue__wf_gvs : forall b lc i0 l0 ps1 ps2 cst0 gvs v
  (HeqR0 : ret v = getValueViaBlockFromValuels l0 b)
  (HcInPNs : const_in_phinodes i0 cst0 (ps1 ++ insn_phi i0 l0 :: ps2))
  (Huniq' : NoDup (getPhiNodesIDs (ps1 ++ insn_phi i0 l0 :: ps2))) 
  (HeqR : ret gvs = getOperandValue v lc),
  const2GV cst0 = gvs.
Proof.
  intros.
  unfold const_in_phinodes in *.
  destruct b.
  simpl in *. 
  assert (lookupPhiNodeViaIDFromPhiNodes (ps1 ++ insn_phi i0 l0 :: ps2) i0 =
    Some (insn_phi i0 l0)) as Hlk. auto with vminus.
  rewrite Hlk in HcInPNs.
  destruct (i0 == i0) as [e' | n]; try solve [contradict n; auto].
  apply HcInPNs in e'. clear HcInPNs Hlk Huniq'. 
  induction l0; inv HeqR0.
    simpl in *.
    destruct v0; tinv e'.
    destruct e'.
    destruct (l0 == l1); subst; eauto.
      inv H0. simpl in *. inv HeqR; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec1_aux : forall f
    b lc id1 l3 cs tmn ps2 ps1 lc' id0 cst0 gvs
  (HcInPNs : const_in_phinodes id0 cst0 (ps1++ps2)),
  Some lc' = getIncomingValuesForBlockFromPHINodes ps2 b lc ->
  List.In id1 (getPhiNodesIDs ps2) ->
  uniqFdef f ->
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  lookupAL _ lc' id1 = Some gvs ->
  wf_GVs id0 cst0 id1 gvs.
Proof.    
  intros f b lc id1 l3 cs tmn ps2 ps1 lc' id0 cst0 gvs HcInPNs H H0 Huniq Hbinf 
    Hlk.
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

    destruct a.
    destruct H0 as [H0 | H0]; subst.
      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].
        remember (getOperandValue v lc) as R.
        destruct R as [g|]; tinv H.
        destruct (getIncomingValuesForBlockFromPHINodes ps2 b lc); inv H.
        simpl in *. intro J; subst.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0) 
          as [e' | n]; try solve [contradict n; auto].
        inv Hlk. eapply getOperandValue__wf_gvs; eauto.

      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].   
        remember (getOperandValue v lc) as R.
        destruct R; tinv H. 
        remember (getIncomingValuesForBlockFromPHINodes ps2 b lc) as R.
        destruct R; inv H. simpl in *.         
        destruct (id1 == i0); subst.
          clear - Huniq' H0.
          rewrite getPhiNodesIDs_app in Huniq'.
          apply NoDup_split in Huniq'.
          destruct Huniq' as [_ Huniq'].
          inv Huniq'. congruence.
     
          eapply IHps2 with (ps1:=ps1 ++ [insn_phi i0 l0]); simpl_env; eauto.
Qed.

Hint Resolve wf_fdef__uniqFdef.

Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall f b 
    lc id1 l3 cs tmn ps lc' id0 cst0 gvs,
  const_in_phinodes id0 cst0 ps ->
  Some lc' = getIncomingValuesForBlockFromPHINodes ps b lc ->
  In id1 (getPhiNodesIDs ps) ->
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_fdef f ->
  lookupAL _ lc' id1 = Some gvs -> 
  wf_GVs id0 cst0 id1 gvs.
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H2.
    apply lookupBlockViaLabelFromFdef_inv in H2; auto.
    destruct H2; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec1_aux with (ps1:=nil); eauto.
Qed.

Export OpsemProps.

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' id0 cst0 b
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock (block_intro l' ps' cs' tmn') b lc = ret lc')
  (HcInPNs : const_in_phinodes id0 cst0 ps')
  (t : list atom)
  (Hwfdfs : wf_defs id0 cst0 lc t)
  (ids0' : list atom)
  (HwfF : wf_fdef F)
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs id0 cst0 lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  intros id1 gvs Hid1 Hlk.
  remember (getIncomingValuesForBlockFromPHINodes ps' b lc) as R1.
  destruct R1 as [rs|]; inv Hswitch.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    eapply getIncomingValuesForBlockFromPHINodes_spec1 in HeqR1; eauto.
    apply updateValuesForNewBlock_spec6 in Hlk; auto.
    eapply getIncomingValuesForBlockFromPHINodes_spec6 in HeqR1; eauto.

    assert (Hnotin' := Hnotin).
    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin.
    apply Hwfdfs; auto.
      eapply getIncomingValuesForBlockFromPHINodes_spec8 in HeqR1; eauto.
      eapply updateValuesForNewBlock_spec7; eauto.
Qed.

Require Import Maps.

Definition const_in_fdef (id0:id) (cst0:const) (f:fdef) : Prop :=
let '(fdef_intro bs) := f in
match lookupInsnViaIDFromBlocks bs id0 with
| Some (insn_cmd (insn_bop id0' bop0 (value_const c1) (value_const c2))) =>
    id0' = id0 -> mbop bop0 (const2GV c1) (const2GV c2) = const2GV cst0
| Some (insn_cmd (insn_bop id0' _ _ _)) =>
    id0' = id0 -> False
| Some (insn_cmd (insn_icmp id0' cond0 (value_const c1) (value_const c2))) =>
    id0' = id0 -> micmp cond0 (const2GV c1) (const2GV c2) = const2GV cst0
| Some (insn_cmd (insn_icmp id0' _ _ _)) =>
    id0' = id0 -> False
| Some (insn_phinode (insn_phi id0' vls)) =>
    id0' = id0 -> const_in_list_value_l cst0 vls
| _ => True
end.

Lemma const_in_fdef__const_in_phinodes : forall id0 cst0 f l' ps' cs' tmn'
  (HcInF : const_in_fdef id0 cst0 f)
  (J : blockInFdefB (block_intro l' ps' cs' tmn') f)
  (Huniq : uniqFdef f),
  const_in_phinodes id0 cst0 ps'.
Proof.
  intros. destruct f. simpl in *. 
  unfold const_in_phinodes. destruct Huniq as [_ Huniq].
  case_eq (lookupInsnViaIDFromBlocks b id0).
    intros instr Hlkup.
    rewrite Hlkup in HcInF. 
    destruct instr. 
      remember (lookupPhiNodeViaIDFromPhiNodes ps' id0) as R.
      destruct R; auto.
      eapply lookupPhiViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes in
        Hlkup; eauto.
      subst. auto.

      eapply lookupCmdViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes in 
        Hlkup; eauto.
      rewrite Hlkup. auto.

      eapply lookupTmnViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes in 
        Hlkup; eauto.
      rewrite Hlkup. auto.

    intros Hlkup.
    eapply lookupNoneViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes in
      Hlkup; eauto.
    rewrite Hlkup. auto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 
  lc lc' id0 cst0 ,
const_in_fdef id0 cst0 F ->
wf_fdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) lc = Some lc' ->
wf_defs id0 cst0 lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs id0 cst0 lc' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 lc lc' id0 cst0 
    HcInF HwfF HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
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
      eapply wf_defs_br_aux; eauto using const_in_fdef__const_in_phinodes.
        
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
      eapply wf_defs_br_aux; eauto using const_in_fdef__const_in_phinodes.
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs ids0 l' ps' cs' tmn' l0 
  lc lc' bid id0 cst0,
const_in_fdef id0 cst0 F ->
wf_fdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) lc = Some lc' ->
wf_defs id0 cst0 lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs id0 cst0 lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c lc lc' id0 cst0,
const_in_fdef id0 cst0 F ->
wf_fdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) lc = Some lc' ->
wf_defs id0 cst0 lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs id0 cst0 lc' ids0'.
Proof.
  intros.
  remember (isGVZero c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Lemma state_tmn_typing : forall f l1 ps1 cs1 tmn1 defs id1 lc id0 cst0 gv,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs id0 cst0 lc defs ->
  wf_fdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  lookupAL _ lc id1 = Some gv ->
  wf_GVs id0 cst0 id1 gv.
Proof.
  intros f l1 ps1 cs1 tmn1 defs id1 lc id0 cst0 gv Hreach HwfInstr Hinscope 
    HwfDefs HuniqF HinOps Hlkup.
  apply wf_insn__wf_insn_base in HwfInstr; 
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  
 
  assert (
     In (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id1)
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
    (insn1:=insn_terminator tmn1)(id1:=id1) in H2; auto.

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

Lemma state_cmd_typing : forall f b c defs id1 lc id0 cst0 gv,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs id0 cst0 lc defs ->
  wf_fdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  lookupAL _ lc id1 = Some gv ->
  wf_GVs id0 cst0 id1 gv.
Proof.
  intros f b c defs id1 lc id0 cst0 gv Hnodup Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps Hlkup.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  

  assert (
     In (f, b, insn_cmd c, id1)
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

  apply wf_operand_list__elim with (f1:=f)(b1:=b)(insn1:=insn_cmd c)(id1:=id1) 
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
  (lc : GVMap)
  (HwfSys1 : wf_fdef f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn) f = true)
  (l0 : list atom) id0 cst0
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (Hinscope : wf_defs id0 cst0 lc l0)
  (v : value)
  (Hvincs : valueInTmnOperands v tmn) gv gv'
  (Hget' : getOperandValue (v {[ value_const cst0 // id0 ]}) lc = Some gv')
  (Hget : getOperandValue v lc = Some gv),
  gv = gv'.
Proof.
  intros.
  destruct v as [vid | vc]; simpl in *; try congruence.
  destruct (id_dec vid id0); simpl in *; subst; try congruence.
    assert (HwfInstr:=HbInF).
    eapply wf_fdef__wf_tmn in HwfInstr; eauto.
    assert (wf_GVs id0 cst0 id0 gv) as Hlkup.
      eapply state_tmn_typing; eauto. 
      apply valueInTmnOperands__InOps; auto.
    rewrite Hlkup in Hget'; congruence.
Qed.

Lemma getOperandValue_inCmdOps_sim : forall
  (f : fdef)
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVMap)
  (HwfSys1 : wf_fdef f)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (c : cmd) id0 cst0
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : wf_defs id0 cst0 lc l0)
  (v : value)
  (Hvincs : valueInCmdOperands v c) gv gv'
  (Hget' : getOperandValue (v {[ value_const cst0 // id0 ]} ) lc = Some gv')
  (Hget : getOperandValue v lc = Some gv),
  gv = gv'.
Proof.
  intros.
  destruct v as [vid | vc]; simpl in Hget', Hget; try congruence.
  destruct (id_dec vid id0); simpl in Hget', Hget; subst; try congruence.
    assert (wf_GVs id0 cst0 id0 gv) as Hlkup.
      eapply state_cmd_typing; eauto. 
      eapply wf_fdef__uniq_block; eauto.
      eapply wf_fdef__wf_cmd; eauto using In_middle.
      apply valueInCmdOperands__InOps; auto.
    rewrite Hlkup in Hget'; congruence.
Qed.

Lemma getValueViaLabelFromValuels_sim : forall l1 id0 v0 l2 v v'
  (HeqR0 : ret v = getValueViaLabelFromValuels l2 l1)
  (HeqR' : ret v' =
          getValueViaLabelFromValuels
            (subst_list_value_l id0 v0 l2) l1),
  v' = v {[ v0 // id0 ]}.
Proof.
  induction l2; simpl; intros; try congruence.
    destruct (l0 == l1); subst; try (congruence || eauto).
Qed.

Lemma getValueViaLabelFromValuels_getOperandValue_sim : forall
  (f : fdef) (l0 : l) (lc : GVMap) (t : list atom) (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator) (id0 : id) (cst0 : const)
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs id0 cst0 lc t)
  (HuniqF : uniqFdef f) (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (i0 : id) (l2 : list_value_l) (ps2 : list phinode)
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (v0 : value)
  (HeqR3 : ret v0 = getValueViaLabelFromValuels l2 l1)
  (g1 : GenericValue) 
  (HeqR4 : ret g1 = getOperandValue v0 lc)
  (g2 : GVMap) (g : GenericValue) (g0 : GVMap)
  (H1 : wf_value_list
         (make_list_fdef_value
            (map_list_value_l (fun (value_ : value) (_ : l) => (f, value_))
               l2)))
  (H7 : wf_phinode f (block_intro l0 ps' cs' tmn') (insn_phi i0 l2))
  (HeqR1 : ret g = getOperandValue (v0 {[value_const cst0 // id0]}) lc),
  g1 = g.
Proof.
  intros.
  destruct v0 as [vid | vc]; simpl in *; try congruence.
  destruct (id_dec vid id0); subst; simpl in *; try congruence.
  app_inv.
  destruct H7 as [Hwfops Hwfvls].
  symmetry_ctx.
  assert (Hnth:=HeqR3).
  eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
  destruct Hnth as [n Hnth].
  assert (HwfV:=HeqR3).
  eapply wf_value_list__getValueViaLabelFromValuels__wf_value in HwfV; eauto.
  eapply wf_phi_operands__elim in Hwfops; eauto.
  destruct Hwfops as [vb [b1 [Hlkvb [Hlkb1 Hdom]]]].
  assert (b1 = block_intro l1 ps1 cs1 tmn1) as EQ.
    clear - Hlkb1 HbInF HuniqF.
    apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
    rewrite HbInF in Hlkb1. inv Hlkb1; auto.
  subst.
  clear - Hdom Hinscope HeqR HeqR3 Hreach H1 HbInF Hlkvb Hlkb1 HuniqF HeqR4.
  destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
  clear Hreach.        
  unfold blockDominates in J3.         
  destruct vb.
  unfold inscope_of_tmn in HeqR.
  destruct f.
  remember ((dom_analyze (fdef_intro b)) !! l1) as R1.
  destruct R1.
  apply fold_left__spec in HeqR.
  destruct (eq_atom_dec l3 l1); subst.
  Case "l3=l1".
    destruct HeqR as [HeqR _].
    apply Hinscope in HeqR4; auto.
      symmetry. apply HeqR4; auto.
   
      clear - HeqR3 HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
      assert (J':=Hlkvb).
      apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
      apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto. 
      destruct Hlkb1 as [J1 J2].
      eapply blockInFdefB_uniq in J2; eauto.
      destruct J2 as [J2 [J4 J5]]; subst.
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
      simpl in J'.
      apply HeqR; auto.
  
  Case "l3<>l1".
    assert (In l3 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as G.
      destruct J3 as [J3 | J3]; subst; try congruence.
      apply ListSet.set_diff_intro; auto.
        simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
    assert (
      lookupBlockViaLabelFromFdef (fdef_intro b) l3 = 
        ret block_intro l3 p c t0) as J1.
      clear - Hlkvb HuniqF.
      apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
      apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkvb; auto.
    destruct HeqR as [_ [HeqR _]].
    apply HeqR in J1; auto.
    apply Hinscope in HeqR4; auto.
      symmetry. apply HeqR4; auto.
  
      clear - J1 HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
      apply J1.
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall
  (f : fdef)
  l0
  (lc : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1 id0 cst0
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs id0 cst0 lc t)
  (HuniqF : uniqFdef f)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block f (block_intro l1 ps1 cs1 tmn1))
  ps2
  (H8 : wf_phinodes f (block_intro l0 ps' cs' tmn') ps2)
  (Hin: exists ps1, ps' = ps1 ++ ps2) RVs RVs'
  (Hget : getIncomingValuesForBlockFromPHINodes ps2 (block_intro l1 ps1 cs1 tmn1)
    lc = ret RVs)
  (Hget' : getIncomingValuesForBlockFromPHINodes 
    (List.map (csubst_phi id0 cst0) ps2) 
    (csubst_block id0 cst0 (block_intro l1 ps1 cs1 tmn1)) lc = ret RVs'),
  RVs = RVs'.
Proof.
  induction ps2; intros; simpl in Hget, Hget'; try congruence.
    destruct a. inv H8. inv H3. simpl in Hget'.
    inv_mbind'. 
    app_inv.
    eapply getValueViaLabelFromValuels_sim in HeqR0; eauto. subst.
    assert (g1 = g) as Heq.
      eapply getValueViaLabelFromValuels_getOperandValue_sim; eauto.
    subst. 
    eapply IHps2 with (RVs:=g2) in H4; eauto.
      congruence.

      destruct Hin as [ps3 Hin]. subst.
      exists (ps3++[insn_phi i0 l2]).
      simpl_env. auto.
Qed.

Lemma switchToNewBasicBlock_sim : forall
  (f : fdef) l2 (lc : GVMap) (t : list atom) l1 ps1 cs1 tmn1 id0 cst0
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs id0 cst0 lc t)
  (HuniqF : uniqFdef f)
  (ps2 : phinodes) (cs2 : cmds) (tmn2 : terminator)
  (Hsucc : In l2 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (block_intro l2 ps2 cs2 tmn2))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block f (block_intro l1 ps1 cs1 tmn1))
  lc0 lc0'
  (H8 : wf_phinodes f (block_intro l2 ps2 cs2 tmn2) ps2) 
  (Hget : switchToNewBasicBlock (block_intro l2 ps2 cs2 tmn2) 
    (block_intro l1 ps1 cs1 tmn1) lc = ret lc0)
  (Hget' : switchToNewBasicBlock 
    (csubst_block id0 cst0 (block_intro l2 ps2 cs2 tmn2))
    (csubst_block id0 cst0 (block_intro l1 ps1 cs1 tmn1)) lc = ret lc0'),
  lc0 = lc0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in *.
  inv_mbind'. app_inv. symmetry_ctx.
  assert (g0 = g) as EQ.
    eapply getIncomingValuesForBlockFromPHINodes_sim; eauto.
      exists nil. auto.
  subst. auto.
Qed.

Definition related_ECs id0 cst0 (f1:fdef) (ec1 ec2:ExecutionContext) : Prop :=
let '(mkEC b1 cs1 tmn1 lc1) := ec1 in
let '(mkEC b2 cs2 tmn2 lc2) := ec2 in
isReachableFromEntry f1 b1 /\
blockInFdefB b1 f1 = true /\
lc1 = lc2 /\
csubst_block id0 cst0 b1 = b2 /\
List.map (csubst_cmd id0 cst0) cs1 = cs2 /\
match cs1 with
| nil => 
    match inscope_of_tmn f1 b1 tmn1 with
    | Some ids => wf_defs id0 cst0 lc1 ids
    | None => False
    end
| c1::_ =>
    match inscope_of_cmd f1 b1 c1 with
    | Some ids => wf_defs id0 cst0 lc1 ids
    | None => False
    end
end /\
(exists l1, exists ps1, exists cs1', exists ps2, exists cs2',
b1 = block_intro l1 ps1 (cs1'++cs1) tmn1 /\
b2 = block_intro l1 ps2 (cs2'++cs2) tmn2).

Lemma subst_block__lookupAL_genLabel2Block_block : forall 
    id0 v0 l0 bs b b',
  lookupAL _ (genLabel2Block_blocks bs) l0 = Some b ->
  lookupAL _ (genLabel2Block_blocks (List.map (subst_block id0 v0) bs)) l0 
    = Some b' ->
  subst_block id0 v0 b = b'.
Proof.
  induction bs; simpl; intros.
    congruence.   

    destruct a. simpl in *.
    destruct (l0 == l1); subst; eauto.
      inv H. inv H0. auto.
Qed.

Lemma subst_fdef__lookupBlockViaLabelFromFdef : forall 
    id0 v0 F l0 b b',
  lookupBlockViaLabelFromFdef F l0 = Some b ->
  lookupBlockViaLabelFromFdef (subst_fdef id0 v0 F) l0 = Some b' ->
  subst_block id0 v0 b = b'.
Proof.
  destruct F. simpl in *. intros. 
  eauto using subst_block__lookupAL_genLabel2Block_block.
Qed.

Lemma subst_getCmdID : forall id0 v0 c1,
  getCmdID (subst_cmd id0 v0 c1) = getCmdID c1.
Proof.
  destruct c1; simpl; auto.
Qed.

Lemma bisimulation_cmd_updated_case : forall
  (F2 F1 : fdef) (B2 : block) (lc2 : GVMap) (gv : GenericValue)
  (cs2 : list cmd) (tmn2 : terminator)
  id1 id2 c2 id0 cst0 B1 c1 cs1 tmn1 lc1
  (Hid2 : Some id2 = getCmdID c2)
  (Hid1 : Some id1 = getCmdID c1)
  (Hwfgv : wf_GVs id0 cst0 id2 gv)
  (HwfF1 : wf_fdef F1)
  (HcInF1 : const_in_fdef id0 cst0 F1)
  (Htrans : csubst_fdef id0 cst0 F1 = F2)
  (Hrel : related_ECs id0 cst0 F1
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
  related_ECs id0 cst0 F1
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
    [Hreach1 [HBinF1 [Heq1 [Hbtrans [Hcstrans [Hinscope1
      [l3 [ps1 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]]]; subst.
  inv Hcstrans. 
  unfold csubst_cmd in Hid2. rewrite subst_getCmdID in Hid2. 
  trans_eq.
  remember (inscope_of_cmd F1 (block_intro l3 ps1 (cs1' ++ c1 :: cs1) tmn1) c1) 
    as R1. 
  assert (uniqFdef F1) as HuniqF1. auto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      assert (Hid1':=Hid1).
      symmetry in Hid1.
      apply getCmdLoc_getCmdID in Hid1.
      subst.
      destruct cs1; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c1) (getCmdsLocs cs1')) as Hnotin.
          eapply wf_fdef__uniq_block with (f:=F1) in HwfF1; eauto.        
          simpl in HwfF1.
          apply NoDup_inv in HwfF1.
          destruct HwfF1 as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c1 (cs1' ++ [c1])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_fdef__wf_cmd with (c:=c1) in Hwfc; 
          eauto.
        rewrite <- Hid1' in J2.
        eapply wf_defs_updateAddAL; eauto.
        
      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs1' ++ [c1] ++ [c] ++ cs1))) as Hnodup.
          eapply wf_fdef__uniq_block with (f:=F1) in HwfF1; eauto.        
          simpl in HwfF1.
          apply NoDup_inv in HwfF1.
          destruct HwfF1 as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c1 (cs1' ++ [c1] ++ [c] ++ cs1)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_fdef__wf_cmd with (c:=c1) in Hwfc; 
          eauto.
        rewrite <- Hid1' in J2.
        eapply wf_defs_updateAddAL; eauto.

  inv Heq3. rewrite List.map_app in H1. simpl in H1.
  apply app_inv_tail in H1. subst.
  exists l3. exists ps1. exists (cs1'++[c1]). 
  exists (List.map (subst_phi id0 (value_const cst0)) ps1). 
  exists (List.map (csubst_cmd id0 cst0) (cs1'++[c1])). 
  simpl. repeat rewrite List.map_app. simpl_env. auto.
Qed.

Lemma BOP__wf_gvs : forall
  (id0 : id) (cst0 : const) (F1 : fdef) (v : value) (v0 : value)
  (HcInF1 : const_in_fdef id0 cst0 F1)
  (id1 : id) (bop0 : bop) gvs3 lc
  (H11 : BOP lc bop0 v v0 = ret gvs3)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_bop id1 bop0 v v0 :: cs1) tmn1)
           F1 = true),
  wf_GVs id0 cst0 id1 gvs3.
Proof.
  intros. intro J; subst. 
  destruct F1 as [bs1]. 
  assert (lookupInsnViaIDFromBlocks bs1 id1 = 
    Some (insn_cmd (insn_bop id1 bop0 v v0))) as Hlk.
    inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  simpl in HcInF1.
  rewrite Hlk in HcInF1.
  destruct v; try solve [contradict HcInF1; auto].
  destruct v0; try solve [contradict HcInF1; auto].
  unfold BOP in H11. simpl in H11. app_inv.
  rewrite HcInF1; auto.
Qed.

Lemma ICMP__wf_gvs : forall
  (id0 : id) (cst0 : const) (F1 : fdef) (v : value) (v0 : value)
  (HcInF1 : const_in_fdef id0 cst0 F1)
  (id1 : id) cond0 gvs3 lc
  (H11 : ICMP lc cond0 v v0 = ret gvs3)
  (Huniq : uniqFdef F1) l3 ps1 cs1' cs1 tmn1
  (Hin : blockInFdefB
           (block_intro l3 ps1 (cs1' ++ insn_icmp id1 cond0 v v0 :: cs1) tmn1)
           F1 = true),
  wf_GVs id0 cst0 id1 gvs3.
Proof.
  intros. intro J; subst. 
  destruct F1 as [bs1]. 
  assert (lookupInsnViaIDFromBlocks bs1 id1 = 
    Some (insn_cmd (insn_icmp id1 cond0 v v0))) as Hlk.
    inv Huniq.
    eapply InBlocksB__lookupInsnViaIDFromBlocks; eauto.
  simpl in HcInF1.
  rewrite Hlk in HcInF1.
  destruct v; try solve [contradict HcInF1; auto].
  destruct v0; try solve [contradict HcInF1; auto].
  unfold ICMP in H11. simpl in H11. app_inv.
  rewrite HcInF1; auto.
Qed.

Ltac destruct_ctx :=
match goal with
| Hrel : related_ECs _ _ _ ?S1 _,
  HsInsn1 : sInsn _ ?S1 _ _ |- _ =>
  destruct S1 as [b1 cs1 tmn1 lc1];
  assert (J:=Hrel); simpl in J;
  destruct J as
    [Hreach1 [HBinF1 [Heq1 [Hbtrans [Hcstrans [Hinscope1
      [l3 [ps1 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]]]; subst;
  match goal with
  | Hcstrans : List.map _ _ = _ :: _ |- _ =>
    destruct cs1; inv Hcstrans;
    match goal with
    | H1 : csubst_cmd _ _ ?c = _ |- _ => 
      destruct c; inv H1
    end
  | Heq3 : csubst_block _ _ _ = _ |- _ =>
    apply map_eq_nil in Hcstrans; auto; subst;
    inv Heq3;
    match goal with
    | H5 : subst_tmn _ _ ?tmn1 = _ |- _ =>
      destruct tmn1; inv H5
    end
  end;
  inv HsInsn1
end.

Ltac bisimulation_cmd :=
match goal with
| H : _ _ _  (?v {[value_const ?cst0 // ?id0]})
        (?v0 {[value_const ?cst0 // ?id0]}) = ret ?gvs3,
  H11 : _ _ _ ?v ?v0 = ret ?gvs0,
  Hrel : related_ECs _ _ _ _ _ |-
  context [_ ?id1 _ ?v ?v0] =>
  assert (wf_GVs id0 cst0 id1 gvs0) as J;
    try solve [eapply BOP__wf_gvs; eauto | eapply ICMP__wf_gvs; eauto];
  assert (gvs0 = gvs3) as Heq;
    (unfold ICMP, BOP in *;
    inv_mbind'; inv_mfalse; app_inv; symmetry_ctx;
    match goal with
    | HeqR : getOperandValue ?v _ = ret _, 
      HeqR0 : getOperandValue ?v0 _ = ret _ |- _ => 
      eapply getOperandValue_inCmdOps_sim in HeqR; try (eauto || simpl; auto);
      eapply getOperandValue_inCmdOps_sim in HeqR0; try (eauto || simpl; auto);
      subst; auto
    end);
  split; try solve [auto |
      eapply bisimulation_cmd_updated_case in Hrel; try solve [simpl; eauto]]
end.
 
Lemma bisimulation : forall id0 cst0 F1 F2 S1 S2 S1' S2' tr1 tr2,
  wf_fdef F1 ->
  const_in_fdef id0 cst0 F1 ->
  csubst_fdef id0 cst0 F1 = F2 ->
  related_ECs id0 cst0 F1 S1 S2 ->
  sInsn F1 S1 S1' tr1 ->
  sInsn F2 S2 S2' tr2 ->
  related_ECs id0 cst0 F1 S1' S2' /\ tr1 = tr2.
Proof.
  intros id0 cst0 F1 F2 S1 S2 S1' S2' tr1 tr2 HwfF1 HcInF1 Htrans Hrel HsInsn1
    HsInsn2.
  (sInsn_cases (destruct HsInsn2) Case); destruct_ctx.
Focus.
Case "sBranch".
  remember (inscope_of_tmn F1
                  (block_intro l3 ps1 (cs1' ++ nil) (insn_br bid v l1 l2))
                  (insn_br bid v l1 l2)) as R1. 
  destruct R1; tinv Hinscope1.
  assert (c0 = c) as Heq.
    eapply getOperandValue_inTmnOperans_sim; try solve [eauto | simpl; auto].
  subst.
  assert (csubst_block id0 cst0 (block_intro l'0 ps'0 cs'0 tmn'0) 
    = block_intro l' ps' cs' tmn') as Hbtrans.
    destruct (isGVZero c); 
      eapply subst_fdef__lookupBlockViaLabelFromFdef; eauto.
  inv Hbtrans.
  assert (isReachableFromEntry F1 (block_intro l' ps'0 cs'0 tmn'0) /\
    In l' (successors_terminator (insn_br bid v l1 l2)) /\
    blockInFdefB (block_intro l' ps'0 cs'0 tmn'0) F1 = true /\
    wf_phinodes F1 (block_intro l' ps'0 cs'0 tmn'0) ps'0) as J.
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
  assert (lc'0 = lc') as Heq.
    assert (HwfB := HBinF1).
    eapply wf_fdef__blockInFdefB__wf_block in HwfB; eauto.
    simpl_env in *.
    eapply switchToNewBasicBlock_sim in H14; eauto.
  subst.
  repeat split; auto.
      clear - HeqR1 H13 H14 Hinscope1 HBinF1 HwfF1 HcInF1.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'0; rewrite <- HeqR1; auto.

      exists l'. exists ps'0. exists nil. 
      exists (List.map (subst_phi id0 (value_const cst0)) ps'0). exists nil.
      auto.
Unfocus.

Focus.
Case "sBranch_uncond". 
  remember (inscope_of_tmn F1
                  (block_intro l3 ps1 (cs1' ++ nil) (insn_br_uncond bid l0))
                  (insn_br_uncond bid l0)) as R1. 
  destruct R1; tinv Hinscope1.
  assert (csubst_block id0 cst0 (block_intro l'0 ps'0 cs'0 tmn'0) 
    = block_intro l' ps' cs' tmn') as Hbtrans.
    eapply subst_fdef__lookupBlockViaLabelFromFdef; eauto.
  inv Hbtrans.
  assert (isReachableFromEntry F1 (block_intro l' ps'0 cs'0 tmn'0) /\
    In l' (successors_terminator (insn_br_uncond bid l0)) /\
    blockInFdefB (block_intro l' ps'0 cs'0 tmn'0) F1 = true /\
    wf_phinodes F1 (block_intro l' ps'0 cs'0 tmn'0) ps'0) as J.
    symmetry in H9.
    assert (J:=H9).
    apply lookupBlockViaLabelFromFdef_inv in J; eauto.
    destruct J as [J H9']; subst.
    symmetry in H9; eapply wf_fdef__lookup__wf_block in H9; eauto.
    (repeat split; simpl; auto); try solve
        [eapply reachable_successors; (eauto || simpl; auto) |
         inv H9; auto].
  destruct J as [Hreach' [Hsucc' [HBinF1' HwfPNs]]].
  assert (lc'0 = lc') as Heq.
    assert (HwfB := HBinF1).
    eapply wf_fdef__blockInFdefB__wf_block in HwfB; eauto.
    simpl_env in *.
    eapply switchToNewBasicBlock_sim in H10; eauto.
  subst.
  repeat split; auto.
      clear - HeqR1 H9 H10 Hinscope1 HBinF1 HwfF1 HcInF1.
      eapply inscope_of_tmn_br_uncond in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'0; rewrite <- HeqR1; auto.

      exists l'. exists ps'0. exists nil. 
      exists (List.map (subst_phi id0 (value_const cst0)) ps'0). exists nil.
      auto.
Unfocus.

Case "sBop". abstract bisimulation_cmd.
Case "sIcmp". abstract bisimulation_cmd.
Qed.

Lemma related_finalstate_is_stuck : forall id0 cst0 F1 F2 S1 S2 S2' tr2
  (Hrel : related_ECs id0 cst0 F1 S1 S2)
  (Hfinal1 : s_isFinialState S1 = true)
  (HsInsn2 : sInsn F2 S2 S2' tr2),
  False.
Proof.
  intros.
  destruct S1. destruct CurCmds0; tinv Hfinal1. 
  destruct Terminator0; inv Hfinal1. destruct S2. 
  destruct Hrel as 
    [J1 [J2 [J3 [J4 [J5 [J6 [l1 [ps1 [cs1' [ps2 [cs2' [J7 J8]]]]]]]]]]]]; 
    subst.
  inv J8. inv HsInsn2.
Qed.

Lemma backsimulation : forall id0 cst0 F1 F2 S1 S2 S2' tr2,
  wf_fdef F1 ->
  const_in_fdef id0 cst0 F1 ->
  csubst_fdef id0 cst0 F1 = F2 ->
  related_ECs id0 cst0 F1 S1 S2 ->
  OpsemPP.wf_ExecutionContext F1 S1 -> 
  sInsn F2 S2 S2' tr2 ->
  exists S1', exists tr1,
    sInsn F1 S1 S1' tr1 /\ related_ECs id0 cst0 F1 S1' S2' /\ tr1 = tr2.
Proof.
  intros id0 cst0 F1 F2 S1 S2 S2' tr2 HwfF1 HcInF1 Htrans Hrel HwfEC1 HsInsn2.
  apply OpsemPP.progress in HwfEC1; auto.
  destruct HwfEC1 as [Hfinal1 | [S1' [tr1 HsInsn1]]].
    eapply related_finalstate_is_stuck in Hrel; eauto. inv Hrel.
    exists S1'. exists tr1. split; eauto using bisimulation.
Qed.
 
(************** More props **************************************)

Lemma getCmdLoc_subst_cmd : forall id1 id2 c, 
  getCmdLoc (subst.subst_cmd id1 id2 c) = getCmdLoc c.
Proof. destruct c; simpl; intros; auto. Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
