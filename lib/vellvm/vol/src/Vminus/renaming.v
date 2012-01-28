Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vminus.
Require Import Lattice.
Import AtomSet.

Definition rename_id (id1:id) (id2:id) (id0:id) : id :=
if id_dec id0 id1 then id2 else id0.

Definition rename_value (id1:id) (id2:id) (v:value) : value :=
match v with
| value_id id0 => value_id (rename_id id1 id2 id0)
| _ => v
end.

Definition rename_cmd (id1:id) (id2:id) (c:cmd) : cmd :=
match c with
| insn_bop id0 bop0 v1 v2 => 
    insn_bop (rename_id id1 id2 id0) bop0 
      (rename_value id1 id2 v1) (rename_value id1 id2 v2)
| insn_icmp id0 cond0 v1 v2 => 
    insn_icmp (rename_id id1 id2 id0) cond0
      (rename_value id1 id2 v1) (rename_value id1 id2 v2)
end.

Definition rename_tmn (id1:id) (id2:id) (tmn:terminator) : terminator :=
match tmn with
| insn_br id0 v0 l1 l2 => 
    insn_br (rename_id id1 id2 id0) (rename_value id1 id2 v0) l1 l2
| insn_return id0 v0 => 
    insn_return (rename_id id1 id2 id0) (rename_value id1 id2 v0) 
| insn_br_uncond id0 l1 => insn_br_uncond (rename_id id1 id2 id0) l1
end.

Fixpoint rename_list_value_l (id1:id) (id2:id) (l0:list_value_l)
  : list_value_l :=
match l0 with
| Nil_list_value_l => Nil_list_value_l
| Cons_list_value_l v0 l0 tl => 
   Cons_list_value_l (rename_value id1 id2 v0) l0 
     (rename_list_value_l id1 id2 tl)
end.

Definition rename_phi (id1:id) (id2:id) (pn:phinode) : phinode :=
match pn with
| insn_phi id0 vls => 
    insn_phi (rename_id id1 id2 id0) (rename_list_value_l id1 id2 vls) 
end.

Definition rename_insn (id1:id) (id2:id) (instr:insn) : insn :=
match instr with
| insn_phinode pn => insn_phinode (rename_phi id1 id2 pn)
| insn_cmd c => insn_cmd (rename_cmd id1 id2 c)
| insn_terminator tmn => insn_terminator (rename_tmn id1 id2 tmn)
end.

Definition rename_block (id1:id) (id2:id) (b:block) : block := 
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro l0 (List.map (rename_phi id1 id2) ps0) 
    (List.map (rename_cmd id1 id2) cs0) (rename_tmn id1 id2 tmn0) 
end.

Definition rename_fdef (id1:id) (id2:id) (f:fdef) : fdef := 
match f with
| fdef_intro bs => fdef_intro (List.map (rename_block id1 id2) bs) 
end.

(************** Preserving wellformedness **************************************)

Definition wf_renaming (f:fdef) (id1 id2:id) : Prop :=
  id1 <> id2 /\
  (let '(fdef_intro bs):=f in ~ In id2 (getBlocksLocs bs)).

Fixpoint rename_list_id (id1 id2: id) (l0:list_id) : list_id :=
match l0 with
| Nil_list_id => Nil_list_id
| Cons_list_id id0 tl => 
    Cons_list_id (rename_id id1 id2 id0) (rename_list_id id1 id2 tl)
end.

Lemma rename_values2ids : forall id1 id2 l0 id_list0,
  values2ids (list_prj1 value l (unmake_list_value_l l0)) =
    unmake_list_id id_list0 ->
  values2ids
     (list_prj1 value l
        (unmake_list_value_l (rename_list_value_l id1 id2 l0))) =
    unmake_list_id (rename_list_id id1 id2 id_list0).
Proof.
  induction l0; simpl; intros.
    destruct id_list0; inv H; auto.

    destruct v; simpl in *; auto.
      unfold rename_id.
      destruct (id_dec i0 id1); subst; destruct id_list0; inv H; 
        simpl; unfold rename_id.
        rewrite <- IHl0; auto.
        destruct (id_dec i0 i0); try congruence; auto.

        destruct (id_dec i1 id1); simpl; try congruence; f_equal; auto.
Qed.

Hint Resolve rename_values2ids : ssa_rename.

Lemma rename_getPhiNodeOperands : forall id1 id2 p id_list0,
  getPhiNodeOperands p = unmake_list_id id_list0 ->
  getPhiNodeOperands (rename_phi id1 id2 p) =
    unmake_list_id (rename_list_id id1 id2 id_list0).
Proof.
  destruct p; simpl; intros; auto with ssa_rename.
Qed.

Lemma rename_getCmdOperands_helper : forall id1 id2 v v0 id_list0
  (H : getValueIDs v ++ getValueIDs v0 = unmake_list_id id_list0),
  getValueIDs (rename_value id1 id2 v)++ getValueIDs (rename_value id1 id2 v0) =
    unmake_list_id (rename_list_id id1 id2 id_list0).
Proof.
  intros.
  destruct v; simpl in *.
    destruct id_list0; inv H.
    destruct v0; simpl in *.
      destruct id_list0; inv H2.
      destruct id_list0; inv H1; simpl. unfold rename_id.
      destruct (id_dec i1 id1); destruct (id_dec i2 id1); subst; auto. 
  
      destruct id_list0; inv H2. unfold rename_id.
      destruct (id_dec i1 id1); subst; auto.
    destruct v0; simpl in *.
      destruct id_list0; inv H.
      destruct id_list0; inv H2; simpl. unfold rename_id.
      destruct (id_dec i1 id1); subst; auto. 
  
      destruct id_list0; inv H; auto.
Qed.

Hint Resolve rename_getCmdOperands_helper: ssa_rename.

Lemma rename_getCmdOperands : forall id1 id2 c id_list0,
 getCmdOperands c = unmake_list_id id_list0 ->
 getCmdOperands (rename_cmd id1 id2 c) =
   unmake_list_id (rename_list_id id1 id2 id_list0).
Proof.
  destruct c; simpl; intros; auto with ssa_rename.
Qed.

Lemma rename_getTerminatorOperands : forall id1 id2 t id_list0,
 getTerminatorOperands t = unmake_list_id id_list0 ->
 getTerminatorOperands (rename_tmn id1 id2 t) =
   unmake_list_id (rename_list_id id1 id2 id_list0).
Proof.
  destruct t; simpl; intros; try solve [destruct id_list0; inv H; simpl; auto].
    destruct v; simpl in *.
      destruct id_list0; tinv H.
      destruct id_list0; inv H; eauto.

      destruct id_list0; inv H. simpl. auto.

    destruct v; simpl in *.
      destruct id_list0; inv H; auto.
      destruct id_list0; inv H2; simpl. unfold rename_id.
      destruct (id_dec i2 id1); subst; auto. 
  
      destruct id_list0; inv H; auto.
Qed.

Hint Resolve rename_getCmdOperands rename_getPhiNodeOperands
  rename_getTerminatorOperands: ssa_rename.

Lemma rename_getInsnOperands : forall id1 id2 instr id_list0,
  getInsnOperands instr = unmake_list_id id_list0 ->
  getInsnOperands (rename_insn id1 id2 instr) =
    unmake_list_id (rename_list_id id1 id2 id_list0).
Proof.
  destruct instr; simpl; intros; auto with ssa_rename.
Qed.

Hint Resolve rename_getInsnOperands: ssa_rename.

Lemma rename_In_values2ids : forall id1 id2 i0 l0 
  (H2 : ListSet.set_In i0 
    (values2ids (list_prj1 value l (unmake_list_value_l l0)))),
  ListSet.set_In (rename_id id1 id2 i0)
    (values2ids
      (list_prj1 value l
        (unmake_list_value_l (rename_list_value_l id1 id2 l0)))).
Proof.
  induction l0; simpl; intros; auto.
    destruct v; simpl in *; auto. 
    unfold rename_id.
    destruct H2 as [H2 | H2]; subst. 
      destruct (id_dec i0 id1); try congruence; simpl; auto.
      destruct (id_dec i1 id1); subst; simpl; auto.
Qed.     

Hint Resolve rename_In_values2ids : ssa_rename.

Lemma rename_In_getPhiNodeOperands : forall id1 id2 i0 p
  (H2 : ListSet.set_In i0 (getPhiNodeOperands p)),
  ListSet.set_In (rename_id id1 id2 i0) 
    (getPhiNodeOperands (rename_phi id1 id2 p)).
Proof.
  destruct p; simpl; intros; auto with ssa_rename.
Qed.

Lemma rename_In_getCmdOperands_helper : forall id1 id2 v v0 i3
  (H2 : ListSet.set_In i3 (getValueIDs v ++ getValueIDs v0)),
  ListSet.set_In (rename_id id1 id2 i3) 
    (getValueIDs (rename_value id1 id2 v) ++ 
     getValueIDs (rename_value id1 id2 v0)).
Proof.
  intros.
  destruct v; simpl in *; unfold rename_value, rename_id.
    destruct H2 as [H2 | H2]; subst.
      destruct v0; simpl in *; 
        destruct (id_dec i3 id1); try congruence; simpl; auto.
  
      destruct v0; simpl in *; try solve [inversion H2].
        destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
        destruct (id_dec i3 id1); destruct (id_dec i0 id1); simpl; auto.

    destruct v0; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      destruct (id_dec i3 id1); try congruence; simpl; auto.
Qed.

Hint Resolve rename_In_getCmdOperands_helper: ssa_rename.

Lemma rename_In_getCmdOperands : forall id1 id2 c i3
  (H2 : ListSet.set_In i3 (getCmdOperands c)),
  ListSet.set_In (rename_id id1 id2 i3) 
    (getCmdOperands (rename_cmd id1 id2 c)).
Proof.
  destruct c; simpl; intros; auto with ssa_rename.
Qed.

Lemma rename_In_getTerminatorOperands : forall id1 id2 t i3
  (H2 : ListSet.set_In i3 (getTerminatorOperands t)),
  ListSet.set_In (rename_id id1 id2 i3) 
    (getTerminatorOperands(rename_tmn id1 id2 t)).
Proof.
  destruct t; simpl; intros; auto.
    destruct v; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      unfold rename_id.
      destruct (id_dec i3 id2); try congruence; simpl; auto.
    destruct v; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      unfold rename_id.
      destruct (id_dec i3 id2); try congruence; simpl; auto.
Qed.

Hint Resolve rename_In_getCmdOperands rename_In_getPhiNodeOperands
  rename_In_getTerminatorOperands: ssa_rename.

Lemma rename_In_getInsnOperands : forall i0 id1 id2 instr 
  (H2 : ListSet.set_In i0 (getInsnOperands instr)),
  ListSet.set_In (rename_id id1 id2 i0)
     (getInsnOperands (rename_insn id1 id2 instr)).
Proof.
  destruct instr; simpl; auto with ssa_rename.
Qed.

Hint Resolve rename_In_getInsnOperands: ssa_rename.

Lemma rename_isPhiNode : forall instr id1 id2,
  isPhiNode instr = isPhiNode (rename_insn id1 id2 instr).
Proof.
  destruct instr; auto.
Qed.

Lemma rename_InBlocksB : forall id1 id2 b bs
  (Hin : InBlocksB b bs = true),
  InBlocksB (rename_block id1 id2 b) (List.map (rename_block id1 id2) bs) = true.
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

Hint Resolve rename_InBlocksB: ssa_rename.

Lemma rename_blockInFdefB : forall f id1 id2 b
  (Hin : blockInFdefB b f = true),
  blockInFdefB (rename_block id1 id2 b) (rename_fdef id1 id2 f) = true.
Proof.
  intros. destruct f. simpl in *.
  auto with ssa_rename.
Qed.

Hint Resolve rename_blockInFdefB: ssa_rename.

Lemma rename_InPhiNodesB : forall id1 id2 p ps, 
  InPhiNodesB p ps = true ->
  InPhiNodesB (rename_phi id1 id2 p) (List.map (rename_phi id1 id2) ps) = true.
Proof.
  induction ps; simpl; intros.
    congruence.
    apply orb_true_iff in H.
    apply orb_true_iff.
    destruct H as [H | H]; auto.
    apply phinodeEqB_inv in H; subst. 
    left. apply phinodeEqB_refl.
Qed.

Hint Resolve rename_InPhiNodesB: ssa_rename.

Lemma rename_phinodeInBlockB : forall id1 id2 p b
  (Hin : phinodeInBlockB p b = true),
  phinodeInBlockB (rename_phi id1 id2 p) (rename_block id1 id2 b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_rename.
Qed. 

Hint Resolve rename_phinodeInBlockB: ssa_rename.

Lemma rename_InCmdsB : forall id1 id2 c cs, 
  InCmdsB c cs = true ->
  InCmdsB (rename_cmd id1 id2 c) (List.map (rename_cmd id1 id2) cs) = true.
Proof.
  induction cs; simpl; intros.
    congruence.
    apply orb_true_iff in H.
    apply orb_true_iff.
    destruct H as [H | H]; auto.
    apply cmdEqB_inv in H; subst. 
    left. apply cmdEqB_refl.
Qed.

Hint Resolve rename_InCmdsB: ssa_rename.

Lemma rename_cmdInBlockB : forall id1 id2 c b
  (Hin : cmdInBlockB c b = true),
  cmdInBlockB (rename_cmd id1 id2 c) (rename_block id1 id2 b) = true.
Proof.
  destruct b. simpl. intro. auto with ssa_rename.
Qed. 

Hint Resolve rename_cmdInBlockB: ssa_rename.

Lemma rename_terminatorInBlockB : forall id1 id2 t b
  (Hin : terminatorInBlockB t b = true),
  terminatorInBlockB (rename_tmn id1 id2 t) (rename_block id1 id2 b) = true.
Proof.
  destruct b. simpl. intro. 
  apply terminatorEqB_inv in Hin. subst.
  apply terminatorEqB_refl.
Qed. 

Hint Resolve rename_terminatorInBlockB: ssa_rename.

Lemma rename_insnInFdefBlockB : forall f id1 id2 b instr
  (Hin : insnInFdefBlockB instr f b = true),
  insnInFdefBlockB (rename_insn id1 id2 instr) (rename_fdef id1 id2 f) 
    (rename_block id1 id2 b) = true.
Proof.
  unfold insnInFdefBlockB.
  intros.
  destruct instr; simpl;
    apply andb_true_iff in Hin; inv Hin;
    apply andb_true_iff; auto with ssa_rename.
Qed.

Hint Resolve rename_insnInFdefBlockB: ssa_rename.

Lemma rename_InGetPhiNodesIDs : forall id0 id1 id2 ps,
  In id0 (getPhiNodesIDs ps) ->
  In (rename_id id1 id2 id0) 
     (getPhiNodesIDs (List.map (rename_phi id1 id2) ps)).
Proof. 
  induction ps; simpl; intros; auto.
    destruct a. simpl in *.
    inv H; auto.
Qed.

Lemma rename_InGetCmdsLocs : forall id0 id1 id2 cs,
  In id0 (getCmdsLocs cs) ->
  In (rename_id id1 id2 id0) 
     (getCmdsLocs (List.map (rename_cmd id1 id2) cs)).
Proof. 
  induction cs; simpl; intros; auto.
    destruct a; simpl in *; inv H; auto.
Qed.

Lemma rename_InGetCmdsIDs : forall id0 id1 id2 cs,
  In id0 (getCmdsIDs cs) ->
  In (rename_id id1 id2 id0) 
     (getCmdsIDs (List.map (rename_cmd id1 id2) cs)).
Proof. 
  induction cs; simpl; intros; auto.
    destruct a; simpl in *; inv H; auto.
Qed.

Lemma rename_id_inv: forall id1 id2 i1 i0,
  i0 <> id2 -> i1 <> id2 ->
  rename_id id1 id2 i1 = rename_id id1 id2 i0 ->
  i1 = i0.
Proof.
  unfold rename_id.
  intros.
  destruct (id_dec i1 id1).
    destruct (id_dec i0 id1); subst; auto.
      congruence.
    destruct (id_dec i0 id1); subst; auto.
      congruence.
Qed.

Lemma rename_InGetPhiNodesIDs' : forall id0 id1 id2 ps,
  id2 <> id0 -> ~ In id2 (getPhiNodesIDs ps) ->
  In (rename_id id1 id2 id0) 
     (getPhiNodesIDs (List.map (rename_phi id1 id2) ps)) ->
  In id0 (getPhiNodesIDs ps).
Proof. 
  induction ps; simpl; intros; auto.
    destruct a. simpl in *.
    inv H1.
      apply rename_id_inv in H2; auto.
      apply IHps in H2; auto.
Qed.

Lemma rename_InGetCmdsLocs' : forall id0 id1 id2 cs,
  id2 <> id0 -> ~ In id2 (getCmdsLocs cs) ->
  In (rename_id id1 id2 id0) 
     (getCmdsLocs (List.map (rename_cmd id1 id2) cs)) ->
  In id0 (getCmdsLocs cs).
Proof. 
  induction cs; simpl; intros; auto.
    destruct a; simpl in *;
      inv H1; try solve [apply rename_id_inv in H2; auto |
                         apply IHcs in H2; auto].
Qed.

Lemma rename_InGetCmdsIDs' : forall id0 id1 id2 cs,
  id2 <> id0 -> ~ In id2 (getCmdsLocs cs) ->
  In (rename_id id1 id2 id0) 
     (getCmdsIDs (List.map (rename_cmd id1 id2) cs)) ->
  In id0 (getCmdsIDs cs).
Proof. 
  induction cs; simpl; intros; auto.
    destruct a; simpl in *;
      inv H1; try solve [apply rename_id_inv in H2; auto |
                         apply IHcs in H2; auto].
Qed.

Lemma rename_lookupBlockViaIDFromBlocks : forall id5 id1 id2 bs b,
  id2 <> id1 -> ~ In id2 (getBlocksLocs bs) ->
  lookupBlockViaIDFromBlocks bs id5 = ret b ->
  lookupBlockViaIDFromBlocks (List.map (rename_block id1 id2) bs) 
    (rename_id id1 id2 id5) = ret (rename_block id1 id2 b).
Proof.
  intros.
  assert (id2 <> id5) as G.
    apply lookupBlockViaIDFromBlocks__InGetBlocksLocs in H1.
    destruct (id_dec id2 id5); subst; auto.
  induction bs; simpl in *; intros.
    congruence.

    destruct a. simpl in *.
    destruct (in_dec eq_dec id5 (getPhiNodesIDs p ++ getCmdsIDs c)).
      inv H1.
      destruct (in_dec eq_dec (rename_id id1 id2 id5)
         (getPhiNodesIDs (List.map (rename_phi id1 id2) p) ++
          getCmdsIDs (List.map (rename_cmd id1 id2) c))); auto.
      contradict n.
      apply in_or_app. apply in_app_or in i0.
      destruct i0 as [i0 | i0].
        left. apply rename_InGetPhiNodesIDs; auto.
        right. apply rename_InGetCmdsIDs; auto.

      destruct (in_dec eq_dec (rename_id id1 id2 id5)
         (getPhiNodesIDs (List.map (rename_phi id1 id2) p) ++
          getCmdsIDs (List.map (rename_cmd id1 id2) c))).
        contradict n.
        apply in_or_app. 
        apply in_app_or in i0.
        destruct i0 as [i0 | i0].
          apply rename_InGetPhiNodesIDs' in i0; auto.  
            intro J. apply H0. apply in_or_app. left. apply in_or_app. auto.
          apply rename_InGetCmdsIDs' in i0; auto.  
            intro J. apply H0. apply in_or_app. left. apply in_or_app. right.
            apply in_or_app. auto.
          
        apply IHbs; auto.
          intro J. apply H0. apply in_or_app. right. auto.
Qed.

Hint Resolve rename_lookupBlockViaIDFromBlocks : ssa_rename.

Lemma rename_lookupBlockViaIDFromFdef : forall f id5 b id1 id2
  (HwfR:wf_renaming f id1 id2),
  lookupBlockViaIDFromFdef f id5 = ret b ->
  lookupBlockViaIDFromFdef (rename_fdef id1 id2 f) (rename_id id1 id2 id5) = 
    ret (rename_block id1 id2 b).
Proof.
  destruct f. simpl; intros. destruct HwfR. auto with ssa_rename.
Qed.

Hint Resolve rename_lookupBlockViaIDFromFdef: ssa_rename.

Lemma rename_insnDominates : forall i0 instr id1 id2 b, 
 NoDup (getBlockLocs b) ->
 insnInBlockB instr b = true ->
 insnDominates i0 instr b ->
 insnDominates (rename_id id1 id2 i0) (rename_insn id1 id2 instr) 
   (rename_block id1 id2 b).
Proof.
 intros i0 instr id1 id2 b Hnodup HiInB. destruct b. simpl.
 destruct instr; simpl; intro J; auto.
   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]]; 
     subst.
     left.
     exists (List.map (rename_phi id1 id2) ps1).
     exists (rename_phi id1 id2 p1).
     exists (List.map (rename_phi id1 id2) ps2).
     repeat rewrite List.map_app. 
     destruct p1. simpl. auto. 

     right.
     exists (List.map (rename_cmd id1 id2) cs1).
     exists (rename_cmd id1 id2 c1).
     exists (List.map (rename_cmd id1 id2) cs2).
     exists (List.map (rename_cmd id1 id2) cs3).
     simpl_env.
     repeat rewrite List.map_app. 
     destruct c1; simpl in *; inv J2; auto. 

   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq]; 
     subst; split; auto.
     left.
     exists (List.map (rename_cmd id1 id2) cs1).
     exists (rename_cmd id1 id2 c1).
     exists (List.map (rename_cmd id1 id2) cs2).
     simpl_env.
     repeat rewrite List.map_app. 
     destruct c1; simpl in *; inv J2; auto. 

     right.
     exists (List.map (rename_phi id1 id2) ps1).
     exists (rename_phi id1 id2 p1).
     exists (List.map (rename_phi id1 id2) ps2).
     repeat rewrite List.map_app. 
     destruct p1. simpl. auto. 
Qed.

Lemma rename_successors_blocks : forall id1 id2 bs,
  successors_blocks bs = successors_blocks (List.map (rename_block id1 id2) bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl.
    rewrite IHbs.
    destruct t; auto.
Qed.

Hint Resolve rename_successors_blocks: ssa_rename.

Lemma rename_successors : forall f id1 id2,
  successors f = successors (rename_fdef id1 id2 f).
Proof.
  intros. destruct f. simpl. auto with ssa_rename.
Qed.

Lemma rename_bound_blocks : forall id1 id2 bs,
  bound_blocks bs = bound_blocks (List.map (rename_block id1 id2) bs).
Proof.
  induction bs; simpl; auto.
    destruct a; simpl. rewrite IHbs. auto.
Qed.

Hint Resolve rename_bound_blocks.

Lemma rename_vertexes_fdef: forall f id1 id2,
  vertexes_fdef f = vertexes_fdef (rename_fdef id1 id2 f).
Proof.
  unfold vertexes_fdef.
  destruct f. simpl. intros.
  rewrite <- rename_bound_blocks. auto.
Qed.

Lemma rename_arcs_fdef: forall f id1 id2,
  arcs_fdef f = arcs_fdef (rename_fdef id1 id2 f).
Proof.
  unfold arcs_fdef.
  destruct f. simpl. intros.
  rewrite <- rename_successors_blocks. auto.
Qed.

Lemma rename_getEntryBlock : forall f id1 id2 b
  (Hentry : getEntryBlock f = Some b),
  getEntryBlock (rename_fdef id1 id2 f) = Some (rename_block id1 id2 b).
Proof.
  intros. destruct f. simpl in *.
  destruct b0; inv Hentry; auto.
Qed.

Lemma rename_getEntryBlock_None : forall f id1 id2
  (Hentry : getEntryBlock f = None),
  getEntryBlock (rename_fdef id1 id2 f) = None.
Proof.
  intros. destruct f. simpl in *.
  destruct b; inv Hentry; auto.
Qed.

Lemma rename_reachable : forall f id1 id2,
  reachable f = reachable (rename_fdef id1 id2 f).
Proof.
  intros.
  unfold reachable.
  case_eq (getEntryBlock f).
    intros b Hentry. 
    apply rename_getEntryBlock with (id1:=id1)(id2:=id2) in Hentry; eauto.
    rewrite Hentry.
    destruct b. simpl. 
    rewrite <- rename_vertexes_fdef.
    rewrite <- rename_arcs_fdef. auto.

    intro Hentry.
    apply rename_getEntryBlock_None with (id1:=id1)(id2:=id2) in Hentry; eauto.
    rewrite Hentry. auto.
Qed.

Lemma rename_isReachableFromEntry : forall f b id1 id2,
  isReachableFromEntry f b = 
    isReachableFromEntry (rename_fdef id1 id2 f) (rename_block id1 id2 b).
Proof.
  unfold isReachableFromEntry. intros.
  destruct b. simpl. rewrite <- rename_reachable; auto.
Qed.

Lemma rename_blockStrictDominates : forall f b1 b2 id1 id2,
  blockStrictDominates f b1 b2 <->
    blockStrictDominates (rename_fdef id1 id2 f) (rename_block id1 id2 b1)
      (rename_block id1 id2 b2).
Proof.
  intros.
  unfold blockStrictDominates. destruct b1. destruct b2. simpl.
  unfold dom_analyze. destruct f. simpl.
  rewrite <- rename_successors_blocks.
  remember (entry_dom b) as R1.
  remember (entry_dom (List.map (rename_block id1 id2) b)) as R2.
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

Lemma rename_blockDominates : forall f b1 b2 id1 id2,
  blockDominates f b1 b2 <->
    blockDominates (rename_fdef id1 id2 f) (rename_block id1 id2 b1)
      (rename_block id1 id2 b2).
Proof.
  intros.
  unfold blockDominates. destruct b1. destruct b2. simpl.
  unfold dom_analyze. destruct f. simpl.
  rewrite <- rename_successors_blocks.
  remember (entry_dom b) as R1.
  remember (entry_dom (List.map (rename_block id1 id2) b)) as R2.
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

Lemma rename_wf_operand : forall instr id1 id2 f b i0
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f)
  (H1 : wf_operand f b instr i0) (HwfR:wf_renaming f id1 id2),
   wf_operand (rename_fdef id1 id2 f) (rename_block id1 id2 b)
     (rename_insn id1 id2 instr) (rename_id id1 id2 i0).
Proof.
  intros.
  inv H1.
  apply rename_In_getInsnOperands with (id1:=id1)(id2:=id2) in H2; auto.
  rewrite rename_isPhiNode with (id1:=id1)(id2:=id2) in H4; auto.
  eapply wf_operand_intro; try solve [eauto with ssa_rename].   
    rewrite <- rename_blockStrictDominates.
    rewrite <- rename_isReachableFromEntry; auto.
    destruct H5 as [H5 | [H5 | H5]]; auto.
    left.
    apply rename_insnDominates; eauto using insnInFdefBlockB__insnInBlockB.
Qed.

Hint Resolve rename_wf_operand: ssa_rename.

Hint Constructors wf_operand_list.

Lemma rename_wf_operand_list : forall instr id1 id2 f b id_list0
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f) 
  (HwfR:wf_renaming f id1 id2)
  (H2 : wf_operand_list
         (make_list_fdef_block_insn_id
            (map_list_id (fun id_ : id => (f, b, instr, id_)) id_list0))),
  wf_operand_list
   (make_list_fdef_block_insn_id
      (map_list_id
         (fun id_ : id =>
          (rename_fdef id1 id2 f, rename_block id1 id2 b,
          rename_insn id1 id2 instr, id_)) (rename_list_id id1 id2 id_list0))).
Proof.
  induction id_list0; simpl; intros; auto.
    inv H2.
    destruct (id_dec i0 id2); subst; simpl; auto with ssa_rename.
Qed.

Hint Resolve rename_wf_operand_list: ssa_rename.

Lemma rename_wf_insn_base : forall f b id1 id2 instr 
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f)
  (HwfI: wf_insn_base f b instr) (HwfR:wf_renaming f id1 id2),
  wf_insn_base (rename_fdef id1 id2 f) (rename_block id1 id2 b) 
    (rename_insn id1 id2 instr).
Proof.
  intros.
  inv HwfI.
  eapply rename_insnInFdefBlockB in H; eauto.
  eapply wf_insn_base_intro; eauto with ssa_rename.
Qed.

Hint Constructors wf_insn wf_value.

Lemma rename_lookupIDFromPhiNodes : forall id5 id1 id2 ps,
  id1 <> id2 -> id5 <> id2 -> ~ In id2 (getPhiNodesIDs ps) ->
  lookupIDFromPhiNodes ps id5 = 
    lookupIDFromPhiNodes (List.map (rename_phi id1 id2) ps) 
      (rename_id id1 id2 id5).
Proof.
  induction ps; simpl; intros; auto.
    rewrite IHps; auto.
    unfold lookupIDFromPhiNode in *.
    destruct a. simpl in *.
    destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) id5 i0); subst.
      destruct (rename_id id1 id2 i0 == rename_id id1 id2 i0); auto.
        congruence.
      destruct (rename_id id1 id2 id5 == rename_id id1 id2 i0); auto.
        apply rename_id_inv in e; subst; auto.
        congruence.
Qed.
 
Lemma getCmdLoc_rename_cmd: forall id1 id2 c,
  getCmdLoc (rename_cmd id1 id2 c) = rename_id id1 id2 (getCmdLoc c).
Proof. destruct c; auto. Qed.

Lemma rename_lookupIDFromCmds : forall id5 id1 id2 cs,
  id1 <> id2 -> id5 <> id2 -> ~ In id2 (getCmdsLocs cs) ->
  lookupIDFromCmds cs id5 = 
    lookupIDFromCmds (List.map (rename_cmd id1 id2) cs)
      (rename_id id1 id2 id5).
Proof.
  induction cs; simpl; intros; auto.
    unfold lookupIDFromCmd in *.
    destruct (id5 == getCmdLoc a); subst.
      destruct (rename_id id1 id2 (getCmdLoc a) == 
                getCmdLoc (rename_cmd id1 id2 a)); auto.
        rewrite getCmdLoc_rename_cmd in n. congruence.
      destruct (rename_id id1 id2 id5 == 
                getCmdLoc (rename_cmd id1 id2 a)); auto.
        rewrite getCmdLoc_rename_cmd in e.
        apply rename_id_inv in e; subst; auto.
        congruence.
Qed.

Lemma getCmdLoc_rename_tmn: forall id1 id2 t,
  rename_id id1 id2 (getTerminatorID t)= getTerminatorID (rename_tmn id1 id2 t).
Proof. destruct t; auto. Qed.

Lemma rename_lookupIDFromTerminator : forall id5 id1 id2 t,
  id1 <> id2 -> id5 <> id2 -> id2 <> (getTerminatorID t) ->
  lookupIDFromTerminator t id5 = 
    lookupIDFromTerminator (rename_tmn id1 id2 t) (rename_id id1 id2 id5).
Proof. 
  unfold lookupIDFromTerminator.
  intros.
  destruct (id5 == getTerminatorID t); subst.
    destruct (rename_id id1 id2 (getTerminatorID t) ==
      getTerminatorID (rename_tmn id1 id2 t)); auto.
      rewrite getCmdLoc_rename_tmn in n. congruence.
    destruct (rename_id id1 id2 id5 == getTerminatorID (rename_tmn id1 id2 t));
      auto.
      rewrite <- getCmdLoc_rename_tmn in e.
      apply rename_id_inv in e; subst; auto.
      congruence.
Qed.      

Lemma rename_lookupIDFromBlocks : forall id5 id1 id2 bs,
  id1 <> id2 -> id5 <> id2 -> ~ In id2 (getBlocksLocs bs) ->
  lookupIDFromBlocks bs id5 = 
    lookupIDFromBlocks (List.map (rename_block id1 id2) bs) 
      (rename_id id1 id2 id5).
Proof.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    assert (~ In id2 (getBlocksLocs bs) /\
            id2 <> getTerminatorID t /\
            ~ In id2 (getCmdsLocs c) /\
            ~ In id2 (getPhiNodesIDs p)) as J.
      split.
        intro J. apply H1. apply in_or_app. auto.
      split.
        intro J. subst. apply H1. apply in_or_app. left. 
        apply in_or_app. right. apply in_or_app. right. simpl. auto.
      split.
        intro J. apply H1. apply in_or_app. left. 
        apply in_or_app. right. apply in_or_app. auto.

        intro J. apply H1. apply in_or_app. left. 
        apply in_or_app. auto.
    destruct J as [J1 [J2 [J3 J4]]].
    rewrite IHbs; auto.
    rewrite <- rename_lookupIDFromPhiNodes; auto.
    rewrite <- rename_lookupIDFromCmds; auto.
    rewrite <- rename_lookupIDFromTerminator; auto. 
Qed.

Lemma rename_lookupIDFromFdef : forall f id5 id1 id2,
  id1 <> id2 -> id5 <> id2 -> 
  (let '(fdef_intro bs):=f in ~ In id2 (getBlocksLocs bs)) ->
  lookupIDFromFdef f id5 = 
    lookupIDFromFdef (rename_fdef id1 id2 f) (rename_id id1 id2 id5).
Proof.
  destruct f. simpl. intros. rewrite <- rename_lookupIDFromBlocks; auto.
Qed.

Lemma rename_lookupBlockViaLabelFromBlocks : forall l5 id1 id2 bs b,
  lookupBlockViaLabelFromBlocks bs l5 = ret b ->
  lookupBlockViaLabelFromBlocks (List.map (rename_block id1 id2) bs) l5 = 
    ret (rename_block id1 id2 b).
Proof.
  unfold lookupBlockViaLabelFromBlocks.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l5 l0); 
      subst; inv H; auto.
Qed.

Hint Resolve rename_lookupBlockViaLabelFromBlocks : ssa_rename.

Lemma rename_lookupBlockViaLabelFromFdef : forall f l5 b id1 id2,
  lookupBlockViaLabelFromFdef f l5 = ret b ->
  lookupBlockViaLabelFromFdef (rename_fdef id1 id2 f) l5 = 
    ret (rename_block id1 id2 b).
Proof.
  destruct f. simpl. intros. apply rename_lookupBlockViaLabelFromBlocks; auto.
Qed.

Hint Resolve rename_lookupBlockViaLabelFromFdef: ssa_rename.

Lemma rename_wf_value : forall f id1 id2 v (Hwfv: wf_value f v)
  (Huniq:uniqFdef f) (Hwfr: wf_renaming f id1 id2),
  wf_value (rename_fdef id1 id2 f) (rename_value id1 id2 v).
Proof.
  intros.
  inv Hwfv; try constructor.
    simpl. 
    destruct Hwfr as [J1 J2].
    rewrite <- rename_lookupIDFromFdef; auto.    
    destruct f as [bs].
    apply lookupIDFromBlocks__InGetBlocksLocs in H.
    destruct (id_dec id5 id2); subst; auto.
Qed.

Hint Constructors wf_phi_operands.

Lemma rename_wf_phi_operands : forall f b id1 id2 id' vls (HwfF: wf_fdef f)
  (Hwf_pnops: wf_phi_operands f b id' vls) (HwfR:wf_renaming f id1 id2),
  wf_phi_operands (rename_fdef id1 id2 f) (rename_block id1 id2 b) 
    (rename_id id1 id2 id') (rename_list_value_l id1 id2 vls).
Proof.
  intros.
  induction Hwf_pnops; simpl; auto.
    assert (H0':=H0).
    apply rename_lookupBlockViaLabelFromFdef with (id1:=id1)(id2:=id2) 
      in H0; auto.
    rewrite rename_isReachableFromEntry with (id1:=id1)(id2:=id2) in H1; auto.
    eapply rename_lookupBlockViaIDFromFdef in H; eauto.
    erewrite rename_blockDominates in H1.
    eapply wf_phi_operands_cons_vid; eauto.
Qed.
     
Lemma rename_genBlockUseDef_block : forall id1 id2 b ud,
  genBlockUseDef_block b ud = 
  genBlockUseDef_block (rename_block id1 id2 b) ud.
Proof.
  intros. destruct b; simpl.
  destruct t; auto.
Qed.

Lemma rename_genBlockUseDef_blocks : forall id1 id2 bs ud,
  genBlockUseDef_blocks bs ud = 
  genBlockUseDef_blocks (List.map (rename_block id1 id2) bs) ud.
Proof.
  induction bs; simpl; intros; auto.
    rewrite <- IHbs.
    rewrite <- rename_genBlockUseDef_block; auto.
Qed.

Lemma rename_hasNonePredecessor : forall f id1 id2 b
  (Hnpred : hasNonePredecessor b (genBlockUseDef_fdef f) = true),
  hasNonePredecessor (rename_block id1 id2 b) 
    (genBlockUseDef_fdef (rename_fdef id1 id2 f)) = true.
Proof.
  intros. destruct f. simpl in *.
  rewrite <- rename_genBlockUseDef_blocks.
  destruct b; auto.
Qed.

Lemma rename_predOfBlock : forall id1 id2 b,
  predOfBlock b = predOfBlock (rename_block id1 id2 b).
Proof.
  destruct b; simpl; auto.
Qed.

Lemma rename_list_value_l__labels : forall id1 id2 vls,
  let '(_, ls1):=split (unmake_list_value_l vls) in
  let '(_, ls2):=split (unmake_list_value_l (rename_list_value_l id1 id2 vls)) in
  ls1 = ls2.
Proof.
  induction vls; simpl; auto.
    destruct (split (unmake_list_value_l vls)).
    destruct (split (unmake_list_value_l (rename_list_value_l id1 id2 vls))).
    subst. auto.
Qed.

Lemma rename_check_list_value_l : forall f b id1 id2 vls
  (Hcl: check_list_value_l f b vls),
  check_list_value_l (rename_fdef id1 id2 f) (rename_block id1 id2 b)
    (rename_list_value_l id1 id2 vls).
Proof.
  unfold check_list_value_l. destruct f as [bs]. simpl. intros until vls.
  repeat rewrite <- rename_genBlockUseDef_blocks.
  repeat rewrite <- rename_predOfBlock. 
  assert (J:=@rename_list_value_l__labels id1 id2 vls).
  destruct (split (unmake_list_value_l vls)).
  destruct (split (unmake_list_value_l (rename_list_value_l id1 id2 vls))).
  subst. auto.
Qed.

Hint Resolve rename_wf_phi_operands rename_check_list_value_l: ssa_rename.

Lemma rename_wf_phinode : forall f b id1 id2 PN (HwfF: wf_fdef f) 
  (HwfPN: wf_phinode f b PN) (HwfR:wf_renaming f id1 id2),
  wf_phinode (rename_fdef id1 id2 f) (rename_block id1 id2 b) 
    (rename_phi id1 id2 PN).
Proof.
  intros. destruct PN as [id' vls].
  unfold wf_phinode in *. simpl.
  destruct HwfPN as [Hwf_pnops Hcl].
  split; auto with ssa_rename.
Qed.

Hint Resolve rename_wf_value : ssa_rename.

Lemma rename_wf_value_list : forall
  (id1 id2 : id)
  (fdef5 : fdef) (Huniq: uniqFdef fdef5)
  (block5 : block) (Hwfr: wf_renaming fdef5 id1 id2)
  (value_l_list : list_value_l)
  (H : wf_value_list
        (make_list_fdef_value
           (map_list_value_l
              (fun (value_ : value) (_ : l) => (fdef5, value_)) value_l_list))),
   wf_value_list
     (make_list_fdef_value
        (map_list_value_l
           (fun (value_ : value) (_ : l) =>
            (rename_fdef id1 id2 fdef5, value_))
           (rename_list_value_l id1 id2 value_l_list))).
Proof.
  induction value_l_list; simpl; intros; auto.
    inv H.
    apply Cons_wf_value_list; auto.
    apply rename_wf_value; auto.  
Qed.

Hint Resolve rename_wf_value_list: ssa_rename.

Lemma rename_wf_insn : forall f b id1 id2 instr (HwfF: wf_fdef f) 
  (HwfI: wf_insn f b instr) (Huniq : NoDup (getBlockLocs b))
  (Hwfr: wf_renaming f id1 id2),
  wf_insn (rename_fdef id1 id2 f) (rename_block id1 id2 b) 
    (rename_insn id1 id2 instr).
Proof.
  intros.

  Ltac DONE := 
  eauto with ssa_rename; try match goal with
  | H : wf_insn_base _ _ _ |- wf_insn_base _ _ _ => 
    eapply rename_wf_insn_base in H; eauto
  | H : wf_value _ ?v |- wf_value _ (rename_value _ _ ?v) => 
    eapply rename_wf_value  in H; eauto
  | H : lookupBlockViaLabelFromFdef _ ?l = Some _ |- 
        lookupBlockViaLabelFromFdef _ ?l = Some _  =>
    eapply rename_lookupBlockViaLabelFromFdef in H; eauto
  | H : insnInFdefBlockB _ _ _ = _ |- insnInFdefBlockB _ _ _ = _ =>
    eapply rename_insnInFdefBlockB in H; eauto
  | H : wf_phinode _ _ _ |- wf_phinode _ _ _ =>
    eapply rename_wf_phinode in H; eauto
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

Hint Resolve rename_wf_insn : ssa_rename.
Hint Constructors wf_phinodes.

Lemma rename_wf_phinodes : forall f b id1 id2 PNs (HwfF: wf_fdef f)
  (HwfPNs: wf_phinodes f b PNs) (Hwfr: wf_renaming f id1 id2)
  (Huniq : NoDup (getBlockLocs b)),
  wf_phinodes (rename_fdef id1 id2 f) (rename_block id1 id2 b)
    (List.map (rename_phi id1 id2) PNs).
Proof.
  intros. 
  induction HwfPNs; simpl; auto.
    eapply rename_wf_insn in H; eauto.
Qed.

Hint Constructors wf_cmds.

Lemma rename_wf_cmds : forall f b id1 id2 Cs (HwfF: wf_fdef f)
  (HwfCs: wf_cmds f b Cs) (Huniq : NoDup (getBlockLocs b))  
  (Hwfr: wf_renaming f id1 id2),
  wf_cmds (rename_fdef id1 id2 f) (rename_block id1 id2 b)
          (List.map (rename_cmd id1 id2) Cs).
Proof.
  intros. 
  induction HwfCs; simpl; auto.
    eapply rename_wf_insn in H; eauto.
Qed.

Lemma rename_wf_block : forall f b id1 id2 (HwfF: wf_fdef f)
  (HwfB : wf_block f b) (Huniq : NoDup (getBlockLocs b))  
  (Hwfr: wf_renaming f id1 id2),
  wf_block (rename_fdef id1 id2 f) (rename_block id1 id2 b).
Proof.
  intros.
  inv_wf_block HwfB; subst.
  match goal with
  | HBinF : blockInFdefB _ _ = _,
    HwfPNs : wf_phinodes _ _ _,
    HwfCs : wf_cmds _ _ _,
    Hwftmn : wf_insn _ _ _ |- _ =>
     eapply rename_blockInFdefB in HBinF; eauto;
     eapply rename_wf_phinodes in HwfPNs; eauto;
     eapply rename_wf_cmds in HwfCs; eauto;
     eapply rename_wf_insn in Hwftmn; eauto
  end.
  apply wf_block_intro; eauto.
Qed.

Hint Resolve rename_wf_block : ssa_rename.

Hint Constructors wf_blocks.

Lemma rename_wf_blocks : forall f bs id1 id2 (HwfF: wf_fdef f)
  (HwfBs : wf_blocks f bs) (Huniq : uniqBlocks bs) 
  (Hwfr: wf_renaming f id1 id2),
  wf_blocks (rename_fdef id1 id2 f) (List.map (rename_block id1 id2) bs).
Proof.
  intros.
  induction HwfBs; simpl; auto.
    simpl_env in Huniq. apply uniqBlocks_inv in Huniq. inv Huniq.
    inv H0. simpl in *. simpl_env in H3.
    apply wf_blocks_cons; eauto with ssa_rename.
Qed.

Hint Resolve rename_wf_blocks : ssa_rename.

Lemma rename_InBlocksLabels : forall (id1 id2 : id) l0 (bs : blocks)
  (Hin : In l0 (getBlocksLabels (List.map (rename_block id1 id2) bs))),
  In l0 (getBlocksLabels bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl. intro.
    destruct Hin as [Hin | Hin]; auto.
Qed.

Lemma rename_uniqBlocksLabels : forall (id1 id2: id) (bs : blocks)
  (HuniqBs : NoDup (getBlocksLabels bs)),
  NoDup (getBlocksLabels (List.map (rename_block id1 id2) bs)).
Proof.
  induction bs; simpl; intros; auto.
    destruct a. simpl.
    inv HuniqBs.
    apply NoDup_cons; eauto using rename_InBlocksLabels.
Qed.

Lemma rename_uniqGetPhiNodesIDs : forall id1 id2 ps,
  id2 <> id1 -> ~ In id2 (getPhiNodesIDs ps) ->
  NoDup (getPhiNodesIDs ps) ->
  NoDup (getPhiNodesIDs (List.map (rename_phi id1 id2) ps)).
Proof.
  induction ps; simpl; intros; auto.
    destruct a. simpl in *. inv H1.
    constructor; auto.
      intro J. apply H4.
      apply rename_InGetPhiNodesIDs' in J; auto.
Qed.

Lemma rename_uniqGetCmdsLocs : forall id1 id2 cs,
  id2 <> id1 -> ~ In id2 (getCmdsLocs cs) ->
  NoDup (getCmdsLocs cs) ->
  NoDup (getCmdsLocs (List.map (rename_cmd id1 id2) cs)).
Proof.
  induction cs; simpl; intros; auto.
    destruct a; simpl in *; inv H1;
    constructor; try solve [auto |
      intro J; apply H4; apply rename_InGetCmdsLocs' in J; auto].
Qed.

Lemma getCmdLoc_rename_cmd_eq: forall id2 c,
  getCmdLoc (rename_cmd (getCmdLoc c) id2 c) = id2.
Proof. 
  unfold rename_cmd, rename_id.
  destruct c; simpl; destruct (id_dec i0 i0); auto; try congruence.
Qed.

Lemma getCmdLoc_rename_cmd_neq: forall id1 id2 c,
  id1 <> getCmdLoc c ->
  getCmdLoc (rename_cmd id1 id2 c) = getCmdLoc c.
Proof. 
  unfold rename_cmd, rename_id.
  destruct c; simpl; intros; destruct (id_dec i0 id1); auto; try congruence.
Qed.

Lemma rename_getCmdsLocs : forall id1 id2 cs (Huniq: NoDup (getCmdsLocs cs)),
  id2 <> id1 -> ~ In id2 (getCmdsLocs cs) ->
  if (in_dec eq_atom_dec id1 (getCmdsLocs cs)) then
    forall a,
      In a (getCmdsLocs (List.map (rename_cmd id1 id2) cs)) ->
      a <> id1 /\
      (In a (getCmdsLocs cs) \/ a = id2)
  else
    getCmdsLocs (List.map (rename_cmd id1 id2) cs) = getCmdsLocs cs.
Proof.
  induction cs; simpl; intros; auto.
  destruct (eq_atom_dec (getCmdLoc a) id1); subst; intros.
    destruct H1 as [H1 | H1]; subst.
      rewrite getCmdLoc_rename_cmd_eq.
      split; auto.

      inv Huniq.
      apply IHcs in H5; auto.
      destruct (in_dec eq_atom_dec (getCmdLoc a) (getCmdsLocs cs)).
        contradict i0; auto.
        rewrite H5 in H1.  
        split; auto.
          destruct (a0 == getCmdLoc a); subst; auto.

    inv Huniq.
    destruct (in_dec eq_atom_dec id1 (getCmdsLocs cs)); intros.
      destruct H1 as [H1 | H1]; subst.
        rewrite getCmdLoc_rename_cmd_neq; auto.
        apply IHcs in H1; auto.
        destruct H1 as [J1 J2]. split; auto.
        destruct J2; auto.

        rewrite IHcs; auto.
        rewrite getCmdLoc_rename_cmd_neq; auto.
Qed.

Lemma getPhiNodeID_rename_phi_eq: forall id2 p,
  getPhiNodeID (rename_phi (getPhiNodeID p) id2 p) = id2.
Proof. 
  unfold rename_phi, rename_id.
  destruct p; simpl; destruct (id_dec i0 i0); auto; try congruence.
Qed.

Lemma getPhiNodeID_rename_phi_neq: forall id1 id2 p,
  id1 <> getPhiNodeID p ->
  getPhiNodeID (rename_phi id1 id2 p) = getPhiNodeID p.
Proof. 
  unfold rename_phi, rename_id.
  destruct p; simpl; intros; destruct (id_dec i0 id1); auto; try congruence.
Qed.

Lemma rename_getPhiNodesIDs : forall id1 id2 ps 
  (Huniq: NoDup (getPhiNodesIDs ps)),
  id2 <> id1 -> ~ In id2 (getPhiNodesIDs ps) ->
  if (in_dec eq_atom_dec id1 (getPhiNodesIDs ps)) then
    forall a,
      In a (getPhiNodesIDs (List.map (rename_phi id1 id2) ps)) ->
      a <> id1 /\
      (In a (getPhiNodesIDs ps) \/ a = id2)
  else
    getPhiNodesIDs (List.map (rename_phi id1 id2) ps) = getPhiNodesIDs ps.
Proof.
  induction ps; simpl; intros; auto.
  destruct (eq_atom_dec (getPhiNodeID a) id1); subst; intros.
    destruct H1 as [H1 | H1]; subst.
      rewrite getPhiNodeID_rename_phi_eq.
      split; auto.

      inv Huniq.
      apply IHps in H5; auto.
      destruct (in_dec eq_atom_dec (getPhiNodeID a) (getPhiNodesIDs ps)).
        contradict i0; auto.
        rewrite H5 in H1.  
        split; auto.
          destruct (a0 == getPhiNodeID a); subst; auto.

    inv Huniq.
    destruct (in_dec eq_atom_dec id1 (getPhiNodesIDs ps)); intros.
      destruct H1 as [H1 | H1]; subst.
        rewrite getPhiNodeID_rename_phi_neq; auto.
        apply IHps in H1; auto.
        destruct H1 as [J1 J2]. split; auto.
        destruct J2; auto.

        rewrite IHps; auto.
        rewrite getPhiNodeID_rename_phi_neq; auto.
Qed.

Lemma getTerminatorID_rename_tmn_eq: forall id2 t,
  getTerminatorID (rename_tmn (getTerminatorID t) id2 t) = id2.
Proof. 
  unfold rename_tmn, rename_id.
  destruct t; simpl; destruct (id_dec i0 i0); auto; try congruence.
Qed.

Lemma getTerminatorID_rename_tmn_neq: forall id1 id2 t,
  id1 <> getTerminatorID t ->
  getTerminatorID (rename_tmn id1 id2 t) = getTerminatorID t.
Proof. 
  unfold rename_tmn, rename_id.
  destruct t; simpl; intros; destruct (id_dec i0 id1); auto; try congruence.
Qed.

Lemma rename_getTerminatorID: forall id1 id2 t,
  id2 <> id1 -> id2 <> (getTerminatorID t) ->
  if (id1 == getTerminatorID t) then
    forall a,
      a = getTerminatorID (rename_tmn id1 id2 t) ->
      a <> id1 /\
      (a = getTerminatorID t \/ a = id2)
  else
    getTerminatorID (rename_tmn id1 id2 t) = getTerminatorID t.
Proof.
  intros.
  destruct (id1 == getTerminatorID t); subst; intros.
    rewrite getTerminatorID_rename_tmn_eq in H1. subst. auto.
    rewrite getTerminatorID_rename_tmn_neq; auto.
Qed.

Lemma rename_getCmdsLocs_getTerminatorID : forall id1 id2 cs t
  (Huniq: NoDup (getCmdsLocs cs ++ [getTerminatorID t])),
  id2 <> id1 -> ~ In id2 (getCmdsLocs cs ++ [getTerminatorID t]) ->
  if (in_dec eq_atom_dec id1 (getCmdsLocs cs ++ [getTerminatorID t])) then
    forall a,
      In a (getCmdsLocs (List.map (rename_cmd id1 id2) cs) ++
            [getTerminatorID (rename_tmn id1 id2 t)]) ->
      a <> id1 /\
      (In a (getCmdsLocs cs ++ [getTerminatorID t]) \/ a = id2)
  else
    getCmdsLocs (List.map (rename_cmd id1 id2) cs) ++
      [getTerminatorID (rename_tmn id1 id2 t)] = 
      getCmdsLocs cs ++ [getTerminatorID t].
Proof.
  intros.
  apply notin_app_inv in H0. destruct H0 as [J1 J2].
  apply NoDup_split' in Huniq. destruct Huniq as [Huniq1 [Huniq2 J]].
  assert (G4:=@rename_getCmdsLocs id1 id2 cs Huniq1 H J1).
  assert (id2 <> (getTerminatorID t)) as J3.
    intro G. subst. apply J2. simpl. auto.
  assert (G5:=@rename_getTerminatorID id1 id2 t H J3).
  destruct (in_dec eq_atom_dec id1 (getCmdsLocs cs ++ [getTerminatorID t])); 
    intros.

    apply in_app_or in i0.
    destruct i0 as [i0 | i0].
      destruct (in_dec eq_atom_dec id1 (getCmdsLocs cs)); 
        try solve [contradict i0; auto].
      destruct (id1 == getTerminatorID t); subst;
        try solve [apply J in i1; contradict i1; simpl; auto].
      rewrite G5 in H0.
      split.
        destruct (id_dec a id1); subst; auto.
        apply in_app_or in H0.
        destruct H0 as [H0 | H0].
          apply G4 in H0. destruct H0; auto.
          contradict H0; auto.

        apply in_app_or in H0.
        destruct H0 as [H0 | H0].
          apply G4 in H0. destruct H0.
          destruct H1; auto.
          left. apply in_or_app; auto.

          left. apply in_or_app; auto.
           
      simpl in i0. destruct i0 as [i0 | i0]; subst; try solve [inversion i0].
      destruct (getTerminatorID t == getTerminatorID t); try congruence.
      destruct (in_dec eq_atom_dec (getTerminatorID t) (getCmdsLocs cs));
        try solve [apply J in i0; contradict i0; simpl; auto].
      rewrite G4 in H0.
      destruct (@G5 (getTerminatorID (rename_tmn (getTerminatorID t) id2 t)))
        as [J4 [J5 | J5]]; auto.
        rewrite J5 in J4. congruence.
        rewrite J5 in J4, H0. clear J5.
        apply in_app_or in H0.
        destruct H0 as [H0 | H0].
          split. apply J in H0. intro J0. subst. apply H0. simpl. auto.
                 left. apply in_or_app; auto.

          simpl in H0. 
          destruct H0 as [H0 | H0]; subst; try solve [inversion H0].
          split; auto.       

    apply notin_app_inv in n.
    destruct n as [n1 n2].
    destruct (in_dec eq_atom_dec id1 (getCmdsLocs cs)); 
      try solve [contradict n1; auto].
    destruct (id1 == getTerminatorID t); subst;
      try solve [contradict n2; simpl; auto].
    rewrite G4. rewrite G5. auto.
Qed.

Lemma rename_uniqBlockLocs : forall (id1 id2 : id) (b : block)
  (Hnotin: ~ In id2 (getBlockLocs b)) (Hneq: id2 <> id1),
  NoDup (getBlockLocs b) ->
  NoDup (getBlockLocs (rename_block id1 id2 b)).
Proof.
  destruct b. simpl.
  intros.
  assert ( ~ In id2 (getCmdsLocs c) /\
           ~ In id2 (getPhiNodesIDs p) /\
           id2 <> getTerminatorID t) as G. 
    apply notin_app_inv in Hnotin.
    destruct Hnotin as [J1 J2].
    apply notin_app_inv in J2.
    destruct J2 as [J2 J3].
    split; auto.
    split; auto.
      intro J. subst. apply J3. simpl. auto.
  destruct G as [G1 [G2 G3]].
  apply NoDup_split' in H. destruct H as [J2 [J3 J4]].
  assert (Huniq1:=J2).
  apply rename_uniqGetPhiNodesIDs with (id1:=id1)(id2:=id2) in J2; auto.
  apply NoDup_app; auto.
    apply NoDup_split' in J3. destruct J3 as [J5 [J6 J7]].
    assert (Huniq2:=J5).
    apply rename_uniqGetCmdsLocs with (id1:=id1)(id2:=id2) in J5; auto.
      apply NoDup_app; auto.
        intros a0 J8 J9.
        assert (G4:=@rename_getCmdsLocs id1 id2 c Huniq2 Hneq G1).
        assert (G5:=@rename_getTerminatorID id1 id2 t Hneq G3).
        destruct (in_dec eq_atom_dec id1 (getCmdsLocs c)).
          apply G4 in J8.
          destruct J8 as [J8 [J10 | J11]]; subst.
            destruct (id1 == getTerminatorID t); subst.
              apply J7 in i0. apply i0. simpl. auto.
              rewrite G5 in J9. apply J7 in J10. auto.
            destruct (id1 == getTerminatorID t); subst.
              apply J7 in i0. apply i0. simpl. auto.
              rewrite G5 in J9. apply G3. simpl in J9. 
                destruct J9 as [J9 | J9]; auto. inversion J9.
          rewrite G4 in J8. assert (J8':=J8).
          apply J7 in J8.
          destruct (id1 == getTerminatorID t); subst.
            destruct (@G5 
              (getTerminatorID (rename_tmn (getTerminatorID t) id2 t))) as
              [G6 [G7 | G8]]; auto.
              rewrite G8 in J9. simpl in J9. clear G8.
              destruct J9 as [J9 | J9]; subst; auto.
            rewrite G5 in J9. auto.
    intros a0 J8 J9. simpl_env in J9. 
    assert (G4:=@rename_getPhiNodesIDs id1 id2 p Huniq1 Hneq G2).
    assert (~ In id2 (getCmdsLocs c ++ [getTerminatorID t])) as G. 
      apply notin_app; auto.
        intro J. apply G3. simpl in J. destruct J as [J | J]; auto.
          inv J.
    assert (G5:=@rename_getCmdsLocs_getTerminatorID id1 id2 c t J3 Hneq G).
        destruct (in_dec eq_atom_dec id1 (getPhiNodesIDs p)).
          apply G4 in J8.
          destruct J8 as [J8 [J10 | J11]]; subst.
            destruct (in_dec eq_atom_dec id1 
              (getCmdsLocs c ++ [getTerminatorID t])).
              apply J4 in i0. apply i0. simpl. auto.
              rewrite G5 in J9. apply J4 in J10. auto.
            destruct (in_dec eq_atom_dec id1 
              (getCmdsLocs c ++ [getTerminatorID t])).
              apply J4 in i0. apply i0. simpl. auto.
              rewrite G5 in J9. apply Hnotin. apply in_or_app. right. auto.
          rewrite G4 in J8. assert (J8':=J8).
          apply J4 in J8.
          destruct (in_dec eq_atom_dec id1 
              (getCmdsLocs c ++ [getTerminatorID t])); subst.
            destruct (@G5 a0) as [G6 [G7 | G8]]; subst; auto.
            rewrite G5 in J9. auto.
Qed.

Lemma rename_getBlockLocs : forall id1 id2 b
  (Huniq: NoDup (getBlockLocs b)),
  id2 <> id1 -> ~ In id2 (getBlockLocs b) ->
  if (in_dec eq_atom_dec id1 (getBlockLocs b)) then
    forall a,
      In a (getBlockLocs (rename_block id1 id2 b)) ->
      a <> id1 /\
      (In a (getBlockLocs b) \/ a = id2)
  else
    getBlockLocs (rename_block id1 id2 b) = getBlockLocs b.
Proof.
  destruct b. simpl. intros. 
  apply notin_app_inv in H0. destruct H0 as [J1 J2].
  apply NoDup_split' in Huniq. destruct Huniq as [Huniq1 [Huniq2 J]].
  assert (G4:=@rename_getPhiNodesIDs id1 id2 p Huniq1 H J1).
  assert (G5:=@rename_getCmdsLocs_getTerminatorID id1 id2 c t Huniq2 H J2).
  destruct (in_dec eq_atom_dec id1 
    (getPhiNodesIDs p ++ getCmdsLocs c ++ getTerminatorID t :: nil)); 
    intros.

    apply in_app_or in i0.
    destruct i0 as [i0 | i0].
      destruct (in_dec eq_atom_dec id1 (getPhiNodesIDs p)); 
        try solve [contradict i0; auto].
      destruct (in_dec eq_atom_dec id1 (getCmdsLocs c ++ [getTerminatorID t])); 
        try solve [apply J in i0; contradict i0; auto].
      simpl_env in H0. rewrite G5 in H0.
      split.
        destruct (id_dec a id1); subst; auto.
        apply in_app_or in H0.
        destruct H0 as [H0 | H0].
          apply G4 in H0. destruct H0; auto.
          contradict H0; auto.

        apply in_app_or in H0.
        destruct H0 as [H0 | H0].
          apply G4 in H0. destruct H0.
          destruct H1; auto.
          left. apply in_or_app; auto.

          left. apply in_or_app; auto.
           
      destruct (in_dec eq_atom_dec id1 (getPhiNodesIDs p));
        try solve [apply J in i1; contradict i1; auto].
      destruct (in_dec eq_atom_dec id1 (getCmdsLocs c ++ [getTerminatorID t]));
        try solve [contradict i0; auto].
      rewrite G4 in H0.
      apply in_app_or in H0.
      destruct H0 as [H0 | H0].
        split. apply J in H0. intro J0. subst. apply H0. simpl. auto.
               left. apply in_or_app; auto.

        apply G5 in H0.
        destruct H0 as [J4 [J5 | J5]]; subst; auto.
        split; auto. left. apply in_or_app; auto.

    apply notin_app_inv in n.
    destruct n as [n1 n2].
    destruct (in_dec eq_atom_dec id1 (getPhiNodesIDs p)); 
      try solve [contradict n1; auto].
    destruct (in_dec eq_atom_dec id1 (getCmdsLocs c ++ [getTerminatorID t])); 
      try solve [contradict n2; auto].
    rewrite G4. simpl_env. rewrite G5. auto.
Qed.

Lemma rename_getBlocksLocs : forall id1 id2 bs
  (Huniq: NoDup (getBlocksLocs bs)),
  id2 <> id1 -> ~ In id2 (getBlocksLocs bs) ->
  if (in_dec eq_atom_dec id1 (getBlocksLocs bs)) then
    forall a,
      In a (getBlocksLocs (List.map (rename_block id1 id2) bs)) ->
      a <> id1 /\
      (In a (getBlocksLocs bs) \/ a = id2)
  else
    getBlocksLocs (List.map (rename_block id1 id2) bs) = getBlocksLocs bs.
Proof.
  induction bs; simpl; intros; auto.
  apply notin_app_inv in H0. destruct H0 as [J1 J2].
  apply NoDup_split' in Huniq. destruct Huniq as [Huniq1 [Huniq2 J]].
  assert (G4:=@rename_getBlockLocs id1 id2 a Huniq1 H J1).
  assert (G5:=@IHbs Huniq2 H J2). clear IHbs.
  destruct (in_dec eq_atom_dec id1 (getBlockLocs a ++ getBlocksLocs bs)); 
    intros.

    apply in_app_or in i0.
    destruct i0 as [i0 | i0].
      destruct (in_dec eq_atom_dec id1 (getBlockLocs a)); 
        try solve [contradict i0; auto].
      destruct (in_dec eq_atom_dec id1 (getBlocksLocs bs)); 
        try solve [apply J in i0; contradict i0; auto].
      rewrite G5 in H0.
      split.
        destruct (id_dec a0 id1); subst; auto.
        apply in_app_or in H0.
        destruct H0 as [H0 | H0].
          apply G4 in H0. destruct H0; auto.
          contradict H0; auto.

        apply in_app_or in H0.
        destruct H0 as [H0 | H0].
          apply G4 in H0. destruct H0.
          destruct H1; auto.
          left. apply in_or_app; auto.

          left. apply in_or_app; auto.
           
      destruct (in_dec eq_atom_dec id1 (getBlockLocs a));
        try solve [apply J in i1; contradict i1; auto].
      destruct (in_dec eq_atom_dec id1 (getBlocksLocs bs));
        try solve [contradict i0; auto].
      rewrite G4 in H0.
      apply in_app_or in H0.
      destruct H0 as [H0 | H0].
        split. apply J in H0. intro J0. subst. apply H0. simpl. auto.
               left. apply in_or_app; auto.

        apply G5 in H0.
        destruct H0 as [J4 [J5 | J5]]; subst; auto.
        split; auto. left. apply in_or_app; auto.

    apply notin_app_inv in n.
    destruct n as [n1 n2].
    destruct (in_dec eq_atom_dec id1 (getBlockLocs a)); 
      try solve [contradict n1; auto].
    destruct (in_dec eq_atom_dec id1 (getBlocksLocs bs)); 
      try solve [contradict n2; auto].
    rewrite G4. rewrite G5. auto.
Qed.

Lemma rename_uniqBlocksLocs : forall (id1 id2 : id) (bs : blocks)
  (Hnotin: ~ In id2 (getBlocksLocs bs)) (Hneq: id2 <> id1),
  NoDup (getBlocksLocs bs) ->
  NoDup (getBlocksLocs (List.map (rename_block id1 id2) bs)).
Proof.
  induction bs; simpl; auto.
    intros.
    apply NoDup_split' in H. destruct H as [J1 [J2 J3]].
    assert (~ In id2 (getBlockLocs a) /\ ~ In id2 (getBlocksLocs bs)) as G. 
      apply notin_app_inv in Hnotin; auto.
    destruct G as [G1 G2].
    assert (Huniq1:=J1). assert (Huniq2:=J2).
    apply rename_uniqBlockLocs with (id1:=id1)(id2:=id2) in J1; auto.
    apply IHbs in J2; auto.
    apply NoDup_app; auto.
    intros a0 J8 J9.
    assert (G4:=@rename_getBlockLocs id1 id2 a Huniq1 Hneq G1).
    assert (G5:=@rename_getBlocksLocs id1 id2 bs Huniq2 Hneq G2).
        destruct (in_dec eq_atom_dec id1 (getBlockLocs a)).
          apply G4 in J8.
          destruct J8 as [J8 [J10 | J11]]; subst.
            destruct (in_dec eq_atom_dec id1 (getBlocksLocs bs)).
              apply J3 in i0. apply i0. simpl. auto.
              rewrite G5 in J9. apply J3 in J10. auto.
            destruct (in_dec eq_atom_dec id1 (getBlocksLocs bs)).
              apply J3 in i0. apply i0. simpl. auto.
              rewrite G5 in J9. apply Hnotin. apply in_or_app. auto.
          rewrite G4 in J8. assert (J8':=J8).
          apply J3 in J8.
          destruct (in_dec eq_atom_dec id1 (getBlocksLocs bs)); subst.
            destruct (@G5 a0) as [G6 [G7 | G8]]; subst; auto.
            rewrite G5 in J9. auto.
Qed.

Hint Resolve rename_uniqBlocksLabels rename_uniqBlocksLocs : ssa_rename.

Lemma rename_uniqBlocks : forall (id1 id2 : id) (bs : blocks)
  (Hnotin: ~ In id2 (getBlocksLocs bs)) (Hneq: id2 <> id1)
  (HuniqBs : uniqBlocks bs),
  uniqBlocks (List.map (rename_block id1 id2) bs).
Proof.
  intros.
  destruct HuniqBs as [J1 J2].
  split; auto with ssa_rename.
Qed. 

Lemma rename_uniqFdef : forall f id1 id2 (HuniqF : uniqFdef f)
  (HwfR: wf_renaming f id1 id2),
  uniqFdef (rename_fdef id1 id2 f).
Proof.
  intros. destruct HwfR.
  destruct f. simpl in *. apply rename_uniqBlocks; auto.
Qed.

Lemma rename_wf_fdef : forall f id1 id2 (HwfF: wf_fdef f)
  (Hwfr: wf_renaming f id1 id2),
  wf_fdef (rename_fdef id1 id2 f).
Proof.
  intros.
  inv_wf_fdef HwfF.
  match goal with
  | Hentry : getEntryBlock _ = _,
    HuniqF : uniqFdef _,
    Hnpred : hasNonePredecessor _ _ = _,
    HwfBs : wf_blocks _ _ |- _ =>
     eapply rename_getEntryBlock in Hentry; eauto;
     eapply rename_hasNonePredecessor in Hnpred; eauto;
     eapply rename_wf_blocks in HwfBs; eauto;
     eapply rename_uniqFdef in HuniqF; eauto
  end.
  eapply wf_fdef_intro; eauto.
Qed.

(************** More props **************************************)

Lemma rename_id_neq: forall id1 id2 id0,
  id1 <> id0 -> rename_id id1 id2 id0 = id0.
Proof.
  intros.
  unfold rename_id.
  destruct (id_dec id0 id1); auto.
    subst. congruence.
Qed.

Lemma rename_id_eq: forall newid i0, rename_id newid i0 newid = i0.
Proof.
  intros.
  unfold rename_id.
  destruct (id_dec newid newid); auto.
    congruence.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
