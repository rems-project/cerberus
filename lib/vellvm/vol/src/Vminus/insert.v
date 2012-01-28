Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vminus.
Require Import Lattice.
Import AtomSet.

Definition insert_cmds (n:nat) (c:cmd) (cs : cmds) : cmds :=
firstn n cs ++ c :: skipn n cs.

(* insert c at the n-th position in block l1 *)
Definition insert_block (l1:l) (n:nat) (c:cmd) (b:block) : block :=
match b with
| block_intro l0 ps0 cs0 tmn0 =>
    block_intro l0 ps0 (if (l_dec l1 l0) 
                        then insert_cmds n c cs0
                        else cs0) tmn0
end.

Definition insert_fdef (l1:l) (n:nat) (c:cmd) (f:fdef) : fdef :=
let '(fdef_intro bs) := f in
fdef_intro (List.map (insert_block l1 n c) bs).

(************** Preserving wellformedness **************************************)

Definition insnDominatesPos (id':id) (n:nat) (b2:block) : Prop :=
  let '(block_intro l2 ps2 cs2 tmn2) := b2 in
  exists c2, 
    List.nth_error cs2 n = Some c2 /\ insnDominates id' (insn_cmd c2) b2.

(* all definitions of variables used by c must strictly dominate l1.n *)
Definition defs_dominate_pos l1 n (c:cmd) (f:fdef) : Prop :=
forall id' block' ids block1, 
  getCmdOperands c = ids ->
  lookupBlockViaLabelFromFdef f l1 = Some block1 ->
  In id' ids ->
  lookupBlockViaIDFromFdef f id' = Some block' ->
  insnDominatesPos id' n block1 \/
  blockStrictDominates f block' block1 \/ 
  (not (isReachableFromEntry f block1)).

(* A good insert of cmd c to l1.n in function f *)
Definition wf_insert l1 n c f : Prop :=
  (exists block1, lookupBlockViaLabelFromFdef f l1 = Some block1) /\
  (let '(fdef_intro bs) := f in ~ In (getCmdLoc c) (getBlocksLocs bs)) /\
  defs_dominate_pos l1 n c f /\
  (forall id1, 
    In id1 (getCmdOperands c) ->
    lookupIDFromFdef f id1 = Some tt /\
    exists b1, lookupBlockViaIDFromFdef f id1 = Some b1).

Lemma insert_getEntryBlock : forall f l1 n c b
  (Hentry : getEntryBlock f = Some b),
  getEntryBlock (insert_fdef l1 n c f) = Some (insert_block l1 n c b).
Proof.
  intros. destruct f. simpl in *.
  destruct b0; inv Hentry; auto.
Qed.

Lemma insert_getEntryBlock_None : forall f l1 n c
  (Hentry : getEntryBlock f = None),
  getEntryBlock (insert_fdef l1 n c f) = None.
Proof.
  intros. destruct f. simpl in *.
  destruct b; inv Hentry; auto.
Qed.

Lemma insert_genBlockUseDef_block : forall l1 n c b ud,
  genBlockUseDef_block b ud = 
  genBlockUseDef_block (insert_block l1 n c b) ud.
Proof.
  intros. destruct b; simpl.
  destruct t; auto.
Qed.

Lemma insert_genBlockUseDef_blocks : forall l1 n c bs ud,
  genBlockUseDef_blocks bs ud = 
  genBlockUseDef_blocks (List.map (insert_block l1 n c) bs) ud.
Proof.
  induction bs; simpl; intros; auto.
    rewrite <- IHbs.
    rewrite <- insert_genBlockUseDef_block; auto.
Qed.

Lemma insert_hasNonePredecessor : forall f l1 n c b
  (Hnpred : hasNonePredecessor b (genBlockUseDef_fdef f) = true),
  hasNonePredecessor (insert_block l1 n c b) 
    (genBlockUseDef_fdef (insert_fdef l1 n c f)) = true.
Proof.
  intros. destruct f. simpl in *.
  rewrite <- insert_genBlockUseDef_blocks.
  destruct b; auto.
Qed.

Lemma insert_InBlocksLabels : forall l1 n c l0 (bs : blocks)
  (Hin : In l0 (getBlocksLabels (List.map (insert_block l1 n c) bs))),
  In l0 (getBlocksLabels bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl. intro.
    destruct Hin as [Hin | Hin]; auto.
Qed.

Lemma insert_uniqBlocksLabels : forall l1 n c (bs : blocks)
  (HuniqBs : NoDup (getBlocksLabels bs)),
  NoDup (getBlocksLabels (List.map (insert_block l1 n c) bs)).
Proof.
  induction bs; simpl; intros; auto.
    destruct a. simpl.
    inv HuniqBs.
    apply NoDup_cons; eauto using insert_InBlocksLabels.
Qed.

Lemma insert_getCmdsLocs : forall c cs n,
  exists cs1, exists cs2, 
    getCmdsLocs (insert_cmds n c cs) = 
      getCmdsLocs cs1 ++ getCmdLoc c :: getCmdsLocs cs2 /\
    cs = cs1 ++ cs2.
Proof.
  unfold insert_cmds.
  induction cs; simpl; intros; auto.
    rewrite firstn_nil. rewrite skipn_nil. 
    exists nil. exists nil. auto.

    destruct n; simpl.
      exists nil. exists (a::cs). auto.

      destruct (@IHcs n) as [cs1 [cs2 [J1 J2]]]; subst.
      rewrite J1.
      exists (a::cs1). exists cs2. auto.
Qed.

Lemma insert_blockLocs : forall l1 n c (b : block),
  if (l_dec l1 (getBlockLabel b)) then
    exists ids1, exists ids2, 
      getBlockLocs (insert_block l1 n c b) = ids1 ++ getCmdLoc c :: ids2 /\
      getBlockLocs b = ids1 ++ ids2
  else
    getBlockLocs (insert_block l1 n c b) = getBlockLocs b.
Proof.
  destruct b. simpl.
  destruct (l_dec l1 l0); subst; auto.
  destruct (insert_getCmdsLocs c c0 n) as [cs1 [cs2 [J1 J2]]]; subst.
  rewrite J1.
  exists (getPhiNodesIDs p ++ getCmdsLocs cs1). 
  exists (getCmdsLocs cs2 ++ getTerminatorID t :: nil).
  rewrite getCmdsLocs_app. simpl_env. auto.
Qed.

Lemma insert_blocksLocs : forall l1 n c (bs : blocks) 
  (Huniq: NoDup (getBlocksLabels bs)),
  if (in_dec l_dec l1 (getBlocksLabels bs)) then
    (exists ids1, exists ids2, 
      getBlocksLocs (List.map (insert_block l1 n c) bs) = 
        ids1 ++ getCmdLoc c :: ids2 /\
      getBlocksLocs bs = ids1 ++ ids2)
  else
    getBlocksLocs (List.map (insert_block l1 n c) bs) = getBlocksLocs bs.
Proof.
  induction bs; simpl; intros; auto.
    assert (J:=@insert_blockLocs l1 n c a).
    destruct a. simpl in *. 
    inv Huniq.
    destruct (l_dec l0 l1); subst.
      destruct (l_dec l1 l1); try congruence.
      destruct J as [ids1 [ids2 [J1 J2]]].
      rewrite J2. rewrite J1.
      exists ids1. exists (ids2 ++ getBlocksLocs bs). 
      destruct (in_dec l_dec l1 (getBlocksLabels bs)); try congruence.
      simpl_env. rewrite IHbs; auto.

      destruct (l_dec l1 l0); subst; try congruence.
      destruct (in_dec l_dec l1 (getBlocksLabels bs)).
        apply IHbs in H2. destruct H2 as [ids1 [ids2 [J1 J2]]].
        rewrite J1. rewrite J2. 
        exists 
          ((getPhiNodesIDs p++getCmdsLocs c0++getTerminatorID t::nil) ++ ids1).
        exists ids2. simpl_env. auto.

        rewrite IHbs; auto.
Qed.

Lemma insert_uniqBlocksLocs : forall l1 n c (bs : blocks)
  (HuniqBs : NoDup (getBlocksLocs bs)) (HuniqLs : NoDup (getBlocksLabels bs)) 
  (Hnotin: ~ In (getCmdLoc c) (getBlocksLocs bs)),
  NoDup (getBlocksLocs (List.map (insert_block l1 n c) bs)).
Proof.
  intros.
  apply insert_blocksLocs with (l1:=l1)(c:=c)(n:=n) in HuniqLs; auto.
  destruct (in_dec l_dec l1 (getBlocksLabels bs)).
    destruct HuniqLs as [ids1 [ids2 [J1 J2]]].
    rewrite J1. rewrite J2 in Hnotin, HuniqBs. apply NoDup_insert; auto.

    rewrite HuniqLs. auto.
Qed.

Hint Resolve insert_uniqBlocksLabels insert_uniqBlocksLocs : ssa_insert.

Lemma insert_uniqBlocks : forall l1 n c (bs : blocks)
  (Hnotin: ~ In (getCmdLoc c) (getBlocksLocs bs))
  (HuniqBs : uniqBlocks bs),
  uniqBlocks (List.map (insert_block l1 n c) bs).
Proof.
  intros.
  destruct HuniqBs as [J1 J2].
  split; auto with ssa_insert.
Qed. 

Lemma insert_uniqFdef : forall f l1 n c (HuniqF : uniqFdef f)
  (Hnotin: let '(fdef_intro bs):=f in ~ In (getCmdLoc c) (getBlocksLocs bs)),
  uniqFdef (insert_fdef l1 n c f).
Proof.
  intros.
  destruct f. simpl in *. apply insert_uniqBlocks; auto.
Qed.

Lemma insert_InBlocksB : forall l1 n c b bs
  (Hin : InBlocksB b bs = true),
  InBlocksB (insert_block l1 n c b) (List.map (insert_block l1 n c) bs) = true.
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

Hint Resolve insert_InBlocksB: ssa_insert.

Lemma insert_blockInFdefB : forall f l1 n c b
  (Hin : blockInFdefB b f = true),
  blockInFdefB (insert_block l1 n c b) (insert_fdef l1 n c f) = true.
Proof.
  intros. destruct f. simpl in *.
  auto with ssa_insert.
Qed.

Hint Resolve insert_blockInFdefB: ssa_insert.

Lemma insert_phinodeInBlockB : forall l1 n c p b
  (Hin : phinodeInBlockB p b = true),
  phinodeInBlockB p (insert_block l1 n c b) = true.
Proof. destruct b. simpl. auto. Qed. 

Hint Resolve insert_phinodeInBlockB: ssa_insert.

Lemma insert_InCmdsB : forall n c0 c cs, 
  InCmdsB c cs = true ->
  InCmdsB c (insert_cmds n c0 cs) = true.
Proof.
  unfold insert_cmds.
  intros.
  rewrite <- firstn_skipn with (l:=cs)(n:=n) in H.
  apply InCmdsB_in in H.
  apply In_InCmdsB.
  apply in_or_app. apply in_app_or in H. simpl.
  destruct H; auto.
Qed.

Lemma insert_InCmdsB' : forall n c0 cs, 
  InCmdsB c0 (insert_cmds n c0 cs) = true.
Proof.
  unfold insert_cmds.
  intros. apply In_InCmdsB. apply in_middle.
Qed.

Hint Resolve insert_InCmdsB insert_InCmdsB': ssa_insert.

Lemma insert_cmdInBlockB : forall l1 n c0 c b
  (Hin : cmdInBlockB c b = true),
  cmdInBlockB c (insert_block l1 n c0 b) = true.
Proof.
  destruct b. simpl. intro. 
  destruct (l_dec l1 l0); auto with ssa_insert.
Qed. 

Hint Resolve insert_cmdInBlockB: ssa_insert.

Lemma insert_terminatorInBlockB : forall l1 n c t b
  (Hin : terminatorInBlockB t b = true),
  terminatorInBlockB t (insert_block l1 n c b) = true.
Proof. destruct b. simpl. intro. auto. Qed. 

Hint Resolve insert_terminatorInBlockB: ssa_insert.

Lemma insert_insnInFdefBlockB : forall f l1 n c b instr
  (Hin : insnInFdefBlockB instr f b = true),
  insnInFdefBlockB instr (insert_fdef l1 n c f) (insert_block l1 n c b) = true.
Proof.
  unfold insnInFdefBlockB.
  intros.
  destruct instr; simpl;
    apply andb_true_iff in Hin; inv Hin;
    apply andb_true_iff; auto with ssa_insert.
Qed.

Hint Resolve insert_insnInFdefBlockB: ssa_insert.

Lemma insert_getCmdsIDs : forall c cs n,
  match getCmdID c with
  | Some id0 => 
      exists cs1, exists cs2, 
        getCmdsIDs (insert_cmds n c cs) = 
          getCmdsIDs cs1 ++ id0 :: getCmdsIDs cs2 /\
        cs = cs1 ++ cs2
  | None => getCmdsIDs (insert_cmds n c cs) = getCmdsIDs cs
  end.
Proof.
  unfold insert_cmds.
  induction cs; simpl; intros.
    rewrite firstn_nil. rewrite skipn_nil. simpl.
    destruct (getCmdID c); auto.
      exists nil. exists nil. auto. 

    destruct n; simpl.
      destruct (getCmdID c); auto.
        exists nil. exists (a::cs). auto.
      destruct (getCmdID c).
        destruct (@IHcs n) as [cs1 [cs2 [J1 J2]]]; subst.
        rewrite J1. exists (a::cs1). exists cs2. 
        simpl. destruct (getCmdID a); auto.

        rewrite (@IHcs n). auto.
Qed.

Lemma insert_lookupBlockViaIDFromBlocks_helper: forall id5 ids0 c0 c ids1 n
  (n1 : ~ In id5 (ids0 ++ getCmdsIDs c0))
  (Hnotin2 : ~ In (getCmdLoc c) ids1)
  (H' : In id5 ids1)
  (i0 : In id5 (ids0 ++ getCmdsIDs (insert_cmds n c c0))),
  False.
Proof.
  intros.
  assert (J:=@insert_getCmdsIDs c c0 n).
  remember (getCmdID c) as R.
  destruct R.
    destruct J as [cs1 [cs2 [J1 J2]]]; subst.
    rewrite J1 in i0. rewrite getCmdsIDs_app in n1.
    contradict n1.
    apply in_or_app.
    apply in_app_or in i0.
    destruct i0 as [i0 | i0]; auto.
    right.
    apply in_or_app.
    apply in_app_or in i0.
    destruct i0 as [i0 | i0]; auto.
    right. simpl in i0.
    destruct i0 as [i0 | i0]; subst; auto.
    symmetry in HeqR.
    apply getCmdLoc_getCmdID in HeqR. subst. 
    contradict H'; auto.
    
    rewrite J in i0. congruence.
Qed.

Lemma insert_getCmdsIDs_incl : forall c cs n,
  incl (getCmdsIDs cs) (getCmdsIDs (insert_cmds n c cs)).
Proof.
  intros.
  assert (J:=@insert_getCmdsIDs c cs n).
  destruct (getCmdID c).
    destruct J as [cs1 [cs2 [J1 J2]]]; subst.
    rewrite J1. rewrite getCmdsIDs_app. apply incl_insert.
    rewrite J. apply incl_refl.
Qed.

Lemma insert_lookupBlockViaIDFromBlocks : forall id5 l1 n c bs b
  (Hnotin: ~ In (getCmdLoc c) (getBlocksLocs bs)),
  lookupBlockViaIDFromBlocks bs id5 = ret b ->
  lookupBlockViaIDFromBlocks (List.map (insert_block l1 n c) bs) id5 = 
      ret (insert_block l1 n c b).
Proof.
  induction bs; simpl; intros.
    congruence.

    assert (~ In (getCmdLoc c) (getBlockLocs a) /\
            ~ In (getCmdLoc c) (getBlocksLocs bs)) as J.
      split; intro J; apply Hnotin; apply in_or_app; auto.
    destruct J as [Hnotin1 Hnotin2].
    destruct a. simpl in *.
    destruct (l_dec l1 l0); subst.
      destruct (in_dec eq_dec id5 (getPhiNodesIDs p ++ getCmdsIDs c0)).
        inv H; simpl.
        destruct (l_dec l0 l0); try congruence.
        destruct (in_dec eq_dec id5 
          (getPhiNodesIDs p ++ getCmdsIDs (insert_cmds n c c0))); auto.
          contradict n0. 
          assert (J:=@insert_getCmdsIDs_incl c c0 n).
          apply incl_app with (l0:=getPhiNodesIDs p) in J; auto.

        assert (H':=H). apply lookupBlockViaIDFromBlocks__InGetBlocksLocs in H'.
        apply IHbs in H; auto. clear IHbs.
        destruct (in_dec eq_dec id5
          (getPhiNodesIDs p ++ getCmdsIDs (insert_cmds n c c0))).
          eapply insert_lookupBlockViaIDFromBlocks_helper in i0; eauto.
          inv i0.

          apply H.
      destruct (in_dec eq_dec id5 (getPhiNodesIDs p ++ getCmdsIDs c0)).
        inv H; simpl in *.
        destruct (l_dec l1 l0); subst; try congruence.
        
        assert (H':=H). apply lookupBlockViaIDFromBlocks__InGetBlocksLocs in H'.
        apply IHbs in H; auto. 
Qed.

Hint Resolve insert_lookupBlockViaIDFromBlocks : ssa_insert.

Lemma insert_lookupBlockViaIDFromFdef : forall f id5 b l1 c n
  (Hnotin: let '(fdef_intro bs):= f in 
           ~ In (getCmdLoc c) (getBlocksLocs bs)),
  lookupBlockViaIDFromFdef f id5 = ret b ->
  lookupBlockViaIDFromFdef (insert_fdef l1 n c f) id5 = 
    ret (insert_block l1 n c b).
Proof.
  destruct f. simpl; intros. apply insert_lookupBlockViaIDFromBlocks; auto.
Qed.

Hint Resolve insert_lookupBlockViaIDFromFdef: ssa_insert.

Lemma insert_successors_blocks : forall l1 n c bs,
  successors_blocks bs = successors_blocks (List.map (insert_block l1 n c) bs).
Proof.
  induction bs; simpl; auto.
    destruct a. simpl.
    rewrite IHbs.
    destruct t; auto.
Qed.

Hint Resolve insert_successors_blocks: ssa_insert.

Lemma insert_successors : forall f l1 n c,
  successors f = successors (insert_fdef l1 n c f).
Proof.
  intros. destruct f. simpl. auto with ssa_insert.
Qed.

Lemma insert_bound_blocks : forall l1 n c bs,
  bound_blocks bs = bound_blocks (List.map (insert_block l1 n c) bs).
Proof.
  induction bs; simpl; auto.
    destruct a; simpl. rewrite IHbs. auto.
Qed.

Hint Resolve insert_bound_blocks.

Lemma insert_vertexes_fdef: forall f l1 n c,
  vertexes_fdef f = vertexes_fdef (insert_fdef l1 n c f).
Proof.
  unfold vertexes_fdef.
  destruct f. simpl. intros.
  rewrite <- insert_bound_blocks. auto.
Qed.

Lemma insert_arcs_fdef: forall f l1 n c,
  arcs_fdef f = arcs_fdef (insert_fdef l1 n c f).
Proof.
  unfold arcs_fdef.
  destruct f. simpl. intros.
  rewrite <- insert_successors_blocks. auto.
Qed.

Lemma insert_reachable : forall f l1 n c,
  reachable f = reachable (insert_fdef l1 n c f).
Proof.
  intros.
  unfold reachable.
  case_eq (getEntryBlock f).
    intros b Hentry. 
    apply insert_getEntryBlock with (l1:=l1)(n:=n)(c:=c) in Hentry; eauto.
    rewrite Hentry.
    destruct b. simpl. 
    rewrite <- insert_vertexes_fdef.
    rewrite <- insert_arcs_fdef. auto.

    intro Hentry.
    apply insert_getEntryBlock_None with (l1:=l1)(n:=n)(c:=c) in Hentry; eauto.
    rewrite Hentry. auto.
Qed.

Lemma insert_isReachableFromEntry : forall f b l1 n c,
  isReachableFromEntry f b = 
    isReachableFromEntry (insert_fdef l1 n c f) (insert_block l1 n c b).
Proof.
  unfold isReachableFromEntry. intros.
  destruct b. simpl. rewrite <- insert_reachable; auto.
Qed.

Lemma insert_blockStrictDominates : forall f b1 b2 l1 n c,
  blockStrictDominates f b1 b2 <->
    blockStrictDominates (insert_fdef l1 n c f) (insert_block l1 n c b1)
      (insert_block l1 n c b2).
Proof.
  intros.
  unfold blockStrictDominates. destruct b1. destruct b2. simpl.
  unfold dom_analyze. destruct f. simpl.
  rewrite <- insert_successors_blocks.
  remember (entry_dom b) as R1.
  remember (entry_dom (List.map (insert_block l1 n c) b)) as R2.
  destruct R1 as [x1 Hx1]. 
  destruct R2 as [x2 Hx2]. 
  destruct x1 as [x1|]. 
  Case "1".
    destruct x1 as [le1 start1].
    destruct start1.
    destruct bs_contents as [|l2' bs_contents]; tinv Hx1.
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

Lemma insert_blockDominates : forall f b1 b2 l0 n c,
  blockDominates f b1 b2 <->
    blockDominates (insert_fdef l0 n c f) (insert_block l0 n c b1)
      (insert_block l0 n c b2).
Proof.
  intros.
  unfold blockDominates. destruct b1. destruct b2. simpl.
  unfold dom_analyze. destruct f. simpl.
  rewrite <- insert_successors_blocks.
  remember (entry_dom b) as R1.
  remember (entry_dom (List.map (insert_block l0 n c) b)) as R2.
  destruct R1 as [x1 Hx1]. 
  destruct R2 as [x2 Hx2]. 
  destruct x1 as [x1|]. 
  Case "1".
    destruct x1 as [le1 start1].
    destruct start1.
    destruct bs_contents as [|l2' bs_contents]; tinv Hx1.
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

Lemma insert_cmds_inv: forall n c cs,
  exists cs1, exists cs2, insert_cmds n c cs = cs1 ++ c :: cs2 /\
    cs = cs1 ++ cs2.
Proof. 
  unfold insert_cmds. intros.
  exists (firstn n cs). exists (skipn n cs).
  rewrite firstn_skipn. auto.
Qed. 

Lemma insert_insnDominates_aux1: forall i0 l1 l0 n c' cs1 c1 cs2 c0 cs3
  (J2 : getCmdID c1 = ret i0),
  exists cs0 : list cmd,
    exists c2 : cmd,
      exists cs4 : list cmd,
        exists cs5 : list cmd,
          (if l_dec l1 l0
           then insert_cmds n c' (cs1 ++ c1 :: cs2 ++ c0 :: cs3)
           else cs1 ++ c1 :: cs2 ++ c0 :: cs3) =
          cs0 ++ c2 :: cs4 ++ c0 :: cs5 /\ getCmdID c2 = ret i0.
Proof.
  intros.
  destruct (l_dec l1 l0); subst.
    destruct (@insert_cmds_inv n c' (cs1 ++ c1 :: cs2 ++ c0 :: cs3)) 
      as [A [B [EQ1 EQ2]]]; subst.
    rewrite EQ1.
    apply app_middle_split in EQ2.
    destruct EQ2 as [[l12 [Heq1 Heq2]] | [l21 [Heq1 Heq2]]]; subst.
      exists (A ++ c' :: l12). exists c1. exists cs2. exists cs3. 
      simpl_env. auto.

      exists cs1. exists c1. 
      apply app_middle_split in Heq2.
      destruct Heq2 as [[l12' [Heq1' Heq2']] | [l21' [Heq1' Heq2']]]; subst.
        exists (l21 ++ c' :: l12'). exists cs3. simpl_env. auto.
        exists cs2. exists (l21' ++ c' :: B). simpl_env. auto.
    
    exists cs1. exists c1. exists cs2. exists cs3. split; auto.
Qed.

Lemma insert_insnDominates_aux2: forall i0 l1 l0 n c' cs1 c1 cs2
  (J2 : getCmdID c1 = ret i0),
  exists cs0 : list cmd,
    exists c0 : cmd,
      exists cs3 : list cmd,
        (if l_dec l1 l0
         then insert_cmds n c' (cs1 ++ c1 :: cs2)
         else cs1 ++ c1 :: cs2) =
        cs0 ++ c0 :: cs3 /\ getCmdID c0 = ret i0.
Proof.
  intros.
  destruct (l_dec l1 l0); subst; eauto.
  destruct (@insert_cmds_inv n c' (cs1 ++ c1 :: cs2)) as [A [B [EQ1 EQ2]]]; 
    subst.
    rewrite EQ1. 
    apply app_middle_split in EQ2.
    destruct EQ2 as [[l12 [Heq1 Heq2]] | [l21 [Heq1 Heq2]]]; subst.
      exists (A ++ c' :: l12). exists c1. exists cs2. simpl_env. auto.
      exists cs1. exists c1. exists (l21 ++ c' :: B). simpl_env. auto.
Qed.

Lemma insert_insnDominates : forall i0 instr l1 n c' b, 
  NoDup (getBlockLocs b) ->
  insnInBlockB instr b = true ->
  insnDominates i0 instr b ->
  insnDominates i0 instr (insert_block l1 n c' b).
Proof.
 intros i0 instr l1 n c' b Hnodup HiInB. destruct b. simpl.
 destruct instr; simpl; intro J; auto.
   destruct J as [[ps1 [p1 [ps2 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]]; 
     subst.
     left. exists ps1. exists p1. exists ps2. auto.
     right. apply insert_insnDominates_aux1; auto.

   destruct J as [[[cs1 [c1 [cs2 [J1 J2]]]] | [ps1 [p1 [ps2 [J1 J2]]]]] Heq]; 
     subst; split; auto.
     left. apply insert_insnDominates_aux2; auto.

     right. exists ps1. exists p1. exists ps2. auto.
Qed.

Lemma insert_wf_operand : forall instr l1 n c f b i0
  (Hnotin: let '(fdef_intro bs):= f in 
           ~ In (getCmdLoc c) (getBlocksLocs bs))
  (Huniq : NoDup (getBlockLocs b))
  (H1 : wf_operand f b instr i0),
  wf_operand (insert_fdef l1 n c f) (insert_block l1 n c b) instr i0.
Proof.
  intros.
  inv H1.
  eapply wf_operand_intro with (block':=insert_block l1 n c block'); 
    try solve [eauto with ssa_insert].

    autounfold.
    rewrite <- insert_blockStrictDominates.
    rewrite <- insert_isReachableFromEntry; auto.
    destruct H5 as [H5 | [H5 | H5]]; auto.
    left. 
    apply insert_insnDominates; eauto using insnInFdefBlockB__insnInBlockB.
Qed.

Hint Resolve insert_wf_operand: ssa_insert.
Hint Constructors wf_operand_list.

Lemma insert_wf_operand_list : forall instr l1 n c f b id_list0
  (Hnotin: let '(fdef_intro bs):= f in 
           ~ In (getCmdLoc c) (getBlocksLocs bs))
  (Huniq : NoDup (getBlockLocs b))
  (H2 : wf_operand_list
         (make_list_fdef_block_insn_id
            (map_list_id (fun id_ : id => (f, b, instr, id_)) id_list0))),
  wf_operand_list
   (make_list_fdef_block_insn_id
      (map_list_id
         (fun id_ : id =>
          (insert_fdef l1 n c f, insert_block l1 n c b, instr, id_)) id_list0)).
Proof.
  induction id_list0; simpl; intros; auto.
    inv H2. simpl; auto with ssa_insert.
Qed.

Hint Resolve insert_wf_operand_list: ssa_insert.

Lemma insert_wf_insn_base : forall f b l1 n c instr 
  (Hnotin: let '(fdef_intro bs):= f in 
           ~ In (getCmdLoc c) (getBlocksLocs bs))
  (Huniq : NoDup (getBlockLocs b))
  (HwfI: wf_insn_base f b instr),
  wf_insn_base (insert_fdef l1 n c f) (insert_block l1 n c b) instr.
Proof.
  intros.
  inv HwfI.
  eapply insert_insnInFdefBlockB in H; eauto.
  eapply wf_insn_base_intro; eauto with ssa_insert.
Qed.

Hint Constructors wf_insn wf_value.

Lemma insert_lookupBlockViaLabelFromBlocks : forall l5 l1 n c bs b,
  lookupBlockViaLabelFromBlocks bs l5 = ret b ->
  lookupBlockViaLabelFromBlocks (List.map (insert_block l1 n c) bs) l5 = 
    ret (insert_block l1 n c b).
Proof.
  unfold lookupBlockViaLabelFromBlocks.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l5 l0); 
      subst; inv H; auto.
Qed.

Hint Resolve insert_lookupBlockViaLabelFromBlocks : ssa_insert.

Lemma insert_lookupBlockViaLabelFromFdef : forall f l5 b l1 n c,
  lookupBlockViaLabelFromFdef f l5 = ret b ->
  lookupBlockViaLabelFromFdef (insert_fdef l1 n c f) l5 = 
    ret (insert_block l1 n c b).
Proof.
  destruct f. simpl. intros. apply insert_lookupBlockViaLabelFromBlocks; auto.
Qed.

Lemma insert_lookupIDFromCmds : forall id5 n c cs,
  lookupIDFromCmds cs id5 = Some tt ->
  lookupIDFromCmds (insert_cmds n c cs) id5 = Some tt.
Proof. 
  intros.
  apply InGetCmdsLocs_lookupIDFromCmds.
  apply lookupIDFromCmds__InCmdsLocs in H.
  destruct (@insert_cmds_inv n c cs) as [cs1 [cs2 [J1 J2]]]; subst.
  rewrite J1. rewrite getCmdsLocs_app. rewrite getCmdsLocs_app in H.
  apply in_or_app. apply in_app_or in H. simpl.
  destruct H as [H | H]; auto.
Qed.

Lemma insert_lookupIDFromBlocks : forall id5 l1 n c bs,
  lookupIDFromBlocks bs id5 = Some tt ->
  lookupIDFromBlocks (List.map (insert_block l1 n c) bs) id5 = Some tt.
Proof.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    destruct (lookupIDFromPhiNodes p id5); auto.
    remember (lookupIDFromCmds c0 id5) as R2.
    destruct R2.
      inv H.
      destruct (l_dec l1 l0); subst.
        rewrite insert_lookupIDFromCmds; auto.
        rewrite <- HeqR2; auto.

      destruct (lookupIDFromCmds 
        (if l_dec l1 l0 then insert_cmds n c c0 else c0) id5).
        destruct u; auto.
        destruct (lookupIDFromTerminator t id5); auto.        
Qed.

Lemma insert_lookupIDFromFdef : forall f id5 l1 n c,
  lookupIDFromFdef f id5 = Some tt ->
  lookupIDFromFdef (insert_fdef l1 n c f) id5 = Some tt.
Proof.
  destruct f. simpl. intros. apply insert_lookupIDFromBlocks; auto.
Qed.

(*
Hint Resolve subst_lookupBlockViaLabelFromFdef: ssa_subst.
*)

Lemma insert_wf_value : forall f l1 n c v (Hwfv: wf_value f v),
  wf_value (insert_fdef l1 n c f) v.
Proof.
  intros.
  inv Hwfv; try constructor.
    apply insert_lookupIDFromFdef; auto.
Qed.

Hint Constructors wf_phi_operands.

Lemma insert_wf_phi_operands : forall f b l1 n c id' vls
  (Hnotin: let 'fdef_intro bs := f in ~ In (getCmdLoc c) (getBlocksLocs bs))
  (Hwf_pnops: wf_phi_operands f b id' vls),
  wf_phi_operands (insert_fdef l1 n c f) (insert_block l1 n c b) id' vls.
Proof.
  intros.
  induction Hwf_pnops; simpl; auto.
    eapply wf_phi_operands_cons_vid; eauto.
      eapply insert_lookupBlockViaIDFromFdef in H; eauto.
      eapply insert_lookupBlockViaLabelFromFdef in H0; eauto.
      autounfold.
      destruct H1 as [H1 | H1].
        rewrite <- insert_blockDominates; auto.
        rewrite <- insert_isReachableFromEntry; auto.
Qed.
     
Lemma insert_predOfBlock : forall l1 n c b,
  predOfBlock b = predOfBlock (insert_block l1 n c b).
Proof.
  destruct b; simpl; auto.
Qed.

Lemma insert_check_list_value_l : forall f b l1 n c vls
  (Hcl: check_list_value_l f b vls),
  check_list_value_l (insert_fdef l1 n c f) (insert_block l1 n c b) vls.
Proof.
  unfold check_list_value_l. destruct f as [bs]. simpl. intros until vls.
  repeat rewrite <- insert_genBlockUseDef_blocks.
  repeat rewrite <- insert_predOfBlock. auto.
Qed.

Hint Resolve insert_wf_phi_operands insert_check_list_value_l: ssa_insert.

Lemma insert_wf_phinode : forall f b l1 n c PN (HwfPN: wf_phinode f b PN)
  (Hnotin: let 'fdef_intro bs := f in ~ In (getCmdLoc c) (getBlocksLocs bs)),
  wf_phinode (insert_fdef l1 n c f) (insert_block l1 n c b) PN.
Proof.
  intros. destruct PN as [id' vls].
  unfold wf_phinode in *. simpl.
  destruct HwfPN as [Hwf_pnops Hcl].
  split; auto with ssa_insert.
Qed.

Hint Resolve insert_wf_value : ssa_insert.

Lemma insert_wf_value_list : forall
  l1 n c (fdef5 : fdef)
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
            (insert_fdef l1 n c fdef5, value_)) value_l_list)).
Proof.
  induction value_l_list; simpl; intros; auto.
    inv H.
    apply Cons_wf_value_list; auto.
    apply insert_wf_value; auto.  
Qed.

Hint Resolve insert_wf_value_list: ssa_insert.

Lemma insert_wf_insn : forall f b l1 n c instr (HwfI: wf_insn f b instr)
  (Hnotin: let 'fdef_intro bs := f in ~ In (getCmdLoc c) (getBlocksLocs bs))
  (Huniq : NoDup (getBlockLocs b)),
  wf_insn (insert_fdef l1 n c f) (insert_block l1 n c b) instr.
Proof.
  intros.

  Ltac DONE := 
  eauto with ssa_insert; try match goal with
  | H : wf_insn_base _ _ _ |- wf_insn_base _ _ _ => 
    eapply insert_wf_insn_base in H; eauto
  | H : wf_value _ ?v |- wf_value _ ?v => 
    eapply insert_wf_value  in H; eauto
  | H : lookupBlockViaLabelFromFdef _ ?l = Some _ |- 
        lookupBlockViaLabelFromFdef _ ?l = Some _  =>
    eapply insert_lookupBlockViaLabelFromFdef in H; eauto
  | H : insnInFdefBlockB _ _ _ = _ |- insnInFdefBlockB _ _ _ = _ =>
    eapply insert_insnInFdefBlockB in H; eauto
  | H : wf_phinode _ _ _ |- wf_phinode _ _ _ =>
    eapply insert_wf_phinode in H; eauto
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

Hint Resolve insert_wf_insn : ssa_insert.

Hint Constructors wf_phinodes.

Lemma insert_wf_phinodes : forall f b l1 n c PNs (HwfPNs: wf_phinodes f b PNs)
  (Hnotin: let 'fdef_intro bs := f in ~ In (getCmdLoc c) (getBlocksLocs bs))
  (Huniq : NoDup (getBlockLocs b)),
  wf_phinodes (insert_fdef l1 n c f) (insert_block l1 n c b) PNs.
Proof.
  intros. 
  induction HwfPNs; simpl; auto.
    eapply insert_wf_insn in H; eauto.
Qed.

Hint Constructors wf_cmds.

Lemma insnDominatesPos_insnDominates: forall i1 n b1 c
  (Huniq: NoDup (getBlockLocs b1)),
  insnDominatesPos i1 n b1 ->
  insnDominates i1 (insn_cmd c) (insert_block (getBlockLabel b1) n c b1).
Proof.
  unfold insnDominatesPos.
  destruct b1.
  intros.
  destruct H as [c2 [J1 J2]].
  simpl in *.
  destruct (l_dec l0 l0); try congruence.
  destruct J2 as [[ps1 [p1 [ps2 [EQ1 EQ2]]]] | 
                  [cs1 [c1 [cs2 [cs3 [EQ1 EQ2]]]]]]; subst.
    left. exists ps1. exists p1. exists ps2. split; auto.
    right. exists cs1. exists c1. exists cs2. exists (c2::cs3).
    split; auto.
      unfold insert_cmds. 
      apply NoDup_inv in Huniq. destruct Huniq as [_ Huniq].
      apply NoDup_inv in Huniq. destruct Huniq as [Huniq _].
      rewrite_env ((cs1 ++ c1 :: cs2) ++ c2 :: cs3) in J1.
      apply nth_error_firstn_skipn in J1; simpl_env in *; auto.
      destruct J1 as [J1 J2].
      rewrite J1. rewrite J2. simpl_env. auto.
Qed.

Lemma wf_insert__wf_value: forall f l1 n c v,
  wf_insert l1 n c f -> valueInCmdOperands v c -> 
  wf_value (insert_fdef l1 n c f) v.
Proof.
  intros.
  destruct v; constructor.
    apply valueInCmdOperands__InOps in H0.
    apply H in H0.
    destruct H0 as [H0 _].
    apply insert_lookupIDFromFdef; auto.
Qed.

Lemma insert_cmdInBlockB' : forall n c b,
  cmdInBlockB c (insert_block (getBlockLabel b) n c b) = true.
Proof.
  intros. unfold insert_block. destruct b. simpl.
  destruct (l_dec l0 l0); try congruence.
    apply insert_InCmdsB'.
Qed.

Lemma list_fdef_block_insn_id_spec: forall b c n f f1 b1 insn1 id1 ids1
  (H : In (f1, b1, insn1, id1)
        (unmake_list_fdef_block_insn_id
           (make_list_fdef_block_insn_id
              (map_list_id
                 (fun id_ : id =>
                  (insert_fdef (getBlockLabel b) n c f,
                  insert_block (getBlockLabel b) n c b, 
                  insn_cmd c, id_)) (make_list_id ids1))))),
  In id1 ids1 /\
    f1 = insert_fdef (getBlockLabel b) n c f /\
    b1 = insert_block (getBlockLabel b) n c b /\ insn1 = insn_cmd c.
Proof.
  induction ids1; simpl in *; intros.
    inv H.

    destruct H as [H | H].
      inv H; auto.
      apply IHids1 in H. destruct H as [J1 [J2 [J3 J4]]]; subst. auto.
Qed.

Lemma wf_insert__wf_insn_base: forall b n c f (Huniq: uniqFdef f)
  (HBinF: blockInFdefB b f = true)
  (HwfI: wf_insert (getBlockLabel b) n c f),
  wf_insn_base (insert_fdef (getBlockLabel b) n c f)
     (insert_block (getBlockLabel b) n c b) (insn_cmd c).
Proof.
  intros.
  destruct HwfI as [[block1 J1] [J2 [J3 G]]].
  assert (block1 = b) as EQ. 
    destruct block1.
    apply lookupBlockViaLabelFromFdef_inv in J1; auto.
    destruct J1 as [EQ J1]; subst.
    destruct b. simpl in *.
    eapply blockInFdefB_uniq in HBinF; eauto.  
      destruct HBinF as [EQ1 [EQ2 EQ3]]; subst. auto.
  subst.
  eapply uniqFdef__uniqBlockLocs in Huniq; eauto. 
  assert (cmdInFdefBlockB c (insert_fdef (getBlockLabel b) n c f)
            (insert_block (getBlockLabel b) n c b) = true) as HcInF'.
    simpl. apply andb_true_iff. 
    split. apply insert_cmdInBlockB'.
           apply insert_blockInFdefB; auto.
  eapply wf_insn_base_intro with (id_list:=make_list_id (getCmdOperands c)); 
    eauto.
    simpl. rewrite unmake_make_list_id; auto.

    apply wf_operand_list__intro.
    intros.  
    assert (In id1 (getCmdOperands c) /\ 
            f1 = insert_fdef (getBlockLabel b) n c f /\ 
            b1 = insert_block (getBlockLabel b) n c b /\ 
            insn1 = insn_cmd c) as J.
      apply list_fdef_block_insn_id_spec; auto.

    destruct J as [Hin [EQ1 [EQ2 EQ3]]]; subst.
    assert (Hin':=Hin).
    apply G in Hin'.
    destruct Hin' as [G1 [bi G2]].
    eapply wf_operand_intro with 
      (block':=insert_block (getBlockLabel b) n c bi); simpl; auto.
      apply insert_lookupBlockViaIDFromFdef; auto.
      intro J. inv J.

      unfold defs_dominate_pos in J3. 
      eapply J3 in J1; eauto.
        destruct J1 as [J1 | [J1 | J1]].
          left. apply insnDominatesPos_insnDominates; auto.
          right. left. apply insert_blockStrictDominates; auto.
          right. right. rewrite <- insert_isReachableFromEntry; auto.
Qed.

Lemma wf_insert__wf_cmd: forall b n c f (Huniq: uniqFdef f)
  (HBinF: blockInFdefB b f = true)
  (HwfI: wf_insert (getBlockLabel b) n c f),
  wf_insn (insert_fdef (getBlockLabel b) n c f)
     (insert_block (getBlockLabel b) n c b) (insn_cmd c).
Proof.
  intros.
  destruct c; simpl; intros; constructor;
    try solve [
      apply wf_insert__wf_value; simpl; auto |
      apply wf_insert__wf_insn_base; auto
    ]. 
Qed.

Lemma insert_wf_cmds : forall f b l1 n c Cs 
  (HBinF: blockInFdefB b f = true)
  (HwfCs: wf_cmds f b Cs) (HwfI: wf_insert l1 n c f)
  (Huniq: uniqFdef f),
  if (l_dec l1 (getBlockLabel b)) then
    wf_cmds (insert_fdef l1 n c f) (insert_block l1 n c b) (insert_cmds n c Cs)
  else
    wf_cmds (insert_fdef l1 n c f) (insert_block l1 n c b) Cs.
Proof.
  intros. 
  assert (Huniq' : NoDup (getBlockLocs b)).
    eapply uniqFdef__uniqBlockLocs in Huniq; eauto. 
  assert (Hnotin:= HwfI). destruct Hnotin as [_ [Hnotin _]].
  destruct (l_dec l1 (getBlockLabel b)); subst.
    apply wf_cmds_intro. 
    intros c0 Hin.
    unfold insert_cmds in Hin.
    assert (c0 = c \/ In c0 Cs) as J.
      rewrite <- firstn_skipn with (n:=n)(l:=Cs).
      apply in_app_or in Hin. simpl in Hin.
      destruct Hin as [Hin | [Hin | Hin]]; subst; auto.
        right. apply in_or_app. auto.
        right. apply in_or_app. auto.

    destruct J as [J | J]; subst.
      apply wf_insert__wf_cmd; auto.
    
      eapply wf_cmds_elim in HwfCs; eauto.
      eapply insert_wf_insn in HwfCs; eauto.

    induction HwfCs; simpl; auto.
      eapply insert_wf_insn in H; eauto.
Qed.

Lemma insert_wf_block : forall f b l1 n c (HwfB : wf_block f b)
  (HBinF: blockInFdefB b f = true)
  (HwfI: wf_insert l1 n c f) (Huniq: uniqFdef f),
  wf_block (insert_fdef l1 n c f) (insert_block l1 n c b).
Proof.
  intros.
  assert (Huniq' : NoDup (getBlockLocs b)).
    eapply uniqFdef__uniqBlockLocs in Huniq; eauto. 
  assert (Hnotin:= HwfI). destruct Hnotin as [_ [Hnotin _]].
  inv_wf_block HwfB; subst.
  match goal with
  | HBinF : blockInFdefB _ _ = _,
    HwfPNs : wf_phinodes _ _ _,
    HwfCs : wf_cmds _ _ _,
    Hwftmn : wf_insn _ _ _ |- _ =>
     eapply insert_blockInFdefB in HBinF; eauto;
     eapply insert_wf_phinodes in HwfPNs; eauto;
     eapply insert_wf_cmds with (l1:=l1)(n:=n) in HwfCs; eauto;
     eapply insert_wf_insn in Hwftmn; eauto
  end.
  simpl in HwfCs.
  apply wf_block_intro; eauto.
    destruct (l_dec l1 l5); subst; auto.
Qed.

Hint Resolve insert_wf_block : ssa_insert.

Hint Constructors wf_blocks.

Lemma insert_wf_blocks : forall f bs l1 n c (HwfBs : wf_blocks f bs)
  (Hincl: let '(fdef_intro bs0):=f in 
          forall b0, InBlocksB b0 bs -> InBlocksB b0 bs0)
  (HwfI: wf_insert l1 n c f) (Huniq : uniqBlocks bs) (Huniq' : uniqFdef f),
  wf_blocks (insert_fdef l1 n c f) (List.map (insert_block l1 n c) bs).
Proof.
  intros.
  induction HwfBs; simpl; auto.
    simpl_env in Huniq. apply uniqBlocks_inv in Huniq. inv Huniq.
    inv H0. simpl in *. simpl_env in H3.
    assert (blockInFdefB block5 fdef5 = true) as Hin1.
      destruct fdef5. simpl. apply Hincl.
      apply orb_true_iff. left. apply blockEqB_refl.
    assert (let 'fdef_intro bs0 := fdef5 in
            forall b0 : block, 
              InBlocksB b0 blocks5 -> InBlocksB b0 bs0) as Hin2.
      destruct fdef5. intros b0 J. apply Hincl.
      apply orb_true_iff. auto.
    apply wf_blocks_cons; eauto with ssa_insert.
Qed.

Hint Resolve insert_getEntryBlock insert_hasNonePredecessor insert_uniqFdef 
  insert_wf_blocks : ssa_insert.

Lemma insert_wf_fdef : forall f l1 n c (HwfI: wf_insert l1 n c f) 
  (HwfF: wf_fdef f), wf_fdef (insert_fdef l1 n c f).
Proof.
  intros.
  assert (Hnotin:= HwfI). destruct Hnotin as [_ [Hnotin _]].
  inv_wf_fdef HwfF.
  match goal with
  | Hentry : getEntryBlock _ = _,
    HuniqF : uniqFdef _,
    Hnpred : hasNonePredecessor _ _ = _,
    HwfBs : wf_blocks _ _ |- _ =>
     eapply insert_getEntryBlock in Hentry; eauto;
     eapply insert_hasNonePredecessor in Hnpred; eauto;
     eapply insert_wf_blocks in HwfBs; eauto;
     eapply insert_uniqFdef in HuniqF; eauto
  end.
  eapply wf_fdef_intro; eauto.
Qed.

(************** More Props **************************************)

Require Import removal.

Definition posDominatesInsn (n:nat) (instr:insn) (b2:block) : Prop :=
  let '(block_intro l2 ps2 cs2 tmn2) := b2 in
  exists c2, 
    List.nth_error cs2 n = Some c2 /\ 
    insnDominates (getCmdLoc c2) instr b2.

Lemma posDominatesInsn__insnDominates: forall c n instr' b' 
  (Huniq: NoDup (getBlockLocs b')),
  posDominatesInsn n instr' b' ->
  insnDominates (getCmdLoc c) instr' (insert_block (getBlockLabel b') n c b').
Proof.
  destruct b'. simpl. intros.
  destruct H as [c2 [J1 J2]].
  destruct (l_dec l0 l0); try congruence.
  destruct instr'; auto.
  destruct J2 as [[ps1 [p1 [ps2 [EQ1 EQ2]]]] | 
                  [cs1 [c1' [cs2 [cs3 [EQ1 EQ2]]]]]]; subst.
    apply NoDup_disjoint with (i0:=getPhiNodeID p1) in Huniq.
      contradict Huniq. apply InGetPhiNodesIDs_middle.
      rewrite EQ2. apply in_or_app. left. apply In_InCmdLocs.
      eapply nth_error_In; eauto.
      
    apply NoDup_inv in Huniq. destruct Huniq as [_ Huniq].
    apply NoDup_inv in Huniq. destruct Huniq as [Huniq _].
    assert (c1'=c2) as EQ. 
      apply getCmdLoc_getCmdID in EQ2.
      apply nth_error_In in J1.
      apply getCmdsLocs_uniq with (cs:=cs1 ++ c1' :: cs2 ++ c1 :: cs3); 
        auto using in_middle.
    subst.
    right. exists cs1. exists c. exists (c2::cs2). exists cs3.
    rewrite getCmdID_getCmdLoc.
    split; auto.
      unfold insert_cmds. 
      apply nth_error_firstn_skipn in J1; simpl_env in *; auto.
      destruct J1 as [J1 J2].
      rewrite J1. rewrite J2. simpl_env. auto.

  destruct J2 as [[[cs1 [c1' [cs2 [EQ1 EQ2]]]] |
                   [ps1 [p1 [ps2 [EQ1 EQ2]]]]] EQ]; subst.
    split; auto.
    apply NoDup_inv in Huniq. destruct Huniq as [_ Huniq].
    apply NoDup_inv in Huniq. destruct Huniq as [Huniq _].
    assert (c1'=c2) as EQ.
      apply getCmdLoc_getCmdID in EQ2.
      apply nth_error_In in J1.
      apply getCmdsLocs_uniq with (cs:=cs1 ++ c1' :: cs2); 
        auto using in_middle.
    subst.
    left. exists cs1. exists c. exists (c2::cs2).
    rewrite getCmdID_getCmdLoc.
    split; auto.
      unfold insert_cmds. 
      apply nth_error_firstn_skipn in J1; simpl_env in *; auto.
      destruct J1 as [J1 J2].
      rewrite J1. rewrite J2. simpl_env. auto.

    apply NoDup_disjoint with (i0:=getPhiNodeID p1) in Huniq.
      contradict Huniq. apply InGetPhiNodesIDs_middle.
      rewrite EQ2. apply in_or_app. left. apply In_InCmdLocs.
      eapply nth_error_In; eauto.
Qed.

Lemma insert_lookupBlockViaLabelFromBlocks_inv : forall l5 l1 n c bs b',
  lookupBlockViaLabelFromBlocks (List.map (insert_block l1 n c) bs) l5 = 
    Some b' ->
  exists b, lookupBlockViaLabelFromBlocks bs l5 = Some b /\
            b' = insert_block l1 n c b.
Proof.
  unfold lookupBlockViaLabelFromBlocks.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l5 l0); 
      subst; inv H; auto.
    exists (block_intro l0 p c0 t). unfold insert_block. auto.
Qed.

Lemma insert_lookupBlockViaLabelFromFdef_inv : forall l5 l1 n c f b',
  lookupBlockViaLabelFromFdef (insert_fdef l1 n c f) l5 = 
    Some b' ->
  exists b, lookupBlockViaLabelFromFdef f l5 = Some b /\
            b' = insert_block l1 n c b.
Proof.
  destruct f. simpl.
  apply insert_lookupBlockViaLabelFromBlocks_inv.
Qed.

Lemma insert_inGetCmdsLocs: forall id5 c n cs,
  id5 <> getCmdLoc c ->
  In id5 (getCmdsIDs (insert_cmds n c cs)) ->
  In id5 (getCmdsIDs cs).
Proof.
  unfold insert_cmds. intros.
  rewrite <- firstn_skipn with (n:=n)(l:=cs).
  rewrite getCmdsIDs_app. rewrite getCmdsIDs_app in H0.
  apply in_or_app.
  apply in_app_or in H0.
  destruct H0 as [H0 | H0]; auto.
  simpl in H0.
  remember (getCmdID c) as R.
  destruct R; auto.
    symmetry in HeqR.
    apply getCmdLoc_getCmdID in HeqR. subst.
    simpl in H0. 
    destruct H0 as [H0 | H0]; subst; auto.
      congruence.
Qed.

Lemma insert_inGetBlocksLocs: forall id5 c l0 n b,
  id5 <> getCmdLoc c ->
  In id5 (getBlockIDs (insert_block l0 n c b)) ->
  In id5 (getBlockLocs b).
Proof.
  destruct b. simpl.
  destruct (l_dec l0 l1); subst; intros.
    apply in_app_or in H0.
    apply in_or_app.
    destruct H0 as [H0 | H0]; auto.
    right.
    apply in_or_app.
    apply insert_inGetCmdsLocs in H0; auto.
    apply in_getCmdsIDs__in_getCmdsLocs in H0; auto.
    
    apply in_app_or in H0.
    apply in_or_app.
    destruct H0 as [H0 | H0]; auto.
    right.
    apply in_getCmdsIDs__in_getCmdsLocs in H0; auto.
    apply in_or_app; auto.
Qed.

Lemma insert_lookupBlockViaIDFromBlocks_inGetBlocksLocs: forall l0 n c bs id5,
  id5 <> getCmdLoc c ->
  lookupBlockViaIDFromBlocks (List.map (insert_block l0 n c) bs) id5 <> None ->
  In id5 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros; auto.
    apply in_or_app.
    destruct (in_dec eq_dec id5 (getBlockIDs (insert_block l0 n c a))).
      left. apply insert_inGetBlocksLocs in i0; auto.
      right. apply IHbs; auto.
Qed.

Lemma insert_lookupBlockViaIDFromBlocks_inv : forall id5 l1 n c bs b'
  (Huniq: NoDup (getBlocksLocs bs))
  (Hneq: id5 <> getCmdLoc c),
  lookupBlockViaIDFromBlocks (List.map (insert_block l1 n c) bs) id5 =
    Some b' ->
  exists b, lookupBlockViaIDFromBlocks bs id5 = Some b/\
            b' = insert_block l1 n c b.
Proof.
  induction bs; simpl; intros.
    congruence.

    destruct a. simpl in *.
    destruct (l_dec l1 l0); subst.
      destruct (in_dec eq_dec id5 (getPhiNodesIDs p ++ getCmdsIDs c0)).
        exists (block_intro l0 p c0 t). simpl. 
        destruct (l_dec l0 l0); try congruence.
        destruct (in_dec eq_dec id5 
          (getPhiNodesIDs p ++ getCmdsIDs (insert_cmds n c c0))).
          inv H. auto.
          apply NoDup_disjoint' with (i0:=id5) in Huniq; auto.
            contradict Huniq.
            assert (lookupBlockViaIDFromBlocks 
              (List.map (insert_block l0 n c) bs) id5 <> None) as G.
              rewrite H. intros J. inv J.
            apply insert_lookupBlockViaIDFromBlocks_inGetBlocksLocs in G; auto.

            apply in_app_or in i0. 
            apply in_or_app.
            destruct i0 as [i0 | i0]; auto. right.
            apply in_or_app.
            apply in_getCmdsIDs__in_getCmdsLocs in i0; auto.

        destruct (in_dec eq_dec id5 
          (getPhiNodesIDs p ++ getCmdsIDs (insert_cmds n c c0))).
          contradict n0.
          apply in_app_or in i0.
          apply in_or_app.
          destruct i0 as [i0 | i0]; auto.
          right.
          apply insert_inGetCmdsLocs in i0; auto.

          apply NoDup_inv in Huniq. destruct Huniq as [_ Huniq].
          apply IHbs in H; auto.
      destruct (in_dec eq_dec id5 (getPhiNodesIDs p ++ getCmdsIDs c0)).
        inv H.
        exists (block_intro l0 p c0 t). simpl.
        destruct (l_dec l1 l0); subst; try congruence.
          auto.

        apply NoDup_inv in Huniq. destruct Huniq as [_ Huniq].
        apply IHbs in H; auto.
Qed.

Lemma insert_lookupBlockViaIDFromFdef_inv : forall id5 l1 n c f b'
  (Huniq: uniqFdef f)
  (Hneq: id5 <> getCmdLoc c),
  lookupBlockViaIDFromFdef (insert_fdef l1 n c f) id5 =
    Some b' ->
  exists b, lookupBlockViaIDFromFdef f id5 = Some b /\
            b' = insert_block l1 n c b.
Proof.
  destruct f. simpl. intros.
  destruct Huniq. 
  apply insert_lookupBlockViaIDFromBlocks_inv; auto.
Qed.

Lemma insert_lookupCmdViaIDFromCmds_inv: forall id1 c n cs c0,
  id1 <> getCmdLoc c ->
  lookupCmdViaIDFromCmds (insert_cmds n c cs) id1 = Some c0 ->
    lookupCmdViaIDFromCmds cs id1 = Some c0.
Proof.
  unfold insert_cmds. intros.
  rewrite <- firstn_skipn with (l:=cs)(n:=n); auto.
  induction (firstn n cs); simpl in *.
    destruct (eq_atom_dec id1 (getCmdLoc c)); subst; auto.
      congruence.
    destruct (eq_atom_dec id1 (getCmdLoc a)); auto.
Qed.

Lemma insert_lookupCmdViaIDFromCmds_inv': forall id1 c n cs,
  lookupCmdViaIDFromCmds (insert_cmds n c cs) id1 = None ->
    lookupCmdViaIDFromCmds cs id1 = None.
Proof.
  unfold insert_cmds. intros.
  rewrite <- firstn_skipn with (l:=cs)(n:=n); auto.
  induction (firstn n cs); simpl in *.
    destruct (eq_atom_dec id1 (getCmdLoc c)); subst; auto.
      congruence.
    destruct (eq_atom_dec id1 (getCmdLoc a)); auto.
Qed.

Lemma insert_lookupInsnViaIDFromBlock_inv: forall id1 c l1 n b c0,
  id1 <> getCmdLoc c ->
  lookupInsnViaIDFromBlock (insert_block l1 n c b) id1 = Some c0 ->
    lookupInsnViaIDFromBlock b id1 = Some c0.
Proof.
  destruct b. simpl. intros.
  destruct (lookupPhiNodeViaIDFromPhiNodes p id1); auto.
  destruct (l_dec l1 l0); subst; auto.
  remember (lookupCmdViaIDFromCmds (insert_cmds n c c0) id1) as R.
  destruct R; inv H0.
  symmetry in HeqR.
  apply insert_lookupCmdViaIDFromCmds_inv in HeqR; auto.
  rewrite HeqR. auto.
Qed.

Lemma insert_lookupInsnViaIDFromBlock_inv': forall id1 c l1 n b,
  lookupInsnViaIDFromBlock (insert_block l1 n c b) id1 = None ->
    lookupInsnViaIDFromBlock b id1 = None.
Proof.
  destruct b. simpl. intros.
  destruct (lookupPhiNodeViaIDFromPhiNodes p id1); auto.
  destruct (l_dec l1 l0); subst; auto.
  remember (lookupCmdViaIDFromCmds (insert_cmds n c c0) id1) as R.
  destruct R; inv H.
  symmetry in HeqR.
  apply insert_lookupCmdViaIDFromCmds_inv' in HeqR; auto.
  rewrite HeqR. auto.
Qed.

Lemma insert_lookupInsnViaIDFromFdef_inv: forall id1 c l1 n f c0,
  id1 <> getCmdLoc c ->
  lookupInsnViaIDFromFdef (insert_fdef l1 n c f) id1 = Some c0 ->
    lookupInsnViaIDFromFdef f id1 = Some c0.
Proof.
  destruct f as [bs]. simpl.
  induction bs; simpl; intros; auto.
    remember (lookupInsnViaIDFromBlock (insert_block l1 n c a) id1) as R.
    destruct R.
      inv H0.
      symmetry in HeqR.
      apply insert_lookupInsnViaIDFromBlock_inv in HeqR; auto.
      rewrite HeqR. auto.

      symmetry in HeqR.
      apply insert_lookupInsnViaIDFromBlock_inv' in HeqR.
      rewrite HeqR. auto.
Qed.

(* l1.n must dominate all uses of id0 *)
Definition pos_dominates_uses l1 n (id0:id) (f:fdef) : Prop :=
forall block2 instr' block', 
  lookupBlockViaLabelFromFdef f l1 = Some block2 ->
  insnInFdefBlockB instr' f block' = true ->
  (not (isReachableFromEntry f block')) \/
  ((~ isPhiNode instr' ->
    removal.used_in_insn id0 instr' = true ->
    (posDominatesInsn n instr' block' /\ getBlockLabel block' = l1) \/
    blockStrictDominates f block2 block') /\
  (forall pid vls l0 block0,
    instr' = insn_phinode (insn_phi pid vls) ->
    In (value_id id0,l0) (unmake_list_value_l vls) ->
    lookupBlockViaLabelFromFdef f l0 = Some block0 ->
    blockDominates f block2 block0)).

Definition id_dominates_uses (id1:id) (id0:id) (f:fdef) : Prop :=
forall block2 instr' block',
  getInsnLoc instr' <> id1 ->
  lookupBlockViaIDFromFdef f id1 = Some block2 ->
  insnInFdefBlockB instr' f block' = true ->
  (not (isReachableFromEntry f block')) \/
  ((~ isPhiNode instr' ->
    removal.used_in_insn id0 instr' = true ->
    (insnDominates id1 instr' block' /\ 
     getBlockLabel block' = getBlockLabel block2) 
    \/
    blockStrictDominates f block2 block') /\
  (forall pid vls l0 block0,
    instr' = insn_phinode (insn_phi pid vls) ->
    In (value_id id0,l0) (unmake_list_value_l vls) ->
    lookupBlockViaLabelFromFdef f l0 = Some block0 ->
    blockDominates f block2 block0)).
     
Lemma insert_lookupBlockViaIDFromFdef_eq_inv : forall l1 n c f b
  (Hnotin: let '(fdef_intro bs):= f in 
           ~ In (getCmdLoc c) (getBlocksLocs bs)),
  lookupBlockViaLabelFromFdef f l1 = Some b ->
  lookupBlockViaIDFromFdef (insert_fdef l1 n c f) (getCmdLoc c) =
    Some (insert_block l1 n c b).
Proof.
  destruct f as [bs]. simpl. 
  induction bs; simpl; intros.
    inv H.
 
    destruct a. simpl in *.
    destruct (l_dec l1 l0); subst.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l0); 
        try congruence.

        inv H.
        destruct (in_dec eq_dec (getCmdLoc c)
          (getPhiNodesIDs p ++ getCmdsIDs (insert_cmds n c c0))).
          unfold insert_block. 
          destruct (l_dec l0 l0); auto; try congruence.

          contradict n0. apply in_or_app. right.
          assert (J:=@insert_getCmdsIDs c c0 n).
          rewrite getCmdID_getCmdLoc in J.
          destruct J as [cs1 [cs2 [J1 J2]]]; subst. rewrite J1.
          apply in_or_app. right. simpl. auto.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l1 l0); 
        try congruence.
      apply notin_app_inv in Hnotin. destruct Hnotin as [J1 J2].
      rewrite_env ((getPhiNodesIDs p ++ getCmdsLocs c0) ++ [getTerminatorID t]) 
        in J1.
      apply notin_app_inv in J1. destruct J1 as [J1 J3].
      destruct (in_dec eq_dec(getCmdLoc c) (getPhiNodesIDs p ++ getCmdsIDs c0));
        auto.
        contradict i0; auto. 
        intro J. apply J1. apply in_or_app.
        apply in_app_or in J. destruct J as [J | J]; auto.
        apply in_getCmdsIDs__in_getCmdsLocs in J; auto.
Qed.

Lemma insert_insnInFdefBlockB': forall l1 b n c f (Huniq: uniqFdef f),
  lookupBlockViaLabelFromFdef f l1 = Some b ->
  insnInFdefBlockB (insn_cmd c) (insert_fdef l1 n c f) (insert_block l1 n c b).
Proof.
  intros.
  destruct b as [l0 ps0 cs0 t0].
  apply lookupBlockViaLabelFromFdef_inv in H; auto.
  destruct H as [Heq H]; subst.
  apply andb_true_iff.
  split.
    assert (J:=@insert_cmdInBlockB' n c (block_intro l0 ps0 cs0 t0)). auto.
    apply insert_blockInFdefB; auto.
Qed.

Lemma insert_InBlocksB_inv : forall l1 n c b' bs,
  InBlocksB b' (List.map (insert_block l1 n c) bs) = true ->
  exists b, insert_block l1 n c b = b' /\ InBlocksB b bs = true.
Proof.
  induction bs; simpl; intros; auto.
    inv H.

    apply orb_prop in H.
    destruct H as [H | H].
      apply blockEqB_inv in H. subst.
      exists a. split; auto.
      apply orb_true_intro. left. apply blockEqB_refl.

      apply IHbs in H. destruct H as [b [J1 J2]]; subst.
      exists b. split; auto. apply orb_true_intro. auto.
Qed.

Lemma insert_blockInFdefB_inv : forall f l1 n c b',
  blockInFdefB b' (insert_fdef l1 n c f) = true ->
  exists b, insert_block l1 n c b = b' /\ blockInFdefB b f = true.
Proof.
  intros. destruct f. simpl in *.
  apply insert_InBlocksB_inv; auto.
Qed.

Lemma insert_cmdInBlockB_inv : forall l1 n c0 c b,
  getCmdLoc c <> getCmdLoc c0 ->
  cmdInBlockB c (insert_block l1 n c0 b) = true ->
  cmdInBlockB c b = true.
Proof.
  unfold insert_block. intros.
  destruct b.
  destruct (l_dec l1 l0); subst; auto.
  unfold insert_cmds in H0. simpl in *.
  rewrite <- firstn_skipn with (n:=n)(l:=c1).
  apply InCmdsB_in in H0.
  apply In_InCmdsB.
  apply in_or_app.
  apply in_app_or in H0.
  destruct H0 as [H0 | H0]; auto.
  simpl in H0.
  destruct H0; subst; auto.
    congruence.
Qed.

Lemma insert_insnInFdefBlockB_inv : forall f l1 n c b' instr
  (Hneq: getInsnLoc instr <> getCmdLoc c),
  insnInFdefBlockB instr (insert_fdef l1 n c f) b' = true ->
  exists b, insert_block l1 n c b = b' /\ insnInFdefBlockB instr f b = true.
Proof.
  unfold insnInFdefBlockB. intros.
  destruct instr; simpl.
    apply andb_true_iff in H. destruct H as [J1 J2].
    apply insert_blockInFdefB_inv in J2. 
    destruct J2 as [b [J3 J4]]; subst. 
    exists b. destruct b. simpl in *. split; auto.
    apply andb_true_iff; auto.

    apply andb_true_iff in H. destruct H as [J1 J2].
    apply insert_blockInFdefB_inv in J2. 
    destruct J2 as [b [J3 J4]]; subst. 
    exists b. split; auto.
    apply andb_true_iff. split; auto.
    eapply insert_cmdInBlockB_inv; eauto.

    apply andb_true_iff in H. destruct H as [J1 J2].
    apply insert_blockInFdefB_inv in J2. 
    destruct J2 as [b [J3 J4]]; subst. 
    exists b. destruct b. simpl in *. split; auto.
    apply andb_true_iff; auto.
Qed.

Lemma insert_dominates_uses: forall l1 n c id0 f (HwfI: wf_insert l1 n c f),
  wf_fdef f ->
  pos_dominates_uses l1 n id0 f ->
  id_dominates_uses (getCmdLoc c) id0 (insert_fdef l1 n c f).
Proof.
  intros.
  intros block2 instr' block' J0 J1 J2.
  destruct HwfI as [[b2 Hlk] [G1 G2]].
  assert (lookupBlockViaLabelFromFdef (insert_fdef l1 n c f) l1 = 
            Some (insert_block l1 n c b2)) as H1.
    apply insert_lookupBlockViaLabelFromFdef; auto.
  assert (exists b', insert_block l1 n c b' = block' /\
                     insnInFdefBlockB instr' f b' = true) as EQ.
    apply insert_insnInFdefBlockB_inv; auto.
  destruct EQ as [b' [H4 H3]]; subst. 
  rewrite <- insert_isReachableFromEntry; auto.
  assert (NoDup (getBlockLocs b')) as Huniq.
    apply insnInFdefBlockB__blockInFdefB in H3.
    eapply uniqFdef__uniqBlockLocs; eauto.
  eapply H0 in H3; eauto.
  destruct H3 as [H3 | [H4 H5]]; auto. 
  assert (Hlk':=Hlk).
  destruct b2. apply lookupBlockViaLabelFromFdef_inv in Hlk'; auto.
  destruct Hlk' as [Heq HBinF]; subst.
  assert (block2=insert_block l0 n c (block_intro l0 p c0 t)) as EQ. 
    apply insert_lookupBlockViaIDFromFdef_eq_inv with (n:=n)(c:=c) in Hlk; auto.
    rewrite Hlk in J1. 
    inv J1. auto.
  subst.
  right.
  split.
    intros H6 H7.
    apply H4 in H7; auto.
    destruct H7 as [[H71 H72] | H7]; subst.
      left. 
      split.
        apply posDominatesInsn__insnDominates; auto.
        unfold insert_block. destruct b'. simpl; auto. 
      right.
        apply insert_blockStrictDominates; auto.         
    intros pid vls l2 block0 H6 H7 H8; subst.
    assert (exists b0, lookupBlockViaLabelFromFdef f l2 = ret b0 /\ 
                       block0 = insert_block l0 n c b0) as H6.
      apply insert_lookupBlockViaLabelFromFdef_inv; auto.
    destruct H6 as [b0 [H9 H10]]; subst.
    eapply H5 in H7; eauto.
   apply insert_blockDominates; auto.
Qed.

Lemma inserted_in_getBlocksLocs : forall l1 n c bs 
  (Huniq:NoDup (getBlocksLabels bs)),
  In l1 (getBlocksLabels bs) ->
  In (getCmdLoc c) (getBlocksLocs (List.map (insert_block l1 n c) bs)).
Proof.
  intros.
  assert (J:=@insert_blocksLocs l1 n c bs Huniq).
  destruct (in_dec l_dec l1 (getBlocksLabels bs)).
    destruct J as [A [B [EQ1 EQ2]]].
    rewrite EQ1. apply in_middle.

    contradict H; auto.
Qed.

Lemma insert_insnInBlockB_eq_inv: forall i0 l1 n c b0, 
  ~ In (getCmdLoc c) (getBlockLocs b0) ->
  getInsnLoc i0 = getCmdLoc c ->
  insnInBlockB i0 (insert_block l1 n c b0) = true ->
  i0 = insn_cmd c.
Proof.
  destruct b0. simpl. intros.
  destruct (l_dec l1 l0); subst.
    destruct i0; simpl in *.
      contradict H. rewrite <- H0.
      apply in_or_app. left.
      apply InPhiNodesB_In in H1.
      apply getPhiNodeID_in_getPhiNodesIDs; auto.

      unfold insert_cmds in H1.
      apply InCmdsB_in in H1.
      assert (In c1 c0 \/ c1 = c) as EQ.
        rewrite <- firstn_skipn with (l:=c0)(n:=n).
        apply in_app_or in H1. simpl in H1.
        destruct H1 as [H1 | [H1 | H1]]; subst; auto.
          left. apply in_or_app; auto.
          left. apply in_or_app; auto.
      destruct EQ as [Hin | EQ]; subst; auto.
      contradict H. rewrite <- H0.
      apply in_or_app. right.
      apply in_or_app. left.
      apply getCmdLoc_in_getCmdsLocs; auto.

      apply terminatorEqB_inv in H1. subst.
      contradict H. rewrite <- H0.
      apply in_or_app. right.
      apply in_or_app. simpl. auto.

    destruct i0; simpl in *.
      contradict H. rewrite <- H0.
      apply in_or_app. left.
      apply InPhiNodesB_In in H1.
      apply getPhiNodeID_in_getPhiNodesIDs; auto.

      contradict H. rewrite <- H0.
      apply in_or_app. right.
      apply in_or_app. left.
      apply InCmdsB_in in H1.
      apply getCmdLoc_in_getCmdsLocs; auto.

      apply terminatorEqB_inv in H1. subst.
      contradict H. rewrite <- H0.
      apply in_or_app. right.
      apply in_or_app. simpl. auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
