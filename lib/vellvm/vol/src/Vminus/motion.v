Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vminus.
Require Import Lattice.
Import AtomSet.
Require Import removal.
Require Import subst.
Require Import vsubst.
Require Import insert.
Require Import renaming.

Definition gen_fresh_cmd (id0:id) (c:cmd) : cmd :=
match c with
| insn_bop _ bop0 v1 v2 => insn_bop id0 bop0 v1 v2
| insn_icmp _ cond0 v1 v2 => insn_icmp id0 cond0 v1 v2
end.

Definition motion_block (l1:l) (n:nat) (newid:id) (c:cmd) (b:block) : block :=
let b1 := insert_block l1 n (gen_fresh_cmd newid c) b in
let b2 := isubst_block (getCmdLoc c) newid b1 in
let b3 := remove_block (getCmdLoc c) b2 in
rename_block newid (getCmdLoc c) b3.

Definition motion_fdef (l1:l) (n:nat) (c:cmd) (f:fdef) : fdef :=
let '(fdef_intro bs) := f in
let 'ex_ids := getBlocksLocs bs in
let '(exist newid _) := AtomImpl.atom_fresh_for_list ex_ids in
let f1 := insert_fdef l1 n (gen_fresh_cmd newid c) f in
let f2 := isubst_fdef (getCmdLoc c) newid f1 in
let f3 := remove_fdef (getCmdLoc c) f2 in
rename_fdef newid (getCmdLoc c) f3.
 
(************** Code motion specification **************************************)

Inductive sp_motion_cmds (c:cmd) : cmds -> cmds -> Prop :=
| sp_motion_cmds_nil: sp_motion_cmds c nil nil
| sp_motion_cmds_cons_right: forall cs1 cs2,
    sp_motion_cmds c cs1 cs2 ->
    sp_motion_cmds c (c::cs1) cs2
| sp_motion_cmds_cons_left: forall cs1 cs2,
    sp_motion_cmds c cs1 cs2 ->
    sp_motion_cmds c cs1 (c::cs2)
| sp_motion_cmds_cons: forall c' cs1 cs2, 
    c <> c' ->
    sp_motion_cmds c cs1 cs2 ->
    sp_motion_cmds c (c'::cs1) (c'::cs2)
.

Inductive sp_motion_block (c:cmd) : block -> block -> Prop :=
| sp_motion_block_intro: forall l0 ps0 cs1 cs2 t0, 
  sp_motion_cmds c cs1 cs2 ->
  sp_motion_block c (block_intro l0 ps0 cs1 t0) (block_intro l0 ps0 cs2 t0)
.

Inductive sp_motion_blocks (c:cmd) : blocks -> blocks -> Prop :=
| sp_motion_blocks_nil: sp_motion_blocks c nil nil
| sp_motion_blocks_cons: forall b1 b2 bs1 bs2, 
  sp_motion_block c b1 b2 ->
  sp_motion_blocks c bs1 bs2 ->
  sp_motion_blocks c (b1::bs1) (b2::bs2)
.

Inductive sp_motion_fdef (c:cmd) : fdef -> fdef -> Prop :=
| sp_motion_fdef_intro: forall bs1 bs2, 
  sp_motion_blocks c bs1 bs2 ->
  sp_motion_fdef c (fdef_intro bs1) (fdef_intro bs2)
.

Hint Constructors sp_motion_cmds sp_motion_block sp_motion_blocks 
  sp_motion_fdef.

(************** Motion holds the spec **************************)

Lemma motion_value_holds_spec: forall oldid newid v,
  ~ In newid (getValueIDs v) ->
  rename_value newid oldid (subst.subst_value oldid (value_id newid) v) = v.
Proof.
  unfold rename_value, rename_id, subst.subst_value.
  destruct v; auto.
  destruct (id_dec i0 oldid); subst.
    destruct (id_dec newid newid); subst; auto.
      congruence.
    destruct (id_dec i0 newid); subst; auto.
      intros. contradict H. simpl. auto.
Qed.

Lemma motion_tmn_holds_spec: forall newid c t0,
  ~ In newid (getTerminatorOperands t0) -> 
  newid <> getTerminatorID t0 ->
  rename_tmn newid (getCmdLoc c) 
    (subst.subst_tmn (getCmdLoc c) (value_id newid) t0) = t0.
Proof.
  unfold subst.subst_tmn, rename_tmn. intros.
  destruct t0; simpl in *.
    rewrite motion_value_holds_spec; auto.
    rewrite rename_id_neq; auto.
   
    rewrite motion_value_holds_spec; auto.
    rewrite rename_id_neq; auto.

    rewrite rename_id_neq; auto.
Qed.

Lemma motion_list_value_l_holds_spec: forall newid c l0,
  ~ In newid (values2ids (list_prj1 _ _ (unmake_list_value_l l0))) ->
  (rename_list_value_l newid (getCmdLoc c)
        (subst.subst_list_value_l (getCmdLoc c) (value_id newid) l0)) = l0.
Proof.
  induction l0; simpl; intros; auto.
    destruct v.
      simpl_env in H. apply notin_app_inv in H. destruct H as [J1 J2].
      rewrite IHl0; auto.
      rewrite motion_value_holds_spec; auto.

      rewrite IHl0; auto.
Qed.

Lemma motion_phinodes_holds_spec: forall newid c ps0,
  (forall p, In p ps0 -> ~ In newid (getPhiNodeOperands p)) ->
  ~ In newid (getPhiNodesIDs ps0) ->
  ~ In (getCmdLoc c) (getPhiNodesIDs ps0) ->
  List.map (rename_phi newid (getCmdLoc c))
    (remove_phinodes (getCmdLoc c)
       (List.map (subst.subst_phi (getCmdLoc c) (value_id newid)) ps0)) = ps0.
Proof.
  unfold subst.subst_phi, rename_phi. 
  induction ps0; simpl in *; intros; auto.
    destruct a. simpl in *.
    destruct (id_dec i0 (getCmdLoc c)); subst; simpl.
      contradict H1; auto.

      rewrite IHps0; auto.
      rewrite rename_id_neq; auto.
      assert (insn_phi i0 l0 = insn_phi i0 l0 \/ In (insn_phi i0 l0) ps0) as J. 
        auto.
      apply H in J. simpl in J.
      rewrite motion_list_value_l_holds_spec; auto.
Qed.

Lemma getCmdLoc_fresh_cmd : forall newid c, 
  getCmdLoc (gen_fresh_cmd newid c) = newid.
Proof. destruct c; simpl; intros; auto. Qed.

Lemma subst_unused_in_vls: forall id1 v1 vls, 
  ~ In id1 (getValueIDs v1) ->
  used_in_list_value_l id1 (subst_list_value_l id1 v1 vls) = false.
Proof.
  induction vls; simpl; intros; auto.
    rewrite IHvls; auto.
    destruct v; simpl; auto.
      destruct (id_dec i0 id1); subst; simpl; auto.
        rewrite notin_unused_in_value; auto.
      destruct (id_dec i0 id1); subst; simpl; auto.
        congruence.
Qed.

Lemma subst_unused_in_phinodes: forall id1 v1 ps, 
  ~ In id1 (getValueIDs v1) ->
  fold_left (fun (re : bool) (p0 : phinode) => re || used_in_phi id1 p0)
     (List.map (subst_phi id1 v1) ps) false = false.
Proof.
  induction ps; simpl; intros; auto.
    destruct a. simpl.
    rewrite subst_unused_in_vls; auto.
Qed.

Lemma subst_unused_in_cmd: forall id1 v1 c, 
  ~ In id1 (getValueIDs v1) ->
  used_in_cmd id1 (subst_cmd id1 v1 c) = false.
Proof.
  destruct c; simpl; intro; auto.
    destruct v; destruct v0; simpl; auto.
      destruct (id_dec i1 id1); subst; simpl.
        destruct (id_dec i2 id1); subst; simpl.
          repeat rewrite notin_unused_in_value; auto.
          repeat rewrite notin_unused_in_value; auto.
          destruct (id_dec i2 id1); subst; simpl; auto; try congruence.

        destruct (id_dec i2 id1); subst; simpl.
          repeat rewrite notin_unused_in_value; auto.
          destruct (id_dec i1 id1); subst; simpl; auto; try congruence.
          destruct (id_dec i1 id1); subst; simpl; auto; try congruence.
          destruct (id_dec i2 id1); subst; simpl; auto; try congruence.
      destruct (id_dec i1 id1); subst; simpl.
        repeat rewrite notin_unused_in_value; auto.
        destruct (id_dec i1 id1); subst; simpl; auto; try congruence.

      destruct (id_dec i1 id1); subst; simpl.
        repeat rewrite notin_unused_in_value; auto.
        destruct (id_dec i1 id1); subst; simpl; auto; try congruence.
    destruct v; destruct v0; simpl; auto.
      destruct (id_dec i1 id1); subst; simpl.
        destruct (id_dec i2 id1); subst; simpl.
          repeat rewrite notin_unused_in_value; auto.
          repeat rewrite notin_unused_in_value; auto.
          destruct (id_dec i2 id1); subst; simpl; auto; try congruence.

        destruct (id_dec i2 id1); subst; simpl.
          repeat rewrite notin_unused_in_value; auto.
          destruct (id_dec i1 id1); subst; simpl; auto; try congruence.
          destruct (id_dec i1 id1); subst; simpl; auto; try congruence.
          destruct (id_dec i2 id1); subst; simpl; auto; try congruence.
      destruct (id_dec i1 id1); subst; simpl.
        repeat rewrite notin_unused_in_value; auto.
        destruct (id_dec i1 id1); subst; simpl; auto; try congruence.

      destruct (id_dec i1 id1); subst; simpl.
        repeat rewrite notin_unused_in_value; auto.
        destruct (id_dec i1 id1); subst; simpl; auto; try congruence.
Qed.

Lemma subst_unused_in_cmds: forall id1 v1 cs, 
  ~ In id1 (getValueIDs v1) ->
  fold_left (fun (re : bool) (c0 : cmd) => re || used_in_cmd id1 c0)
     (List.map (subst_cmd id1 v1) cs) false = false.
Proof.
  induction cs; simpl; intros; auto.
    rewrite subst_unused_in_cmd; auto.
Qed.

Lemma subst_unused_in_tmn: forall id1 v1 t, 
  ~ In id1 (getValueIDs v1) ->
  used_in_tmn id1 (subst_tmn id1 v1 t) = false.
Proof.
  destruct t; simpl; intro; auto.
    destruct v; simpl; auto.
      destruct (id_dec i1 id1); subst; simpl.
        repeat rewrite notin_unused_in_value; auto.
        destruct (id_dec i1 id1); subst; simpl; auto; try congruence.
    destruct v; simpl; auto.
      destruct (id_dec i1 id1); subst; simpl.
        repeat rewrite notin_unused_in_value; auto.
        destruct (id_dec i1 id1); subst; simpl; auto; try congruence.
Qed.

Lemma subst_unused_in_block: forall id1 v1 b, 
  ~ In id1 (getValueIDs v1) ->
  used_in_block id1 (subst_block id1 v1 b) = false. 
Proof.
  destruct b. simpl. intro.
  rewrite subst_unused_in_phinodes; auto.
  rewrite subst_unused_in_cmds; auto.
  rewrite subst_unused_in_tmn; auto.
Qed.

Lemma subst_unused_in_fdef: forall id1 v1 f, 
  ~ In id1 (getValueIDs v1) ->
  used_in_fdef id1 (subst_fdef id1 v1 f) = false. 
Proof.
  destruct f as [bs]. simpl. 
  intros.
  induction bs; simpl; auto.
    rewrite subst_unused_in_block; auto.
Qed.

Lemma rename_subst_value_eq: forall newid i0 v,
  ~ In newid (getValueIDs v) ->
  rename_value newid i0 (subst.subst_value i0 (value_id newid) v) = v.
Proof.
  destruct v; simpl; intros; auto.
    destruct (id_dec i1 i0); subst; simpl.
      rewrite rename_id_eq; auto.
      rewrite rename_id_neq; auto.
Qed.

Lemma rename_subst_fresh_cmd_eq: forall newid c,
  ~ In newid (getCmdOperands c) ->
  rename_cmd newid (getCmdLoc c)
    (subst.subst_cmd (getCmdLoc c) (value_id newid)
       (gen_fresh_cmd newid c)) = c.
Proof.
  destruct c; simpl; intros.
    rewrite rename_id_eq.
    apply notin_app_inv in H. destruct H as [J1 J2].
    rewrite rename_subst_value_eq; auto.
    rewrite rename_subst_value_eq; auto.

    rewrite rename_id_eq.
    apply notin_app_inv in H. destruct H as [J1 J2].
    rewrite rename_subst_value_eq; auto.
    rewrite rename_subst_value_eq; auto.
Qed.

Lemma rename_subst_fresh_cmd_eq': forall newid id1 a,
  ~ In newid (getCmdOperands a) ->
  newid <> getCmdLoc a ->
  rename_cmd newid id1
    (subst.subst_cmd id1 (value_id newid) a) = a.
Proof.
  destruct a; simpl; intros.
    rewrite rename_id_neq; auto.
    apply notin_app_inv in H. destruct H as [J1 J2].
    rewrite rename_subst_value_eq; auto.
    rewrite rename_subst_value_eq; auto.

    rewrite rename_id_neq; auto.
    apply notin_app_inv in H. destruct H as [J1 J2].
    rewrite rename_subst_value_eq; auto.
    rewrite rename_subst_value_eq; auto.
Qed.

Lemma sp_motion_cmds_middle_left_inv: forall cs1 c cs2 cs',
  sp_motion_cmds c (cs1++c::cs2) cs' -> sp_motion_cmds c (cs1++cs2) cs'.
Proof.
  intros.
  remember (cs1++c::cs2) as cs.
  generalize dependent cs1.
  generalize dependent cs2.
  induction H; intros; subst; auto.
    destruct cs1; inv Heqcs.
    destruct cs3; inv Heqcs; simpl; auto.
    destruct cs3; inv Heqcs; simpl; auto.
Qed.

Lemma sp_motion_cmds_cons_left_inv: forall cs c cs',
  sp_motion_cmds c (c::cs) cs' -> sp_motion_cmds c cs cs'.
Proof.
  intros.
  rewrite_env (nil++cs).
  eapply sp_motion_cmds_middle_left_inv; eauto.
Qed.

Lemma sp_motion_cmds_middle_right_inv: forall cs cs1' c cs2',
  sp_motion_cmds c cs (cs1'++c::cs2') -> sp_motion_cmds c cs (cs1'++cs2').
Proof.
  intros.
  remember (cs1'++c::cs2') as cs'.
  generalize dependent cs1'.
  generalize dependent cs2'.
  induction H; intros; subst; auto.
    destruct cs1'; inv Heqcs'.
    destruct cs1'; inv Heqcs'; simpl; auto.
    destruct cs1'; inv Heqcs'; simpl; auto.
Qed.

Lemma sp_motion_cmds_cons_right_inv: forall cs c cs',
  sp_motion_cmds c cs (c::cs') -> sp_motion_cmds c cs cs'.
Proof.
  intros.
  rewrite_env (nil++cs').
  eapply sp_motion_cmds_middle_right_inv; eauto.
Qed.

Lemma sp_motion_cmds_middle_split: forall cs1 c c1 cs2 cs',
  c1 <> c ->
  sp_motion_cmds c (cs1++c1::cs2) cs' -> 
  exists cs1', exists cs2', cs' = cs1'++c1::cs2' /\ 
    sp_motion_cmds c cs1 cs1' /\ sp_motion_cmds c cs2 cs2'.
Proof.
  intros.
  remember (cs1++c1::cs2) as cs.
  generalize dependent cs1.
  generalize dependent cs2.
  induction H0; intros; subst; auto.
    destruct cs1; inv Heqcs.
    destruct cs3; inv Heqcs; simpl; try congruence.
      destruct (@IHsp_motion_cmds cs0 cs3) as [A [B [J1 [J2 J3]]]]; subst; auto.
      exists A. exists B. split; auto.
      
    destruct (@IHsp_motion_cmds cs0 cs3) as [A [B [J1 [J2 J3]]]]; subst; auto.
    exists (c::A). exists B. split; auto.
        
    destruct cs3; inv Heqcs; simpl.
      exists nil. exists cs2. split; auto.

      destruct (@IHsp_motion_cmds cs0 cs3) as [A [B [J1 [J2 J3]]]]; subst; auto.
      exists (c0::A). exists B. split; auto.
Qed.

Lemma sp_motion_cmds_app: forall c cs1 cs1' cs2 cs2',
  sp_motion_cmds c cs1 cs1' ->
  sp_motion_cmds c cs2 cs2' ->
  sp_motion_cmds c (cs1++cs2) (cs1'++cs2').
Proof.
  intros. 
  induction H; simpl; auto.
Qed.

Lemma sp_motion_cmds_trans: forall c cs1 cs2 cs3
  (H1: sp_motion_cmds c cs1 cs2)
  (H2: sp_motion_cmds c cs2 cs3),
  sp_motion_cmds c cs1 cs3.
Proof.
  intros. 
  generalize dependent cs3.
  induction H1; intros; inv H2; auto.
    apply sp_motion_cmds_cons_left_inv in H. auto.

    rewrite_env (nil ++ c' :: cs2) in H0.
    apply sp_motion_cmds_middle_split in H0; auto.
    destruct H0 as [A [B [J1 [J2 J3]]]]; subst.
    constructor.
    rewrite_env (nil ++ c' :: cs1).
    apply sp_motion_cmds_app; auto.
Qed.

Lemma sp_motion_cmds_middle_insert: forall c cs1 cs1' cs2 cs2',
  sp_motion_cmds c cs1 cs1' ->
  sp_motion_cmds c cs2 cs2' ->
  sp_motion_cmds c (cs1++cs2) (cs1'++c::cs2').
Proof.
  intros. 
  induction H; simpl; auto.
Qed.

Lemma sp_motion_cmds_refl: forall c cs, sp_motion_cmds c cs cs.
Proof.
  intros. 
  induction cs; simpl; auto.
    destruct (cmd_dec a c); subst; auto.
Qed.

Lemma motion_cmds_holds_spec_helper: forall c newid cs0
  (G: forall c0, In c0 cs0 -> getCmdLoc c0 = getCmdLoc c -> c0 = c),
  (forall c0, In c0 cs0 -> ~ In newid (getCmdOperands c0)) ->
  ~ In newid (getCmdsLocs cs0) ->
  ~ In newid (getCmdOperands c) ->
  newid <> getCmdLoc c ->
 sp_motion_cmds c cs0
   (List.map (rename_cmd newid (getCmdLoc c))
      (remove_cmds (getCmdLoc c)
         (List.map (subst.subst_cmd (getCmdLoc c) (value_id newid)) cs0))).
Proof.
  induction cs0; simpl; intros; auto.
    apply IHcs0 in H1; auto.
    rewrite getCmdLoc_subst_cmd.
    destruct (id_dec (getCmdLoc a) (getCmdLoc c)); simpl.
      assert (a=c) as EQ. apply G; auto.
      subst. auto.

      assert (a<>c) as NEQ. 
        destruct (cmd_dec a c); subst; auto.
      rewrite rename_subst_fresh_cmd_eq'; auto.
Qed.

Lemma motion_cmds_holds_spec: forall l1 l0 newid c cs0 n
  (G: forall c0, In c0 cs0 -> getCmdLoc c0 = getCmdLoc c -> c0 = c),
  (forall c0, In c0 cs0 -> ~ In newid (getCmdOperands c0)) ->
  ~ In newid (getCmdsLocs cs0) ->
  ~ In newid (getCmdOperands c) ->
  newid <> getCmdLoc c ->
  sp_motion_cmds c cs0
    (List.map (rename_cmd newid (getCmdLoc c))
      (remove_cmds (getCmdLoc c)
          (List.map (subst.subst_cmd (getCmdLoc c) (value_id newid))
              (if l_dec l1 l0
               then insert_cmds n (gen_fresh_cmd newid c) cs0
               else cs0)))).
Proof.
  intros l1 l0.
  destruct (l_dec l1 l0); subst; simpl; auto.
    unfold insert_cmds. intros.
    rewrite <- firstn_skipn with (n:=n)(l:=cs0) at 1.
    rewrite List.map_app. simpl. 
    destruct (@remove_cmds_neq (getCmdLoc c) 
      (List.map (subst.subst_cmd (getCmdLoc c) (value_id newid)) (skipn n cs0))
      (subst.subst_cmd (getCmdLoc c) (value_id newid) (gen_fresh_cmd newid c))
      (List.map (subst.subst_cmd (getCmdLoc c) (value_id newid)) (firstn n cs0)))
      as [cs1 [cs2 [J1 [J2 J3]]]]; subst.
      rewrite getCmdLoc_subst_cmd. rewrite getCmdLoc_fresh_cmd. auto.
    rewrite J1. clear J1.
    rewrite List.map_app. simpl. 
    rewrite rename_subst_fresh_cmd_eq; auto.
    apply sp_motion_cmds_trans with (cs2:=
      List.map (rename_cmd newid (getCmdLoc c))
        (remove_cmds (getCmdLoc c)
           (List.map (subst.subst_cmd (getCmdLoc c) (value_id newid))
              (firstn n cs0))) ++
      List.map (rename_cmd newid (getCmdLoc c))
           (remove_cmds (getCmdLoc c)
              (List.map (subst.subst_cmd (getCmdLoc c) (value_id newid))
                 (skipn n cs0)))).
      apply sp_motion_cmds_app.      
        apply motion_cmds_holds_spec_helper; auto.
          intros. apply G; auto. 
          rewrite <- firstn_skipn with (n:=n)(l:=cs0).
          apply in_or_app; auto.

          intros. apply H; auto. 
          rewrite <- firstn_skipn with (n:=n)(l:=cs0).
          apply in_or_app; auto.

          intros J. apply H0.
          rewrite <- firstn_skipn with (n:=n)(l:=cs0). 
          rewrite getCmdsLocs_app. apply in_or_app; auto.
        apply motion_cmds_holds_spec_helper; auto.
          intros. apply G; auto. 
          rewrite <- firstn_skipn with (n:=n)(l:=cs0).
          apply in_or_app; auto.

          intros. apply H; auto. 
          rewrite <- firstn_skipn with (n:=n)(l:=cs0).
          apply in_or_app; auto.

          intros J. apply H0.
          rewrite <- firstn_skipn with (n:=n)(l:=cs0). 
          rewrite getCmdsLocs_app. apply in_or_app; auto.

      apply sp_motion_cmds_middle_insert; apply sp_motion_cmds_refl.

    induction cs0; simpl; intros; auto.
      apply motion_cmds_holds_spec_helper; auto.
Qed.

Lemma motion_block_holds_spec: forall l1 n newid c b
  (G: forall c0, cmdInBlockB c0 b = true -> 
      getCmdLoc c0 = getCmdLoc c -> c0 = c),
  (forall i0, insnInBlockB i0 b = true -> 
      ~ In newid (getInsnOperands i0)) ->
  ~ In newid (getBlockLocs b) ->
  ~ In newid (getCmdOperands c) ->
  newid <> getCmdLoc c ->
  (match b with
   | block_intro _ ps0 _ _ => ~ In (getCmdLoc c) (getPhiNodesIDs ps0)
   end) ->
  sp_motion_block c b (motion_block l1 n newid c b).
Proof.
  destruct b as [l0 ps0 cs0 t0].
  unfold motion_block. simpl. intros.
  apply notin_app_inv in H0. destruct H0 as [J1 J2].
  apply notin_app_inv in J2. destruct J2 as [J2 J3].
  assert (newid <> getTerminatorID t0) as J4.
    intro J. apply J3. simpl; auto.
  assert (~ In newid (getTerminatorOperands t0)). 
    assert (insnInBlockB (insn_terminator t0) (block_intro l0 ps0 cs0 t0) 
      = true ) as G0. simpl. apply terminatorEqB_refl.
    apply H in G0. auto.
  rewrite motion_tmn_holds_spec; auto.
  assert (forall p : phinode, In p ps0 -> ~ In newid (getPhiNodeOperands p)).
    intros.
    assert (insnInBlockB (insn_phinode p) (block_intro l0 ps0 cs0 t0) 
      = true ) as G0. simpl. apply In_InPhiNodesB; auto.
    apply H in G0. auto.
  rewrite motion_phinodes_holds_spec; auto.
  constructor.
  assert (forall c0 : cmd, In c0 cs0 -> getCmdLoc c0 = getCmdLoc c -> c0 = c).
    intros. apply G; auto. apply In_InCmdsB; auto.
  assert (forall c0 : cmd, In c0 cs0 -> ~ In newid (getCmdOperands c0)).
    intros.
    assert (insnInBlockB (insn_cmd c0) (block_intro l0 ps0 cs0 t0) 
      = true ) as G0. simpl. apply In_InCmdsB; auto.
    apply H in G0. auto.
  apply motion_cmds_holds_spec; auto.
Qed.

Lemma motion_blocks_holds_spec: forall l1 n newid c bs,
  (forall b, InBlocksB b bs ->
    (match b with
     | block_intro _ ps0 _ _ => ~ In (getCmdLoc c) (getPhiNodesIDs ps0)
     end) /\
    (forall c0, cmdInBlockB c0 b = true -> 
        getCmdLoc c0 = getCmdLoc c -> c0 = c) /\
    (forall i0, insnInBlockB i0 b = true -> 
        ~ In newid (getInsnOperands i0))) ->
  ~ In newid (getBlocksLocs bs) ->
  ~ In newid (getCmdOperands c) ->
  newid <> getCmdLoc c ->
  sp_motion_blocks c bs (List.map (motion_block l1 n newid c) bs).
Proof.
  induction bs; intros; auto.
    simpl in H0. apply notin_app_inv in H0.
    destruct H0 as [J1 J2].
    simpl.
    constructor.
      assert (InBlocksB a (a::bs)) as J.
        simpl.
        apply orb_true_iff. left. apply blockEqB_refl.
      apply H in J.
      destruct J as [J3 [J4 J5]].
      apply motion_block_holds_spec; auto.

      apply IHbs; auto.
      intros. 
      assert (InBlocksB b (a::bs)) as J.
        simpl.
        apply orb_true_iff. right. auto.
      apply H in J.
      destruct J as [J3 [J4 J5]]. auto.
Qed.

Lemma motion_fdef_holds_spec: forall l1 n c f (HwfF:wf_fdef f)
  (Hin: lookupInsnViaIDFromFdef f (getCmdLoc c) = Some (insn_cmd c)),
  sp_motion_fdef c f (motion_fdef l1 n c f).
Proof.
  unfold motion_fdef. destruct f as [bs].
  remember (atom_fresh_for_list (getBlocksLocs bs)) as R.
  destruct R as [newid G]. clear HeqR.
  intros. simpl. repeat rewrite map_map.
  constructor. 
  assert (HwfF':=HwfF). 
  inv HwfF'.
  apply motion_blocks_holds_spec; auto.
    intros [l0 ps0 cs0 t0] HBinBs.
    eapply wf_blocks__wf_block in HBinBs; eauto.
    assert (HwfB:=HBinBs). 
    inv HBinBs.
    split.
      intro J. 
      eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in J; eauto.
      destruct J as [p2 [J1 J2]].
      rewrite J1 in Hin. inv Hin.
    split.
      intros c0 HcInB Heq.
      eapply IngetCmdsIDs__lookupCmdViaIDFromFdef with (c1:=c0) in H8; eauto.
        rewrite Heq in H8. rewrite H8 in Hin. inv Hin. auto.
        simpl in HcInB. apply InCmdsB_in; auto.

      eapply notin_getInsnOperands; eauto.

    clear H0 H2.
    apply lookupInsnViaIDFromFdef__insnInFdefBlockB in Hin.
    destruct Hin as [b1 Hin]. destruct b1.
    assert (J:=Hin).
    apply insnInFdefBlockB__blockInFdefB in Hin.
    apply insnInFdefBlockB__insnInBlockB in J.
    eapply notin_getInsnOperands in J; eauto.
      apply wf_fdef__blockInFdefB__wf_block in Hin; auto.
  
    simpl in Hin.
    apply lookupInsnViaIDFromBlocks__In in Hin.
    destruct (id_dec newid (getCmdLoc c)); subst; auto.
Qed.
 
(************** Another isubst for code motion ********************************)

Definition wf_msubst f id1 id2 : Prop :=
  (forall b i0, insnInFdefBlockB i0 f b = true -> 
                getInsnLoc i0 = id1 -> 
                ~ In id2 (getInsnOperands i0)) /\
  (forall b i0, insnInFdefBlockB i0 f b = true -> 
     ~ In id1 (getInsnOperands i0)) /\
  (exists b1 : block, lookupBlockViaIDFromFdef f id1 = ret b1).

Lemma isubst_used_in_insn: forall id1 instr id2
  (H : ~ In id1 (getInsnOperands instr))
  (H2 : ListSet.set_In id1 (getInsnOperands (isubst_insn id2 id1 instr))),
  used_in_insn id2 instr = true.
Proof.
  intros.
  destruct instr.
    destruct p; simpl in *.
    induction l0; simpl in *.
      inv H2.
      destruct v; simpl in *; auto.
      destruct (id_dec i1 id2); simpl in *; auto.
      destruct H2 as [H2 | H2]; subst; auto.
  
    destruct c; simpl in *.
      destruct v; destruct v0; simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto.
        destruct (id_dec i2 id2); simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto. 
        destruct (id_dec i1 id2); simpl in *; auto.
      destruct v; destruct v0; simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto.
        destruct (id_dec i2 id2); simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto. 
        destruct (id_dec i1 id2); simpl in *; auto.
  
    destruct t; simpl in *; auto.
      destruct v; simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto.
      destruct v; simpl in *; auto.
        destruct (id_dec i1 id2); simpl in *; auto.
Qed.

Lemma msubst_wf_operand : forall instr id1 id2 f b i0
  (HwfM: wf_msubst f id1 id2)
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f)
  (H1 : wf_operand f b instr i0) (Hdom: id_dominates_uses id1 id2 f),
   wf_operand (isubst_fdef id2 id1 f) (isubst_block id2 id1 b)
     (isubst_insn id2 id1 instr) (subst_id id2 id1 i0).
Proof.
  intros. destruct HwfM as [J1 [J2 G1]].
  inv H1.
  apply isubst_In_getInsnOperands with (id1:=id1)(id2:=id2) in H2; auto.
  rewrite subst_isPhiNode with (id':=id2)(v':=value_id id1) in H4; auto.
  unfold subst_id in *.
  destruct (id_dec i0 id2); subst.
    destruct G1 as [b1 G1].
    eapply wf_operand_intro; try solve 
      [eauto with ssa_subst | autounfold; eauto with ssa_subst].   
      autounfold.
      rewrite <- subst_insnDominates; eauto 
        using insnInFdefBlockB__insnInBlockB.
      rewrite <- subst_blockStrictDominates.
      rewrite <- subst_isReachableFromEntry; auto.
      unfold id_dominates_uses in Hdom.
      assert (used_in_insn id2 instr = true) as G4.
        clear - J2 H H2.
        apply J2 in H. clear J2.
        apply isubst_used_in_insn in H2; auto.
      assert (getInsnLoc instr <> id1) as G5.
        destruct (id_dec (getInsnLoc instr) id1); subst; auto.
        apply J1 in H; auto.
        contradict H. apply used_in_insn__getInsnOperands; auto.
      apply Hdom with (block2:=b1) in H; auto.
      destruct H as [G3 | [G6 _]]; auto.
      rewrite <- subst_isPhiNode in H4.
      apply G6 in H4; auto.
      destruct H4 as [[H4 _] | H4]; auto.

    eapply wf_operand_intro; try solve 
      [eauto with ssa_subst | autounfold; eauto with ssa_subst].   
      autounfold.
      rewrite <- subst_insnDominates; eauto using insnInFdefBlockB__insnInBlockB.
      rewrite <- subst_blockStrictDominates.
      rewrite <- subst_isReachableFromEntry; auto.
Qed.

Hint Resolve msubst_wf_operand: ssa_subst.

Hint Constructors wf_operand_list.

Lemma msubst_wf_operand_list : forall instr id1 id2 f b id_list0
  (HwfM: wf_msubst f id1 id2)
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f)
  (H2 : wf_operand_list
         (make_list_fdef_block_insn_id
            (map_list_id (fun id_ : id => (f, b, instr, id_)) id_list0)))
  (Hdom: id_dominates_uses id1 id2 f),
  wf_operand_list
   (make_list_fdef_block_insn_id
      (map_list_id
         (fun id_ : id =>
          (isubst_fdef id2 id1 f, isubst_block id2 id1 b,
          isubst_insn id2 id1 instr, id_)) (subst_list_id id2 id1 id_list0))).
Proof.
  induction id_list0; simpl; intros; auto.
    inv H2.
    destruct (id_dec i0 id2); subst; simpl; auto with ssa_subst.
Qed.

Hint Resolve msubst_wf_operand_list: ssa_subst.

Lemma msubst_wf_insn_base : forall f b id1 id2 instr 
  (HwfM: wf_msubst f id1 id2)
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f)
  (HwfI: wf_insn_base f b instr) (Hdom: id_dominates_uses id1 id2 f),
  wf_insn_base (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) 
    (isubst_insn id2 id1 instr).
Proof.
  intros.
  inv HwfI.
  eapply subst_insnInFdefBlockB in H; eauto.
  eapply wf_insn_base_intro; eauto with ssa_subst.
Qed.

Hint Constructors wf_insn wf_value.

Lemma msubst_wf_value : forall f id1 id2 v (Hwfv: wf_value f v)
  (HwfM: wf_msubst f id1 id2)
  (Hdom: id_dominates_uses id1 id2 f) (Huniq:uniqFdef f),
  wf_value (isubst_fdef id2 id1 f) (isubst_value id2 id1 v).
Proof.
  intros. destruct HwfM as [J1 [J2 G1]].
  inv Hwfv; try constructor.
    simpl. 
    autounfold.
    destruct (id_dec id5 id2); subst; 
      constructor; rewrite <- subst_lookupIDFromFdef; auto.    
      destruct G1 as [b1 G1].
      assert (G1':=G1).
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in G1.
      apply lookupBlockViaIDFromFdef__blockInFdefB in G1'.
      eapply inGetBlockIDs__lookupIDFromFdef; eauto.
Qed.

Hint Constructors wf_phi_operands.

Lemma msubst_wf_phi_operands_aux : forall f b id1 id2 id' (HwfF: wf_fdef f)
  (HwfM: wf_msubst f id1 id2)
  (Hdom: id_dominates_uses id1 id2 f)
  vls 
  (Hwf_pnops: wf_phi_operands f b id' vls) vls0 
  (HPhiInF: insnInFdefBlockB 
              (insn_phinode (insn_phi id' (app_list_value_l vls0 vls)))
              f b = true),
   wf_phi_operands (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) id'
    (subst_list_value_l id2 (value_id id1) vls).
Proof. 
  intros. 
  generalize dependent vls0.
  induction Hwf_pnops; intros; simpl; auto.
    assert (H0':=H0).
    apply subst_lookupBlockViaLabelFromFdef with (id':=id2)(v':=value_id id1) 
      in H0; auto.
    destruct (id_dec vid1 id2); subst.
      destruct HwfM as [J1 [J2 G1]].
      destruct G1 as [vb1 J].
      eapply wf_phi_operands_cons_vid; eauto.
        eapply subst_lookupBlockViaIDFromFdef in J; eauto.

        autounfold.
        rewrite <- subst_blockDominates; auto.
        rewrite <- subst_isReachableFromEntry; auto.
        unfold id_dominates_uses in Hdom.
        remember ((insn_phinode
                   (insn_phi id'
                     (app_list_value_l vls0
                       (Cons_list_value_l (value_id id2) l1 vls))))) as instr.
        assert (used_in_insn id2 instr = true) as G4.
          subst. clear. simpl.
          induction vls0; simpl.
            destruct (id_dec id2 id2); simpl; auto. 
            rewrite IHvls0. destruct (used_in_value id2 v); auto.
        assert (getInsnLoc instr <> id1) as G5.
          destruct (id_dec (getInsnLoc instr) id1); subst; simpl; auto.
          apply J1 in HPhiInF; simpl; auto.
          contradict HPhiInF. apply used_in_insn__getInsnOperands; auto.
        apply Hdom with (block2:=vb1) in HPhiInF; auto.
        destruct HPhiInF as [G3 | [_ G6]]; auto.
        apply G6 with (l0:=l1)(block0:=b1) in Heqinstr; auto.
          clear. induction vls0; simpl; auto.

       apply IHHwf_pnops with (vls0:=app_list_value_l vls0 
          (Cons_list_value_l (value_id id2) l1 Nil_list_value_l)); auto.
         rewrite <- app_list_value_l_cons; auto.

      rewrite subst_isReachableFromEntry with (id':=id2)(v':=value_id id1) 
        in H1; auto.
      eapply wf_phi_operands_cons_vid; eauto.
        eapply subst_lookupBlockViaIDFromFdef in H; eauto.
        autounfold.
        destruct H1 as [H1 | H1]; auto.
          rewrite <- subst_blockDominates; auto.

       apply IHHwf_pnops with (vls0:=app_list_value_l vls0 
          (Cons_list_value_l (value_id vid1) l1 Nil_list_value_l)); auto.
         rewrite <- app_list_value_l_cons; auto. 

    constructor.
      apply IHHwf_pnops with (vls0:=app_list_value_l vls0 
        (Cons_list_value_l (value_const c1) l1 Nil_list_value_l)); auto.
        rewrite <- app_list_value_l_cons; auto.
Qed.

Lemma msubst_wf_phi_operands : forall f b id1 id2 id' vls (HwfF: wf_fdef f)
  (HwfM: wf_msubst f id1 id2)
  (HPhiInF: insnInFdefBlockB (insn_phinode (insn_phi id' vls))
              f b = true)
  (Hwf_pnops: wf_phi_operands f b id' vls) 
  (Hdom: id_dominates_uses id1 id2 f),
  wf_phi_operands (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) id'
    (subst_list_value_l id2 (value_id id1) vls).
Proof.
  intros.
  eapply msubst_wf_phi_operands_aux with (vls0:=Nil_list_value_l); eauto.
Qed.

Hint Resolve msubst_wf_phi_operands: ssa_subst.

Lemma msubst_wf_phinode : forall f b id1 id2 PN (HwfF: wf_fdef f) 
  (HwfM: wf_msubst f id1 id2)
  (HPhiInF: insnInFdefBlockB (insn_phinode PN) f b = true)
  (HwfPN: wf_phinode f b PN) (Hdom: id_dominates_uses id1 id2 f),
  wf_phinode (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) 
    (isubst_phi id2 id1 PN).
Proof.
  intros. destruct PN as [id' vls].
  unfold wf_phinode in *. simpl.
  destruct HwfPN as [Hwf_pnops Hcl].
  split; auto with ssa_subst.
    autounfold. auto with ssa_subst.
Qed.

Hint Resolve msubst_wf_value : ssa_subst.

Lemma msubst_wf_value_list : forall
  (id1 id2 : id)
  (fdef5 : fdef) (Huniq: uniqFdef fdef5)
  (block5 : block)
  (value_l_list : list_value_l)
  (HwfM: wf_msubst fdef5 id1 id2)
  (Hdom: id_dominates_uses id1 id2 fdef5)
  (H : wf_value_list
        (make_list_fdef_value
           (map_list_value_l
              (fun (value_ : value) (_ : l) => (fdef5, value_)) value_l_list))),
   wf_value_list
     (make_list_fdef_value
        (map_list_value_l
           (fun (value_ : value) (_ : l) =>
            (isubst_fdef id2 id1 fdef5, value_))
           (subst_list_value_l id2 (value_id id1) value_l_list))).
Proof.
  induction value_l_list; simpl; intros; auto.
    inv H.
    apply Cons_wf_value_list; auto.
    apply msubst_wf_value; auto.  
Qed.

Hint Resolve msubst_wf_value_list: ssa_subst.

Lemma msubst_wf_insn : forall f b id1 id2 instr (HwfF: wf_fdef f) 
  (HwfM: wf_msubst f id1 id2)
  (HwfI: wf_insn f b instr)
  (Huniq : NoDup (getBlockLocs b)) (Hdom: id_dominates_uses id1 id2 f),
  wf_insn (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) 
    (isubst_insn id2 id1 instr).
Proof.
  intros.

  Ltac DONE := 
  eauto with ssa_subst; try match goal with
  | H : wf_insn_base _ _ _ |- wf_insn_base _ _ _ => 
    eapply msubst_wf_insn_base in H; eauto
  | H : wf_value _ ?v |- wf_value _ (?v {[ _ // _ ]}) => 
    eapply msubst_wf_value  in H; eauto
  | H : lookupBlockViaLabelFromFdef _ ?l = Some _ |- 
        lookupBlockViaLabelFromFdef _ ?l = Some _  =>
    eapply subst_lookupBlockViaLabelFromFdef in H; eauto
  | H : insnInFdefBlockB _ _ _ = _ |- insnInFdefBlockB _ _ _ = _ =>
    eapply subst_insnInFdefBlockB in H; eauto
  | H : wf_phinode _ _ _ |- wf_phinode _ _ _ =>
    eapply msubst_wf_phinode in H; eauto
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

Hint Resolve msubst_wf_insn : ssa_subst.
Hint Constructors wf_phinodes.

Lemma msubst_wf_phinodes : forall f b id1 id2 PNs (HwfF: wf_fdef f)
  (HwfM: wf_msubst f id1 id2)
  (HwfPNs: wf_phinodes f b PNs)
  (Huniq : NoDup (getBlockLocs b)) (Hdom: id_dominates_uses id1 id2 f),
  wf_phinodes (isubst_fdef id2 id1 f) (isubst_block id2 id1 b)
    (List.map (isubst_phi id2 id1) PNs).
Proof.
  intros. 
  induction HwfPNs; simpl; auto.
    eapply msubst_wf_insn in H; eauto.
Qed.

Hint Constructors wf_cmds.

Lemma msubst_wf_cmds : forall f b id1 id2 Cs (HwfF: wf_fdef f)
  (HwfM: wf_msubst f id1 id2)
  (HwfCs: wf_cmds f b Cs)
  (Huniq : NoDup (getBlockLocs b)) (Hdom: id_dominates_uses id1 id2 f),
  wf_cmds (isubst_fdef id2 id1 f) 
          (isubst_block id2 id1 b)
          (List.map (isubst_cmd id2 id1) Cs).
Proof.
  intros. 
  induction HwfCs; simpl; auto.
    eapply msubst_wf_insn in H; eauto.
Qed.

Lemma msubst_wf_block : forall f b id1 id2 (HwfF: wf_fdef f)
  (HwfM: wf_msubst f id1 id2)
  (HwfB : wf_block f b)
  (Huniq : NoDup (getBlockLocs b)) (Hdom: id_dominates_uses id1 id2 f),
  wf_block (isubst_fdef id2 id1 f) (isubst_block id2 id1 b).
Proof.
  intros.
  inv_wf_block HwfB; subst.
  match goal with
  | HBinF : blockInFdefB _ _ = _,
    HwfPNs : wf_phinodes _ _ _,
    HwfCs : wf_cmds _ _ _,
    Hwftmn : wf_insn _ _ _ |- _ =>
     eapply subst_blockInFdefB in HBinF; eauto;
     eapply msubst_wf_phinodes in HwfPNs; eauto;
     eapply msubst_wf_cmds in HwfCs; eauto;
     eapply msubst_wf_insn in Hwftmn; eauto
  end.
  apply wf_block_intro; eauto.
Qed.

Hint Resolve msubst_wf_block : ssa_subst.

Hint Constructors wf_blocks.

Lemma msubst_wf_blocks : forall f bs id1 id2 (HwfF: wf_fdef f)
  (HwfM: wf_msubst f id1 id2)
  (HwfBs : wf_blocks f bs)
  (Huniq : uniqBlocks bs) (Hdom: id_dominates_uses id1 id2 f),
  wf_blocks (isubst_fdef id2 id1 f) (List.map (isubst_block id2 id1) bs).
Proof.
  intros.
  induction HwfBs; simpl; auto.
    simpl_env in Huniq. apply uniqBlocks_inv in Huniq. inv Huniq.
    inv H0. simpl in *. simpl_env in H3.
    apply wf_blocks_cons; eauto with ssa_subst.
Qed.

Hint Resolve msubst_wf_blocks : ssa_subst.

Lemma msubst_wf_fdef: forall id1 id2 f (HwfF:wf_fdef f)
  (HwfM: wf_msubst f id1 id2)
  (Hdom: id_dominates_uses id1 id2 f),
  wf_fdef (isubst_fdef id2 id1 f).
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
     eapply msubst_wf_blocks in HwfBs; eauto;
     eapply subst_uniqFdef in HuniqF; eauto
  end.
  eapply wf_fdef_intro; eauto.
Qed.

(************** Motion preserves well-formedness **************************)

Definition wf_motion l1 n c f : Prop :=
  (exists block1, lookupBlockViaLabelFromFdef f l1 = Some block1) /\
  defs_dominate_pos l1 n c f /\
  pos_dominates_uses l1 n (getCmdLoc c) f /\
  (forall id1, 
    In id1 (getCmdOperands c) ->
    lookupIDFromFdef f id1 = Some tt /\
    exists b1, lookupBlockViaIDFromFdef f id1 = Some b1) /\
  (exists b, insnInFdefBlockB (insn_cmd c) f b = true /\ 
             isReachableFromEntry f b).

Lemma gen_fresh_cmd__getCmdOperands: forall newid c,
  getCmdOperands (gen_fresh_cmd newid c) = getCmdOperands c.
Proof. destruct c; auto. Qed.

Lemma wf_motion__wf_insert: forall l1 n c f
  (Hwfm : wf_motion l1 n c f)
  (newid : atom) 
  (Hnotin : let '(fdef_intro bs):=f in ~ In newid (getBlocksLocs bs)),
  wf_insert l1 n (gen_fresh_cmd newid c) f.
Proof.
  intros.
  destruct Hwfm as [G1 [G2 [G3 [G4 G5]]]]. destruct f as [bs].
  split; auto.
  rewrite getCmdLoc_fresh_cmd.
  split; auto.
  split.
    clear - G2.
    unfold defs_dominate_pos in *.
    intros. subst.
    eapply G2; eauto.
    rewrite gen_fresh_cmd__getCmdOperands in H1. auto.

    intros. apply G4.
    rewrite gen_fresh_cmd__getCmdOperands in H. auto.
Qed.

Lemma remove_wf_renaming: forall id1 id2 f 
  (H: forall b t, insnInFdefBlockB (insn_terminator t) f b -> 
      getTerminatorID t <> id1)
  (Hneq: id2 <> id1),
  wf_renaming (remove_fdef id1 f) id2 id1.
Proof.
  intros. destruct f as [bs].
  split; auto.
    simpl. apply remove_notin_getBlocksLocs; auto.
Qed.

Lemma wf_insert__wf_msubst: forall bs newid c l1 n
  (W: exists bc, insnInFdefBlockB (insn_cmd c) (fdef_intro bs) bc = true /\
                 isReachableFromEntry (fdef_intro bs) bc)
  (HwfF : wf_fdef (fdef_intro bs))
  (Hnotin : ~ In newid (getBlocksLocs bs))
  (HwfI : wf_insert l1 n (gen_fresh_cmd newid c) (fdef_intro bs)),
  wf_msubst (insert_fdef l1 n (gen_fresh_cmd newid c) (fdef_intro bs)) newid
    (getCmdLoc c).
Proof.
  intros.
  destruct HwfI as [G1 [G2 G3]].
  split. 
    intros. subst.
    assert (H':=H).
    apply insnInFdefBlockB__insnInBlockB in H.
    apply insnInFdefBlockB__blockInFdefB in H'.
    apply insert_blockInFdefB_inv in H'.
    destruct H' as [b0 [Heq H']]; subst.
    apply insert_insnInBlockB_eq_inv in H.
      destruct i0; tinv H; simpl in *.
      assert (getCmdOperands c = getCmdOperands c0) as EQ.
        destruct c0; destruct c; inv H; simpl; auto.
      clear H. rewrite <- EQ.
      destruct W as [bc [W1 W2]].
      intro J.
      apply wf_insn_base__non_selfref with (f:=fdef_intro bs)(b:=bc) in J; auto.
      apply wf_insn__wf_insn_base.
        intro K. inv K.
        apply andb_true_iff in W1. destruct W1 as [W1 W3].
        destruct bc.
        simpl in W1. apply InCmdsB_in in W1.
        apply wf_fdef__wf_cmd; simpl; auto.
  
      rewrite getCmdLoc_fresh_cmd. intro K. apply Hnotin.
      simpl in H'.
      eapply in_getBlockLocs__in_getBlocksLocs in H'; eauto.

      rewrite getCmdLoc_fresh_cmd. auto.
        
  split. 
    intros.
    destruct (id_dec (getInsnLoc i0) (getCmdLoc (gen_fresh_cmd newid c))).
      assert (H':=H).
      apply insnInFdefBlockB__insnInBlockB in H.
      apply insnInFdefBlockB__blockInFdefB in H'.
      apply insert_blockInFdefB_inv in H'.
      destruct H' as [b0 [Heq H']]; subst.
      apply insert_insnInBlockB_eq_inv in H; auto.
        destruct i0; tinv H; simpl in *.
        assert (getCmdOperands c = getCmdOperands c0) as EQ.
          destruct c0; destruct c; inv H; simpl; auto.
        clear H. rewrite <- EQ.
        destruct W as [bc [W1 W2]].
        apply andb_true_iff in W1. destruct W1 as [W1 W3].
        destruct bc.
        assert (HwfB:=HwfF).
        apply wf_fdef__blockInFdefB__wf_block with (b:=block_intro l0 p c1 t) 
          in HwfF; auto.
        eapply notin_getInsnOperands with (i0:=insn_cmd c) in HwfF; eauto.

        rewrite getCmdLoc_fresh_cmd. intro K. apply Hnotin.
        simpl in H'.
        eapply in_getBlockLocs__in_getBlocksLocs in H'; eauto.

      apply insert_insnInFdefBlockB_inv in H; auto.
      destruct H as [b0 [Heq H]]; subst. 
      assert (H':=H).
      apply insnInFdefBlockB__insnInBlockB in H.
      apply insnInFdefBlockB__blockInFdefB in H'.
      destruct b0 as [l0 ps0 cs0 t0].
      apply wf_fdef__blockInFdefB__wf_block in H'; auto.
      eapply notin_getInsnOperands; eauto.

    destruct G1 as [b1 G1].
    destruct b1. apply lookupBlockViaLabelFromFdef_inv in G1; auto.
    destruct G1 as [Heq G]; subst.
    exists (insert_block l0 n (gen_fresh_cmd newid c) 
             (block_intro l0 p c0 t)).
    apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
      apply insert_uniqFdef; auto.
    
      simpl in *.
      destruct (l_dec l0 l0); try congruence.
      apply in_or_app. right.
      assert (J:=@insert_getCmdsIDs (gen_fresh_cmd newid c) c0 n).
      rewrite getCmdID_getCmdLoc in J.
      destruct J as [cs1 [cs2 [J1 J2]]]; subst. rewrite J1.
      rewrite getCmdLoc_fresh_cmd. apply in_middle.
    
      apply insert_blockInFdefB; auto.     
Qed.

Lemma motion_wf_fdef: forall l1 n c f (HwfF:wf_fdef f)
  (Hwfm: wf_motion l1 n c f),
  wf_fdef (motion_fdef l1 n c f).
Proof.
  intros.
  unfold motion_fdef. destruct f as [bs].
  destruct (atom_fresh_for_list (getBlocksLocs bs)) as [newid Hnotin].
  assert (wf_insert l1 n (gen_fresh_cmd newid c) (fdef_intro bs)) as HwfI.
    apply wf_motion__wf_insert; auto.
  destruct Hwfm as [G1 [G2 [G3 [G4 G5]]]].
  assert (newid <> getCmdLoc c) as Hneq.
    destruct (id_dec newid (getCmdLoc c)); subst; auto.
    destruct G5 as [b [J1 J2]].
    apply andb_true_iff in J1.
    destruct J1 as [J11 J12].
    apply cmdInBlockB__inGetBlockIDs in J11.
    simpl in J12.
    eapply in_getBlockLocs__in_getBlocksLocs in J12; eauto.
  apply rename_wf_fdef.
    apply remove_wf_fdef.
      apply msubst_wf_fdef.
        apply insert_wf_fdef; auto.
 
        apply wf_insert__wf_msubst; auto.

        rewrite <- getCmdLoc_fresh_cmd with (newid:=newid) (c:=c) at 1.
        apply insert_dominates_uses; auto.

      apply subst_unused_in_fdef.
        intro J. simpl in J. destruct J as [J | J]; auto.

    apply remove_wf_renaming; auto.
      destruct G5 as [b [J1 J2]].
      apply insert_insnInFdefBlockB with (l1:=l1)(n:=n)
        (c:=gen_fresh_cmd newid c) in J1.
      apply subst_insnInFdefBlockB with (id0:=getCmdLoc c)
        (v0:=value_id newid) in J1.
      intros. 
      assert (exists c', 
        subst_insn (getCmdLoc c) (value_id newid) (insn_cmd c) =
        insn_cmd c' /\ getCmdLoc c = getCmdLoc c') as W.
        clear. 
        destruct c; simpl; eauto.
      destruct W as [c' [EQ1 EQ2]].
      rewrite EQ1 in J1.
      apply getTerminatorID__neq__getCmdLoc with (t:=t)(b1:=b0) in J1; 
        simpl; auto.
        rewrite EQ2. auto.
        apply wf_fdef__uniqFdef in HwfF.
        apply insert_uniqFdef with (l1:=l1)(c:=gen_fresh_cmd newid c)
          (n:=n) in HwfF; auto.
          apply subst_uniqFdef with (id0:=getCmdLoc c)
            (v0:=value_id newid) in HwfF; auto.
          simpl in HwfF. inv HwfF; auto.

          rewrite getCmdLoc_fresh_cmd. auto.
Qed.

(************** Bisimulation for code motion **************************)

Definition related_ECs c0 (f1 f2:fdef) (ec1 ec2:ExecutionContext) : Prop :=
let '(mkEC b1 cs1 tmn1 lc1) := ec1 in
let '(mkEC b2 cs2 tmn2 lc2) := ec2 in
isReachableFromEntry f1 b1 /\
blockInFdefB b1 f1 = true /\
blockInFdefB b2 f2 = true /\
(forall id', id' <> getCmdLoc c0 -> lookupAL _ lc1 id' = lookupAL _ lc2 id') /\
sp_motion_block c0 b1 b2 /\
sp_motion_cmds c0 cs1 cs2 /\
(exists l1, exists ps1, exists cs1', exists cs2',
b1 = block_intro l1 ps1 (cs1'++cs1) tmn1 /\
b2 = block_intro l1 ps1 (cs2'++cs2) tmn2).

Definition motionable_EC c (ec:ExecutionContext) : Prop :=
match ec with
| mkEC _ (c'::_) _ _ => c = c'
| _ => False
end.

Lemma bisimulation_cmd_case1 : forall c F F' B cs tmn lc S2 gvs3
  (Hrel: related_ECs c F F'
           {|
           CurBB := B;
           CurCmds := c :: cs;
           Terminator := tmn;
           Locals := lc |} S2),
  related_ECs c F F'
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
  destruct J as [Hreach1 [HBinF1 [HBinF2 [Heq1 [Hbtrans [Hcstrans
      [l3 [ps1 [cs1' [cs2' [Heq2 Heq3]]]]]]]]]]]; subst.
  destruct (id_dec (getCmdLoc c) (getCmdLoc c)); subst; simpl; try congruence.
  repeat split; auto.
    intros id' Hneq.
    rewrite <- lookupAL_updateAddAL_neq; auto. 

    apply sp_motion_cmds_cons_left_inv; auto.

    exists l3. exists ps1. exists (cs1' ++ [c]). exists cs2'. 
    simpl_env. auto.
Qed.

Lemma bisimulation_cmd_case2 : forall c F F' B cs tmn lc S1 gvs3
  (Hrel: related_ECs c F F' S1
           {|
           CurBB := B;
           CurCmds := c :: cs;
           Terminator := tmn;
           Locals := lc |}),
  related_ECs c F F' S1
    {|
    CurBB := B;
    CurCmds := cs;
    Terminator := tmn;
    Locals := updateAddAL GenericValue lc (getCmdLoc c) gvs3 |} /\
  trace_nil = trace_nil.
Proof.
  intros.
  destruct S1 as [b1 cs1 tmn1 lc1].
  assert (J:=Hrel); simpl in J.
  destruct J as [Hreach1 [HBinF1 [HBinF2 [Heq1 [Hbtrans [Hcstrans
      [l3 [ps1 [cs1' [cs2' [Heq2 Heq3]]]]]]]]]]]; subst.
  destruct (id_dec (getCmdLoc c) (getCmdLoc c)); subst; simpl; try congruence.
  repeat split; auto.
    intros id' Hneq.
    rewrite <- lookupAL_updateAddAL_neq; auto. 

    apply sp_motion_cmds_cons_right_inv; auto.

    exists l3. exists ps1. exists cs1'. exists (cs2' ++ [c]). 
    simpl_env. auto.
Qed.

Lemma sp_motion_fdef__getEntryBlockSome: forall c0 f f' b,
  sp_motion_fdef c0 f f' ->
  getEntryBlock f = Some b ->
  exists b', getEntryBlock f' = Some b' /\ sp_motion_block c0 b b'.
Proof.
  intros.
  inv H. 
  inv H1; inv H0; simpl. eauto.
Qed.

Lemma sp_motion_fdef__getEntryBlockNone: forall c0 f f',
  sp_motion_fdef c0 f f' ->
  getEntryBlock f = None ->
  getEntryBlock f' = None.
Proof.
  intros. inv H.
  inv H1; inv H0; auto.
Qed.

Lemma sp_motion_fdef__vertexes_fdef: forall c0 f f',
  sp_motion_fdef c0 f f' ->
  (forall v, vertexes_fdef f v <-> vertexes_fdef f' v).
Proof.
  intros. inv H.
  unfold vertexes_fdef. simpl.
  induction H0; simpl; auto.
    destruct v. split; auto.

    destruct v. inv H.
    simpl. 
    split; intro J.
      destruct J as [Heq | J]; subst; auto.
        right. eapply IHsp_motion_blocks; eauto.
      destruct J as [Heq | J]; subst; auto.
        right. eapply IHsp_motion_blocks; eauto.
Qed.

Require Import Maps.

Lemma sp_motion_fdef__arcs_fdef: forall c0 f f',
  sp_motion_fdef c0 f f' ->
  (forall a, arcs_fdef f a <-> arcs_fdef f' a).
Proof.
  intros. inv H.
  unfold arcs_fdef. simpl.
  induction H0; simpl; auto.
    destruct a. split; auto.

    destruct a as [[] []]. inv H.
    unfold Kildall.successors_list.
    destruct (eq_atom_dec l0 a0); subst.
      rewrite ATree.gss. rewrite ATree.gss. split; auto.
      rewrite ATree.gso; auto. rewrite ATree.gso; auto.
Qed.

Lemma sp_motion__isReachableFromEntry : forall c0 f f' b b',
  sp_motion_fdef c0 f f' ->
  sp_motion_block c0 b b' ->
  (isReachableFromEntry f b <-> isReachableFromEntry f' b').
Proof.
  intros.
  unfold isReachableFromEntry. 
  inv H0. unfold reachable.
  remember (getEntryBlock f) as R.
  destruct R.  
    symmetry in HeqR.
    eapply sp_motion_fdef__getEntryBlockSome in HeqR; eauto.
    destruct HeqR as [b' [J1 J2]].
    rewrite J1. inv J2.
    split; intro J.
      destruct J as [vl [al J]].
      exists vl. exists al.
      eapply Dipaths.D_walk_iff; eauto.
        eapply sp_motion_fdef__vertexes_fdef; eauto.
        eapply sp_motion_fdef__arcs_fdef; eauto.

      destruct J as [vl [al J]].
      exists vl. exists al.
      eapply Dipaths.D_walk_iff; eauto.
        intro x.
        eapply sp_motion_fdef__vertexes_fdef with (v:=x) in H; eauto.
        split; eapply H; eauto.

        intro x.
        eapply sp_motion_fdef__arcs_fdef with (a:=x) in H; eauto.
        split; eapply H; eauto.

    symmetry in HeqR.
    eapply sp_motion_fdef__getEntryBlockNone in HeqR; eauto.
    rewrite HeqR. split; auto.
Qed.

Lemma eval_rhs_spec : forall f b c0 lc lc'
  (Hreach: isReachableFromEntry f b) (HwfF:wf_fdef f)
  (Hwfc : wf_insn_base f b (insn_cmd c0))
  (Heq1 : forall id' : id,
         id' <> getCmdLoc c0 ->
         lookupAL GenericValue lc id' = lookupAL GenericValue lc' id'),
  OpsemDom.eval_rhs lc c0 = OpsemDom.eval_rhs lc' c0.
Proof.
  intros.
  unfold OpsemDom.eval_rhs.
  destruct c0; simpl in *.
    unfold BOP.
    destruct v; simpl.
      assert (i1 <> i0) as Hneq1.
        eapply wf_insn_base__non_selfref in Hwfc; simpl; eauto.
      rewrite Heq1; auto. 
      destruct v0; simpl; auto.
        assert (i2 <> i0) as Hneq2.
          eapply wf_insn_base__non_selfref in Hwfc; simpl; eauto.
        rewrite Heq1; auto. 
  
      destruct v0; simpl; auto.
        assert (i1 <> i0) as Hneq1.
          eapply wf_insn_base__non_selfref in Hwfc; simpl; eauto.
        rewrite Heq1; auto. 
    unfold ICMP.
    destruct v; simpl.
      assert (i1 <> i0) as Hneq1.
        eapply wf_insn_base__non_selfref in Hwfc; simpl; eauto.
      rewrite Heq1; auto. 
      destruct v0; simpl; auto.
        assert (i2 <> i0) as Hneq2.
          eapply wf_insn_base__non_selfref in Hwfc; simpl; eauto.
        rewrite Heq1; auto. 
  
      destruct v0; simpl; auto.
        assert (i1 <> i0) as Hneq1.
          eapply wf_insn_base__non_selfref in Hwfc; simpl; eauto.
        rewrite Heq1; auto. 
Qed.

Definition wf_motion' (f f':fdef) c0 : Prop :=
  lookupInsnViaIDFromFdef f (getCmdLoc c0) = Some (insn_cmd c0) /\
  lookupInsnViaIDFromFdef f' (getCmdLoc c0) = Some (insn_cmd c0) /\
  (exists b, wf_insn_base f b (insn_cmd c0) /\ isReachableFromEntry f b).
(* FIXME: Can we remove the 3rd condition? Moving instructions of unreachable
          blocks to other unreachable blocks shouls be fine. *)

Lemma getOperandValue_inTmnOperans_sim : forall
  (f f': fdef)
  (tmn : terminator)
  (lc lc' : GVMap)
  (HwfF : wf_fdef f) (HwfF' : wf_fdef f')
  (l1 : l)
  (ps1 : phinodes) c0 (Hwfm: wf_motion' f f' c0)
  (cs1 cs1': list cmd) (Htrans: sp_motion_fdef c0 f f')
  (Hbtrans: sp_motion_block c0 (block_intro l1 ps1 cs1 tmn)
     (block_intro l1 ps1 cs1' tmn))
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn) f = true)
  (HbInF' : blockInFdefB (block_intro l1 ps1 cs1' tmn) f' = true)
  (l0 l0': list atom)
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (HeqR' : ret l0' = inscope_of_tmn f' (block_intro l1 ps1 cs1' tmn) tmn)
  (Hinscope: OpsemDom.wf_defs f lc l0) (Hinscope': OpsemDom.wf_defs f' lc' l0')
  (Heq1 : forall id' : id,
          id' <> getCmdLoc c0 ->
          lookupAL GenericValue lc id' = lookupAL GenericValue lc' id')
  (v : value)
  (Hvincs : valueInTmnOperands v tmn) gv gv'
  (Hget' : getOperandValue v lc' = Some gv')
  (Hget : getOperandValue v lc = Some gv),
  gv = gv'.
Proof.
  intros.
  destruct v as [vid | vc]; simpl in Hget, Hget'; try congruence.
  destruct (id_dec vid (getCmdLoc c0)); subst.
    assert (HwfInstr:=HbInF).
    eapply wf_fdef__wf_tmn in HwfInstr; eauto.
    assert (OpsemDom.wf_GVs f lc (getCmdLoc c0) gv) as Hwfg.
      eapply OpsemDom.state_tmn_typing; eauto.
        apply valueInTmnOperands__InOps; auto.
    assert (OpsemDom.wf_GVs f' lc' (getCmdLoc c0) gv') as Hwfg'.
      eapply OpsemDom.state_tmn_typing; eauto.
        erewrite sp_motion__isReachableFromEntry in Hreach; eauto.
        eapply wf_fdef__wf_tmn; eauto.
        apply valueInTmnOperands__InOps; auto.
    destruct Hwfm as [Hlk [Hlk' [b [Hwfinsn Hreach']]]].
    apply Hwfg in Hlk; auto.
    apply Hwfg' in Hlk'; auto.
    erewrite eval_rhs_spec with (f:=f)(b:=b) in Hlk; eauto.
    destruct Hlk as [Hlk _]. destruct Hlk' as [Hlk' _].
    rewrite Hlk in Hlk'. inv Hlk'. auto.

    rewrite Heq1 in Hget; auto.
    rewrite Hget in Hget'. inv Hget'. auto.
Qed.

Lemma getOperandValue_inCmdOps_sim : forall
  (f f': fdef)
  (tmn : terminator)
  (lc lc' : GVMap)
  (HwfF : wf_fdef f) (HwfF' : wf_fdef f')
  (l1 : l)
  (ps1 : phinodes) c0 c (Hwfm: wf_motion' f f' c0)
  (cs1 cs1' cs cs': list cmd) (Htrans: sp_motion_fdef c0 f f')
  (Hbtrans: sp_motion_block c0 (block_intro l1 ps1 (cs1 ++ c :: cs) tmn)
     (block_intro l1 ps1 (cs1' ++ c :: cs') tmn))
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (HbInF' : blockInFdefB (block_intro l1 ps1 (cs1' ++ c :: cs') tmn) f' = true)
  (l0 l0': list atom)
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (HeqR' : ret l0' = inscope_of_cmd f' (block_intro l1 ps1 (cs1' ++ c :: cs') tmn) c)
  (Hinscope : OpsemDom.wf_defs f lc l0) (Hinscope' : OpsemDom.wf_defs f' lc' l0')
  (Heq1 : forall id' : id,
          id' <> getCmdLoc c0 ->
          lookupAL GenericValue lc id' = lookupAL GenericValue lc' id')
  (v : value)
  (Hvincs : valueInCmdOperands v c) gv gv'
  (Hget' : getOperandValue v lc' = Some gv')
  (Hget : getOperandValue v lc = Some gv),
  gv = gv'.
Proof.
  intros.
  destruct v as [vid | vc]; simpl in Hget', Hget; try congruence.
  destruct (id_dec vid (getCmdLoc c0)); subst.
    assert (HwfInstr:=HbInF).
    eapply wf_fdef__wf_cmd in HwfInstr; eauto using In_middle.
    assert (OpsemDom.wf_GVs f lc (getCmdLoc c0) gv) as Hwfg.
      eapply OpsemDom.state_cmd_typing; eauto.
        eapply wf_fdef__uniq_block; eauto.
        apply valueInCmdOperands__InOps; auto.
    assert (OpsemDom.wf_GVs f' lc' (getCmdLoc c0) gv') as Hwfg'.
      erewrite sp_motion__isReachableFromEntry in Hreach; eauto.
      eapply OpsemDom.state_cmd_typing; eauto.
        eapply wf_fdef__uniq_block; eauto.
        eapply wf_fdef__wf_cmd; eauto using In_middle.
        apply valueInCmdOperands__InOps; auto.
    destruct Hwfm as [Hlk [Hlk' [b [Hwfinsn Hreach']]]].
    apply Hwfg in Hlk; auto.
    apply Hwfg' in Hlk'; auto.
    erewrite eval_rhs_spec with (f:=f)(b:=b) in Hlk; eauto.
    destruct Hlk as [Hlk _]. destruct Hlk' as [Hlk' _].
    rewrite Hlk in Hlk'. inv Hlk'. auto.

    rewrite Heq1 in Hget; auto.
    rewrite Hget in Hget'. inv Hget'. auto.
Qed.

Require Import Maps.

Lemma getValueViaLabelFromValuels_inscope_of_tmn:
  forall (f : fdef) (l0 : l) (t : list atom) (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator) (id0 : id)
  (HeqR : inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 = ret t)
  (HwfF : wf_fdef f)
  (ps' : phinodes) (cs' : cmds) (tmn' : terminator) (i0 : id) (l2 : list_value_l)
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (H7 : wf_phinode f (block_intro l0 ps' cs' tmn') (insn_phi i0 l2))
  (n : nat) (Hnth : nth_list_value_l n l2 = ret (value_id id0, l1)),
  In id0 t.
Proof.
  intros.
  destruct H7 as [Hwfops Hwfvls].
  eapply wf_phi_operands__elim in Hwfops; eauto.
  destruct Hwfops as [vb [b1 [Hlkvb [Hlkb1 Hdom]]]].
  assert (b1 = block_intro l1 ps1 cs1 tmn1) as EQ.
    clear - Hlkb1 HbInF HwfF.
    apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
    rewrite HbInF in Hlkb1. inv Hlkb1; auto.
  subst.
  clear Hwfvls.
  destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
  unfold blockDominates in J3.         
  destruct vb. 
    clear - HeqR Hlkb1 J3 Hlkvb HwfF.
    unfold inscope_of_tmn in HeqR.
    destruct f.
    remember ((dom_analyze (fdef_intro b)) !! l1) as R1.
    destruct R1.
    apply fold_left__spec in HeqR.
    destruct (eq_atom_dec l3 l1); subst.
    Case "l3=l1".
      destruct HeqR as [HeqR _].
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
        clear - Hlkvb HwfF.
        apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
        apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkvb; auto.
      destruct HeqR as [_ [HeqR _]].
      apply HeqR in J1; auto.
      apply J1.
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
Qed.

Lemma sp_motion_fdef__blockInFdefB : forall c0 f f', 
  sp_motion_fdef c0 f f' ->
  forall b,
  blockInFdefB b f = true ->
  exists b', blockInFdefB b' f' = true /\ sp_motion_block c0 b b'.
Proof.
  intros c0 f f' J.
  inv J. simpl.
  induction H; simpl in *; intros.
    inv H.
    
    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst.
      exists b2.
      split; auto. 
        apply orb_true_iff. left. apply blockEqB_refl.

      apply IHsp_motion_blocks in H1.
      destruct H1 as [b' [J1 J2]].
      exists b'. 
      split; auto.
        apply orb_true_iff; auto.
Qed.

Lemma sp_motion_fdef__wf_phinode: forall c0 f f' l0 ps' cs' tmn' i0 l2
  (HwfF : wf_fdef f) (HwfF' : wf_fdef f')
  (Hin : insnInFdefBlockB (insn_phinode (insn_phi i0 l2)) f 
    (block_intro l0 ps' cs' tmn') = true),
  sp_motion_fdef c0 f f' ->
  wf_phinode f (block_intro l0 ps' cs' tmn') (insn_phi i0 l2) ->
  exists cs'', 
    wf_phinode f' (block_intro l0 ps' cs'' tmn') (insn_phi i0 l2) /\
    sp_motion_cmds c0 cs' cs''.
Proof.
  intros. 
  apply andb_true_iff in Hin. destruct Hin as [Hin1 Hin2].
  eapply sp_motion_fdef__blockInFdefB in Hin2; eauto.
  destruct Hin2 as [b' [J1 J2]]. inv J2.
  exists cs2. split; auto.
  apply wf_fdef__wf_phinodes in J1; auto.
  eapply wf_phinodes__wf_phinode in J1; eauto.
Qed.

Lemma getValueViaLabelFromValuels_getOperandValue_sim : forall
  (f f': fdef) (l0 : l) (lc lc': GVMap) (t t': list atom) (l1 : l) 
  (ps1 : phinodes) (cs1 cs1': cmds) (tmn1 : terminator)
  c0 (Htrans: sp_motion_fdef c0 f f') (Hwfm: wf_motion' f f' c0)
  (Hbtrans: sp_motion_block c0 (block_intro l1 ps1 cs1 tmn1) 
    (block_intro l1 ps1 cs1' tmn1))
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (HeqR' : ret t' = inscope_of_tmn f' (block_intro l1 ps1 cs1' tmn1) tmn1)
  (Hinscope : OpsemDom.wf_defs f lc t) (Hinscope' : OpsemDom.wf_defs f' lc' t')
  (HwfF : wf_fdef f) (HwfF' : wf_fdef f')
  (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (i0 : id) (l2 : list_value_l) (ps2 : list phinode)
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (HbInF' : blockInFdefB (block_intro l1 ps1 cs1' tmn1) f' = true)
  (v0 : value)
  (HeqR3 : ret v0 = getValueViaLabelFromValuels l2 l1)
  (g1 : GenericValue) 
  (HeqR4 : ret g1 = getOperandValue v0 lc)
  (g2 : GVMap) (g : GenericValue) (g0 : GVMap)
  (H1 : wf_value_list
         (make_list_fdef_value
            (map_list_value_l (fun (value_ : value) (_ : l) => (f, value_))
               l2)))
  (Hin : insnInFdefBlockB (insn_phinode (insn_phi i0 l2)) f 
    (block_intro l0 ps' cs' tmn') = true)
  (H7 : wf_phinode f (block_intro l0 ps' cs' tmn') (insn_phi i0 l2))
  (Heq1 : forall id' : id,
          id' <> getCmdLoc c0 ->
          lookupAL GenericValue lc id' = lookupAL GenericValue lc' id')
  (HeqR1 : ret g = getOperandValue v0 lc'),
  g1 = g.
Proof.
  intros.
  destruct v0 as [vid | vc]; simpl in HeqR1, HeqR4; try congruence.
  destruct (id_dec vid (getCmdLoc c0)); subst.
  Case "1".
    symmetry_ctx.
    assert (Hnth:=HeqR3).
    eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
    destruct Hnth as [n Hnth].
    
    eapply getValueViaLabelFromValuels_inscope_of_tmn in HeqR; eauto.
    
    assert (exists cs'', 
      wf_phinode f' (block_intro l0 ps' cs'' tmn') (insn_phi i0 l2) /\
      sp_motion_cmds c0 cs' cs'') as H7'.
      eapply sp_motion_fdef__wf_phinode with (f:=f); eauto.
    destruct H7' as [cs'' [H7' Hcstrans]].
    erewrite sp_motion__isReachableFromEntry in Hreach; eauto.
    eapply getValueViaLabelFromValuels_inscope_of_tmn in HeqR'; eauto.
    
    destruct Hwfm as [Hlk [Hlk' [b [HwfI Hreach']]]].
    apply Hinscope in HeqR4; auto.
    apply HeqR4 in Hlk; auto.
    apply Hinscope' in HeqR1; auto.
    apply HeqR1 in Hlk'; auto.
    erewrite eval_rhs_spec with (b:=b) in Hlk; eauto.
    destruct Hlk as [Hlk _]. destruct Hlk' as [Hlk' _].
    rewrite Hlk' in Hlk. inv Hlk. auto.

  Case "2".
    rewrite Heq1 in HeqR4; auto.
    rewrite <- HeqR4 in HeqR1. inv HeqR1. auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall
  (f f': fdef)
  l0
  (lc lc': GVMap)
  (t t': list atom)
  l1 ps1 cs1 cs1' tmn1 c0 (Hwfm: wf_motion' f f' c0)
  (Heq1 : forall id' : id,
          id' <> getCmdLoc c0 ->
          lookupAL GenericValue lc id' = lookupAL GenericValue lc' id')
  (Htrans: sp_motion_fdef c0 f f')
  (Hbtrans: sp_motion_block c0 (block_intro l1 ps1 cs1 tmn1)
    (block_intro l1 ps1 cs1' tmn1))
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (HeqR' : ret t' = inscope_of_tmn f' (block_intro l1 ps1 cs1' tmn1) tmn1)
  (Hinscope: OpsemDom.wf_defs f lc t) (Hinscope': OpsemDom.wf_defs f' lc' t')
  (HwfF : wf_fdef f) (HwfF' : wf_fdef f')
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HbInF' : blockInFdefB
            (block_intro l1 ps1 cs1' tmn1) f' = true)
  (HwfB : wf_block f (block_intro l1 ps1 cs1 tmn1))
  ps2
  (H8 : wf_phinodes f (block_intro l0 ps' cs' tmn') ps2)
  (Hin: exists ps1, ps' = ps1 ++ ps2) RVs RVs'
  (Hget: getIncomingValuesForBlockFromPHINodes ps2 (block_intro l1 ps1 cs1 tmn1)
    lc = ret RVs)
  (Hget': getIncomingValuesForBlockFromPHINodes ps2 
    (block_intro l1 ps1 cs1' tmn1) lc' = ret RVs'),
  forall id', id' <> getCmdLoc c0 -> lookupAL _ RVs id' = lookupAL _ RVs' id'.
Proof.
  induction ps2; intros; simpl in Hget, Hget'; try congruence.
    destruct a. inv H8. inv H4. simpl in Hget'.
    inv_mbind'. 
    app_inv.
    assert (g1 = g) as Heq.
      eapply getValueViaLabelFromValuels_getOperandValue_sim; eauto.
    subst. 
    eapply IHps2 with (RVs:=g2) in H5; eauto.
      simpl. rewrite H5. reflexivity.

      destruct Hin as [ps3 Hin]. subst.
      exists (ps3++[insn_phi i0 l2]).
      simpl_env. auto.
Qed.

Lemma switchToNewBasicBlock_sim : forall
  (f f': fdef) l2 (lc lc': GVMap) (t t': list atom) l1 ps1 cs1 cs1' tmn1 c0
  (Heq1 : forall id' : id,
          id' <> getCmdLoc c0 ->
          lookupAL GenericValue lc id' = lookupAL GenericValue lc' id')
  (Htrans: sp_motion_fdef c0 f f') (Hwfm: wf_motion' f f' c0)
  (Hbtrans1: sp_motion_block c0 (block_intro l1 ps1 cs1 tmn1)
    (block_intro l1 ps1 cs1' tmn1))
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (HeqR' : ret t' = inscope_of_tmn f' (block_intro l1 ps1 cs1' tmn1) tmn1)
  (Hinscope : OpsemDom.wf_defs f lc t) (Hinscope' : OpsemDom.wf_defs f' lc' t')
  (HwfF : wf_fdef f) (HwfF' : wf_fdef f')
  (ps2 : phinodes) (cs2 cs2': cmds) (tmn2 : terminator)
  (Hbtrans2: sp_motion_block c0 (block_intro l2 ps2 cs2 tmn2)
    (block_intro l2 ps2 cs2' tmn2))
  (Hsucc : In l2 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (block_intro l2 ps2 cs2 tmn2))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HbInF' : blockInFdefB
            (block_intro l1 ps1 cs1' tmn1) f' = true)
  (HwfB : wf_block f (block_intro l1 ps1 cs1 tmn1))
  lc0 lc0'
  (H8 : wf_phinodes f (block_intro l2 ps2 cs2 tmn2) ps2) 
  (Hget : switchToNewBasicBlock (block_intro l2 ps2 cs2 tmn2) 
    (block_intro l1 ps1 cs1 tmn1) lc = ret lc0)
  (Hget' : switchToNewBasicBlock (block_intro l2 ps2 cs2' tmn2) 
    (block_intro l1 ps1 cs1' tmn1) lc' = ret lc0'),
  forall id' : id,
    id' <> getCmdLoc c0 ->
    lookupAL GenericValue lc0 id' = lookupAL GenericValue lc0' id'.
Proof.
  intros.
  unfold switchToNewBasicBlock in *.
  inv_mbind'. app_inv. symmetry_ctx. 
  assert (forall id', id' <> getCmdLoc c0 -> 
    lookupAL _ g0 id' = lookupAL _ g id') as EQ.
    eapply getIncomingValuesForBlockFromPHINodes_sim with (cs1':=cs1'); eauto.
      exists nil. auto.
  eapply updateValuesForNewBlock_sim; eauto.
Qed.

Lemma sp_motion_fdef__lookupBlockViaLabelFromFdef : forall c0 f f' l0 b b', 
  sp_motion_fdef c0 f f' -> uniqFdef f -> uniqFdef f' ->
  lookupBlockViaLabelFromFdef f l0 = Some b ->
  lookupBlockViaLabelFromFdef f' l0 = Some b' ->
  sp_motion_block c0 b b'.
Proof.
  intros.
  destruct b.
  apply lookupBlockViaLabelFromFdef_inv in H2; auto.
  destruct H2 as [Heq H2]; subst.
  eapply sp_motion_fdef__blockInFdefB in H2; eauto.
  destruct H2 as [b2 [J1 J2]].
  inv J2.
  apply blockInFdefB_lookupBlockViaLabelFromFdef in J1; auto.
  rewrite H3 in J1. inv J1. auto.
Qed.

Lemma bisimulation_cmd_updated_case : forall
  (F2 F1 : fdef) (B2 : block) lc1 lc2 (gv : GenericValue)
  (cs2 : list cmd) (tmn2 : terminator)
  c0 B1 c5 id5 cs1 tmn1
  (Hid2 : Some id5 = getCmdID c5)
  (HwfF1 : wf_fdef F1) (HwfF2 : wf_fdef F2)
  (Htrans : sp_motion_fdef c0 F1 F2) (Hneq: c5 <> c0)
  (Hrel : related_ECs c0 F1 F2
            {| CurBB := B1;
               CurCmds := c5 :: cs1;
               Terminator := tmn1;
               Locals := lc1
            |}
            {| CurBB := B2;
               CurCmds := c5 :: cs2;
               Terminator := tmn2;
               Locals := lc2
            |}),
  related_ECs c0 F1 F2
     {| CurBB := B1;
        CurCmds := cs1;
        Terminator := tmn1;
        Locals := updateAddAL _ lc1 id5 gv
     |}
     {| CurBB := B2;
        CurCmds := cs2;
        Terminator := tmn2;
        Locals := updateAddAL _ lc2 id5 gv
     |}.
Proof.
  intros.
  destruct Hrel as
    [Hreach1 [HBinF1 [HBinF2 [Heq1 [Hbtrans [Hcstrans
      [l3 [ps1 [cs1' [cs2' [Heq2 Heq3]]]]]]]]]]]; subst.
  inv Hcstrans; try congruence.
  repeat (split; try solve [auto]).
    intros.   
    destruct (id_dec id5 id'); subst.
      repeat rewrite lookupAL_updateAddAL_eq; auto.
      repeat rewrite <- lookupAL_updateAddAL_neq; auto.

    exists l3. exists ps1. exists (cs1'++[c5]). exists (cs2'++[c5]). 
    simpl_env. auto.
Qed.

Ltac destruct_ctx :=
match goal with
| Hrel : related_ECs _ _ _ ?S1 _,
  HwfS1 : OpsemDom.wf_ExecutionContext _ ?S1,
  HwfS2 : OpsemDom.wf_ExecutionContext _ ?S2,
  HsInsn1 : sInsn _ ?S1 _ _ |- _ =>
  destruct S1 as [b1 cs1 tmn1 lc1];
  assert (J:=Hrel); simpl in J;
  destruct J as
    [Hreach1 [HBinF1 [HBinF2 [Heq1 [Hbtrans [Hcstrans
      [l3 [ps1 [cs1' [cs2' [Heq2 Heq3]]]]]]]]]]]; subst;
  destruct HwfS1 as [_ [_ [_ [Hinscope1 _]]]];
  destruct HwfS2 as [_ [_ [_ [Hinscope2 _]]]];
  match goal with
  | Hmotion : ~ motionable_EC _ _ /\
              ~ motionable_EC _ {|CurCmds := nil|} |- _ =>
    simpl in Hmotion;
    destruct Hmotion as [HnmS1 HnmS2];
    destruct cs1; try solve [inv Hcstrans; congruence];
    inv Hbtrans;
    inv HsInsn1
  | Hmotion : ~ motionable_EC ?c0 {|CurCmds := ?cs1|} /\
              ~ motionable_EC _ {|CurCmds := ?c::?cs|} |- _ =>
    simpl in Hmotion;
    destruct Hmotion as [HnmS1 HnmS2];
    destruct cs1; inv Hcstrans; try congruence;
    inv Hbtrans;
    inv HsInsn1
  end;
  match goal with
  | Hinscope : match inscope_of_cmd ?f ?b ?c with
                | ret _ => _
                | merror => False
                end,
    Hinscope' : match inscope_of_cmd ?f' ?b' ?c' with
                | ret _ => _
                | merror => False
                end |- _ => 
    remember (inscope_of_cmd f b c) as R1;
    destruct R1; tinv Hinscope;
    remember (inscope_of_cmd f' b' c') as R2;
    destruct R2; tinv Hinscope'
  | Hinscope : match inscope_of_tmn ?f ?b ?c with
                | ret _ => _
                | merror => False
                end,
    Hinscope' : match inscope_of_tmn ?f' ?b' ?c' with
                | ret _ => _
                | merror => False
                end |- _ => 
    remember (inscope_of_tmn f b c) as R1;
    destruct R1; tinv Hinscope;
    remember (inscope_of_tmn f' b' c') as R2;
    destruct R2; tinv Hinscope'
  end
end.

Ltac bisimulation_cmd :=
match goal with
| H : _ ?lc _  ?v ?v0 = ret ?gvs3,
  H11 : _ ?lc1 _ ?v ?v0 = ret ?gvs0,
  Hrel : related_ECs _ ?F1 _ _ _ |-
  context [_ ?id1 _ ?v ?v0] =>
  assert (gvs0 = gvs3) as Heq;
    try (unfold ICMP, BOP in *;
    inv_mbind'; inv_mfalse; app_inv; symmetry_ctx;
    match goal with
    | HeqR : getOperandValue ?v ?lc = ret ?g0, 
      HeqR' : getOperandValue ?v ?lc1 = ret ?g1, 
      HeqR0 : getOperandValue ?v0 ?lc = ret ?g2,
      HeqR0' : getOperandValue ?v0 ?lc1 = ret ?g3 |- _ => 
      eapply getOperandValue_inCmdOps_sim with (f:=F1) in HeqR; 
        try (eauto || simpl; auto);
      eapply getOperandValue_inCmdOps_sim with (f:=F1) in HeqR0; 
        try (eauto || simpl; auto);
      subst; auto
    end);
  split; try solve [auto |
    eapply bisimulation_cmd_updated_case in Hrel; try solve [simpl; eauto]]
end.

Lemma bisimulation : forall c0 F1 F2 S1 S2,
  wf_motion' F1 F2 c0 ->
  wf_fdef F1 -> wf_fdef F2 ->
  OpsemDom.wf_ExecutionContext F1 S1 -> 
  OpsemDom.wf_ExecutionContext F2 S2 -> 
  sp_motion_fdef c0 F1 F2 ->
  related_ECs c0 F1 F2 S1 S2 ->
  (motionable_EC c0 S1 ->
   forall S1' tr1, 
    sInsn F1 S1 S1' tr1 ->
    related_ECs c0 F1 F2 S1' S2 /\ tr1 = trace_nil) /\
  ( motionable_EC c0 S2 ->
   forall S2' tr2, 
    sInsn F2 S2 S2' tr2 ->
    related_ECs c0 F1 F2 S1 S2' /\ tr2 = trace_nil) /\
  ((~ motionable_EC c0 S1 /\ ~ motionable_EC c0 S2) ->
   forall S1' S2' tr1 tr2,
    sInsn F1 S1 S1' tr1 ->
    sInsn F2 S2 S2' tr2 ->
    related_ECs c0 F1 F2 S1' S2' /\ tr1 = tr2).
Proof.
  intros c0 F1 F2 S1 S2 hwfm HwfF1 HwfF2 HwfS1 HwfS2 Htrans Hrel.
  split.
Case "S1 is motionable, but S2 is not".
  intros HmotionS1 S1' tr1 HsInsn1.
  (sInsn_cases (destruct HsInsn1) SCase); inv HmotionS1. 
  SCase "sBop". apply bisimulation_cmd_case1; auto.
  SCase "sIcmp". apply bisimulation_cmd_case1; auto.

  split.
Case "S2 is motionable, but S1 is not".
  intros HmotionS2 S2' tr2 HsInsn2.
  (sInsn_cases (destruct HsInsn2) SCase); inv HmotionS2. 
  SCase "sBop". apply bisimulation_cmd_case2; auto.
  SCase "sIcmp". apply bisimulation_cmd_case2; auto.

Case "otherwise".
  intros Hmotion S1' S2' tr1 tr2 HsInsn1 HsInsn2.
  (sInsn_cases (destruct HsInsn2) SCase); destruct_ctx.
Focus.
SCase "sBranch".
  assert (c1 = c) as Heq.
    eapply getOperandValue_inTmnOperans_sim with (f:=F1)(f':=F)(c0:=c0); 
      try solve [eauto | simpl; auto].
  subst.
  assert (sp_motion_block c0 (block_intro l'0 ps'0 cs'0 tmn'0) 
    (block_intro l' ps' cs' tmn')) as Hbtrans.
    destruct (isGVZero c);
      eapply sp_motion_fdef__lookupBlockViaLabelFromFdef; eauto.
  inv Hbtrans.
  assert (isReachableFromEntry F1 (block_intro l' ps' cs'0 tmn') /\
    In l' (successors_terminator (insn_br bid Cond l1 l2)) /\
    blockInFdefB (block_intro l' ps' cs'0 tmn') F1 = true /\
    wf_phinodes F1 (block_intro l' ps' cs'0 tmn') ps') as J.
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
  assert (forall id', id' <> getCmdLoc c0 ->
    lookupAL GenericValue lc'0 id' = lookupAL GenericValue lc' id') as Heq.
    assert (HwfB := HBinF1).
    eapply wf_fdef__blockInFdefB__wf_block in HwfB; eauto.
    simpl_env in *.
    intros. eapply switchToNewBasicBlock_sim in H1; eauto.
  assert (blockInFdefB (block_intro l' ps' cs' tmn') F = true) as HBinF2'.
    symmetry in H0.
    destruct (isGVZero c);
      apply lookupBlockViaLabelFromFdef_inv in H0;
      destruct H0 as [J H13']; subst; auto.
  repeat split; auto. 
    exists l'. exists ps'. exists nil. exists nil. auto.
Unfocus.

Focus.
SCase "sBranch_uncond".
  assert (sp_motion_block c0 (block_intro l'0 ps'0 cs'0 tmn'0) 
    (block_intro l' ps' cs' tmn')) as Hbtrans.
    eapply sp_motion_fdef__lookupBlockViaLabelFromFdef; eauto.
  inv Hbtrans.
  assert (isReachableFromEntry F1 (block_intro l' ps' cs'0 tmn') /\
    In l' (successors_terminator (insn_br_uncond bid l0)) /\
    blockInFdefB (block_intro l' ps' cs'0 tmn') F1 = true /\
    wf_phinodes F1 (block_intro l' ps' cs'0 tmn') ps') as J.
    symmetry in H9.
    assert (J:=H9);
    apply lookupBlockViaLabelFromFdef_inv in J; eauto;
    destruct J as [J H9']; subst;
    symmetry in H9; eapply wf_fdef__lookup__wf_block in H9; eauto;
    (repeat split; simpl; auto); try solve
      [eapply reachable_successors; (eauto || simpl; auto) |
       inv H9; auto].
  destruct J as [Hreach' [Hsucc' [HBinF1' HwfPNs]]].
  assert (forall id', id' <> getCmdLoc c0 ->
    lookupAL GenericValue lc'0 id' = lookupAL GenericValue lc' id') as Heq.
    assert (HwfB := HBinF1).
    eapply wf_fdef__blockInFdefB__wf_block in HwfB; eauto.
    simpl_env in *.
    intros. eapply switchToNewBasicBlock_sim in H0; eauto.
  assert (blockInFdefB (block_intro l' ps' cs' tmn') F = true) as HBinF2'.
    symmetry in H.
    apply lookupBlockViaLabelFromFdef_inv in H; auto.
    destruct H as [J H13']; subst; auto.
  repeat split; auto. 
    exists l'. exists ps'. exists nil. exists nil. auto.
Unfocus.

SCase "sBop". abstract bisimulation_cmd.
SCase "sIcmp". abstract bisimulation_cmd.
Qed.

Lemma related_finalstate_is_stuck : forall c0 F1 F2 S1 S2 S2' tr2
  (Hrel : related_ECs c0 F1 F2 S1 S2)
  (Hmotion : ~ motionable_EC c0 S1 /\ ~ motionable_EC c0 S2)
  (Hfinal1 : s_isFinialState S1 = true)
  (HsInsn2 : sInsn F2 S2 S2' tr2),
  False.
Proof.
  intros.
  destruct S1. destruct CurCmds0; tinv Hfinal1. 
  destruct Terminator0; inv Hfinal1. destruct S2. 
  destruct Hrel as 
    [J1 [J2 [J2' [J3 [J4 [J5 [l1 [ps1 [cs1' [cs2' [J7 J8]]]]]]]]]]]; 
    subst; simpl in *.
  destruct Hmotion as [M1 M2].
    destruct CurCmds0.
      inv J4. inv HsInsn2.
      inv J5. auto.
Qed.

Lemma finalstate_isnt_motionable : forall c0 S1
  (Hfinal1 : s_isFinialState S1 = true),
  ~ motionable_EC c0 S1.
Proof.
  intros. destruct S1. simpl in *.
  destruct CurCmds0; auto. congruence.
Qed.

Lemma backsimulation : forall c0 F1 F2 S1 S2,
  wf_motion' F1 F2 c0 ->
  wf_fdef F1 ->
  wf_fdef F2 ->
  OpsemPP.wf_ExecutionContext F1 S1 ->  
  OpsemDom.wf_ExecutionContext F1 S1 ->  
  OpsemDom.wf_ExecutionContext F2 S2 ->  
  sp_motion_fdef c0 F1 F2 ->
  related_ECs c0 F1 F2 S1 S2 ->
  (motionable_EC c0 S1 ->
   exists S1',
    sInsn F1 S1 S1' trace_nil /\ related_ECs c0 F1 F2 S1' S2) /\ 
  (motionable_EC c0 S2 ->
   forall S2' tr,
    sInsn F2 S2 S2' tr ->
    related_ECs c0 F1 F2 S1 S2' ) /\
  ((~ motionable_EC c0 S1 /\ ~ motionable_EC c0 S2) ->
   forall S2' tr,
    sInsn F2 S2 S2' tr ->
    exists S1', 
    sInsn F1 S1 S1' tr /\ related_ECs c0 F1 F2 S1' S2' ).
Proof.
  intros c0 F1 F2 S1 S2 Hwfm HwfF1 HwfF2 HwfEC1 HwfEC1' HwfEC2' Htrans Hrel.
  apply OpsemPP.progress in HwfEC1; auto.
  assert (J:=Hrel).
  eapply bisimulation in J; eauto.
  destruct J as [J1 [J2 J3]].
  split.
    intros HmS1.
    destruct HwfEC1 as [Hfinal1 | [S1' [tr1 HsInsn1]]].
      apply finalstate_isnt_motionable with (c0:=c0) in Hfinal1; auto.
        congruence.
      exists S1'. eapply J1 in HmS1; eauto. destruct HmS1; subst; auto.
  split.
    intros HmS2 S2' tr2 HsInsn2.
    eapply J2 in HmS2; eauto. destruct HmS2; subst; auto.

    intros Hmotion S2' tr HsInsn2. 
    destruct HwfEC1 as [Hfinal1 | [S1' [tr1 HsInsn1]]].
      eapply related_finalstate_is_stuck in Hrel; eauto. inv Hrel.
      exists S1'. eapply J3 in Hmotion; eauto. destruct Hmotion; subst; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
