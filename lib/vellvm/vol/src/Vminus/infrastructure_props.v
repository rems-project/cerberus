Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".

Require Import syntax.
Require Import infrastructure.
Require Import Coq.Program.Equality.
Require Import CoqListFacts.
Require Import Metatheory.
Require Import alist.
Require Import Coqlib.
Require Import Kildall.
Require Import Maps.

Import VMsyntax.
Import VMinfra.

Ltac tinv H := try solve [inv H].

Ltac symmetry_ctx :=
  repeat match goal with
  | H : Some _ = _ |- _ => symmetry in H
  end.

Ltac inv_mbind' :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [|]; tinv H
         end.

Ltac inv_mbind :=
  repeat match goal with
         | H : Some _ = match ?e with
               | Some _ => _
               | None => None
               end |- _ => remember e as R; destruct R as [|]; tinv H
         end.

Ltac app_inv :=
  repeat match goal with
  | [ H: Some _ = Some _ |- _ ] => inv H
  end.

Ltac trans_eq :=
  repeat match goal with 
  | H1 : ?a = ?b, H2 : ?c = ?b |- _ => rewrite <- H1 in H2; inv H2
  | H1 : ?a = ?b, H2 : ?b = ?c |- _ => rewrite <- H1 in H2; inv H2
  end.

Ltac inv_mfalse :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => False
               end |- _ => remember e as R; destruct R as [|]; tinv H
         end.

Tactic Notation "binvt" ident(H) "as" ident(J1) ident(J2) :=
apply orb_true_iff in H; destruct H as [J1 | J2].

Tactic Notation "binvf" ident(H) "as" ident(J1) ident(J2) :=
apply orb_false_iff in H; destruct H as [J1 J2].

(* eq is refl *)

Lemma neq_refl : forall n, n =n= n.
Proof.
  intros.
  symmetry.
  apply beq_nat_refl.
Qed.

Lemma true_sumbool2bool : forall A (H:sumbool A (~A)),
  A -> sumbool2bool A (~A) H = true.
Proof.
  intros A H H0.
  destruct H; auto.
Qed.

Lemma false_sumbool2bool : forall A (H:sumbool A (~A)),
  ~A -> sumbool2bool A (~A) H = false.
Proof.
  intros A H H0.
  destruct H; auto.
    contradict a; auto.
Qed.

Ltac sumbool2bool_refl := intros; apply true_sumbool2bool; auto.

Lemma idEqB_refl : forall i, idEqB i i.
Proof. sumbool2bool_refl. Qed.

Lemma lEqB_refl : forall l, lEqB l l.
Proof. sumbool2bool_refl. Qed.

Lemma constEqB_refl : forall c, constEqB c c.
Proof. sumbool2bool_refl. Qed.

Lemma valueEqB_refl: forall v, valueEqB v v.
Proof. sumbool2bool_refl. Qed.

Lemma bopEqB_refl: forall op, bopEqB op op.
Proof. sumbool2bool_refl. Qed.

Lemma condEqB_refl: forall c, condEqB c c.
Proof. sumbool2bool_refl. Qed.

Lemma eqb_refl : forall i0, eqb i0 i0.
unfold eqb.
destruct i0; unfold is_true; auto.
Qed.

Lemma cmdEqB_refl : forall c, cmdEqB c c.
Proof. sumbool2bool_refl. Qed.

Lemma terminatorEqB_refl : forall tmn, terminatorEqB tmn tmn.
Proof. sumbool2bool_refl. Qed.

Lemma list_value_lEqB_refl : forall l0, list_value_lEqB l0 l0.
Proof. sumbool2bool_refl. Qed.

Lemma phinodeEqB_refl : forall p, phinodeEqB p p.
Proof. sumbool2bool_refl. Qed.
  
Lemma phinodesEqB_refl : forall ps, phinodesEqB ps ps.
Proof. sumbool2bool_refl. Qed.

Lemma cmdsEqB_refl : forall cs, cmdsEqB cs cs.
Proof. sumbool2bool_refl. Qed.

Lemma blockEqB_refl : forall B,
  blockEqB B B.
Proof. sumbool2bool_refl. Qed.
     
Lemma blocksEqB_refl : forall bs, blocksEqB bs bs.
Proof. sumbool2bool_refl. Qed.

Lemma fdefEqB_refl : forall f, fdefEqB f f.
Proof. sumbool2bool_refl. Qed.

(* refl implies eq *)

Lemma neq_inv : forall n m, n =n= m -> n = m.
Proof.
  intros. apply beq_nat_eq; auto.
Qed.

Ltac sumbool2bool_inv := intros e1 e2 H; apply sumbool2bool_true in H; auto.

Lemma idEqB_inv : forall i1 i2, idEqB i1 i2 -> i1 = i2.
Proof. sumbool2bool_inv. Qed.

Lemma lEqB_inv : forall l1 l2, lEqB l1 l2 -> l1 = l2.
Proof. sumbool2bool_inv. Qed.

Lemma constEqB_inv : forall c1 c2, constEqB c1 c2 -> c1 = c2.
Proof. sumbool2bool_inv. Qed.

Lemma valueEqB_inv: forall v1 v2, valueEqB v1 v2 -> v1 = v2.
Proof. sumbool2bool_inv. Qed.

Lemma bopEqB_inv: forall op1 op2, bopEqB op1 op2 -> op1=op2.
Proof. sumbool2bool_inv. Qed.

Lemma condEqB_inv: forall c1 c2, condEqB c1 c2 -> c1=c2.
Proof. sumbool2bool_inv. Qed.

Lemma eqb_inv : forall i1 i2, eqb i1 i2 -> i1=i2.
Proof. destruct i1; destruct i2; auto. Qed.

Lemma cmdEqB_inv : forall c1 c2, cmdEqB c1 c2 -> c1 = c2.
Proof. sumbool2bool_inv. Qed.

Lemma terminatorEqB_inv : forall tmn1 tmn2, terminatorEqB tmn1 tmn2 -> tmn1=tmn2.
Proof. sumbool2bool_inv. Qed.

Lemma list_value_lEqB_inv : forall l1 l2, list_value_lEqB l1 l2 -> l1=l2.
Proof. sumbool2bool_inv. Qed.

Lemma phinodeEqB_inv : forall p1 p2, phinodeEqB p1 p2 -> p1=p2.
Proof. sumbool2bool_inv. Qed.
  
Lemma phinodesEqB_inv : forall ps1 ps2, phinodesEqB ps1 ps2 -> ps1=ps2.
Proof. sumbool2bool_inv. Qed.

Lemma cmdsEqB_inv : forall cs1 cs2, cmdsEqB cs1 cs2 -> cs1=cs2.
Proof. sumbool2bool_inv. Qed.

Lemma blockEqB_inv : forall B1 B2,
  blockEqB B1 B2 -> B1 = B2.
Proof. sumbool2bool_inv. Qed.
     
Lemma blocksEqB_inv : forall bs1 bs2, blocksEqB bs1 bs2 -> bs1=bs2.
Proof. sumbool2bool_inv. Qed.

Lemma fdefEqB_inv : forall f1 f2, fdefEqB f1 f2 -> f1=f2.
Proof. sumbool2bool_inv. Qed.

(* nth_err *)

Lemma nil_nth_error_Some__False : forall X n (v:X),
  nth_error (@nil X) n = Some v -> False.
Proof.
  induction n; intros; simpl in *; inversion H.
Qed.   

Lemma nth_error_cons__inv : forall X b lb n (b':X),
  nth_error (b::lb) n = Some b' ->
  b = b' \/ (exists n', S n' = n /\ nth_error lb n' = Some b').
Proof.
  destruct n; intros; simpl in *.
    inversion H; auto.

    right. exists n. split; auto.
Qed.

(* NoDup *)

Lemma NotIn_inv : forall X (a:X) (lb1 lb2:list X),
  ~ In a (lb1++lb2) ->
  ~ In a lb1 /\ ~ In a lb2.
Proof.
  intros.
  split; intro J'; apply H; auto using in_or_app.
Qed.

Lemma NoDup_inv : forall X (lb1 lb2:list X),
  NoDup (lb1++lb2) ->
  NoDup lb1 /\ NoDup lb2.
Proof.
  induction lb1; intros.
    split; auto using NoDup_nil.

    simpl in *. inversion H; subst.
    apply IHlb1 in H3. destruct H3.
    apply NotIn_inv in H2.
    destruct H2 as [J1 J2].
    split; auto using NoDup_cons.
Qed.

Lemma NoDup_split : forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2.
Proof.
  induction l1; intros.
    simpl in *. 
    split; auto using NoDup_nil.
 
    inversion H; subst.
    apply IHl1 in H3.
    destruct H3 as [J1 J2].
    split; auto.
      apply NoDup_cons; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma NoDup_last_inv : forall X (a:X) l0,
  NoDup (l0++a::nil) ->
  ~ In a l0.
Proof.
  induction l0; intros.
    intro J. inversion J.
  
    simpl in H.
    inversion H; subst.
    apply IHl0 in H3.
    intro J.
    simpl in J.
    inversion J; subst; auto.
      apply NotIn_inv in H2.
      destruct H2.
      apply H1; simpl; auto.
Qed.

Lemma NoDup_disjoint : forall l1 l2 (i0:atom),
  NoDup (l1++l2) ->
  In i0 l2 -> 
  ~ In i0 l1.    
Proof.
  induction l1; intros.
    intro J. inversion J.  

    simpl. simpl_env in H.
    inv H.
    eapply IHl1 in H4; eauto.
    destruct (eq_atom_dec i0 a); subst.
      intro J. apply H3. apply in_or_app; auto.
      intro J. destruct J; auto.
Qed.    

Lemma NoDup_disjoint' : forall l1 l2 (i0:atom),
  NoDup (l1++l2) ->
  In i0 l1 -> 
  ~ In i0 l2.    
Proof.
  induction l1; intros.
    inversion H0.

    simpl. simpl_env in H.
    inv H. simpl in H0.
    destruct H0 as [H0 | H0]; subst; eauto.
      intro J. apply H3. apply in_or_app; auto.
Qed.    

(* gets *)

Lemma getCmdsLocs_app : forall cs1 cs2,
  getCmdsLocs (cs1++cs2) = getCmdsLocs cs1++getCmdsLocs cs2.
Proof.
  induction cs1; intros; auto.
    simpl. rewrite IHcs1. auto.
Qed.

Lemma getCmdsIDs_app : forall cs1 cs2,
  getCmdsIDs (cs1++cs2) = getCmdsIDs cs1++getCmdsIDs cs2.
Proof.
  induction cs1; intros; auto.
    simpl. 
    rewrite IHcs1.
    destruct (getCmdID a); auto.
Qed.

Lemma getPhiNodesIDs_app : forall ps1 ps2,
  getPhiNodesIDs (ps1++ps2) = getPhiNodesIDs ps1++getPhiNodesIDs ps2.
Proof.
  induction ps1; intros; auto.
    simpl. 
    rewrite IHps1; auto.
Qed.

Lemma getBlocksLocs_app : forall lb1 lb2,
  getBlocksLocs (lb1++lb2) = getBlocksLocs lb1++getBlocksLocs lb2.
Proof.
  induction lb1; intros; auto.
    simpl. rewrite IHlb1. simpl_env. auto.
Qed.

Lemma getBlocksLabels_app : forall lb1 lb2,
  getBlocksLabels (lb1++lb2) = getBlocksLabels lb1++getBlocksLabels lb2.
Proof.
  induction lb1; intros; auto.
    simpl. rewrite IHlb1. destruct a. simpl_env. auto.
Qed.

Lemma genLabel2Block_block_inv : forall b l0 b',
  lookupAL _ (genLabel2Block_block b) l0 = Some b' ->
  b = b'.
Proof.
  intros. unfold genLabel2Block_block in H.
  destruct b.
  simpl in H.
  destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); subst; 
    inversion H; auto.
Qed.        

Lemma NotInGetBlocksLabels__NotInGenLabel2Block_blocks : forall lb l0,
  ~ In l0 (getBlocksLabels lb) ->
  l0 `notin` dom (genLabel2Block_blocks lb).
Proof.
  induction lb; intros.
    simpl. auto.

    destruct a. simpl in *.
    destruct (l1==l0); subst.
      contradict H; auto.

      destruct (In_dec eq_atom_dec l0 (getBlocksLabels lb)) as [J | J].
        contradict H; auto.
        apply IHlb in J; auto.
Qed.

Lemma getBlockLabel_in_genLabel2Block_block : forall B,
  getBlockLabel B `in` dom (genLabel2Block_block B).
Proof.
  destruct B. simpl. auto.
Qed.

(* inclusion *)

Lemma InBlocksB_middle : forall lb1 B lb2,
  InBlocksB B (lb1++B::lb2).
Proof.
  induction lb1; intros; simpl; auto.
    apply orb_true_intro.
    left. apply blockEqB_refl.

    apply orb_true_intro.
    right. apply IHlb1.
Qed. 

Lemma uniqBlocks__uniqLabel2Block : forall lb,
  uniqBlocks lb ->
  uniq (genLabel2Block_blocks lb).
Proof.
  induction lb; intros; simpl; auto.
    destruct a.
    unfold uniqBlocks in H.
    destruct H.
    unfold genLabel2Block_block.
    simpl in *.
    inversion H; subst.
    apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H3.
    apply uniq_cons; auto.
      apply IHlb.
      rewrite ass_app in H0.
      apply NoDup_inv in H0. destruct H0.
      split; auto.
Qed.


Lemma uniqBlocks_nil : uniqBlocks nil.
unfold uniqBlocks. simpl. split; auto using NoDup_nil.
Qed.

Lemma uniqBlocks_inv : forall lb1 lb2,
  uniqBlocks (lb1++lb2) ->
  uniqBlocks lb1 /\ uniqBlocks lb2.
Proof.
  induction lb1; intros.
    split; auto using uniqBlocks_nil.

    destruct a.
    simpl in H.
    inversion H; subst. simpl in *.
    inversion H0; subst.
    clear H H0.
    rewrite getBlocksLocs_app in H1.
    rewrite getBlocksLabels_app in H4, H5.
    apply NoDup_inv in H5. destruct H5.
    simpl_env in H1.
    rewrite ass_app in H1.
    rewrite ass_app in H1.
    rewrite ass_app in H1.
    apply NoDup_inv in H1. destruct H1.
    apply NotIn_inv in H4. destruct H4.
    split.
      split; simpl. 
        auto using NoDup_cons.
        rewrite <- ass_app in H1.
        rewrite <- ass_app in H1.
        simpl_env. auto.
      split; auto.
Qed.

Lemma genLabel2Block_blocks_inv : forall lb l0 l' ps' cs' tmn',
  uniqBlocks lb ->
  lookupAL _ (genLabel2Block_blocks lb) l0 = Some (block_intro l' ps' cs' tmn') ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') (fdef_intro lb).
Proof.
  induction lb; intros; simpl in *.
    inversion H0.

    assert (J:=H).
    apply uniqBlocks__uniqLabel2Block in H.
    apply mergeALs_inv in H0; auto.
    destruct H0 as [H0 | H0].
      unfold genLabel2Block_block in H0.
      destruct a. simpl in H0.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); subst.
        inversion H0; subst. clear H0.
        split; auto.
        apply orb_true_intro.
        left. apply blockEqB_refl.

        inversion H0.

      simpl_env in J. 
      apply uniqBlocks_inv in J.
      destruct J.
      apply IHlb in H0; simpl_env; auto.
      destruct H0.
      split; auto.
      apply orb_true_intro; auto.
Qed.

Lemma lookupBlockViaLabelFromFdef_inv : forall F l0 l' ps' cs' tmn',
  uniqFdef F ->
  lookupBlockViaLabelFromFdef F l0 = Some (block_intro l' ps' cs' tmn') ->
  l0 = l' /\
  blockInFdefB (block_intro l' ps' cs' tmn') F.
Proof.
  intros.
  unfold lookupBlockViaLabelFromFdef in H.
  unfold genLabel2Block_fdef in H.
  destruct F.
  apply genLabel2Block_blocks_inv; auto.
Qed. 

Lemma lookupBlockViaLabelFromFdef__blockInFdefB : forall F l0 B,
  uniqFdef F ->
  lookupBlockViaLabelFromFdef F l0 = Some B ->
  blockInFdefB B F.
Proof.
  intros.
  destruct B. apply lookupBlockViaLabelFromFdef_inv in H0; auto.
  destruct H0; auto.
Qed. 

Lemma entryBlockInFdef : forall F B,
  getEntryBlock F = Some B ->
  blockInFdefB B F.
Proof.
  intros.
  unfold getEntryBlock in H.
  destruct F.
  destruct b; inversion H; subst.
    simpl. 
    apply orb_true_intro.
    left. apply blockEqB_refl.
Qed.

Lemma NotIn_NotInBlocksB : forall lb l0 ps cs tmn,
  ~ In l0 (getBlocksLabels lb) ->
  ~ InBlocksB (block_intro l0 ps cs tmn) lb.
Proof.
  induction lb; intros; simpl in *.
    intro J. inversion J.

    destruct a.
    simpl in *.
    remember (block_intro l0 ps cs tmn =b= block_intro l1 p c t) as J.
    destruct J.
      unfold blockEqB in HeqJ.
      unfold lEqB in HeqJ.
      destruct (l0==l1); subst.
        contradict H; auto.

        symmetry in HeqJ.
        apply sumbool2bool_true in HeqJ.
        inversion HeqJ; subst.
        contradict n; auto.

      intro J.
      apply H.
      right.
      apply orb_prop in J.
      destruct J as [J | J].
        inversion J.
     
        destruct (@In_dec _ eq_dec l0 (getBlocksLabels lb)) as [J1 | J1]; auto.
        apply IHlb with (ps:=ps)(cs:=cs)(tmn:=tmn) in J1.
        rewrite J in J1.
        contradict J1; auto.
        unfold is_true. auto.
Qed.

Lemma InBlocksB_In : forall lb l0 ps cs tmn,
  InBlocksB (block_intro l0 ps cs tmn) lb ->
  In l0 (getBlocksLabels lb).
Proof.
  intros.
  destruct (@In_dec _ eq_dec l0 (getBlocksLabels lb)) as [J1 | J1]; auto.
    apply NotIn_NotInBlocksB with (ps:=ps)(cs:=cs)(tmn:=tmn) in J1.
    contradict H; auto.
Qed.

Lemma InBlocksB__NotIn : forall l2 bs l0 cs ps tmn,
  InBlocksB (block_intro l0 cs ps tmn) bs = true ->
  ~ In l2 (getBlocksLabels bs) ->
  l0 <> l2.
Proof.
  intros l2 bs l0 cs ps tmn HbInF H1.
  apply InBlocksB_In in HbInF.
  destruct (eq_dec l0 l2); subst; auto.
Qed.

Lemma InBlocksB__lookupAL : forall bs l3 ps cs tmn
  (Huniq : uniqBlocks bs)
  (HBinF : InBlocksB (block_intro l3 ps cs tmn) bs = true)
  (b1 : block)
  (J9 : lookupAL block (genLabel2Block_blocks bs) l3 = Some b1),
  b1 = block_intro l3 ps cs tmn.
Proof.
  intros.
  simpl in Huniq.
  induction bs; simpl in *.
    inversion J9; subst.

    apply orb_prop in HBinF.   
    destruct HBinF as [HBinF | HBinF].
      apply blockEqB_inv in HBinF; subst.
      simpl in J9.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l3 l3); subst;
        simpl.
        inversion J9; subst; auto.
        contradict n; auto.

      assert (Huniq':=Huniq).
      simpl_env in Huniq'.
      apply uniqBlocks_inv in Huniq'.
      destruct Huniq'.
      destruct a. destruct Huniq as [Huniq _]. simpl in *.
      inversion Huniq; subst.
      assert (J:=HBinF).
      apply InBlocksB_In in J.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l3 l0); subst.
        contradict J; auto.
        apply IHbs; auto.
Qed.

Lemma InBlocksB_uniq : forall lb l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  uniqBlocks lb ->
  InBlocksB (block_intro l1 ps1 cs1 tmn1) lb ->
  InBlocksB (block_intro l1 ps2 cs2 tmn2) lb ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  induction lb; intros.
    unfold InBlocksB in *.
    inversion H0.

    inversion H; subst. clear H.
    simpl in *.
    destruct a.
    inversion H2; subst. clear H2.
    assert (J:=H5).
    apply NotIn_NotInBlocksB with (ps:=p)(cs:=c)(tmn:=t) in H5.
    apply orb_prop in H0.
    apply orb_prop in H1.
    destruct H0 as [H0 | H0].    
      apply blockEqB_inv in H0.
      inversion H0; subst. clear H0.
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1.
        inversion H1; subst. clear H1.
        auto.

        apply InBlocksB_In in H1.
        contradict H1; auto.
 
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1.
        inversion H1; subst. clear H1.
        apply InBlocksB_In in H0.
        contradict H0; auto.

        eapply IHlb; eauto.
          apply NoDup_split in H3.
          destruct H3.
          split; auto.
Qed.

Lemma blockInFdefB_uniq : forall l1 ps1 cs1 tmn1 ps2 cs2 tmn2 F,
  uniqFdef F ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F ->
  blockInFdefB (block_intro l1 ps2 cs2 tmn2) F ->
  ps1 = ps2 /\ cs1 = cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold blockInFdefB in *.
  destruct F. 
  eapply InBlocksB_uniq; eauto.
Qed.

Lemma nth_error__InBlocksB : forall n lb B,
  nth_error lb n = Some B ->
  InBlocksB B lb.
Proof.
  induction n; intros; simpl in *.
    destruct lb; inversion H; subst; simpl.
      apply orb_true_intro.
      left. apply blockEqB_refl.

    destruct lb; inversion H; subst; simpl.
      apply orb_true_intro.
      right. apply IHn; auto.
Qed.

Lemma blockInFdefB__exists_nth_error : forall lb B,
  blockInFdefB B (fdef_intro lb) ->
  exists n, nth_error lb n = Some B.
Proof.
  induction lb; intros; simpl in *.
    inversion H.

    apply orb_prop in H.
    destruct H.
      apply blockEqB_inv in H. subst.
      exists O. simpl; auto.

      apply IHlb in H; auto.
      destruct H as [n H].
      exists (S n). simpl. auto.
Qed.

Lemma nth_error__blockInFdef : forall lb n B,
  nth_error lb n = Some B ->
  blockInFdef B (fdef_intro lb).
Proof.
  intros.
  eapply nth_error__InBlocksB; eauto.
Qed.

(* uniqness *)

Lemma nth_error__lookupAL_genLabel2Block_blocks : forall n lb1 B1,
  uniqBlocks lb1 ->
  nth_error lb1 n = Some B1 ->
  exists l0,  lookupAL _ (genLabel2Block_blocks lb1) l0 = Some B1.
Proof.
  induction n; intros.
    simpl in H0. destruct lb1; inversion H0; subst.
    exists (getBlockLabel B1).
    simpl. destruct B1. simpl.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 l0); subst; auto.
      contradict n; auto.

    simpl in H0.
    destruct lb1; inversion H0; subst.
    simpl_env in H.
    assert (J:=H).
    apply uniqBlocks_inv in J. destruct J.
    apply IHn in H0; auto.
    destruct H0 as [l0 H0].
    exists l0. simpl. destruct b.
    destruct H. simpl in *.
    inversion H; subst.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l1); subst; auto.
      apply lookupAL_Some_indom in H0.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      contradict H0; auto.

      rewrite H2. auto.
Qed.          

Lemma nth_error_uniqBlocks__indom : forall n lb B,
  uniqBlocks lb ->
  nth_error lb n = Some B ->
  (getBlockLabel B) `in` dom (genLabel2Block_blocks lb).
Proof.
  induction n; intros.
    destruct lb; inversion H0; subst.
    simpl in *.
    assert (J:=@getBlockLabel_in_genLabel2Block_block B).
    simpl_env. fsetdec.

    destruct lb; try solve [inversion H0].
    simpl in *.
    simpl_env in H.
    apply uniqBlocks_inv in H. 
    destruct H.
    apply IHn in H0; auto.
    simpl_env. fsetdec.
Qed.

Lemma uniqBlocks__uniq_nth_error : forall n lb1 n' B1,
  uniqBlocks lb1 ->
  nth_error lb1 n = Some B1 ->
  nth_error lb1 n' = Some B1 ->
  n = n'.
Proof.
  induction n; intros.
    destruct n'; auto.
      simpl in *.
      destruct lb1; inversion H0; subst.
      assert (J:=H).
      simpl_env in J. apply uniqBlocks_inv in J. destruct J.
      apply nth_error_uniqBlocks__indom in H1; auto.
      destruct H. simpl in H. destruct B1. inversion H; subst.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      simpl in H1. contradict H7; auto.

    destruct n'; auto.
      simpl in *.
      destruct lb1; inversion H1; subst.
      assert (J:=H).
      simpl_env in J. apply uniqBlocks_inv in J. destruct J.
      apply nth_error_uniqBlocks__indom in H0; auto.
      destruct H. simpl in H. destruct B1. inversion H; subst.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H7.
      simpl in H0. contradict H7; auto.
     
      simpl in *.
      destruct lb1; inversion H0.
      simpl_env in H. apply uniqBlocks_inv in H. destruct H.
      apply IHn with (n':=n')(B1:=B1) in H0; auto.
Qed.      
      
Lemma uniqBlocks__uniqBlock : forall lb n l1 ps1 cs1 tmn1,
  uniqBlocks lb ->
  nth_error lb n = Some (block_intro l1 ps1 cs1 tmn1) ->
  NoDup (getCmdsLocs cs1).
Proof.
  induction lb; intros.
    apply nil_nth_error_Some__False in H0.
    inversion H0.

    apply nth_error_cons__inv in H0.
    simpl_env in H. 
    apply uniqBlocks_inv in H.
    destruct H as [J1 J2].
    destruct H0 as [EQ | [n' [EQ H0]]]; subst; eauto.
      unfold uniqBlocks in J1.
      destruct J1.
      simpl in H0.
      simpl_env in H0.
      apply NoDup_inv in H0.
      destruct H0.
      apply NoDup_inv in H1.
      destruct H1; auto.
Qed.

Lemma uniqFdef__uniqBlock : forall lb n l1 ps1 cs1 tmn1,
  uniqFdef (fdef_intro lb) ->
  nth_error lb n = Some (block_intro l1 ps1 cs1 tmn1) ->
  NoDup (getCmdsLocs cs1).
Proof.
  intros.
  unfold uniqFdef in H.
  eapply uniqBlocks__uniqBlock; eauto.
Qed.

Lemma lookupAL_update_udb_eq : forall ud l0 l1,
  exists ls0, lookupAL _ (update_udb ud l0 l1) l1 = Some ls0 /\ In l0 ls0.
Proof.
  intros.
  unfold update_udb.
  remember (lookupAL (list l) ud l1) as R1.
  destruct R1.
    remember (in_dec l_dec l0 l2) as R2.
    destruct R2.
      exists l2. split; auto.
      exists (l0 :: l2). simpl. split; auto.
        apply lookupAL_updateAddAL_eq; auto.
    remember (in_dec l_dec l0 nil) as R2.
    destruct R2.
      inversion i0.
      exists (l0 :: nil). simpl. split; auto.
        apply lookupAL_updateAddAL_eq; auto.
Qed.  

Lemma update_udb__mono : forall l0 ud l1 l2,
  l0 `in` dom ud ->
  l0 `in` dom (update_udb ud l1 l2).
Proof.
  intros.
  unfold update_udb.
  destruct (in_dec l_dec l1
           match lookupAL (list l) ud l2 with
           | Some ls0 => ls0
           | merror => nil
           end); auto.
    apply updateAddAL_mono; auto.
Qed. 

Lemma lookupAL_update_udb_spec : forall l0 ud l1 l2 re,
  lookupAL _ ud l0 = Some re ->
  exists re', lookupAL _ (update_udb ud l1 l2) l0 = Some re' /\
    incl re re'.
Proof.
  intros.
  unfold update_udb.
  remember (lookupAL (list l) ud l2) as R1.
  destruct R1.
    remember (in_dec l_dec l1 l3) as R2.
    destruct R2.
      exists re. split; auto using incl_refl.
      destruct (eq_atom_dec l2 l0); subst.
        rewrite H in HeqR1. inversion HeqR1; subst.
        exists (l1 :: re). 
        split.
          apply lookupAL_updateAddAL_eq; auto.
          apply incl_tl; auto using incl_refl.
        exists re. 
        split.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          auto using incl_refl.

    remember (in_dec l_dec l1 nil) as R2.
    destruct R2.
      inversion i0.
      destruct (eq_atom_dec l2 l0); subst.
        rewrite H in HeqR1. inversion HeqR1.

        exists re. 
        split.
          rewrite <- lookupAL_updateAddAL_neq; auto.
          auto using incl_refl.
Qed.  

Definition usedef_block_inc (ud1 ud2:usedef_block) :=
  forall l0 l1, 
     lookupAL _ ud1 l0 = Some l1 ->
     exists l2, lookupAL _ ud2 l0 = Some l2 /\ incl l1 l2.

Lemma update_udb_inc : forall ud1 ud2 l1 l2,
  usedef_block_inc ud1 ud2 ->
  usedef_block_inc (update_udb ud1 l1 l2) (update_udb ud2 l1 l2).
Proof.
  unfold update_udb.
  intros.
  remember (lookupAL (list l) ud1 l2) as R1.
  remember (lookupAL (list l) ud2 l2) as R2.
  destruct R1.
    symmetry in HeqR1.
    apply H in HeqR1.
    destruct HeqR1 as [l3' [J1 J2]].
    rewrite J1 in HeqR2. subst.
    destruct (in_dec l_dec l1 l0).
        destruct (in_dec l_dec l1 l3'); auto.
          apply J2 in i0. contradict i0; auto.
        destruct (in_dec l_dec l1 l3').
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             exists l3'. split; auto.
             intros z H0.
             simpl in H0.               
             destruct H0 as [H0 | H0]; subst; eauto.

             rewrite <- lookupAL_updateAddAL_neq in J; auto.
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             rewrite lookupAL_updateAddAL_eq.
             exists (l1::l3'). split; auto.
             intros z H0.
             simpl in H0. simpl.               
             destruct H0 as [H0 | H0]; subst; eauto.

             rewrite <- lookupAL_updateAddAL_neq in J; auto.
             rewrite <- lookupAL_updateAddAL_neq; auto.
    destruct R2. 
      destruct (in_dec l_dec l1 nil).
        inversion i0.
        destruct (in_dec l_dec l1 l0).
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             exists l0. split; auto.
             intros z H0.
             simpl in H0.               
             destruct H0 as [H0 | H0]; subst; auto.
               inversion H0.
             rewrite <- lookupAL_updateAddAL_neq in J; auto.
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             rewrite lookupAL_updateAddAL_eq.
             exists (l1::l0). split; auto.
             intros z H0.
             simpl in H0. simpl.               
             destruct H0 as [H0 | H0]; subst; auto.
               inversion H0.
             rewrite <- lookupAL_updateAddAL_neq in J; auto.
             rewrite <- lookupAL_updateAddAL_neq; auto.
      destruct (in_dec l_dec l1 nil).
        inversion i0.
        destruct (in_dec l_dec l1 nil).
          inversion i0.
          intros x ls0 J.
          destruct (eq_atom_dec l2 x); subst.
             rewrite lookupAL_updateAddAL_eq in J. inv J.
             rewrite lookupAL_updateAddAL_eq.
             exists (l1::nil). split; auto using incl_refl.

             rewrite <- lookupAL_updateAddAL_neq in J; auto.
             rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma genBlockUseDef_block_inc : forall b ud1 ud2,
  usedef_block_inc ud1 ud2 ->
  usedef_block_inc (genBlockUseDef_block b ud1) (genBlockUseDef_block b ud2).
Proof.
  intros. 
  destruct b. simpl. 
  destruct t; auto.
    apply update_udb_inc; auto.
    apply update_udb_inc; auto.
    apply update_udb_inc; auto.
Qed.

Lemma genBlockUseDef_blocks_inc : forall bs ud1 ud2,
  usedef_block_inc ud1 ud2 ->
  usedef_block_inc (genBlockUseDef_blocks bs ud1) (genBlockUseDef_blocks bs ud2).
Proof.
  induction bs; simpl; intros; auto.
    apply IHbs.
    apply genBlockUseDef_block_inc; auto.
Qed.

Lemma hasNonPredecessor__mono : forall b bs ud,
  hasNonePredecessor b (genBlockUseDef_blocks bs ud) = true ->
  hasNonePredecessor b (genBlockUseDef_blocks bs nil) = true.
Proof.
  unfold hasNonePredecessor.
  unfold predOfBlock.
  intros.
  assert (usedef_block_inc nil ud) as J0.
    intros x l0 J. inversion J.
  assert (J:=@genBlockUseDef_blocks_inc bs nil ud J0).
  remember (lookupAL (list l) (genBlockUseDef_blocks bs ud) (getBlockLabel b))
    as R1.  
  remember (lookupAL (list l) (genBlockUseDef_blocks bs nil) (getBlockLabel b))
    as R2.
  destruct R1.
    destruct R2; auto.
      destruct l1; auto.
        destruct l0; inversion H.
          symmetry in HeqR2.
          apply J in HeqR2. 
          destruct HeqR2 as [l3 [J1 J2]].
          rewrite J1 in HeqR1. inv HeqR1.
          assert (In l1 (l1::l2)) as J'. simpl. auto.
          apply J2 in J'. inv J'.
    destruct R2; auto.
      destruct l0; auto.
        symmetry in HeqR2.
        apply J in HeqR2. 
        destruct HeqR2 as [l3 [J1 J2]].
        rewrite J1 in HeqR1. inv HeqR1.
Qed.

Lemma getValueViaLabelFromValuels__nth_list_value_l : forall
  (l1 : l)  v vls
  (J : getValueViaLabelFromValuels vls l1 = Some v),
  exists n, nth_list_value_l n vls = Some (v, l1).
Proof.
  intros.
  induction vls; intros; simpl in *.
    inversion J.

    destruct (l0 == l1); subst.
      inversion J; subst; simpl in *.
      exists 0%nat. auto.

      destruct IHvls as [n' IHvls]; auto.
      exists (S n'). simpl. auto.
Qed.

Lemma genBlockUseDef_blocks__mono : forall bs ud l0,
  l0 `in` dom ud ->
  l0 `in` dom (genBlockUseDef_blocks bs ud).
Proof.
  induction bs; intros ud l0 Hin; simpl in *; auto.  
    destruct a; simpl.
    destruct t; simpl; auto.
      apply IHbs. 
        apply update_udb__mono; auto.
        apply update_udb__mono; auto.
      apply IHbs. 
        apply update_udb__mono; auto.
Qed.        

Lemma lookupAL_genBlockUseDef_blocks_spec : forall bs l0 ud re,
  lookupAL _ ud l0 = Some re ->
  exists re', lookupAL _ (genBlockUseDef_blocks bs ud) l0 = Some re' /\
    incl re re'.
Proof.
  induction bs; intros ud l0 re Hin; simpl in *; auto.  
    exists re. split; auto using incl_refl.

    destruct a.
    destruct t; simpl; auto.
      apply lookupAL_update_udb_spec with (l1:=l1)(l2:=l3) in Hin.
      destruct Hin as [re1 [Hin Hinc1]].
      apply lookupAL_update_udb_spec with (l1:=l1)(l2:=l2) in Hin.
      destruct Hin as [re2 [Hin Hinc2]].
      apply IHbs in Hin.
      destruct Hin as [re3 [Hin Hinc3]].
      exists re3. split; eauto using incl_tran.

      apply lookupAL_update_udb_spec with (l1:=l1)(l2:=l2) in Hin.
      destruct Hin as [re1 [Hin Hinc1]].
      apply IHbs in Hin.
      destruct Hin as [re2 [Hin Hinc2]].
      exists re2. split; eauto using incl_tran.
Qed.        

Lemma InPhiNodes_lookupIDFromPhiNodes : forall ps id1,
  In id1 (getPhiNodesIDs ps) ->
  lookupIDFromPhiNodes ps id1 = Some tt.
Proof.
  induction ps; intros; simpl in *.
    inversion H. 

    destruct H as [H | H]; subst; auto.
      destruct a. simpl. unfold lookupIDFromPhiNode. simpl.
      destruct (i0==i0); subst; auto.
        contradict n; auto.

      apply IHps in H.
      rewrite H.
      destruct (lookupIDFromPhiNode a id1); auto.
        destruct u; auto.
Qed.

Lemma InPhiNodes_lookupIDFromFdef : forall f id1 l' ps cs tmn,
  Some (block_intro l' ps cs tmn) = lookupBlockViaLabelFromFdef f l' ->
  In id1 (getPhiNodesIDs ps) ->
  lookupIDFromFdef f id1 = Some tt.
Proof.
  intros.
  destruct f.
  simpl in *.
  induction b; simpl in *.
    inversion H.
    
    destruct a. simpl in *.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l' l0); subst.
      inversion H; subst.
      apply InPhiNodes_lookupIDFromPhiNodes in H0.
      rewrite H0. auto.
      
      apply IHb in H.
      rewrite H. 
      destruct (lookupIDFromPhiNodes p id1); auto. destruct u; auto.
      destruct (lookupIDFromCmds c id1); auto. destruct u; auto.
      destruct (lookupIDFromTerminator t id1); auto. destruct u; auto.
Qed.  

Lemma InBlocksB__lookupAL_genLabel2Block_blocks : forall lb1 l' ps' cs' tmn',
  uniqBlocks lb1 ->
  InBlocksB (block_intro l' ps' cs' tmn') lb1 ->
  lookupAL _ (genLabel2Block_blocks lb1) l' = Some (block_intro l' ps' cs' tmn').
Proof.
  induction lb1; intros.
    inversion H0.

    simpl in H0. destruct a. simpl.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0.
      inv H0.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 l0); subst; 
        auto.
        contradict n; auto.

        simpl_env in H.
        assert (J:=H).
        apply uniqBlocks_inv in J. destruct J.
        eapply IHlb1 in H2; eauto.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l' l0); subst;
          auto.

      destruct H.
      simpl in H. inv H.
      apply lookupAL_Some_indom in H2.
      apply NotInGetBlocksLabels__NotInGenLabel2Block_blocks in H6.
      contradict H6; auto.
Qed.          

Lemma blockInFdefB_lookupBlockViaLabelFromFdef : forall F l' ps' cs' tmn',
  uniqFdef F ->
  blockInFdefB (block_intro l' ps' cs' tmn') F ->
  lookupBlockViaLabelFromFdef F l' = Some (block_intro l' ps' cs' tmn').
Proof.
  intros. destruct F. simpl in *.
  apply InBlocksB__lookupAL_genLabel2Block_blocks; auto.
Qed.

Lemma lookupBlockViaIDFromFdef__blockInFdefB : forall F id1 B,
  lookupBlockViaIDFromFdef F id1 = Some B ->
  blockInFdefB B F.
Proof.         
  intros.
  destruct F.
  simpl in *.
  induction b; simpl in *.
    inversion H.

    destruct a. simpl in *.
    destruct (in_dec eq_dec id1 (getPhiNodesIDs p ++ getCmdsIDs c)).
      inv H. apply orb_true_iff. left.
      apply blockEqB_refl.

      apply orb_true_iff. right. apply IHb in H; auto.
Qed.

Lemma lookupBlockViaIDFromFdef__InGetBlockIDs : forall F id1 B,
  lookupBlockViaIDFromFdef F id1 = Some B ->
  In id1 (getBlockIDs B).
Proof.         
  intros.
  destruct F.
  simpl in *.
  induction b; simpl in *.
    inversion H.

    destruct a. simpl in *.
    remember (in_dec eq_dec id1 (getPhiNodesIDs p ++ getCmdsIDs c)) as R.
    destruct R; eauto.
      inv H. auto.
Qed.

Lemma getValueViaLabelFromValuels__In : forall vls v l1 vs1 ls1,
  getValueViaLabelFromValuels vls l1 = Some v ->
  split (unmake_list_value_l vls) = (vs1, ls1) ->
  In l1 ls1.
Proof.
  induction vls; intros; simpl in *.
    inversion H.

    remember (split (unmake_list_value_l vls)) as R.
    destruct R.
    inv H0.
    destruct (l0 == l1); subst.
      simpl. auto.

      simpl. right. eauto.
Qed.

Lemma In__getValueViaLabelFromValuels : forall vls l1 vs1 ls1,
  In l1 ls1 ->
  split (unmake_list_value_l vls) = (vs1, ls1) ->
  NoDup ls1 ->
  exists v, getValueViaLabelFromValuels vls l1 = Some v.
Proof.
  induction vls; intros; simpl in *.
    inv H0. inversion H.
   
    destruct (l0 == l1); subst; eauto.
    remember (split (unmake_list_value_l vls)) as R.
    destruct R.
    symmetry in HeqR.
    inv H0. inv H1.
    simpl in H.
    destruct H as [H | H]; subst.
      contradict n; auto.
    
      eapply IHvls in H; eauto.
Qed.      

Lemma valueInTmnOperands__InOps : forall vid tmn,
  valueInTmnOperands (value_id vid) tmn ->
  In vid (getInsnOperands (insn_terminator tmn)).
Proof.
  intros vid tmn H.
  destruct tmn; simpl in *; subst; simpl; eauto.
Qed.

Lemma In_middle : forall A (c:A) cs1 cs2, In c (cs1++c::cs2).
Proof.                    
  induction cs1; simpl; auto.
Qed.

Lemma valueInCmdOperands__InOps : forall vid c,
  valueInCmdOperands (value_id vid) c ->
  In vid (getInsnOperands (insn_cmd c)).
Proof.
  intros vid c H.
  destruct c; simpl in *; try solve [
    destruct H; subst; simpl; try solve [auto | apply in_or_app; simpl; auto]
  ].
Qed.

Lemma uniqF__uniqBlocks : forall lb,
  uniqFdef (fdef_intro lb) -> uniqBlocks lb.
Proof.
  intros. inversion H; auto.
Qed.

Lemma getCmdID_in_getCmdsLocs : forall cs i0 c,
  getCmdID c = Some i0 ->
  In c cs ->
  In i0 (getCmdsLocs cs ).
Proof.
  induction cs; intros.
    inversion H0.

    simpl in *. 
    destruct H0 as [H0 | H0]; subst; eauto.
      apply getCmdLoc_getCmdID in H; auto.   
Qed.

Lemma getCmdLoc_in_getCmdsLocs : forall cs c,
  In c cs ->
  In (getCmdLoc c) (getCmdsLocs cs).
Proof.
  induction cs; intros.
    inversion H.

    simpl in *. 
    destruct H as [H | H]; subst; eauto.
Qed.

Lemma in_getBlockLocs__in_getBlocksLocs : forall bs b i0,
  In i0 (getBlockLocs b) ->
  InBlocksB b bs ->
  In i0 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros.
    inversion H0.

    apply orb_prop in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0. subst.
      apply in_or_app; auto.
    
      apply in_or_app; eauto.
Qed.

Lemma NotInPhiNodesIDs__lookupIDFromPhiNodes : forall la id1,
  ~ In id1 (getPhiNodesIDs la) ->
  lookupIDFromPhiNodes la id1 = None.
Proof.
  induction la; intros; simpl in *; auto.
    destruct a. unfold lookupIDFromPhiNode.
    simpl in H. simpl.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst; 
      eauto.
      contradict H; eauto.
Qed.

Lemma NotInCmdLocs__lookupIDFromCmds : forall cs id1,
  ~ In id1 (getCmdsLocs cs) ->
  lookupIDFromCmds cs id1 = None.
Proof.
  induction cs; intros; simpl in *; auto.
    unfold lookupIDFromCmd.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 (getCmdLoc a)); 
      subst; eauto.
    contradict H; auto.
Qed.

Lemma lookupIDFromCmds__InCmdsLocs : forall cs id1 t,
  lookupIDFromCmds cs id1 = Some t ->
  In id1 (getCmdsLocs cs).
Proof.
  intros.
  destruct (In_dec eq_atom_dec id1 (getCmdsLocs cs)); auto.
    apply NotInCmdLocs__lookupIDFromCmds in n.   
    rewrite H in n. inversion n.
Qed.

Lemma lookupIDFromPhiNodes__InPhiNodesIDs : forall la id1 t,
  lookupIDFromPhiNodes la id1 = Some t ->
  In id1 (getPhiNodesIDs la).
Proof.
  intros.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs la)); auto.
    apply NotInPhiNodesIDs__lookupIDFromPhiNodes in n.   
    rewrite H in n. inversion n.
Qed.

Lemma notInBlock__lookupIDFromBlock : forall b i0,
  ~ In i0 (getBlockLocs b) ->
  lookupIDFromBlock b i0 = None.
Proof.
  intros.
  destruct b. simpl in *.
  remember (lookupIDFromPhiNodes p i0) as R.
  destruct R.
    symmetry in HeqR.    
    apply lookupIDFromPhiNodes__InPhiNodesIDs in HeqR.
    contradict H. apply in_or_app; auto.
  remember (lookupIDFromCmds c i0) as R1.
  destruct R1.
    symmetry in HeqR1. destruct u.   
    apply lookupIDFromCmds__InCmdsLocs in HeqR1.
    contradict H. apply in_or_app. right. apply in_or_app; auto.
  unfold lookupIDFromTerminator.
  destruct (i0 == getTerminatorID t); subst; auto.
    contradict H. apply in_or_app. right. apply in_or_app; simpl; auto.
Qed.

Lemma lookupIDFromBlock__inBlock : forall b i0 t0,
  lookupIDFromBlock b i0 = Some t0 -> In i0 (getBlockLocs b).
Proof.
  intros.
  destruct (In_dec eq_atom_dec i0 (getBlockLocs b)); auto.
    apply notInBlock__lookupIDFromBlock in n.   
    rewrite H in n. inversion n.
Qed.

Lemma lookupIDFromBlock__inBlocks : forall bs b i0 t0,
  lookupIDFromBlock b i0 = Some t0 ->
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  lookupIDFromBlocks bs i0 = Some t0.
Proof.
  induction bs; simpl; intros.
    inversion H1.

    assert (J:=H0).
    apply NoDup_inv in H0. destruct H0.
    apply orb_prop in H1.
    destruct H1 as [H1 | H1]; eauto.
      apply blockEqB_inv in H1. subst.
      rewrite H. auto.
    
      assert (H':=H).
      apply lookupIDFromBlock__inBlock in H.
      apply NoDup_disjoint with (i0:=i0) in J; 
        eauto using in_getBlockLocs__in_getBlocksLocs.
      apply notInBlock__lookupIDFromBlock in J.
      rewrite J. eauto.
Qed.

Lemma NoDup__InBlocksB : forall bs b,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  NoDup (getBlockLocs b).
Proof.
  induction bs; simpl; intros.
    inversion H0.

    apply NoDup_inv in H. destruct H.
    apply orb_prop in H0.
    destruct H0 as [H0 | H0]; eauto.
      apply blockEqB_inv in H0. subst. auto.
Qed.

Lemma InCmds_lookupIDFromPhiNodes : forall cs id1 c,
  NoDup (getCmdsLocs cs) ->
  In c cs ->
  getCmdID c = Some id1 ->
  lookupIDFromCmds cs id1 = Some tt.
Proof.
  induction cs; intros.
    inversion H0.

    simpl in *.
    inv H. unfold lookupIDFromCmd.
    destruct H0 as [H0 | H0]; subst.
      apply getCmdLoc_getCmdID in H1.
      rewrite H1.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 id1); subst;
        auto.
        contradict n; auto.

      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 (getCmdLoc a));
        subst; eauto.
Qed.

Lemma uniqF__lookupIDFromFdef : forall l1 ps1 cs1 tmn1 f c i0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  In c cs1 ->
  getCmdID c = Some i0 ->
  lookupIDFromFdef f i0 = Some tt.
Proof.
  intros.
  destruct f. inversion H.
  assert (In i0 (getCmdsLocs cs1)) as HInCs.
    eapply getCmdID_in_getCmdsLocs in H1; eauto.
  assert (In i0 (getBlocksLocs b)) as Hin.
    eapply in_getBlockLocs__in_getBlocksLocs in H0; eauto.
    simpl. apply in_or_app. right. apply in_or_app; auto.
  destruct H as [J1 J2].
  eapply lookupIDFromBlock__inBlocks; eauto.
  simpl.
  apply NoDup__InBlocksB in H0; auto.
  simpl in H0.
  rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsLocs cs1) ++ [getTerminatorID tmn1])
    in H0.
  apply NoDup_inv in H0. destruct H0 as [H0 _].
  assert (~ In i0 (getPhiNodesIDs ps1)) as HnotinPs.
    eapply NoDup_disjoint; eauto.
  apply NotInPhiNodesIDs__lookupIDFromPhiNodes in HnotinPs.
  rewrite HnotinPs.
  apply NoDup_inv in H0. destruct H0 as [_ H0]. 
  erewrite InCmds_lookupIDFromPhiNodes; eauto.
Qed.

Lemma uniqFdef__uniqBlockLocs : forall F b1,
  uniqFdef F -> blockInFdefB b1 F -> NoDup (getBlockLocs b1).
Proof.
  intros.
  destruct F. simpl in H. destruct H as [_ H]. 
  apply NoDup__InBlocksB in H0; auto.
Qed.

Lemma notInBlocks__lookupIDFromBlocks : forall bs i0,
  ~ In i0 (getBlocksLocs bs) ->
  lookupIDFromBlocks bs i0 = None.
Proof.
  induction bs; simpl; intros; auto.
    rewrite notInBlock__lookupIDFromBlock.
      rewrite IHbs; auto.
      intro J. apply H. apply in_or_app. auto.
    intro J. apply H. apply in_or_app. auto.
Qed.    

Lemma lookupIDFromBlocks__InGetBlocksLocs: forall bs id5,
  lookupIDFromBlocks bs id5 = Some tt ->
  In id5 (getBlocksLocs bs).
Proof.
  intros.
  destruct (in_dec eq_atom_dec id5 (getBlocksLocs bs)); auto.
  apply notInBlocks__lookupIDFromBlocks in n.
  rewrite H in n. inv n.
Qed.

Lemma lookupIDFromBlocks__inBlocks : forall bs b i0,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  In i0 (getBlockLocs b) ->
  lookupIDFromBlocks bs i0 = lookupIDFromBlock b i0.
Proof.
  induction bs; simpl; intros.
    inversion H0.

    assert (J:=H).
    apply NoDup_inv in H. destruct H.
    apply orb_prop in H0. 
    destruct H0 as [H0 | H0]; eauto.
      apply blockEqB_inv in H0. subst.
      apply NoDup_disjoint' with (i0:=i0) in J; auto.
      apply notInBlocks__lookupIDFromBlocks in J.
      rewrite J. destruct (lookupIDFromBlock a i0); auto.

      apply NoDup_disjoint with (i0:=i0) in J;
        eauto using in_getBlockLocs__in_getBlocksLocs.
      rewrite notInBlock__lookupIDFromBlock; auto.
Qed.

Lemma InCmds_lookupIDFromCmds' : forall cs id1 c,
  NoDup (getCmdsLocs cs) ->
  In c cs ->
  getCmdID c = Some id1 ->
  lookupIDFromCmds cs id1 = Some tt.
Proof.
  induction cs; intros.
    inversion H0.

    simpl in *.
    inv H. unfold lookupIDFromCmd.
    destruct H0 as [H0 | H0]; subst.
      apply getCmdLoc_getCmdID in H1.
      rewrite H1.
      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 id1); subst; auto.
        contradict n; auto.

      destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 (getCmdLoc a));
        subst; eauto.
Qed.

Lemma uniqF__lookupIDFromFdef' : forall l1 ps1 cs1 tmn1 f c i0,
  uniqFdef f ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  In c cs1 ->
  getCmdID c = Some i0 ->
  lookupIDFromFdef f i0 = Some tt.
Proof.
  intros.
  destruct f. inversion H.
  simpl in *.
  assert (In i0 (getCmdsLocs cs1)) as HInCs.
    eapply getCmdID_in_getCmdsLocs in H1; eauto.
  assert (In i0 (getBlocksLocs b)) as Hin.
    eapply in_getBlockLocs__in_getBlocksLocs in H0; eauto.
    simpl. apply in_or_app. right. apply in_or_app; auto.
  destruct H as [J1 J2].
  erewrite lookupIDFromBlocks__inBlocks; eauto. 
    simpl.
    apply NoDup__InBlocksB in H0; auto.
    assert (J:=H0).
    rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsLocs cs1) ++ 
      [getTerminatorID tmn1]) in H0.
    apply NoDup_inv in H0. destruct H0 as [H0 _].
    assert (~ In i0 (getPhiNodesIDs ps1)) as HnotinPs.
      eapply NoDup_disjoint in H0; eauto.
    apply NotInPhiNodesIDs__lookupIDFromPhiNodes in HnotinPs.
    rewrite HnotinPs.
    apply NoDup_inv in H0. destruct H0 as [_ H0]. 
    erewrite InCmds_lookupIDFromCmds'; eauto.
    simpl. apply in_or_app. right. apply in_or_app. auto.
Qed.

Lemma lookupIDFromFdef__lookupIDFromPhiNodes : forall F id1 t b1,
  uniqFdef F ->
  lookupIDFromFdef F id1 = Some t ->
  blockInFdefB b1 F ->
  In id1 (getPhiNodesIDs (getPHINodesFromBlock b1)) ->
  lookupIDFromPhiNodes (getPHINodesFromBlock b1) id1 = Some t. 
Proof.
  intros F id1 t b1 Huniq Hlk HBinF Hin.
  destruct F. simpl in *.
  destruct Huniq as [Huniq1 Huniq2].
  assert (Huniq2':=Huniq2).
  eapply NoDup__InBlocksB with (b:=b1) in Huniq2; eauto.
  destruct b1. simpl in *.
    erewrite lookupIDFromBlocks__inBlocks in Hlk; eauto.
      simpl in Hlk.
      destruct (lookupIDFromPhiNodes p id1); auto. 
      remember (lookupIDFromCmds c id1) as R.
      destruct R.
        symmetry in HeqR.
        apply lookupIDFromCmds__InCmdsLocs in HeqR.
        eapply NoDup_disjoint' with (i0:=id1) in Huniq2; eauto.
          contradict Huniq2. apply in_or_app; auto.
        
        unfold lookupIDFromTerminator in Hlk.
        destruct (id1 == getTerminatorID t0); subst; try solve [inv Hlk].
        eapply NoDup_disjoint' with (i0:=getTerminatorID t0) in Huniq2; eauto.
          contradict Huniq2. apply in_or_app. simpl. auto.
        
      simpl. apply in_or_app. auto.
Qed.

Lemma NoDupBlockLocs__notInCmds : forall l2 ps2 cs2' c' tmn',
  NoDup (getBlockLocs (block_intro l2 ps2 (cs2' ++ [c']) tmn')) ->
  ~ In (getCmdLoc c') (getCmdsLocs cs2').
Proof.
  intros.
  simpl in H.
  apply NoDup_inv in H.
  destruct H as [_ J].
  apply NoDup_inv in J.
  destruct J as [J _].
  rewrite getCmdsLocs_app in J.
  simpl in J.
  apply NoDup_last_inv in J. auto.
Qed.

Lemma NoDupBlockLocs__NoDupCmds : forall l2 ps2 cs2' tmn',
  NoDup (getBlockLocs (block_intro l2 ps2 cs2' tmn')) ->
  NoDup (getCmdsLocs cs2').
Proof.
  intros.
  simpl in H.
  apply NoDup_inv in H.
  destruct H as [_ J].
  apply NoDup_inv in J.
  destruct J as [J _]. auto.
Qed.

Lemma NoDup_lookupIDFromPhiNodes : forall ps1 i0 l0 ps2,
  NoDup (getPhiNodesIDs (ps1 ++ insn_phi i0 l0 :: ps2)) ->
  lookupIDFromPhiNodes (ps1 ++ insn_phi i0 l0 :: ps2) i0 = Some tt.
Proof.
  induction ps1; simpl; unfold lookupIDFromPhiNode; simpl; intros.
    destruct (i0 == i0); auto.
      contradict n; auto.

    destruct a.
    inv H. simpl.
    destruct (i0 == i1); subst; auto.
Qed.

Lemma in_middle : forall A (c:A) cs1 cs2, In c (cs1 ++ c :: cs2).
Proof.
  intros.
  apply in_app_iff; simpl; auto.
Qed.

Lemma uniqBlocksLocs__uniqBlockLocs : forall bs b,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  NoDup (getBlockLocs b).
Proof.
  induction bs; intros.
     inv H0.

     simpl in *.
     apply orb_prop in H0.
     apply NoDup_inv in H.
     destruct H.
     destruct H0 as [H0 | H0]; subst; auto.
       apply blockEqB_inv in H0; subst; auto.
Qed.

Lemma lookupBlockViaLabelFromFdef_prop : forall l1 p c t f l3 
  (Huniq: uniqFdef f),
  Some (block_intro l1 p c t) = lookupBlockViaLabelFromFdef f l3 ->
  Some (block_intro l1 p c t) = lookupBlockViaLabelFromFdef f l1.
Proof.
  intros.
  assert (J:=H).
  symmetry in H.
  eapply lookupBlockViaLabelFromFdef_inv in H; eauto.
  destruct H; subst. auto.
Qed.

Lemma lookupPhiNodeViaIDFromPhiNodes_middle : forall ps1 i0 l0 ps2,
  NoDup (getPhiNodesIDs (ps1 ++ insn_phi i0 l0 :: ps2)) ->
  lookupPhiNodeViaIDFromPhiNodes  (ps1 ++ insn_phi i0 l0 :: ps2) i0 =
    Some (insn_phi i0 l0).
Proof.
  induction ps1; simpl; intros; auto.
    destruct (i0==i0); try (auto || congruence).
    
    inv H. 
    destruct (i0==getPhiNodeID a); subst; eauto.
      rewrite getPhiNodesIDs_app in H2.
      apply NotIn_inv in H2. destruct H2.
      contradict H0; simpl; auto.
Qed.

Lemma notin__lookupPhiNodeViaIDFromPhiNodes_none : forall i0 ps,
  ~ In i0 (getPhiNodesIDs ps) ->
  lookupPhiNodeViaIDFromPhiNodes ps i0 = None.
Proof.
  induction ps; simpl; intros; auto.
    destruct(@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) i0 (getPhiNodeID a)); 
      subst; auto.
      contradict H; auto.
Qed.

Lemma In_weakening : forall A (l2 l3 l1:list A) a,
  In a (l1 ++ l3) -> In a (l1 ++ l2 ++ l3).
Proof.
  induction l1; simpl; intros.
    apply in_or_app; auto.
    destruct H as [H | H]; auto.
Qed.

Lemma NoDup_strenthening : forall A (l2 l3 l1:list A),
  NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof.
  induction l1; simpl; intros.
    apply NoDup_inv in H. destruct H; auto.

    inv H. apply NoDup_cons; auto using In_weakening.
Qed.

Lemma lookupCmdViaIDFromCmds__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    id0 l' ps' tmn' cs' c,
  NoDup (getBlockLocs (block_intro l' ps' cs' tmn')) ->
  lookupCmdViaIDFromCmds cs' id0 = Some c ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = None.
Proof.
  induction cs'; simpl; intros.
    congruence.

    destruct (eq_atom_dec id0 (getCmdLoc a)); inv H0.
      apply NoDup_disjoint with (i0:=getCmdLoc c) in H; simpl; 
        eauto using notin__lookupPhiNodeViaIDFromPhiNodes_none.
      eapply IHcs'; eauto.           
        simpl. simpl_env in *. apply NoDup_strenthening in H; auto.
Qed.

Lemma lookupPhiNodeViaIDFromPhinodes__In : forall id0 ps p,
  lookupPhiNodeViaIDFromPhiNodes ps id0 = Some p ->
  In id0 (getPhiNodesIDs ps).
Proof.
  induction ps; simpl; intros.
    congruence.
    destruct (id0 == getPhiNodeID a); inv H; eauto.
Qed.

Lemma lookupCmdViaIDFromCmds__In : forall id0 cs c,
  lookupCmdViaIDFromCmds cs id0 = Some c ->
  In id0 (getCmdsLocs cs).
Proof.
  induction cs; simpl; intros.
    congruence.
     destruct (eq_atom_dec id0 (getCmdLoc a)); inv H; eauto.
Qed.

Lemma lookupInsnViaIDFromBlock__In : forall b id0 instr,
  lookupInsnViaIDFromBlock b id0 = Some instr ->
  In id0 (getBlockLocs b).
Proof.
  destruct b; simpl; intros.
  remember (lookupPhiNodeViaIDFromPhiNodes p id0) as R1.
  destruct R1; inv H.
    apply in_or_app; eauto using lookupPhiNodeViaIDFromPhinodes__In.
    remember (lookupCmdViaIDFromCmds c id0) as R2.
    destruct R2; inv H1.
      apply in_or_app. right.
      apply in_or_app; eauto using lookupCmdViaIDFromCmds__In.
Qed.

Lemma lookupCmdViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    id0 c l' ps' cs' tmn' bs,
  NoDup (getBlocksLocs bs) ->
  lookupInsnViaIDFromBlocks bs id0 = Some (insn_cmd c) ->
  InBlocksB (block_intro l' ps' cs' tmn') bs ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = None.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H1. 
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst. simpl in H0.
      destruct (lookupPhiNodeViaIDFromPhiNodes ps' id0); inv H0.
      remember (lookupCmdViaIDFromCmds cs' id0) as R.
      destruct R; inv H2; auto.

      remember (lookupInsnViaIDFromBlock a id0) as R.
      assert (H':=H).
      apply NoDup_inv in H. destruct H.
      destruct R; inv H0; eauto.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR.
      eapply NoDup_disjoint' in H'; eauto.
      assert (~ In id0 (getBlockLocs (block_intro l' ps' cs' tmn'))) as J.
        eauto using in_getBlockLocs__in_getBlocksLocs.         
      apply notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
        intro J'. apply J. apply in_or_app; auto.
 Qed.

Lemma lookupTmnViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    bs id0 tmn l' ps' cs' tmn',
  NoDup (getBlocksLocs bs) ->
  lookupInsnViaIDFromBlocks bs id0 = Some (insn_terminator tmn) ->
  InBlocksB (block_intro l' ps' cs' tmn') bs ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = None.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H1. 
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst. simpl in H0.
      destruct (lookupPhiNodeViaIDFromPhiNodes ps' id0); inv H0.
      destruct (lookupCmdViaIDFromCmds cs' id0); inv H2; auto.

      remember (lookupInsnViaIDFromBlock a id0) as R.
      assert (H':=H).
      apply NoDup_inv in H. destruct H.
      destruct R; inv H0; eauto.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR.
      eapply NoDup_disjoint' in H'; eauto.
      assert (~ In id0 (getBlockLocs (block_intro l' ps' cs' tmn'))) as J.
        eauto using in_getBlockLocs__in_getBlocksLocs.         
      apply notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
        intro J'. apply J. apply in_or_app; auto.
Qed.

Lemma lookupNoneViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    bs id0 l' ps' cs' tmn',
  NoDup (getBlocksLocs bs) ->
  lookupInsnViaIDFromBlocks bs id0 = None ->
  InBlocksB (block_intro l' ps' cs' tmn') bs ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = None.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H1. 
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst. simpl in H0.
      destruct (lookupPhiNodeViaIDFromPhiNodes ps' id0).
        congruence. auto.

      apply NoDup_inv in H. destruct H.
      destruct (lookupInsnViaIDFromBlock a id0); inv H0; eauto.
Qed.

Lemma lookupPhiViaIDFromBlocks__lookupPhiNodeInsnViaIDFromPhiNodes : forall
    bs id0 p l' ps' cs' tmn' p',
  NoDup (getBlocksLocs bs) ->
  lookupInsnViaIDFromBlocks bs id0 = Some (insn_phinode p) ->
  InBlocksB (block_intro l' ps' cs' tmn') bs ->
  lookupPhiNodeViaIDFromPhiNodes ps' id0 = Some p' ->
  p = p'.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply orb_true_iff in H1. 
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst. simpl in H0.
      destruct (lookupPhiNodeViaIDFromPhiNodes ps' id0); congruence.

      remember (lookupInsnViaIDFromBlock a id0) as R.
      assert (H':=H).
      apply NoDup_inv in H. destruct H.
      destruct R; inv H0; eauto.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR.
      eapply NoDup_disjoint' in H'; eauto.
      assert (~ In id0 (getBlockLocs (block_intro l' ps' cs' tmn'))) as J.
        eauto using in_getBlockLocs__in_getBlocksLocs. 
      assert (lookupPhiNodeViaIDFromPhiNodes ps' id0 = None) as J'.
        apply notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
        intro J'. apply J. apply in_or_app; auto.
      rewrite H2 in J'. congruence.
Qed.

Lemma notin__lookupCmdViaIDFromCmds_none : forall id0 cs,
  ~ In id0 (getCmdsLocs cs) ->
  lookupCmdViaIDFromCmds cs id0 = None.
Proof.
  induction cs; simpl; intros; auto.
    destruct (eq_atom_dec id0 (getCmdLoc a)); subst; auto.
      contradict H; auto.
Qed.

Lemma notin__lookupPhiNodeViaIDFromPhinodes_none : forall id0 ps,
  ~ In id0 (getPhiNodesIDs ps) ->
  lookupPhiNodeViaIDFromPhiNodes ps id0 = None.
Proof.
  induction ps; simpl; intros; auto.
    destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) id0(getPhiNodeID a));
      subst; eauto.
      contradict H; auto.
Qed.

Lemma notin__lookupInsnViaIDFromBlock_none : forall b id0,
  ~ In id0 (getBlockLocs b) ->
  lookupInsnViaIDFromBlock b id0 = None.
Proof.
  destruct b; simpl; intros.
  assert (lookupPhiNodeViaIDFromPhiNodes p id0 = None) as J.
    apply notin__lookupPhiNodeViaIDFromPhinodes_none.
    intro J. apply H. apply in_or_app; auto.
  rewrite J.
  assert (lookupCmdViaIDFromCmds c id0 = None) as J'.
    apply notin__lookupCmdViaIDFromCmds_none.
    intro J'. apply H. 
    apply in_or_app. right.
    apply in_or_app; auto.
  rewrite J'; auto.
Qed.

Lemma in_middle__lookupCmdViaIDFromCmds : forall cs1 id1 c
  (Hid : getCmdID c = Some id1) cs1',
  NoDup (getCmdsLocs (cs1' ++ c :: cs1)) ->
  lookupCmdViaIDFromCmds (cs1' ++ c :: cs1) id1 = Some c.
Proof.
  induction cs1'; simpl; intros; auto.
    apply getCmdLoc_getCmdID in Hid.
    rewrite Hid.
    destruct (eq_atom_dec id1 id1); congruence; auto.

    inv H.
    destruct (eq_atom_dec id1 (getCmdLoc a)); subst; auto.
      apply getCmdLoc_getCmdID in Hid.
      contradict H2. rewrite getCmdsLocs_app. 
      apply in_or_app. simpl. auto.
Qed.

Lemma cmdInBlock__lookupInsnViaIDFromBlock : forall id1 c
  (Hid : getCmdID c = Some id1) l3 ps1 cs1' cs1 tmn1
  (Huniq : NoDup (getBlockLocs ((block_intro l3 ps1 (cs1' ++ c :: cs1) tmn1)))),
  lookupInsnViaIDFromBlock (block_intro l3 ps1 (cs1' ++ c :: cs1) tmn1) id1 = 
    Some (insn_cmd c).
Proof.
  simpl. intros.
  assert (lookupPhiNodeViaIDFromPhiNodes ps1 id1 = None) as J.
    apply notin__lookupPhiNodeViaIDFromPhinodes_none.
    eapply NoDup_disjoint; eauto.
    rewrite getCmdsLocs_app.
    apply in_or_app. left.
    apply in_or_app. right. simpl.
    apply getCmdLoc_getCmdID in Hid. auto.
  rewrite J.
  assert (lookupCmdViaIDFromCmds (cs1' ++ c :: cs1) id1 = Some c) as J'.
    apply NoDup_inv in Huniq. inv Huniq.
    apply NoDup_inv in H0. inv H0.
    apply in_middle__lookupCmdViaIDFromCmds; auto.
  rewrite J'. auto.
Qed.  

Lemma cmdInBlocks__InGetBlocksLocs : forall bs1 l3 ps1 cs1' c cs1 tmn1 id1, 
  getCmdID c = Some id1 ->
  InBlocksB (block_intro l3 ps1 (cs1' ++ c :: cs1) tmn1) bs1 = true ->
  In id1 (getBlocksLocs bs1).
Proof.
  induction bs1; simpl; intros.
    congruence.

    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0. subst.
      apply in_or_app. left. simpl.
      apply in_or_app. right. 
      apply in_or_app. left. 
      rewrite getCmdsLocs_app.
      apply in_or_app. right. simpl.
      apply getCmdLoc_getCmdID in H. auto.

      apply in_or_app. right. eauto.
Qed.

Lemma InBlocksB__lookupInsnViaIDFromBlocks : forall bs1 id1 c
  (Hid : getCmdID c = Some id1)
  (Huniq : NoDup (getBlocksLocs bs1)) l3 ps1 cs1' cs1 tmn1
  (Hin : InBlocksB (block_intro l3 ps1 (cs1' ++ c :: cs1) tmn1) bs1 = true),
  lookupInsnViaIDFromBlocks bs1 id1 = Some (insn_cmd c).
Proof.
  induction bs1; simpl; intros.
    congruence.

    apply orb_true_iff in Hin.
    assert (J:=Huniq).
    apply NoDup_inv in J.    
    destruct J.
    destruct Hin as [Hin | Hin].
      apply blockEqB_inv in Hin. subst.
      eapply cmdInBlock__lookupInsnViaIDFromBlock in H; eauto.
      rewrite H. auto.

      assert (lookupInsnViaIDFromBlock a id1 = None) as J.
        apply notin__lookupInsnViaIDFromBlock_none; auto.
        eapply NoDup_disjoint in Huniq; eauto. 
        eapply cmdInBlocks__InGetBlocksLocs; eauto.        
      rewrite J; eauto.
Qed.

Lemma map_app_inv : forall A B l1 l2 l (f:A->B),
  List.map f l = l1 ++ l2 ->
  exists l1', exists l2', 
    l = l1' ++ l2' /\ List.map f l1' = l1 /\ List.map f l2' = l2.
Proof.
  induction l1; simpl; intros.
    exists nil. exists l0. auto.

    destruct l0; inv H.
    apply IHl1 in H2. destruct H2 as [l1' [l2' [J1 [J2 J3]]]]; subst.
    exists (a0::l1'). exists l2'. auto.
Qed.

Lemma insnInFdefBlockB__insnInBlockB : forall instr f b,
  insnInFdefBlockB instr f b = true ->
  insnInBlockB instr b = true.
Proof.
  intros.
  destruct instr; simpl in *; try (apply andb_true_iff in H; destruct H; auto).
Qed.

Lemma insnInFdefBlockB__blockInFdefB : forall instr f b,
  insnInFdefBlockB instr f b = true ->
  blockInFdefB b f = true.
Proof.
  intros.
  destruct instr; simpl in *; try (apply andb_true_iff in H; destruct H; auto).
Qed.

Lemma In_InCmdLocs : forall c cs,
  In c cs -> In (getCmdLoc c) (getCmdsLocs cs).
Proof.
  induction cs; intros; inv H; simpl; auto.
Qed.

Lemma NoDup_getCmdsLocs_prop : forall c1 c2 cs,
  NoDup (getCmdsLocs cs) ->
  In c1 cs ->
  In c2 cs ->
  getCmdLoc c1 = getCmdLoc c2 ->
  c1 = c2. 
Proof.
  induction cs; simpl; intros.
    inv H0.

    inv H. 
    destruct H0 as [H0 | H0]; subst.
      destruct H1 as [H1 | H1]; subst; auto.
        rewrite H2 in H5. apply In_InCmdLocs in H1. contradict H1; auto.
      destruct H1 as [H1 | H1]; subst; auto.
        rewrite <- H2 in H5. apply In_InCmdLocs in H0. contradict H0; auto.
Qed.

Lemma InCmdsB_in : forall c cs, InCmdsB c cs = true -> In c cs.
Proof.
  induction cs; simpl; intros.
    congruence.
    apply orb_true_iff in H.
    destruct H as [H | H]; auto.
    apply cmdEqB_inv in H; auto.
Qed.

Lemma In_InCmdsB : forall c cs, In c cs -> InCmdsB c cs = true.
Proof.
  induction cs; simpl; intros.
    inv H.

    apply orb_true_iff.
    destruct H as [H | H]; subst; auto.
      left. apply cmdEqB_refl.
Qed.

Lemma fold_left_eq : forall B f (J:forall a b, f a b = false -> a = false), 
  forall (l1:list B) a, List.fold_left f l1 a = false -> a = false.
Proof.
  induction l1; simpl; intros; eauto.
Qed.

Lemma fold_left_congruence : forall B (f:Prop -> B -> Prop) 
  (J:forall (a b:Prop) c, (a->b) -> (f a c -> f b c))
  (l1:list B) (a b:Prop),
  (a -> b) ->
  (List.fold_left f l1 a -> List.fold_left f l1 b).
Proof. induction l1; simpl; intros; eauto. Qed.

Lemma fold_left_prop : forall B (f:Prop -> B -> Prop),
  (forall (a:Prop) b, f a b -> a) ->
  (forall (a b:Prop) c, (a->b) -> (f a c -> f b c)) ->
  forall (l1:list B) (a:Prop),
  (List.fold_left f l1 a -> a).
Proof. 
  induction l1; simpl; intros; auto. 
    apply IHl1; auto.  
    apply fold_left_congruence with (a:=f a0 a); auto.
    apply H.
Qed.

Lemma not_id_dec__neq : forall id5 id0,
  @eq _ (@proj_sumbool _ _ (id_dec id5 id0)) false ->
  id5 <> id0.
Proof.
  intros.
  destruct (id_dec id5 id0); subst; auto.
    simpl in *. congruence.
Qed.

Inductive sublist A : list A -> list A -> Prop :=
| sublist_nil : forall l, sublist A nil l
| sublist_cons : forall a l1 l2, sublist A l1 l2 -> sublist A (a::l1) (a::l2)
| sublist_sub : forall a l1 l2, sublist A l1 l2 -> sublist A l1 (a::l2)
.

Lemma in_sublist : forall A l1 l2 a,
  sublist A l1 l2 -> In a l1 -> In a l2.
Proof.
  induction 1; intros; simpl; auto.
    inv H. 
    inv H0; auto.
Qed.

Hint Constructors NoDup sublist.

Lemma sublist_NoDup : forall A l1 l2,
  sublist A l1 l2 -> NoDup l2 -> NoDup l1.
Proof.
  induction 1; intros; auto.
    inv H0. apply NoDup_cons; eauto using in_sublist.
    inv H0. auto.
Qed.

Lemma sublist_refl : forall A l2, sublist A l2 l2.
Proof. induction l2; simpl; auto. Qed.

Lemma sublist_weaken : forall A l1 l2 l3,
  sublist A l1 l2 ->
  sublist A l1 (l3++l2).
Proof. induction l3; simpl; auto. Qed.

Lemma sublist_app : forall A l1 l2 l1' l2',
  sublist A l1 l2 -> 
  sublist A l1' l2' -> 
  sublist A (l1++l1') (l2++l2').
Proof. induction 1; intros; simpl; auto using sublist_refl, sublist_weaken. Qed.

Lemma in_getCmdsIDs__in_getCmdsLocs: forall id1 cs,
  In id1 (getCmdsIDs cs) -> In id1 (getCmdsLocs cs).
Proof.
  induction cs; simpl; intros; auto.
    remember (getCmdID a) as R.
    destruct R; auto.
    symmetry in HeqR.
    apply getCmdLoc_getCmdID in HeqR. subst.
    simpl in H. destruct H; auto.
Qed.

Lemma in_getBlockIDs__in_getBlockLocs: forall id1 b,
  In id1 (getBlockIDs b) -> In id1 (getBlockLocs b).
Proof.
  destruct b. simpl. intros.
  apply in_app_or in H.
  apply in_or_app.
  destruct H as [H | H]; auto.
  right.
  apply in_or_app.
  left. apply in_getCmdsIDs__in_getCmdsLocs; auto.
Qed.

Lemma inGetBlockIDs__lookupBlockViaIDFromFdef: forall id1 b f,
  uniqFdef f -> In id1 (getBlockIDs b) -> blockInFdefB b f = true ->
  lookupBlockViaIDFromFdef f id1 = Some b.
Proof.
  destruct f as [bs]. simpl. 
  generalize dependent b.
  generalize dependent id1.
  induction bs; simpl; intros.
    inv H1.

    apply orb_true_iff in H1.
    destruct H1 as [H1 | H1].
      apply blockEqB_inv in H1. subst.
      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) id1
         (getBlockIDs a)); auto.
        contradict H0; auto.

      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) id1
         (getBlockIDs a)).
        destruct H as [J1 J2].
        simpl in *.
        apply in_getBlockIDs__in_getBlockLocs in i0.
        apply NoDup_disjoint' with (i0:=id1) in J2; auto.
          apply in_getBlockIDs__in_getBlockLocs in H0.
          apply in_getBlockLocs__in_getBlocksLocs with (i0:=id1) in H1; auto.
            contradict H0; auto.
        
        simpl_env in H.
        apply uniqBlocks_inv in H. destruct H as [J1 J2].
        apply IHbs; auto.
Qed.

Lemma lookupBlockViaIDFromFdef__uniq: forall f id0 b1 b2,
  uniqFdef f -> 
  lookupBlockViaIDFromFdef f id0 = Some b1 ->
  lookupBlockViaIDFromFdef f id0 = Some b2 ->
  b1 = b2.
Proof.
  destruct f as [bs]. simpl. 
  induction bs; simpl; intros.
    inv H0.

    simpl_env in H.
    apply uniqBlocks_inv in H. destruct H as [J1 J2].
    destruct (in_dec eq_dec id0 (getBlockIDs a)); eauto.
      inv H0. inv H1; auto.
Qed.

Lemma block_eq1: forall f id0 b1 b2,
  uniqFdef f -> blockInFdefB b2 f = true ->
  lookupBlockViaIDFromFdef f id0 = Some b1 ->
  In id0 (getBlockIDs b2) ->
  b1 = b2.
Proof.
  intros.
  eapply inGetBlockIDs__lookupBlockViaIDFromFdef in H2; eauto.
  eapply lookupBlockViaIDFromFdef__uniq in H1; eauto.
Qed.

Lemma lookupBlockViaLabelFromFdef_inv' : forall F l0 b,
  uniqFdef F ->
  lookupBlockViaLabelFromFdef F l0 = Some b ->
  blockInFdefB b F.
Proof.
  intros.
  destruct b.
  apply lookupBlockViaLabelFromFdef_inv in H0; auto.
  destruct H0; auto.
Qed. 

Lemma lookupIDFromPhiNodes__NotInPhiNodesIDs : forall la id1,
  lookupIDFromPhiNodes la id1 = None ->
  ~ In id1 (getPhiNodesIDs la).
Proof.
  induction la; intros; simpl in *; auto.
    destruct a. unfold lookupIDFromPhiNode in *. simpl in *.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 i0); subst.
      inv H. 
      apply IHla in H. intro J. 
      destruct J; subst; auto.
Qed.

Lemma lookupIDFromCmds__NotInCmdLocs : forall cs id1,
  lookupIDFromCmds cs id1 = None ->
  ~ In id1 (getCmdsLocs cs).
Proof.
  induction cs; intros; simpl in *; auto.
    unfold lookupIDFromCmd in *.
    destruct (@eq_dec id (@EqDec_eq_of_EqDec id EqDec_atom) id1 (getCmdLoc a)); 
      subst.
      inv H.
      apply IHcs in H. intro J. 
      destruct J; subst; auto.
Qed.

Lemma lookupIDFromBlock__notInBlock : forall b i0,
  lookupIDFromBlock b i0 = None ->
  ~ In i0 (getBlockIDs b).
Proof.
  destruct b. simpl; intros; auto.
    remember (lookupIDFromPhiNodes p i0) as R.
    destruct R.
      inv H.
      remember (lookupIDFromCmds c i0) as R.
      destruct R.
        inv H.
        symmetry in HeqR, HeqR0.
        apply lookupIDFromPhiNodes__NotInPhiNodesIDs in HeqR.
        apply lookupIDFromCmds__NotInCmdLocs in HeqR0.
        intro J. apply in_app_or in J. destruct J; auto.
        apply in_getCmdsIDs__in_getCmdsLocs in H0; auto.
Qed.

Lemma inGetBlockIDs__lookupIDFromFdef: forall f id1 b,
  In id1 (getBlockIDs b) ->
  blockInFdefB b f = true ->
  lookupIDFromFdef f id1 = Some tt.
Proof.
  destruct f as [bs]. simpl.
  induction bs; simpl; intros.
    inv H0.

    remember (lookupIDFromBlock a id1) as R.
    destruct R.
    destruct u; auto.
    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0]; eauto.
      apply blockEqB_inv in H0. subst.
      symmetry in HeqR.
      apply lookupIDFromBlock__notInBlock in HeqR.
      contradict H; auto. 
Qed.

Lemma in_getPhiNodesIDs_inv: forall id1 p,
  In id1 (getPhiNodesIDs p) ->
  exists ps1 : list phinode,
    exists p1 : phinode,
      exists ps2 : list phinode,
        p = ps1 ++ p1 :: ps2 /\ getPhiNodeID p1 = id1.
Proof.
  induction p; simpl; intros.
    inv H.
    
    destruct H as [H | H]; subst.
      exists nil. exists a. exists p. simpl. split; auto.

      apply IHp in H. 
      destruct H as [ps1 [p1 [ps2 [J1 J2]]]]; subst.
      exists (a::ps1). exists p1. exists ps2. split; auto.
Qed.

Lemma in_getCmdsLocs_inv: forall id1 cs,
  In id1 (getCmdsLocs cs) ->
  exists cs1, exists c, exists cs2,
        cs = cs1 ++ c :: cs2 /\ getCmdLoc c = id1.
Proof.
  induction cs; simpl; intros.
    inv H.

    destruct H as [H | H]; subst.
      exists nil. exists a. exists cs. auto.

      apply IHcs in H.
      destruct H as [cs1 [c [cs2 [J1 J2]]]]; subst.
      exists (a::cs1). exists c. exists cs2. auto.
Qed.

Lemma getCmdID_getCmdLoc: forall c, getCmdID c = Some (getCmdLoc c).
Proof.
  destruct c; simpl; auto.
Qed.

Lemma IngetPhiNodesIDs__lookupPhiNodeViaIDFromPhiNodes: forall id2 ps1
  (H0 : In id2 (getPhiNodesIDs ps1)),
  exists p2, lookupPhiNodeViaIDFromPhiNodes ps1 id2 = Some p2 /\
             getPhiNodeID p2 = id2.
Proof.
  induction ps1; simpl; intros.
    inv H0.

    destruct H0 as [H0 | H0]; subst.
      destruct (getPhiNodeID a == getPhiNodeID a); eauto.
        congruence.

      destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) id2
                 (getPhiNodeID a)); subst; eauto.
Qed.

Lemma lookupInsnViaIDFromBlocks__In : forall id0 instr bs,
  lookupInsnViaIDFromBlocks bs id0 = Some instr ->
  In id0 (getBlocksLocs bs).
Proof.
  induction bs; simpl; intros.
    inv H.

    apply in_or_app.
    remember (lookupInsnViaIDFromBlock a id0) as R.
    destruct R; eauto.
      inv H.
      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__In in HeqR; auto.
Qed.

Lemma IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef: forall id2 l1 ps1 cs1 tmn1 f
  (Huniq: uniqFdef f)
  (H : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (H0 : In id2 (getPhiNodesIDs ps1)),
  exists p2, lookupInsnViaIDFromFdef f id2 = Some (insn_phinode p2) /\
             getPhiNodeID p2 = id2.
Proof.
  destruct f as [bs]. simpl. intros.
  destruct Huniq as [_ Huniq].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  generalize dependent id2.
  induction bs; simpl; intros.
    inv H.

    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H.
      subst. simpl.
      apply IngetPhiNodesIDs__lookupPhiNodeViaIDFromPhiNodes in H0.
      destruct H0 as [ps [H0 Heq]]; subst.
      rewrite H0. eauto.

      simpl_env in Huniq. rewrite getBlocksLocs_app in Huniq.
      assert (Huniq':=Huniq).
      apply NoDup_inv in Huniq'. destruct Huniq'.
      eapply IHbs in H; eauto.
      destruct H as [p2 [H Heq]]; subst.
      rewrite H. 
      apply lookupInsnViaIDFromBlocks__In in H.
      eapply NoDup_disjoint in Huniq; eauto.
      simpl in Huniq. simpl_env in Huniq.
      apply notin__lookupInsnViaIDFromBlock_none in Huniq.
      rewrite Huniq. eauto.
Qed.

Lemma lookupCmdViaIDFromFdef_spec : forall f id2 l1 ps1 cs1 tmn1
  (Huniq: uniqFdef f)
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = Some (insn_cmd c2)),
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  In id2 (getPhiNodesIDs ps1 ++ getCmdsIDs cs1) ->
  In id2 (getCmdsIDs cs1).
Proof.
  intros.
  apply in_app_or in H0.
  destruct H0 as [H0 | H0]; auto.
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in H; eauto.
  destruct H as [p2 [J1 J2]]; subst.
  destruct G as [c2 G].
  rewrite G in J1. inv J1.
Qed.

Lemma lookupPhiNodeViaIDFromPhiNodes__NotIn : forall id0 ps,
  lookupPhiNodeViaIDFromPhiNodes ps id0 = None ->
  ~ In id0 (getPhiNodesIDs ps).
Proof.
  induction ps; simpl; intros; auto.
    destruct (id0 == getPhiNodeID a); tinv H.
      apply IHps in H. intro J. destruct J; subst; auto.
Qed.    

Lemma lookupCmdViaIDFromCmds__NotIn : forall id0 cs,
  lookupCmdViaIDFromCmds cs id0 = None ->
  ~ In id0 (getCmdsLocs cs).
Proof.
  induction cs; simpl; intros; auto.
    destruct (eq_atom_dec id0 (getCmdLoc a)); subst; tinv H.
      apply IHcs in H. intro J. destruct J; subst; auto.
Qed.    

Lemma lookupInsnViaIDFromBlock__NotIn : forall id0 bs,
  lookupInsnViaIDFromBlock bs id0 = None ->
  ~ In id0 (getBlockIDs bs).
Proof.
  destruct bs. simpl. intros.
  remember (lookupPhiNodeViaIDFromPhiNodes p id0) as R.
  destruct R; tinv H.
  remember (lookupCmdViaIDFromCmds c id0) as R.
  destruct R; tinv H.
  symmetry in HeqR, HeqR0.
  apply lookupPhiNodeViaIDFromPhiNodes__NotIn in HeqR.
  apply lookupCmdViaIDFromCmds__NotIn in HeqR0.
  intro J. apply in_app_or in J. destruct J; auto.
  apply in_getCmdsIDs__in_getCmdsLocs in H0; auto.
Qed.

Lemma lookupCmdViaIDFromCmds__InCmds : forall cs c i0,
  lookupCmdViaIDFromCmds cs i0 = Some c ->
  In c cs.
Proof.  
  induction cs; simpl; intros.
    inv H.
    destruct (eq_atom_dec i0 (getCmdLoc a)); eauto.
      inv H; auto.
Qed.     
    
Lemma lookupInsnViaIDFromBlock__InCmds : forall l0 p cs t c1,
  NoDup (getBlockLocs (block_intro l0 p cs t)) ->
  lookupInsnViaIDFromBlock (block_intro l0 p cs t) (getCmdLoc c1) =
    Some (insn_cmd c1) ->
  In c1 cs.
Proof.
  intros. simpl in *.
  remember (lookupPhiNodeViaIDFromPhiNodes p (getCmdLoc c1)) as R.
  destruct R; tinv H0.
  remember (lookupCmdViaIDFromCmds cs (getCmdLoc c1)) as R.
  destruct R; inv H0.
  apply NoDup_inv in H. destruct H as [_ H].
  apply NoDup_inv in H. destruct H as [H _].
  eapply lookupCmdViaIDFromCmds__InCmds; eauto.
Qed.

Lemma getCmdID__getCmdLoc: forall c, getCmdID c = Some (getCmdLoc c).
Proof. destruct c; simpl; auto. Qed.

Lemma in_getCmdsLocs__in_getCmdsIDs: forall c1 cs
  (J : In (getCmdLoc c1) (getCmdsLocs cs))
  (J' : lookupCmdViaIDFromCmds cs (getCmdLoc c1) = Some c1),
  In (getCmdLoc c1) (getCmdsIDs cs).
Proof.
  induction cs; simpl; intros; auto.
    destruct J as [J | J].
      destruct (eq_atom_dec (getCmdLoc c1) (getCmdLoc a)).
        inv J'.
        rewrite getCmdID__getCmdLoc. simpl. auto.

        contradict J; auto.
      destruct (eq_atom_dec (getCmdLoc c1) (getCmdLoc a)).
        inv J'.
        rewrite getCmdID__getCmdLoc. simpl. auto.

        rewrite getCmdID__getCmdLoc. simpl. auto.
Qed.      

Lemma in_getBlockLocs__in_getBlockIDs: forall c1 b
  (J : In (getCmdLoc c1) (getBlockLocs b)) (Huniq: NoDup (getBlockLocs b))
  (J' : lookupInsnViaIDFromBlock b (getCmdLoc c1) = Some (insn_cmd c1)),
  In (getCmdLoc c1) (getBlockIDs b).
Proof.
  destruct b. simpl. intros.
  remember (lookupPhiNodeViaIDFromPhiNodes p (getCmdLoc c1)) as R.
  destruct R; tinv J'.
  remember (lookupCmdViaIDFromCmds c (getCmdLoc c1)) as R.
  destruct R; inv J'.
  apply in_or_app.
  apply in_app_or in J.
  destruct J as [J | J]; auto.
  apply in_app_or in J.
  destruct J as [J | J].
    right. 
    apply in_getCmdsLocs__in_getCmdsIDs; auto.

    symmetry in HeqR0.
    apply lookupCmdViaIDFromCmds__In in HeqR0.
    rewrite_env ((getPhiNodesIDs p ++ getCmdsLocs c) ++ [getTerminatorID t])
      in Huniq.
    eapply NoDup_disjoint in Huniq; eauto.
    contradict Huniq.
    apply in_or_app; auto.
Qed.

Lemma lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef_In: 
  forall F (Huniq: uniqFdef F) c1 l0 p cs t 
  (J2 : lookupInsnViaIDFromFdef F (getCmdLoc c1) = Some (insn_cmd c1))
  (Hlkb : lookupBlockViaIDFromFdef F (getCmdLoc c1) = 
    Some (block_intro l0 p cs t)),
  In c1 cs.
Proof.
  destruct F as [bs]. simpl.
  induction bs; simpl; intros.
    inv J2.

    simpl_env in Huniq. 
    apply uniqBlocks_inv in Huniq. destruct Huniq.
    remember (lookupInsnViaIDFromBlock a (getCmdLoc c1)) as R.
    destruct R.
      inv J2.
      symmetry in HeqR. assert (HeqR':=HeqR).
      apply lookupInsnViaIDFromBlock__In in HeqR.
      destruct (in_dec eq_dec (getCmdLoc c1) (getBlockIDs a)).
        inv Hlkb. 
        unfold uniqBlocks in H. simpl in H. destruct H. simpl_env in H1.
        apply lookupInsnViaIDFromBlock__InCmds in HeqR'; simpl; auto.

        unfold uniqBlocks in H. destruct H. simpl in H1. simpl_env in H1.
        apply in_getBlockLocs__in_getBlockIDs in HeqR; auto.
        congruence.

      symmetry in HeqR.
      apply lookupInsnViaIDFromBlock__NotIn in HeqR.
      destruct (in_dec eq_dec (getCmdLoc c1) (getBlockIDs a)); try congruence.
      apply IHbs in Hlkb; auto.
Qed.

Lemma phinode_isnt_cmd : forall f l3 ps cs tmn id1 c1,
  uniqFdef f ->
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  In id1 (getPhiNodesIDs ps) ->
  lookupInsnViaIDFromFdef f id1 = Some (insn_cmd c1) ->
  False.
Proof.
  intros. symmetry in H0.
  apply lookupBlockViaLabelFromFdef__blockInFdefB in H0; auto.
  eapply IngetPhiNodesIDs__lookupPhinodeViaIDFromFdef in H0; eauto.
  destruct H0 as [p2 [J1 J2]]; subst.
  rewrite H2 in J1. inv J1.
Qed.

Lemma lookupInsnViaIDFromFdef__insnInFdefBlockB : forall F id1 c1,
  lookupInsnViaIDFromFdef F id1 = Some (insn_cmd c1) ->
  exists b1, insnInFdefBlockB (insn_cmd c1) F b1.
Proof.
  destruct F as [bs]. simpl.
  induction bs; simpl; intros.
    inv H.

    remember (lookupInsnViaIDFromBlock a id1) as R.
    destruct R.
      inv H.
      exists a.
      destruct a. simpl in *.
      destruct (lookupPhiNodeViaIDFromPhiNodes p id1); tinv HeqR.
      remember (lookupCmdViaIDFromCmds c id1) as R.
      destruct R; inv HeqR.
      symmetry in HeqR0.
      apply lookupCmdViaIDFromCmds__InCmds in HeqR0.
      apply In_InCmdsB in HeqR0.
      apply andb_true_iff. split; auto.
      apply orb_true_iff. left. apply blockEqB_refl.

      apply IHbs in H.
      destruct H as [b H].
      apply andb_true_iff in H. destruct H as [J1 J2].
      exists b. apply andb_true_iff. split; auto.
      apply orb_true_iff; auto.
Qed.

Lemma lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef : 
  forall F l1 b1 id1 (Huniq: uniqFdef F)
  (J2 : lookupBlockViaLabelFromFdef F l1 = Some b1)
  (J3 : In id1 (getBlockIDs b1)),
  lookupBlockViaIDFromFdef F id1 = Some b1.
Proof.
  intros.
  destruct b1.
  apply lookupBlockViaLabelFromFdef_inv in J2; auto.
  destruct J2 as [Heq J2]; subst.
  apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
Qed.

Lemma lookupBlockViaIDFromFdef_getBlockLocs_getBlockIDs: forall F i0 block1 
  block2 (Huniq : uniqFdef F) (HBinF: blockInFdefB block1 F = true)
  (HeqR1' : In i0 (getBlockLocs block1))
  (H5 : lookupBlockViaIDFromFdef F i0 = Some block2),
  In i0 (getBlockIDs block1).
Proof.
  destruct F as [bs]. simpl. 
  induction bs; simpl; intros.
    inv H5.

    destruct (in_dec eq_dec i0 (getBlockIDs a)).
      inv H5. 
      apply orb_true_iff in HBinF.
      destruct HBinF as [HBinF | HBinF].
        apply blockEqB_inv in HBinF. subst. auto.

        unfold uniqBlocks in Huniq.
        destruct Huniq as [_ Huniq].
        simpl in Huniq.
        eapply in_getBlockLocs__in_getBlocksLocs in HBinF; eauto.
        apply NoDup_disjoint with (i0:=i0) in Huniq; auto.
          contradict Huniq.
          apply in_getBlockIDs__in_getBlockLocs; auto.

      apply orb_true_iff in HBinF.
      destruct HBinF as [HBinF | HBinF].
        apply blockEqB_inv in HBinF. subst.
        unfold uniqBlocks in Huniq.
        destruct Huniq as [_ Huniq].
        simpl in Huniq.
        apply NoDup_disjoint' with (i0:=i0) in Huniq; auto.
        contradict Huniq.
        assert (lookupBlockViaIDFromFdef (fdef_intro bs) i0 = Some block2) as J.
          simpl. auto.
        assert (J1:=J).
        apply lookupBlockViaIDFromFdef__blockInFdefB in J1.
        apply in_getBlockLocs__in_getBlocksLocs with (b:=block2); auto.
        apply in_getBlockIDs__in_getBlockLocs; auto.
        apply lookupBlockViaIDFromFdef__InGetBlockIDs in J; auto.

        simpl_env in Huniq. apply uniqBlocks_inv in Huniq.
        destruct Huniq. eauto.
Qed.

Lemma lookupBlockViaIDFromFdef__lookupBlockViaLabelFromFdef__eq : forall F block1
  i0 block2 l'
  (Huniq : uniqFdef F)
  (Hlkup : Some block1 = lookupBlockViaLabelFromFdef F l')
  (HeqR1' : In i0 (getBlockLocs block1))
  (H5 : lookupBlockViaIDFromFdef F i0 = Some block2),
  block1 = block2.
Proof.
  intros.
  symmetry in Hlkup.
  apply lookupBlockViaLabelFromFdef__lookupBlockViaIDFromFdef with (id1:=i0) 
    in Hlkup; auto.
    rewrite Hlkup in H5. inv H5; auto.

    apply lookupBlockViaLabelFromFdef__blockInFdefB in Hlkup; auto.
    eapply lookupBlockViaIDFromFdef_getBlockLocs_getBlockIDs in H5; eauto.
Qed.

Lemma getCmdsIDs_eq_getCmdsLocs: forall cs, getCmdsIDs cs = getCmdsLocs cs.
Proof.
  induction cs; simpl; auto.
    rewrite IHcs. destruct a; auto.
Qed.

Lemma InCmdsB_InCmdsLocs : forall c cs,
  InCmdsB c cs = true -> In (getCmdLoc c) (getCmdsLocs cs).
Proof. intros. apply In_InCmdLocs. apply InCmdsB_in; auto. Qed.

Lemma insnInFdefBlockB__lookupBlockViaIDFromFdef : forall c1 F b1
  (Huniq: uniqFdef F)
  (H : insnInFdefBlockB (insn_cmd c1) F b1 = true),
  lookupBlockViaIDFromFdef F (getCmdLoc c1) = Some b1.
Proof.
  intros.
  assert (H':=H). 
  apply insnInFdefBlockB__blockInFdefB in H.
  apply insnInFdefBlockB__insnInBlockB in H'.
  apply inGetBlockIDs__lookupBlockViaIDFromFdef; auto.
  destruct b1. simpl in *.
  apply in_or_app. right.
  apply InCmdsB_InCmdsLocs in H'.
  rewrite getCmdsIDs_eq_getCmdsLocs. auto.
Qed.

Lemma lookupPhiNodeViaIDFromPhiNodes__eqid : forall p id1 p0
  (HeqR0 : Some p0 = lookupPhiNodeViaIDFromPhiNodes p id1),
  getInsnLoc (insn_phinode p0) = id1.
Proof.
  induction p; simpl; intros.
    inv HeqR0.
     
    destruct (id1 == getPhiNodeID a).
      inv HeqR0. auto.
      apply IHp in HeqR0. simpl in HeqR0. auto.
Qed.

Lemma lookupCmdViaIDFromCmds__eqid : forall cs id1 c
  (HeqR0 : Some c = lookupCmdViaIDFromCmds cs id1),
  getInsnLoc (insn_cmd c) = id1.
Proof.
  induction cs; simpl; intros.
    inv HeqR0.
     
    destruct (eq_atom_dec id1 (getCmdLoc a)).
      inv HeqR0. auto.
      apply IHcs in HeqR0. simpl in HeqR0. auto.
Qed.

Lemma lookupInsnViaIDFromFdef__eqid : forall F id1 insn1,
  lookupInsnViaIDFromFdef F id1 = Some insn1 ->
  getInsnLoc insn1 = id1.
Proof.
  destruct F as [bs]. simpl. 
  induction bs; simpl; intros.
    inv H.

    remember (lookupInsnViaIDFromBlock a id1) as R.
    destruct R.
      inv H.
      destruct a. simpl in HeqR.
      remember (lookupPhiNodeViaIDFromPhiNodes p id1) as R.
      destruct R.
        inv HeqR.
        apply lookupPhiNodeViaIDFromPhiNodes__eqid in HeqR0; auto.

        remember (lookupCmdViaIDFromCmds c id1) as R.
        destruct R; inv HeqR.
          apply lookupCmdViaIDFromCmds__eqid in HeqR1; auto.
          apply IHbs in H; auto.
Qed.

Lemma insnInFdefBlockB__lookupBlockViaIDFromFdef__eq: forall c1 F1 b1 block'
  (Huniq: uniqFdef F1)
  (H0 : insnInFdefBlockB (insn_cmd c1) F1 b1 = true)
  (H5 : lookupBlockViaIDFromFdef F1 (getCmdLoc c1) = Some block'),
  b1 = block'.
Proof.
  intros.
  apply insnInFdefBlockB__lookupBlockViaIDFromFdef in H0; auto.
  rewrite H0 in H5. inv H5. auto.
Qed.

Lemma InGetPhiNodesIDs_middle: forall ps1 p1 ps2,
  In (getPhiNodeID p1) (getPhiNodesIDs (ps1 ++ p1 :: ps2)).
Proof.
  intros.
  rewrite getPhiNodesIDs_app. apply in_or_app. simpl. auto.
Qed.

Lemma InGetCmdsLocs_middle: forall cs1 c1 cs2,
  In (getCmdLoc c1) (getCmdsLocs (cs1 ++ c1 :: cs2)).
Proof.
  intros.
  rewrite getCmdsLocs_app. apply in_or_app. simpl. auto.
Qed.

Lemma getCmdLoc_in_getCmdsLocs': forall c1 cs ls
  (H0 : InCmdsB c1 cs), In (getCmdLoc c1) (getCmdsLocs cs ++ ls).
Proof.
  intros. apply in_or_app. left. apply getCmdLoc_in_getCmdsLocs; auto.
  apply InCmdsB_in; auto.
Qed.

Lemma getCmdsLocs_uniq: forall c1 c2 cs,
  NoDup (getCmdsLocs cs) ->
  In c1 cs ->
  In c2 cs ->
  getCmdLoc c1 = getCmdLoc c2 ->
  c1 = c2.
Proof.
  induction cs; simpl; intros.
    inv H0.

    inv H.
    destruct H0 as [H0 | H0]; subst.
      destruct H1 as [H1 | H1]; auto.
        apply getCmdLoc_in_getCmdsLocs in H1.
        rewrite H2 in H5. congruence.

      destruct H1 as [H1 | H1]; subst; eauto.
        apply getCmdLoc_in_getCmdsLocs in H0.
        rewrite H2 in H0. congruence.
Qed.

Lemma in_middle_inv: forall cs1 c cs2 cs1' cs2',
  NoDup (getCmdsLocs (cs1 ++ c :: cs2)) ->
  cs1 ++ c :: cs2 = cs1' ++ c :: cs2' ->
  cs1 = cs1' /\ cs2 = cs2'.
Proof.
  induction cs1; simpl; intros.
    destruct cs1'; inv H0; auto.
      inv H. contradict H2. apply InGetCmdsLocs_middle.  

    inv H. 
    destruct cs1'; inv H0.
      contradict H3. apply InGetCmdsLocs_middle.  
      apply IHcs1 in H2; auto. destruct H2; subst; auto.
Qed.

Lemma cmdInBlockB__inGetBlockIDs: forall c b, 
  cmdInBlockB c b -> In (getCmdLoc c) (getBlockLocs b).
Proof.
  destruct b. simpl. intros.
  apply InCmdsB_in in H. apply In_InCmdLocs in H.
  apply in_or_app. right. apply in_or_app. auto.
Qed.

Lemma InGetBlockLocs_uniqBlocks_false: forall a bs b c
  (H : uniqBlocks (a :: bs))
  (H1 : InBlocksB b bs = true)
  (H3 : In (getCmdLoc c) (getBlockLocs b))
  (H2 : In (getCmdLoc c) (getBlockLocs a)),
  False.
Proof.
  intros.
  eapply in_getBlockLocs__in_getBlocksLocs in H1; eauto.
  unfold uniqBlocks in H.
  destruct H as [_ H].
  simpl in H.
  apply NoDup_disjoint with (i0:=getCmdLoc c) in H; auto.
Qed.

Lemma cmdInBlockB_eqBlock_aux: forall a bs b c 
  (H : uniqBlocks (a :: bs))
  (H1 : InBlocksB b bs = true)
  (H3 : cmdInBlockB c b)
  (H2 : cmdInBlockB c a),
  False.
Proof.
  intros.
  apply cmdInBlockB__inGetBlockIDs in H2.
  apply cmdInBlockB__inGetBlockIDs in H3.
  eapply InGetBlockLocs_uniqBlocks_false in H1; eauto.
Qed.

Lemma in_getBlockIDs__in_getBlocksLocs : forall bs b i0,
  In i0 (getBlockIDs b) ->
  InBlocksB b bs ->
  In i0 (getBlocksLocs bs).
Proof.
  intros.
  eapply in_getBlockLocs__in_getBlocksLocs in H0; eauto.
  apply in_getBlockIDs__in_getBlockLocs; auto.
Qed.

Lemma InGetBlockIDs_uniqBlocks_false: forall a bs b i0
  (H : uniqBlocks (a :: bs))
  (H1 : InBlocksB b bs = true)
  (H3 : In i0 (getBlockIDs b))
  (H2 : In i0 (getBlockIDs a)),
  False.
Proof.
  intros.
  eapply in_getBlockIDs__in_getBlocksLocs in H1; eauto.
  unfold uniqBlocks in H.
  destruct H as [_ H].
  simpl in H.
  apply in_getBlockIDs__in_getBlockLocs in H2; auto.
  apply NoDup_disjoint with (i0:=i0) in H; auto.
Qed.

Lemma InGetBlockIDs__lookupBlockViaIDFromFdef: forall F1 b i0,
  uniqFdef F1 ->
  blockInFdefB b F1 ->
  In i0 (getBlockIDs b) ->
  lookupBlockViaIDFromFdef F1 i0 = Some b.
Proof.
  destruct F1 as [bs]. simpl. 
  induction bs; simpl; intros.
    inv H0.

    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0. subst.
      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) i0
         (getBlockIDs a)); auto.
        contradict H1; auto.
 
      destruct (@in_dec id (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom)) i0
         (getBlockIDs a)).
        eapply InGetBlockIDs_uniqBlocks_false with (i0:=i0) in H0; eauto.
        inv H0.

        simpl_env in H. apply uniqBlocks_inv in H. destruct H; eauto.
Qed.

Lemma cmdInBlockB_eqBlock : forall F1 b b' c,
  uniqFdef F1 ->
  blockInFdefB b F1 ->
  blockInFdefB b' F1 ->
  cmdInBlockB c b ->
  cmdInBlockB c b' -> b = b'.
Proof.
  destruct F1 as [bs]. simpl. 
  induction bs; simpl; intros.
    inv H0.

    apply orb_true_iff in H0.
    apply orb_true_iff in H1.
    destruct H0 as [H0 | H0].
      apply blockEqB_inv in H0. subst.
      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1. subst. auto.
        eapply cmdInBlockB_eqBlock_aux in H1; eauto. inv H1.

      destruct H1 as [H1 | H1].
        apply blockEqB_inv in H1. subst.
        eapply cmdInBlockB_eqBlock_aux in H0; eauto. inv H0.

        simpl_env in H.
        apply uniqBlocks_inv in H. destruct H; eauto.
Qed.

Lemma nodup_getCmdsLocs_in_first: forall c1 cs1 cs2,
  NoDup (getCmdsLocs (cs1++cs2)) ->
  In (getCmdLoc c1) (getCmdsLocs cs1) ->
  In c1 (cs1++cs2) ->
  In c1 cs1.
Proof.
  intros.
  apply in_app_or in H1.
  destruct H1; auto.
  rewrite getCmdsLocs_app in H.
  apply NoDup_disjoint' with (i0:=getCmdLoc c1) in H; auto.
  apply In_InCmdLocs in H1. contradict H1; auto.
Qed.

Lemma blockInFdefB__cmdInFdefBlockB__eqBlock: forall l3 ps1 cs tmn1 f c b1
  (Huniq: uniqFdef f)
  (Hin : blockInFdefB (block_intro l3 ps1 cs tmn1) f = true)
  (H : cmdInFdefBlockB c f b1 = true)
  (Hin : In c cs),
  block_intro l3 ps1 cs tmn1 = b1.
Proof.
  intros.
  assert (insnInFdefBlockB (insn_cmd c) f b1) as J1. simpl. auto.
  apply insnInFdefBlockB__lookupBlockViaIDFromFdef in J1; auto.
  assert (insnInFdefBlockB (insn_cmd c) f (block_intro l3 ps1 cs tmn1)) as J2. 
    simpl. apply andb_true_iff. split; auto.
    apply In_InCmdsB; auto.
  apply insnInFdefBlockB__lookupBlockViaIDFromFdef in J2; auto.
  rewrite J1 in J2. inv J2; auto.
Qed.

Lemma incl_insert: forall A (l1 l2:list A) a, incl (l1++l2) (l1++a::l2).
Proof.
  induction l1; simpl; intros; intros x J; simpl; auto.
    simpl in J. destruct J as [J | J]; auto.
    right. apply IHl1; auto.
Qed.    

Lemma incl_app: forall A (l0 l1 l2:list A), 
  incl l1 l2 -> incl (l0++l1) (l0++l2).
Proof. 
  intros. intros x J. 
  apply in_or_app. apply in_app_or in J. 
  destruct J as [J | J]; auto.
Qed.

Lemma lookupBlockViaIDFromBlocks__InGetBlocksLocs : forall bs id1 b,
  lookupBlockViaIDFromBlocks bs id1 = Some b ->
  In id1 (getBlocksLocs bs).
Proof.         
  induction bs; simpl; intros.
    inv H.

    apply in_or_app. 
    destruct (in_dec eq_dec id1 (getBlockIDs a)).
      inv H.
      apply in_getBlockIDs__in_getBlockLocs in i0; auto.

      apply IHbs in H. auto.
Qed.

Lemma firstn_nil : forall A n, firstn n (@nil A) = nil.
Proof. induction n; simpl; auto. Qed.

Lemma skipn_nil : forall A n, skipn n (@nil A) = nil.
Proof. induction n; simpl; auto. Qed.

Lemma NoDup_insert: forall A (l1 l2:list A) a,
  NoDup (l1++l2) -> ~ In a (l1++l2) -> NoDup (l1 ++ a:: l2).
Proof.
  induction l1; simpl; intros.
    constructor; auto.
 
    inv H. 
    constructor; auto.
      intro J. apply H3.
      apply in_or_app. apply in_app_or in J. simpl in J.
      destruct J as [J | [J | J]]; subst; auto.
      contradict H0; auto.
Qed.

Lemma app_middle_split: forall A (l1 l2 l3 l4:list A) a, 
  l1++a::l2 = l3++l4 ->
  (exists l12, l1 = l3++l12 /\ l4 = l12++a::l2) \/
  (exists l21, l3 = l1++a::l21 /\ l2 = l21++l4).
Proof.
  induction l1; simpl; intros.
    destruct l3.
      destruct l4; inv H.
        left. exists nil. auto.
      inv H. right. exists l3. auto.

    destruct l3.
      destruct l4; inv H.
        left. exists (a1::l1). auto.
      inv H. apply IHl1 in H2.
      destruct H2 as [[l21 [J1 J2]]|[l21 [J1 J2]]]; subst; simpl; eauto.
Qed.

Lemma InGetCmdsLocs_lookupIDFromCmds : forall cs id1,
  In id1 (getCmdsLocs cs) -> lookupIDFromCmds cs id1 = Some tt.
Proof.
  induction cs; simpl; intros.
    inversion H.

    unfold lookupIDFromCmd.
    inv H. 
      destruct (getCmdLoc a == getCmdLoc a); auto.
        congruence.
 
      destruct (id1 == getCmdLoc a); auto.
Qed.

Lemma nth_error_In : forall A n (l1:list A) a, 
  nth_error l1 n = Some a -> In a l1.
Proof.
  induction n; simpl; intros; destruct l1; inv H; simpl; auto.
Qed.

Lemma nth_error_firstn_skipn: forall c n cs1 cs2,
  NoDup (getCmdsLocs (cs1++c::cs2)) ->
  nth_error (cs1++c::cs2) n = Some c ->
  firstn n (cs1++c::cs2) = cs1 /\
  skipn n (cs1++c::cs2) = c::cs2.
Proof.
  induction n; simpl; intros.
    destruct cs1; inv H0; auto.
      inv H. contradict H2. apply InGetCmdsLocs_middle.
      
    destruct cs1; inv H0; simpl in *.
      inv H.
      apply nth_error_In in H2.
      contradict H3. apply In_InCmdLocs; auto.

      inv H.
      apply IHn in H2; auto.
      destruct H2 as [J1 J2].
      rewrite J1. rewrite J2. auto.
Qed.

Lemma NoDup_app: forall A (l1 l2:list A),
  NoDup l1 -> NoDup l2 -> 
  (forall (a:A), In a l1 -> ~ In a l2) ->
  NoDup (l1++l2).
Proof.
  induction l1; simpl; intros; auto.
    inv H.
    constructor; auto.
      intro J. apply in_app_or in J.
      destruct J as [J | J]; auto.
      assert (a = a \/ In a l1) as Hin. auto.
      apply H1 in Hin. auto.
Qed.

Lemma NoDup_split': forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2 /\ (forall (a:A), In a l1 -> ~ In a l2).
Proof.
  induction l1; simpl; intros; auto.
    inv H.
    apply IHl1 in H3. destruct H3 as [J1 [J2 J3]].
    split.
      constructor; auto.
        intro J. apply H2. apply in_or_app; auto.
    split; auto.
      intros. 
      destruct H as [H | H]; subst; auto.
        intro J. apply H2. apply in_or_app; auto.
Qed.

Lemma notin_app_inv: forall A (l1 l2:list A) a,
  ~ In a (l1 ++ l2) -> ~ In a l1 /\ ~ In a l2.
Proof.
  intros.
  split; intro J; apply H; apply in_or_app; auto.
Qed.   

Lemma notin_app: forall A (l1 l2:list A) a,
  ~ In a l1 -> ~ In a l2 ->
  ~ In a (l1 ++ l2).
Proof.
  intros. intro J.
  apply in_app_or in J.
  destruct J as [J | J].   
    apply H; auto.
    apply H0; auto.
Qed.   

Lemma IngetCmdsLocs__lookupCmdViaIDFromCmds: forall c1 cs1
  (Huniq: NoDup (getCmdsLocs cs1)) (H0 : In c1 cs1),
  lookupCmdViaIDFromCmds cs1 (getCmdLoc c1) = Some c1.
Proof.
  induction cs1; simpl; intros.
    inv H0.

    destruct H0 as [H0 | H0]; subst.
      destruct (eq_atom_dec (getCmdLoc c1) (getCmdLoc c1)); auto.
        congruence.
      inv Huniq.
      destruct (eq_atom_dec (getCmdLoc c1) (getCmdLoc a)); auto.
        contradict H2. rewrite <- e. apply In_InCmdLocs; auto. 
Qed.

Lemma IngetCmdsIDs__lookupCmdViaIDFromFdef: forall c1 l1 ps1 cs1 tmn1 f
  (Huniq: uniqFdef f)
  (H : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (H0 : In c1 cs1),
  lookupInsnViaIDFromFdef f (getCmdLoc c1) = Some (insn_cmd c1).
Proof.
  destruct f as [bs]. simpl. intros.
  destruct Huniq as [_ Huniq].
  generalize dependent l1.
  generalize dependent ps1.
  generalize dependent cs1.
  generalize dependent tmn1.
  induction bs; simpl; intros.
    inv H.

    simpl in Huniq.
    apply NoDup_split' in Huniq.
    destruct Huniq as [J1 [J2 J3]].
    apply orb_true_iff in H.
    destruct H as [H | H].
      apply blockEqB_inv in H.
      subst. simpl.
      assert (~ In (getCmdLoc c1) (getPhiNodesIDs ps1)) as Hnotin.
        simpl in J1.
        apply NoDup_disjoint with (i0:=getCmdLoc c1) in J1; auto.
        apply in_or_app. left. apply In_InCmdLocs; auto.
      rewrite notin__lookupPhiNodeViaIDFromPhiNodes_none; auto.
      simpl in J1. apply NoDup_inv in J1. destruct J1 as [_ J1].
      apply NoDup_inv in J1. destruct J1 as [Huniq _].
      rewrite IngetCmdsLocs__lookupCmdViaIDFromCmds; auto.

      assert (~ In (getCmdLoc c1) (getBlockLocs a)) as Hnotin.     
        intro J. apply J3 in J. apply J.
        eapply in_getBlockLocs__in_getBlocksLocs in H; eauto.
        simpl. apply in_or_app. right. 
        apply in_or_app. left. apply In_InCmdLocs; auto.
      rewrite notin__lookupInsnViaIDFromBlock_none; auto.
      eapply IHbs; eauto.
Qed.

Lemma InGetValueIDs__eq: forall vid v,
  In vid (getValueIDs v) -> v = value_id vid.
Proof.
  destruct v; simpl; intros.
    destruct H as [H | H]; subst; auto.
      inv H.
    inv H.
Qed.

Lemma InOps__valueInCmdOperands : forall vid c,
  In vid (getInsnOperands (insn_cmd c)) ->
  valueInCmdOperands (value_id vid) c.
Proof.
  intros vid c H.
  destruct c; simpl in *;
    apply in_app_or in H; 
    destruct H as [H | H]; apply InGetValueIDs__eq in H; auto.
Qed.

Lemma InOps__valueInTmnOperands : forall vid tmn,
  In vid (getInsnOperands (insn_terminator tmn)) ->
  valueInTmnOperands (value_id vid) tmn.
Proof.
  intros vid tmn H.
  destruct tmn; simpl in *; subst; simpl; try solve
    [auto | apply InGetValueIDs__eq in H; auto].
Qed.

Lemma InOps__valueInPhiNodeOperands: forall x vls
  (Hin' : In x
    (values2ids (list_prj1 value l (unmake_list_value_l vls)))),
  exists n1 : nat,
    exists l2 : l, nth_list_value_l n1 vls = Some (value_id x, l2).
Proof.
  induction vls; simpl; intros.
    inv Hin'.

    destruct v.    
      simpl in Hin'.
      destruct Hin' as [J | J]; subst.
        exists O. exists l0. simpl. auto.

        apply IHvls in J. destruct J as [n1 [l2 J]].
        exists (S n1). exists l2. simpl. auto.
      
      apply IHvls in Hin'. destruct Hin' as [n1 [l2 J]].
      exists (S n1). exists l2. simpl. auto.
Qed.

Lemma In_InPhiNodesB: forall p ps, In p ps -> InPhiNodesB p ps.
Proof.
  induction ps; simpl; intros.
    inv H.
    apply orb_true_iff.
    destruct H as [H | H]; subst.
      left. apply phinodeEqB_refl.
      right. apply IHps; auto.
Qed.

Lemma app_list_value_l_cons: forall vls1 vls2 v0 l0,
  app_list_value_l vls1 (Cons_list_value_l v0 l0 vls2) =
  app_list_value_l 
    (app_list_value_l vls1 (Cons_list_value_l v0 l0 Nil_list_value_l)) vls2.
Proof.
  induction vls1; simpl; intros; auto.
    rewrite IHvls1; auto.
Qed.

Lemma getPhiNodeID_in_getPhiNodesIDs : forall ps p,
  In p ps ->
  In (getPhiNodeID p) (getPhiNodesIDs ps).
Proof.
  induction ps; intros.
    inversion H.

    simpl in *. 
    destruct H as [H | H]; subst; eauto.
Qed.

Lemma InPhiNodesB_In: forall p ps, InPhiNodesB p ps -> In p ps.
Proof.
  induction ps; simpl; intros.
    inv H.
    apply orb_true_iff in H.
    destruct H as [H | H]; subst.
      apply phinodeEqB_inv in H. subst. auto.
      right. apply IHps; auto.
Qed.

Lemma terminatorInBlockB__inGetBlockLocs: forall t b, 
  terminatorInBlockB t b -> In (getTerminatorID t) (getBlockLocs b).
Proof.
  destruct b. simpl. intros.
  apply terminatorEqB_inv in H. subst.
  apply in_or_app. right. apply in_or_app. simpl; auto.
Qed.
      
Lemma getTerminatorID__neq__getCmdLoc: forall t c b1 b2 f,
  (let '(fdef_intro bs) := f in NoDup (getBlocksLocs bs)) ->
  insnInFdefBlockB (insn_terminator t) f b1 = true->
  insnInFdefBlockB (insn_cmd c) f b2 = true ->
  getTerminatorID t <> getCmdLoc c.
Proof.
  destruct f as [bs].
  induction bs; simpl; intros.
    apply andb_true_iff in H0. destruct H0 as [_ H0]. inv H0.

    apply andb_true_iff in H0. destruct H0 as [J1 J2].
    apply andb_true_iff in H1. destruct H1 as [J3 J4].
    apply orb_true_iff in J2.
    apply orb_true_iff in J4.
    apply NoDup_split' in H. destruct H as [G1 [G2 G3]].
    destruct J2 as [J2 | J2].
      apply blockEqB_inv in J2. inv J2.   
      destruct J4 as [J4 | J4].
        apply blockEqB_inv in J4. inv J4. 
        clear - G1 J1 J3.
        destruct a. simpl in *.
        apply terminatorEqB_inv in J1. subst.
        apply InCmdsB_in in J3.
        apply NoDup_inv in G1.
        destruct G1 as [_ G1].
        apply NoDup_disjoint with (i0:=getTerminatorID t0) in G1; simpl; auto.
          intro J. apply G1. rewrite J. apply In_InCmdLocs; auto.

        intro J.
        apply (@G3 (getCmdLoc c)).
          rewrite <- J.
          apply terminatorInBlockB__inGetBlockLocs; auto. 

          eapply in_getBlockLocs__in_getBlocksLocs; eauto.
          apply cmdInBlockB__inGetBlockIDs; auto.

      destruct J4 as [J4 | J4].
        apply blockEqB_inv in J4. inv J4. 
        intro J.
        apply (@G3 (getCmdLoc c)).
          apply cmdInBlockB__inGetBlockIDs; auto.

          eapply in_getBlockLocs__in_getBlocksLocs; eauto.
          rewrite <- J.
          apply terminatorInBlockB__inGetBlockLocs; auto. 

        apply IHbs; auto.
          apply andb_true_iff. auto.
          apply andb_true_iff. auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
