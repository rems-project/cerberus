Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import typings.
Require Import infrastructure_props.
Require Import analysis.

Import VMinfra.
Import VMtypings.
Import VMgv.
Import AtomSet.

Ltac inv_wf_fdef HwfF :=
  let blocks := fresh "blocks" in
  let block := fresh "block" in
  let usedef_block := fresh "usedef_block" in
  let Hentry := fresh "Hentry" in
  let Hgetud := fresh "Hgetud" in
  let Hnpred := fresh "Hnpred" in
  let HwfBs := fresh "HwfBs" in
  let HuniqF := fresh "HuniqF" in
  let Heq := fresh "Heq" in
  inversion HwfF as 
    [blocks block usedef_block Hentry Hgetud Hnpred HwfBs HuniqF Heq]; subst.

Ltac inv_wf_block HwfB :=
  let fdef := fresh "fdef" in
  let l5 := fresh "l5" in
  let phinodes := fresh "phinodes" in
  let cmds := fresh "cmds" in
  let terminator := fresh "terminator" in
  let HBinF := fresh "HBinF" in
  let HwfPNs := fresh "HwfPNs" in
  let HwfCs := fresh "HwfCs" in
  let Hwftmn := fresh "Hwftmn" in
  let Heq1 := fresh "Heq1" in
  let Heq2 := fresh "Heq2" in
  inversion HwfB as 
    [fdef l5 phinodes cmds terminator HBinF HwfPNs HwfCs Hwftmn Heq1 Heq2]; 
    subst.

(********************************************)
(** * Inversion of well-formedness *)

Lemma getEntryBlock_inv : forall 
  (bs : blocks)
  (l3 : l)
  (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (HwfF : wf_fdef (fdef_intro bs))
  (HBinF : InBlocksB (block_intro l3 ps cs tmn) bs = true)
  (a : atom)
  (Hsucc : In l' (successors_terminator tmn))
  ps1 cs1 tmn1
  (H : getEntryBlock (fdef_intro bs) = ret block_intro a ps1 cs1 tmn1),
  l' <> a.
Proof.
  intros.  
   destruct (eq_atom_dec l' a); subst; auto.
   inv HwfF.
   rewrite H in H1. inv H1.
   simpl in H3.
   clear - H3 Hsucc HBinF.
   induction bs; simpl in *.
     inversion HBinF.
  
     apply orb_prop in HBinF.          
     destruct HBinF as [HBinF | HBinF].
       apply blockEqB_inv in HBinF; subst.
       simpl in H3.
       destruct tmn; try solve [inversion Hsucc].
         unfold hasNonePredecessor in H3.
         unfold predOfBlock in H3. simpl in H3.  
         simpl in Hsucc. 
         destruct Hsucc as [Hsucc | [Hsucc | Hsucc]]; subst; 
           try inversion Hsucc.
  
           destruct (@lookupAL_update_udb_eq (update_udb nil l3 l1) l3 a)
             as [re [Hlk Hin]]. 
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re' [Hlk Hinc]].
           rewrite Hlk in H3.
           destruct re'; inversion H3.
           apply Hinc in Hin. inversion Hin.
  
           destruct (@lookupAL_update_udb_eq nil l3 a) as [re [Hlk Hin]].
           apply lookupAL_update_udb_spec with (l1:=l3)(l2:=l0) in Hlk.
           destruct Hlk as [re1 [Hlk Hinc1]].
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.  
           destruct Hlk as [re2 [Hlk Hinc2]].
           rewrite Hlk in H3.
           destruct re2; inversion H3.
           apply Hinc1 in Hin. 
           apply Hinc2 in Hin. 
           inversion Hin.
  
         unfold hasNonePredecessor in H3.
         unfold predOfBlock in H3. simpl in H3.  
         simpl in Hsucc. 
         destruct Hsucc as [Hsucc | Hsucc]; subst; try inversion Hsucc.
           destruct (@lookupAL_update_udb_eq nil l3 a) as [re [Hlk Hin]]. 
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re' [Hlk Hinc]].
           rewrite Hlk in H3.
           destruct re'; inversion H3.
           apply Hinc in Hin. inversion Hin.
     apply hasNonPredecessor__mono in H3; eauto.
Qed.

Lemma wf_blocks__wf_block : forall f bs b,
  wf_blocks f bs -> 
  InBlocksB b bs = true ->
  wf_block f b.
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

Lemma wf_fdef__blockInFdefB__wf_block : forall b f,
  blockInFdefB b f = true -> 
  wf_fdef f ->
  wf_block f b.
Proof.
  intros.
  inv H0.  
  eapply wf_blocks__wf_block; eauto.
Qed.

Lemma wf_fdef__uniqFdef : forall f,
  wf_fdef f -> uniqFdef f.
Proof.
  intros. inv H; auto.
Qed.

Lemma wf_fdef__lookup__wf_block : forall b f l0,
  Some b = lookupBlockViaLabelFromFdef f l0 ->
  wf_fdef f ->
  wf_block f b.
Proof.
  intros.
  eapply wf_fdef__blockInFdefB__wf_block; eauto.
    symmetry in H. destruct b.
    assert (uniqFdef f) as J. eapply wf_fdef__uniqFdef; eauto.
    eapply lookupBlockViaLabelFromFdef_inv in H; eauto.
    destruct H; auto.
Qed.

Lemma wf_fdef__uniq_block : forall b f,
  blockInFdefB b f = true -> 
  wf_fdef f ->
  NoDup (getBlockLocs b).
Proof.
  intros.
  eapply wf_fdef__uniqFdef in H0; eauto.
  destruct f. simpl in *.
  inv H0.
  eapply uniqBlocksLocs__uniqBlockLocs; eauto.
Qed.

Lemma wf_cmds__wf_cmd : forall f b cs c,
  wf_cmds f b cs ->
  In c cs ->
  wf_insn f b (insn_cmd c).
Proof.
  induction cs; intros.
    inversion H0.
    
    simpl in H0.
    inv H.
    destruct H0 as [H0 | H0]; subst; eauto.
Qed.

Lemma wf_fdef__wf_cmd : forall l1 ps1 cs1 tmn1 f c,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  wf_fdef f ->
  In c cs1 ->
  wf_insn f (block_intro l1 ps1 cs1 tmn1) (insn_cmd c).
Proof.
  intros.
  eapply wf_fdef__blockInFdefB__wf_block in H; eauto.
  inv H. eapply wf_cmds__wf_cmd; eauto.
Qed.

Lemma wf_fdef__wf_tmn : forall l1 ps1 cs1 tmn1 f,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  wf_fdef f ->
  wf_insn f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1).
Proof.
  intros.
  eapply wf_fdef__blockInFdefB__wf_block in H; eauto.
  inv H. auto.
Qed.

Lemma wf_fdef__non_entry: forall f, wf_fdef f -> getEntryBlock f <> None.
Proof.
  intros. inv H. rewrite H0. congruence.
Qed.

Lemma wf_tmn__wf_value : forall f b tmn v,
  wf_insn f b (insn_terminator tmn) ->
  valueInTmnOperands v tmn ->
  wf_value f v.
Proof.
  intros f b tmn v Hwfinsn HvInOps.
  inv Hwfinsn; simpl in HvInOps; subst; try solve [
    eauto | inversion HvInOps
  ].
Qed.

Lemma entryBlock_has_no_phinodes : forall f l1 ps1 cs1 tmn1,
  wf_fdef f ->
  getEntryBlock f = Some (block_intro l1 ps1 cs1 tmn1) ->
  ps1 = nil.  
Proof.
  intros f l1 ps1 cs1 tmn1 Hwff Hentry.
  assert (wf_block f (block_intro l1 ps1 cs1 tmn1)) as Hwfb.
    apply entryBlockInFdef in Hentry.
    eapply wf_fdef__blockInFdefB__wf_block; eauto.
  inv Hwfb.
  clear H6 H7.
  destruct ps1; auto.
  inv H5.
  clear H6.
  inv H3.
  inv H6.
  unfold check_list_value_l in H2.
  remember (split (unmake_list_value_l value_l_list)) as R.
  destruct R.
  destruct H2 as [J1 [J2 J3]].
  inv Hwff.
  rewrite H2 in Hentry. inv Hentry.
  unfold hasNonePredecessor in H5.
  simpl in *.
  destruct (predOfBlock
            (block_intro l1 (insn_phi id5 value_l_list :: ps1) cs1 tmn1)
            (genBlockUseDef_blocks blocks5 nil)); inversion H5.
  simpl in J1. contradict J1. omega.
Qed.

Lemma wf_operand_list__wf_operand : forall id_list fdef5 block5 insn5 id_ n,
  wf_operand_list (make_list_fdef_block_insn_id (map_list_id
    (fun id_ : id => (fdef5, block5, insn5, id_)) id_list)) ->
  nth_list_id n id_list = Some id_ ->
  wf_operand fdef5 block5 insn5 id_.
Proof.
  induction id_list; intros fdef5 block5 insn5 id_ n Hwfops Hnth.
    destruct n; inversion Hnth.

    simpl in Hwfops.
    inv Hwfops.
    destruct n; inv Hnth; eauto.
Qed.        

Lemma wf_phi_operands__elim : forall f b i0 vls0 vid1 l1 n,
  wf_phi_operands f b i0 vls0 ->
  nth_list_value_l n vls0 = Some (value_id vid1, l1) ->
  exists vb, exists b1,
    lookupBlockViaIDFromFdef f vid1 = Some vb /\
    lookupBlockViaLabelFromFdef f l1 = Some b1 /\
    (blockDominates f vb b1 \/ (notT (isReachableFromEntry f b))).
Proof.
  induction vls0; intros.
    destruct n; inversion H0.
    destruct v; inv H; destruct n; inv H0; eauto.
Qed.

Lemma wf_value_list__getValueViaLabelFromValuels__wf_value : forall
  (f : fdef)
  (lc : GVMap)
  (l1 : l)
  v
  l2
  (H2 : wf_value_list
         (make_list_fdef_value
            (map_list_value_l
               (fun (value_ : value) (_ : l) => (f, value_)) l2)))
  (J : getValueViaLabelFromValuels l2 l1 = ret v),
  wf_value f v.
Proof.
  intros.
  induction l2; simpl in *.
    inversion J.
    
    inv H2.
    destruct (l0==l1); subst; eauto.
      inv J. auto.
Qed.        

Lemma wf_cmd__wf_value : forall f b c v,
  wf_insn f b (insn_cmd c) ->
  valueInCmdOperands v c ->
  wf_value f v.
Proof.
  intros f b c v Hwfinsn HvInOps.
  inv Hwfinsn; simpl in HvInOps; subst; try solve [
    eauto |
    destruct HvInOps as [HvInOps | HvInOps]; subst; eauto
  ].
Qed.

Lemma wf_operand_list__elim : forall ops f1 b1 insn1 id1,
  wf_operand_list ops ->
  In (f1, b1, insn1, id1) (unmake_list_fdef_block_insn_id ops) ->
  wf_operand f1 b1 insn1 id1.
Proof.
  induction ops; intros f1 b1 insn1 id1 Hwfops Hin; simpl in *.
    inversion Hin.

    inv Hwfops.
    destruct Hin as [Hin | Hin]; auto.
      inv Hin; auto.
Qed.     

Lemma wf_insn__wf_insn_base : forall f b insn,
  ~ isPhiNode insn -> wf_insn f b insn -> wf_insn_base f b insn.
Proof.
  intros f b insn Hnonphi Hwf.
  inv Hwf; auto.
    unfold isPhiNode in Hnonphi. simpl in Hnonphi. contradict Hnonphi; auto.
Qed.

Lemma wf_value_list__getValueViaBlockFromValuels__wf_value : forall
  (f : fdef)  (lc : GVMap) b v l2
  (H2 : wf_value_list
         (make_list_fdef_value
            (map_list_value_l
               (fun (value_ : value) (_ : l) => (f, value_)) l2)))
  (J : getValueViaBlockFromValuels l2 b = ret v),
  wf_value f v.
Proof.
  intros. destruct b. simpl in J.
  eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H2; eauto.
Qed.        
   
Lemma wf_fdef__wf_phinodes : forall f l3 cs tmn ps,
  wf_fdef f ->
  blockInFdefB (block_intro l3 ps cs tmn) f ->
  wf_phinodes f (block_intro l3 ps cs tmn) ps.
Proof.
  intros.
  inv H.
  eapply wf_blocks__wf_block in H4; eauto.
  inv H4; auto.
Qed.

Lemma wf_phinodes_elim: forall f b ps p,
  wf_phinodes f b ps ->
  InPhiNodesB p ps ->
  wf_insn f b (insn_phinode p).
Proof.
  induction ps; simpl; intros.
    inv H0.

    inv H.
    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0]; auto.
      apply phinodeEqB_inv in H0. subst. auto.
Qed.

Lemma notin_getInsnOperands: forall bs x
  (n0 : ~ In x (getBlocksLocs bs))
  (HwfF : wf_fdef (fdef_intro bs))
  l0 ps0 cs0 t0
  (HwfB : wf_block (fdef_intro bs) (block_intro l0 ps0 cs0 t0)),
  forall i0 : insn,
    insnInBlockB i0 (block_intro l0 ps0 cs0 t0) = true ->
    ~ In x (getInsnOperands i0).
Proof.
  intros. intro Hin.
  assert (uniqFdef (fdef_intro bs)) as HuniqF.
    apply wf_fdef__uniqFdef in HwfF; auto.
  inv HwfB.
      destruct i0; simpl in H.      
        eapply wf_phinodes_elim in H; eauto.
        inv H.
        assert (exists n, exists l1, 
          nth_list_value_l n value_l_list = Some (value_id x, l1)) as G.
          simpl in Hin.
          apply InOps__valueInPhiNodeOperands; auto.
        destruct G as [n2 [l2 G]].
        destruct H9 as [H12 H13].
        eapply wf_phi_operands__elim in G; eauto.
        destruct G as [vb [b1 [J1 [J2 J3]]]].
        simpl in J1.
        apply lookupBlockViaIDFromBlocks__InGetBlocksLocs in J1; auto.
        
        apply InCmdsB_in in H.
        eapply wf_fdef__wf_cmd in H; eauto.
        apply wf_cmd__wf_value with (v:=value_id x) in H.
          inv H.
          simpl in H2. apply lookupIDFromBlocks__InGetBlocksLocs in H2; auto.
          apply InOps__valueInCmdOperands; auto.

        apply terminatorEqB_inv in H. subst.
        apply wf_tmn__wf_value with (v:=value_id x) in H8.
          inv H8.
          simpl in H1. apply lookupIDFromBlocks__InGetBlocksLocs in H1; auto.

          apply InOps__valueInTmnOperands; auto.
Qed.

Lemma wf_phinodes__wf_phinode: forall f b ps p,
  wf_phinodes f b ps -> InPhiNodesB p ps = true -> wf_phinode f b p.
Proof.
  induction ps; simpl; intros.
    inv H0.

    inv H.
    apply orb_true_iff in H0.
    destruct H0 as [H0 | H0]; eauto.
      apply phinodeEqB_inv in H0. subst.
      inv H5. auto.
Qed.

(********************************************)
(** * Correctness of analysis *)

Lemma dom_successors : forall
  (bs : blocks)
  (l3 : l)
  (l' : l)
  ps cs tmn
  (HwfF : wf_fdef (fdef_intro bs))
  (Huniq : uniqBlocks bs)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) (fdef_intro bs) = true)
  (Doms : AMap.t
           (Dominators.t (bound_fdef (fdef_intro bs))))
  (HeqDoms : Doms = dom_analyze (fdef_intro bs))
  (contents3 : ListSet.set atom)
  (inbound3 : incl contents3 (bound_fdef (fdef_intro bs)))
  (Heqdefs3 : {|
             DomDS.L.bs_contents := contents3;
             DomDS.L.bs_bound := inbound3 |} = Doms !! l3)
  (Hsucc : In l' (successors_terminator tmn))
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef (fdef_intro bs)))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = Doms !! l'),
  incl contents' (l3 :: contents3).
Proof. 
  intros. simpl in *.
  unfold dom_analyze in *.
  remember (entry_dom bs) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
  Case "entry is good".
    remember (DomDS.fixpoint (bound_blocks bs) (successors_blocks bs)
                (transfer (bound_blocks bs)) ((le, start) :: nil)) as R1.
    destruct start.
    destruct bs_contents; tinv Hp.
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      assert (In l' (successors_blocks bs) !!! l3) as J1.
        clear - HBinF Hsucc Huniq.
        assert (successors_terminator tmn = (successors_blocks bs) !!! l3) as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ. auto.
      
      apply DomDS.fixpoint_solution with (s:=l')(n:=l3) in HeqR1; eauto.
      unfold transfer, DomDS.L.ge, DomDS.L.top, DomDS.L.bot, DomDS.L.sub, 
        DomDS.L.eq, Dominators.add in HeqR1.
      remember (t !! l') as R2.
      destruct R2.              
      assert (contents' = bs_contents) as EQ.
        clear - Heqdefs' HeqR2.
        eapply atomset_eq__proof_irr1; eauto.
      subst.
      remember (t !! l3) as R3.
      destruct R3.              
      assert (contents3 = bs_contents0) as EQ.
        clear - Heqdefs3 HeqR3.
        eapply atomset_eq__proof_irr1; eauto.
      subst.
      clear - Heqdefs3 Heqdefs' HeqR2 HeqR3 HeqR1.
      destruct HeqR1 as [HeqR1 | [HeqR1 | HeqR1]].
        destruct HeqR1 as [G1 G2].
        intros x G.
        apply G1 in G. inversion G.

        destruct (in_dec eq_atom_dec l3 (bound_blocks bs)).
          eapply incl_set_eq_right; eauto using set_eq_sym.
          apply incl_tran with (m:=bs_contents0).
            eapply incl_set_eq_right; eauto using set_eq_sym.
            apply incl_tl; auto using incl_refl.
          
        destruct (in_dec eq_atom_dec l3 (bound_blocks bs)); auto.
          apply incl_tl; auto.

    SCase "analysis fails".
      subst.
      unfold Dominators.top in Heqdefs3, Heqdefs'.
      simpl in Heqdefs3, Heqdefs'.
      destruct bs; tinv HeqR.
      destruct b; inv HeqR.
      assert (exists ps, exists cs, exists tmn,
        getEntryBlock (fdef_intro ((block_intro l0 p c t) :: bs)) = 
          Some (block_intro l0 ps cs tmn)) as H.
        unfold entry_dom in HeqR1.
        exists p. exists c. exists t. auto.
      assert (l' <> l0) as Neq.
        clear - H Hsucc HwfF HBinF. 
        destruct H as [ps1 [cs1 [tmn1 H]]].
        eapply getEntryBlock_inv; eauto.
      rewrite AMap.gso in Heqdefs'; auto.
      rewrite AMap.gi in Heqdefs'.
      inv Heqdefs'.
      clear.
      intros x J. inversion J.

  Case "entry is wrong".   
    subst. inversion HBinF.
Qed.

Lemma wf_tmn__in_successors: forall f l0 cs ps tmn l1
  (HuniqF : uniqFdef f)
  (Hwftmn : wf_insn f (block_intro l0 cs ps tmn) (insn_terminator tmn))
  (Hin : In l1 (successors_terminator tmn)),
  exists cs1, exists ps1, exists tmn1, 
    blockInFdefB (block_intro l1 cs1 ps1 tmn1) f.
Proof.
  intros.
  inv Hwftmn; simpl in Hin.
    inv Hin.

    destruct Hin as [Hin | [Hin | Hin]]; tinv Hin; subst.
      destruct block1.
      apply lookupBlockViaLabelFromFdef_inv in H1; auto.
      destruct H1 as [J1 J2]; subst; eauto.

      destruct block2.
      apply lookupBlockViaLabelFromFdef_inv in H2; auto.
      destruct H2 as [J1 J2]; subst; eauto.

    destruct Hin as [Hin | Hin]; tinv Hin; subst.
      apply lookupBlockViaLabelFromFdef_inv in H0; auto.
      destruct H0 as [J1 J2]; subst; eauto.
Qed.

Lemma getCmdOperands__nth_list_id : forall i0 c1 id_list
  (i1 : In i0 (getCmdOperands c1))
  (H1 : getInsnOperands (insn_cmd c1) = unmake_list_id id_list),
  exists n : nat, nth_list_id n id_list = ret i0.
Proof.
  destruct c1; simpl; intros.
    unfold getValueIDs in H1.
    destruct v; destruct v0; simpl in *.
      destruct i2 as [Heq | [Heq | i2]]; subst; try inversion i2.
        exists 0%nat. destruct id_list; tinv H1. destruct id_list; inv H1; auto.
        exists 1%nat. destruct id_list; tinv H1. destruct id_list; inv H1; auto.
      destruct i2 as [Heq | i2]; subst; try inversion i2.
        exists 0%nat. destruct id_list; inv H1; auto.
      destruct i2 as [Heq | i2]; subst; try inversion i2.
        exists 0%nat. destruct id_list; inv H1; auto.
      inv i2.

    unfold getValueIDs in H1.
    destruct v; destruct v0; simpl in *.
      destruct i2 as [Heq | [Heq | i2]]; subst; try inversion i2.
        exists 0%nat. destruct id_list; tinv H1. destruct id_list; inv H1; auto.
        exists 1%nat. destruct id_list; tinv H1. destruct id_list; inv H1; auto.
      destruct i2 as [Heq | i2]; subst; try inversion i2.
        exists 0%nat. destruct id_list; inv H1; auto.
      destruct i2 as [Heq | i2]; subst; try inversion i2.
        exists 0%nat. destruct id_list; inv H1; auto.
      inv i2.
Qed.

Lemma wf_fdef__wf_insn_base : forall F id1 c1,
  wf_fdef F ->
  lookupInsnViaIDFromFdef F id1 = ret insn_cmd c1 ->
  exists b1, wf_insn_base F b1 (insn_cmd c1).
Proof.
  intros.
  apply lookupInsnViaIDFromFdef__insnInFdefBlockB in H0.
  destruct H0 as [b H0]. exists b.
  destruct b. simpl in H0.
  apply andb_true_iff in H0.
  destruct H0 as [J1 J2].
  apply InCmdsB_in in J1.
  apply wf_fdef__wf_cmd with (c:=c1) in J2; auto.
  apply wf_insn__wf_insn_base in J2; auto.
  intro J. inv J.
Qed.

Lemma wf_cmds_intro: forall f b cs,
  (forall c, In c cs -> wf_insn f b (insn_cmd c)) ->
  wf_cmds f b cs.
Proof.
  induction cs; intros.
    constructor.
    constructor.
      apply H; simpl; auto.
      apply IHcs. intros. apply H; simpl; auto.
Qed.

Lemma wf_cmds_elim: forall f b cs,
  wf_cmds f b cs -> forall c, In c cs -> wf_insn f b (insn_cmd c).
Proof.
  intros f b cs J.
  induction J; intros.
    inv H.

    simpl in H0. 
    destruct H0 as [H0 | H0]; subst; auto.
Qed.

Lemma wf_operand_list__intro : forall ops,
  (forall f1 b1 insn1 id1,
    In (f1, b1, insn1, id1) (unmake_list_fdef_block_insn_id ops) ->
    wf_operand f1 b1 insn1 id1) ->
  wf_operand_list ops.
Proof.
  induction ops; intros.
    constructor.
    constructor.
      apply H; simpl; auto.
      apply IHops; intros. apply H; simpl; auto.
Qed.

Lemma unmake_make_list_id: forall l1, unmake_list_id (make_list_id l1) = l1.
Proof.
  induction l1; simpl; auto.
    rewrite IHl1. auto.
Qed.

Require Import Dipaths.

Module DomComplete. Section DomComplete.
  
Variable bs : blocks.
Definition f := fdef_intro bs.
Definition bound := bound_blocks bs.
Definition predecessors := make_predecessors (successors f).
Definition transf := transfer bound.
Definition top := Dominators.top bound.
Definition bot := Dominators.bot bound.
Definition dt := DomDS.dt bound.
Variable entry: l.
Variable entrypoints: list (atom * dt).

Hypothesis wf_entrypoints:
  predecessors!!!entry = nil /\
  match bs with
  | block_intro l0 _ _ _ :: _ => l0 = entry
  | _ => False 
  end /\
  exists v, [(entry, v)] = entrypoints /\ Dominators.eq _ v top.

Hypothesis HwfF: wf_fdef f.

Definition non_sdomination (l1 l2:l) : Prop :=
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  exists vl, exists al, 
    D_walk vertexes arcs (index l2) (index entry) vl al /\
    ~ In (index l1) vl.

Definition non_sdomination_prop (res: AMap.t dt) : Prop :=
  forall l1 l2, 
    vertexes_fdef f (index l1) ->
    ~ Dominators.member _ l1 res!!l2 -> 
    non_sdomination l1 l2.
    
Lemma start_non_sdomination: 
  non_sdomination_prop 
    (DomDS.st_in _ (DomDS.start_state _ (successors f) entrypoints)).
Proof.
  intros l1 l2 Hin Hnotin.
  destruct (eq_atom_dec l2 entry); try subst l2.
    unfold non_sdomination.
    exists V_nil. exists A_nil. 
    split. 
      constructor.
      unfold f. 
      destruct wf_entrypoints as [_ [J _]].
      destruct bs; tinv J.
      destruct b; subst.
      eapply entry_in_vertexes; simpl; eauto.

      intro J. inv J.

    apply EntryDomsOthers.dom_nonentry_start_state_in 
      with (bs:=bs)(entrypoints:=entrypoints) in n; auto.
    contradict Hnotin.
    unfold DomDS.start_state. simpl.
    apply Dominators.member_eq with (x2:=bot); auto.
Qed.

Lemma non_sdomination_refl : forall l1,
  l1 <> entry ->
  reachable f l1 ->
  non_sdomination l1 l1.
Proof.
  unfold reachable, non_sdomination.
  intros.  
  unfold f in *. 
  destruct bs; simpl in *.
    inv H0.
    destruct b; simpl in *.
    destruct H0 as [vl [al H0]].
    apply DWalk_to_dpath in H0.
    destruct H0 as [vl0 [al0 Hp]].
    exists vl0. exists al0. 
    destruct wf_entrypoints as [_ [Heq _]]; subst.
    split.
      apply D_path_isa_walk; auto.
      eapply DP_endx_ninV; eauto. congruence.
Qed.

Lemma propagate_succ_non_sdomination: forall st p n out
  (Hinpds: In p predecessors!!!n)
  (Hout: Dominators.ge _ (transf p st.(DomDS.st_in _)!!p) out)
  (Hdom: non_sdomination_prop st.(DomDS.st_in _)),
  non_sdomination_prop (DomDS.propagate_succ _ st out n).(DomDS.st_in _).
Proof.
  unfold non_sdomination_prop. intros.
  destruct (@DomDS.propagate_succ_spec _ st out n) as [J1 J2].
  destruct (eq_atom_dec n l2) as [Heq | Hneq]; subst.
  Case "n=l2".
    destruct (Dominators.member_dec _ l1 (DomDS.st_in _ st) !! l2) 
      as [Hin12 | Hnotin12]; auto.
    assert (~ Dominators.member bound l1
      (DomDS.L.lub bound (DomDS.st_in bound st) !! l2 out)) as Hnotlub12.
      intro J. apply H0.
      eapply Dominators.member_eq; eauto.
    clear J1 J2.
    destruct (Dominators.member_dec _ l1 out) as [Hinout | Hnotout]; auto.
    SCase "l1 in out".
      contradict Hnotlub12. apply Dominators.lub_intro; auto.
    SCase "l1 notin out".
      assert (~ Dominators.member _ l1 (transf p (DomDS.st_in bound st) !! p))
        as Hnotintransf.
        intro J. apply Hnotout.
        eapply Dominators.ge_elim in Hout; eauto.
      unfold transf, transfer in Hnotintransf.
      assert (l1 <> p /\ ~ Dominators.member _ l1 (DomDS.st_in bound st)!!p) 
        as J.
        split; intro J; subst; apply Hnotintransf.
          apply Dominators.add_member1; auto.
          apply Dominators.add_member2; auto.
      clear Hnotintransf.
      destruct J as [Hneq J].
      apply Hdom in J; auto.
      destruct J as [vl [al [J1 J2]]].
      exists (index p::vl). exists (A_ends (index l2) (index p)::al).
      split.
        constructor; auto.
          apply make_predecessors_correct' in Hinpds.
          apply successors__blockInFdefB in Hinpds.
          destruct Hinpds as [ps0 [cs0 [tmn0 [J3 J4]]]].
          apply wf_fdef__blockInFdefB__wf_block in J3; auto.
          inv J3. inv HwfF.
          eapply wf_tmn__in_successors in H9; eauto.
          destruct H9 as [cs1 [ps1 [tmn1 H9]]].
          eapply blockInFdefB_in_vertexes; eauto.

          apply make_predecessors_correct' in Hinpds.
          apply successors__blockInFdefB in Hinpds; auto.
          destruct Hinpds as [ps0 [cs0 [tmn0 [J3 J4]]]].
          inv HwfF.
          eapply successor_in_arcs; eauto.

          intro J. simpl in J. 
          destruct J as [J | J]; auto.
            inv J. auto.
  Case "n<>l2".
    rewrite J2 in H0; auto.
Qed.

Lemma propagate_succ_list_non_sdomination_aux:
  forall p scs st out,
  (forall s, In s scs -> In p predecessors!!!s) ->
  non_sdomination_prop st.(DomDS.st_in _) ->   
  Dominators.ge _ (transf p st.(DomDS.st_in _)!!p) out ->
  non_sdomination_prop (DomDS.propagate_succ_list _ st out scs).(DomDS.st_in _).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs; auto.
      eapply propagate_succ_non_sdomination; eauto.
      apply Dominators.ge_trans with (y:=transf p (DomDS.st_in _ st) !! p);
        auto.
        eapply EntryDomsOthers.transf_mono; eauto.
        destruct (@DomDS.propagate_succ_spec _ st out a) as [J1 J2].
        destruct (eq_atom_dec a p); subst.
          apply Dominators.ge_trans with 
            (y:=Dominators.lub _ (DomDS.st_in _ st) !! p out).
            apply Dominators.ge_refl; auto.
            apply Dominators.ge_lub_left.
          rewrite J2; auto.
            apply Dominators.ge_refl'.
Qed.

Lemma propagate_succ_list_non_sdomination:
  forall p scs st,
  (forall s, In s scs -> In p predecessors!!!s) ->
  non_sdomination_prop st.(DomDS.st_in _) ->
  non_sdomination_prop (DomDS.propagate_succ_list _ st 
    (transf p st.(DomDS.st_in _)!!p) scs).(DomDS.st_in _).
Proof.
  intros.
  eapply propagate_succ_list_non_sdomination_aux; eauto.
    apply Dominators.ge_refl'.
Qed.

Lemma step_non_sdomination:
  forall st n rem,
  AtomNodeSet.pick st.(DomDS.st_wrk _) = Some(n, rem) ->
  non_sdomination_prop st.(DomDS.st_in _) ->
  non_sdomination_prop (DomDS.propagate_succ_list _ 
                                   (DomDS.mkstate _ st.(DomDS.st_in _) rem)
                                   (transf n st.(DomDS.st_in _)!!n)
                                   ((successors f)!!!n)).(DomDS.st_in _).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_non_sdomination; auto.
    apply make_predecessors_correct.
Qed.

Theorem dom_non_sdomination: forall res, 
  DomDS.fixpoint _ (successors f) transf entrypoints = Some res -> 
  non_sdomination_prop res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res. 
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _ _) 
    (fun st => non_sdomination_prop st.(DomDS.st_in _))); eauto.
    intros st GOOD. unfold DomDS.step. 
    caseEq (AtomNodeSet.pick st.(DomDS.st_wrk _)); auto.
    intros [n rem] PICK. apply step_non_sdomination; auto. 

    apply start_non_sdomination.
Qed.

End DomComplete. End DomComplete.

Lemma reachable_successors:
  forall f l0 cs ps tmn l1,
  wf_fdef f ->
  blockInFdefB (block_intro l0 cs ps tmn) f ->
  In l1 (successors_terminator tmn) ->
  reachable f l0 ->
  reachable f l1.
Proof.
  intros f l0 cs ps tmn l1 HuniqF HbInF Hin.
  unfold reachable. intro Hreach.
  remember (getEntryBlock f) as R.
  destruct R; auto.
  destruct b as [le ? ? ?].
  destruct Hreach as [vl [al Hreach]].
  exists (index l0::vl). exists (A_ends (index l1) (index l0)::al).
  apply DW_step; auto.
    apply wf_fdef__wf_tmn in HbInF; auto.    
    eapply wf_tmn__in_successors in HbInF; eauto using wf_fdef__uniqFdef.
    destruct HbInF as [cs1 [ps1 [tmn1 HbInF]]].
    eapply blockInFdefB_in_vertexes; eauto.

    eapply successor_in_arcs; eauto using wf_fdef__uniqFdef.
Qed.

Module UnreachableDoms. Section UnreachableDoms.

Variable bs : blocks.
Definition f := fdef_intro bs.
Definition bound := bound_blocks bs.
Definition predecessors := make_predecessors (successors f).
Definition transf := transfer bound.
Definition top := Dominators.top bound.
Definition bot := Dominators.bot bound.
Definition dt := DomDS.dt bound.
Variable entry: l.
Variable entrypoints: list (atom * dt).

Hypothesis wf_entrypoints:
  predecessors!!!entry = nil /\
  match bs with
  | block_intro l0 _ _ _ :: _ => l0 = entry
  | _ => False 
  end /\
  exists v, [(entry, v)] = entrypoints /\ Dominators.eq _ v top.

Hypothesis HwfF: wf_fdef f.

Definition unrechable_doms (res: AMap.t dt) : Prop :=
  forall l0, ~ reachable f l0 -> l0 <> entry -> Dominators.eq _ res!!l0 bot.

Lemma start_unrechable_doms: 
  unrechable_doms 
    (DomDS.st_in _ (DomDS.start_state _ (successors f) entrypoints)).
Proof.
  intros l0 Hunreach Heq.
  unfold DomDS.start_state. simpl.
  eapply EntryDomsOthers.dom_nonentry_start_state_in in Heq; eauto.
Qed.

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma propagate_succ_unrechable_doms: forall st n out,
  (~ reachable f n -> n <> entry -> Dominators.eq _ out bot) ->
  unrechable_doms st.(DomDS.st_in _) -> 
  unrechable_doms (DomDS.propagate_succ _ st out n).(DomDS.st_in _).
Proof.
  unfold unrechable_doms.
  intros. 
  destruct (@DomDS.propagate_succ_spec _ st out n) as [J1 J2].
  assert (H':=H1). 
  apply H0 in H1; auto.
  destruct (eq_atom_dec n l0); subst.
    apply H in H'; auto.
    apply Dominators.eq_trans with 
      (y:=DomDS.L.lub bound (DomDS.st_in bound st) !! l0 out); auto.
    apply Dominators.eq_trans with (y:=DomDS.L.lub _ bot bot); auto.
       apply Dominators.lub_compat_eq; auto.
       apply Dominators.eq_sym. apply Dominators.lub_refl.

    rewrite J2; auto.
Qed.

Lemma propagate_succ_list_unrechable_doms:
  forall scs st out,
  (forall s, In s scs ->
             ~ reachable f s -> s <> entry ->
             Dominators.eq _ out bot) ->
  unrechable_doms st.(DomDS.st_in _) ->   
  unrechable_doms (DomDS.propagate_succ_list _ st out scs).(DomDS.st_in _).
Proof.
  induction scs; simpl; intros; auto.
    apply IHscs.
      intros. apply H with (s:=s); auto.
      apply propagate_succ_unrechable_doms; auto.
        intros J1 J2. eapply H; eauto.
Qed.

Lemma step_unrechable_doms:
  forall st n rem,
  AtomNodeSet.pick st.(DomDS.st_wrk _) = Some(n, rem) ->
  unrechable_doms st.(DomDS.st_in _) ->
  unrechable_doms (DomDS.propagate_succ_list _ 
                                   (DomDS.mkstate _ st.(DomDS.st_in _) rem)
                                   (transf n st.(DomDS.st_in _)!!n)
                                   ((successors f)!!!n)).(DomDS.st_in _).
Proof.
  intros st n rem WKL GOOD.
  destruct st. simpl.
  apply propagate_succ_list_unrechable_doms; auto.
  intros s Hin Hunreach.
    destruct (reachable_dec f n).
      assert(exists ps0, exists cs0, exists tmn0, 
        blockInFdefB (block_intro n ps0 cs0 tmn0) (fdef_intro bs) /\
        In s (successors_terminator tmn0)) as J.
        apply successors__blockInFdefB; auto.
      destruct J as [ps0 [cs0 [tmn0 [J1 J2]]]].
      eapply reachable_successors with (l1:=s) in H; eauto.
      congruence.

      apply GOOD in H. simpl in H.
      unfold transf, transfer.
      intros. 
      destruct (eq_atom_dec n entry); subst.
        assert (exists ps0, exists cs0, exists tmn0, 
          blockInFdefB (block_intro entry ps0 cs0 tmn0) f /\
          In s (successors_terminator tmn0)) as J.
          apply successors__blockInFdefB; auto.
        destruct J as [ps0 [cs0 [tmn0 [J1 J2]]]].
        contradict Hunreach.
        unfold reachable. unfold f in *. inv HwfF. rewrite H2. 
        destruct block5.
        destruct wf_entrypoints as [_ [J _]].
        destruct bs; tinv J.
        destruct b. subst entry.
        unfold successors_list in Hin. simpl in Hin. rewrite ATree.gss in Hin.
        inv H2. subst.
        exists (index l0::nil). exists (A_ends (index s) (index l0)::nil).
        constructor.
          constructor.
            eapply entry_in_vertexes; simpl; eauto.          
          clear H3. inv H5. inv H7.
          eapply wf_tmn__in_successors in Hin; eauto.
          destruct Hin as [cs1 [ps1 [tmn1 Hin]]].
          eapply blockInFdefB_in_vertexes; eauto.

          eapply successor_in_arcs; eauto.
      apply Dominators.eq_trans with (y:=Dominators.add _ (Dominators.bot _) n).
        apply Dominators.add_eq; auto.
        apply Dominators.add_bot.
Qed.

Theorem dom_unrechable_doms: forall res, 
  DomDS.fixpoint _ (successors f) transf entrypoints = Some res -> 
  unrechable_doms res.
Proof.
  unfold DomDS.fixpoint. intros res PI. pattern res. 
  eapply (PrimIter.iterate_prop _ _ (DomDS.step _ _ _) 
    (fun st => unrechable_doms st.(DomDS.st_in _))); eauto.
  intros st GOOD. unfold DomDS.step. 
  caseEq (AtomNodeSet.pick st.(DomDS.st_wrk _)); auto.
  intros [n rem] PICK. 
  apply step_unrechable_doms; auto. 
    apply start_unrechable_doms.
Qed.

End UnreachableDoms. 

End UnreachableDoms.

Lemma dom_unreachable: forall
  (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hunreach: ~ reachable f l3)
  (Hnempty: DomDS.L.bs_contents _ ((dom_analyze f) !! l3) <> nil),
  DomDS.L.eq _ ((dom_analyze f) !! l3) (DomDS.L.bot _).
Proof.
  intros. 
  assert (HwfF':=HwfF). inv HwfF'.
  destruct block5. 
  rename blocks5 into bs.
  assert (J:=H). destruct bs; inv J. 
  apply dom_entrypoint in H.
  destruct (id_dec l3 l0); subst.
    rewrite H in Hnempty. congruence.
   
    clear H. 
    unfold dom_analyze in *. 
    remember (entry_dom (block_intro l0 p c t :: bs)) as R.
    destruct R as [R Hp].
    destruct R as [[le start] | ]; tinv Hp.
    destruct start; tinv Hp.
    destruct bs_contents; tinv Hp. inv HeqR.
    remember (DomDS.fixpoint (bound_blocks (block_intro l0 p c t :: bs))
                  (successors_blocks (block_intro l0 p c t :: bs))
                  (transfer (bound_blocks (block_intro l0 p c t :: bs)))
                  ((l0,
                   {|
                   DomDS.L.bs_contents := nil;
                   DomDS.L.bs_bound := bs_bound |}) :: nil)) as R.
    destruct R.
      symmetry in HeqR. 
      apply UnreachableDoms.dom_unrechable_doms with (entry:=l0) in HeqR; auto.
        split. 
           remember ((DomComplete.predecessors (block_intro l0 p c t :: bs)) 
             !!! l0) as R.
           destruct R; auto.
           assert (In a (DomComplete.predecessors (block_intro l0 p c t :: bs)) 
             !!! l0) as Hin. rewrite <- HeqR0. simpl; auto.
           unfold DomComplete.predecessors in Hin.
           apply make_predecessors_correct' in Hin.
           unfold DomComplete.f in Hin.
           apply successors__blockInFdefB in Hin.
           destruct Hin as [ps0 [cs0 [tmn0 [J1 J2]]]].
           eapply getEntryBlock_inv with (l3:=a)(a:=l0) in J2; simpl; eauto.
           congruence.

        split; auto.
               exists {| DomDS.L.bs_contents := nil; DomDS.L.bs_bound := bs_bound |}.
               split; auto. simpl. apply set_eq_refl. 

      simpl in Hnempty.
      destruct (id_dec l0 l3); subst.
        rewrite AMap.gss in *. simpl in *. congruence.
        rewrite AMap.gso in *; auto. rewrite AMap.gi in *; auto. 
        simpl in *. unfold ListSet.empty_set in *. congruence.
Qed.

Definition domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  forall vl al, 
    D_walk vertexes arcs (index l2) (index entry) vl al -> 
    (In (index l1) vl \/ l1 = l2)
| _ => False
end.

Definition strict_domination (f:fdef) (l1 l2:l) : Prop :=
domination f l1 l2 /\ l1 <> l2.

Lemma sdom_is_complete: forall
  (f : fdef) (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HwfF : wf_fdef f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: strict_domination f l' l3)
  (Hnempty: DomDS.L.bs_contents _ ((dom_analyze f) !! l3) <> nil),
  In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3)).
Proof.
  intros. unfold dom_analyze in *. destruct f as [bs].
  remember (entry_dom bs) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
    destruct start; tinv Hp.
    destruct bs_contents; tinv Hp. 
    destruct bs; tinv HeqR.
    destruct b; inv HeqR.
    remember (DomDS.fixpoint (bound_blocks (block_intro l0 p c t :: bs))
                  (successors_blocks (block_intro l0 p c t :: bs))
                  (transfer (bound_blocks (block_intro l0 p c t :: bs)))
                  ((l0,
                   {|
                   DomDS.L.bs_contents := nil;
                   DomDS.L.bs_bound := bs_bound |}) :: nil)) as R.
    destruct R.
      symmetry in HeqR.
      apply DomComplete.dom_non_sdomination with (entry:=l0) in HeqR; auto.
        Focus.
        unfold DomComplete.non_sdomination_prop in HeqR.
        destruct (in_dec eq_atom_dec l'
          (DomDS.L.bs_contents
            (bound_fdef (fdef_intro (block_intro l0 p c t :: bs))) 
            t0 !! l3)); auto.
        assert (vertexes_fdef (DomComplete.f (block_intro l0 p c t :: bs))
           (index l')) as J. 
          apply blockInFdefB_in_vertexes in HBinF'; auto.
        apply HeqR with (l2:=l3) in J.
          unfold DomComplete.non_sdomination in J.
          destruct J as [vl [al [J1 J2]]].
          unfold strict_domination in Hsdom.
          destruct Hsdom as [Hdom Hneq].
          unfold domination in Hdom.
          simpl in Hdom.
          apply Hdom in J1.
          destruct J1; subst; congruence.
         
          unfold Dominators.member. 
          unfold DomComplete.dt. unfold DomComplete.bound.
          destruct (t0!!l3). simpl in *; auto.
        Unfocus.

        assert (HwfF':=HwfF). inv HwfF'.
        split. 
           remember ((DomComplete.predecessors (block_intro l0 p c t :: bs)) 
             !!! l0) as R.
           destruct R; auto.
           assert (In a (DomComplete.predecessors (block_intro l0 p c t :: bs)) 
             !!! l0) as Hin. rewrite <- HeqR0. simpl; auto.
           unfold DomComplete.predecessors in Hin.
           apply make_predecessors_correct' in Hin.
           unfold DomComplete.f in Hin.
           apply successors__blockInFdefB in Hin.
           destruct Hin as [ps0 [cs0 [tmn0 [J1 J2]]]].
           eapply getEntryBlock_inv with (l3:=a)(a:=l0) in J2; simpl; eauto.
           congruence.

        split; auto.
               exists {| DomDS.L.bs_contents := nil; DomDS.L.bs_bound := bs_bound |}.
               split; auto. simpl. apply set_eq_refl. 

      simpl in Hnempty.
      destruct (id_dec l0 l3); subst.
        rewrite AMap.gss in *. simpl in *. auto.
        rewrite AMap.gso in *; auto. rewrite AMap.gi in *; auto. 
        simpl in *. auto.

    subst. inv HBinF.
Qed.

Lemma dom_is_sound : forall
  (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : 
    In l' (l3::(DomDS.L.bs_contents _ ((dom_analyze f) !! l3)))),
  domination f l' l3.
Proof. 
  unfold domination, strict_domination.
  intros. destruct f as [bs].
  assert (Huniq : uniqBlocks bs). 
    apply wf_fdef__uniqFdef in HwfF. simpl in HwfF. auto.
  assert (HwfF':=HwfF).
  inv HwfF'. rewrite H0 in *.
  destruct block5 as [l5 ps5 cs5 t5].
  clear H4. intros vl al Hreach.
  generalize dependent ps.
  generalize dependent cs.
  generalize dependent tmn.
  remember (vertexes_fdef (fdef_intro bs)) as Vs.
  remember (arcs_fdef (fdef_intro bs)) as As.
  remember (index l3) as v0.
  remember (index l5) as v1.
  generalize dependent bs.
  generalize dependent l3.
  generalize dependent l5.
  induction Hreach; intros; subst.
    inv Heqv0.
    apply dom_entrypoint in H0.
    rewrite H0 in Hin.
    simpl in Hin. destruct Hin as [Hin | Hin]; tinv Hin; auto.

    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0, 
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) (fdef_intro bs) /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF'' Hinsucc]]]].
    remember ((dom_analyze (fdef_intro bs)) !! a0) as R.
    destruct R as [bs_contents bs_bounds].
    destruct (id_dec l' l3); subst; auto.
    left.
    assert (In l'
      (a0 :: DomDS.L.bs_contents (bound_fdef (fdef_intro bs))
                (dom_analyze (fdef_intro bs)) !! a0)) as J.
      remember ((dom_analyze (fdef_intro bs)) !! l3) as R.
      destruct R.
      assert (incl bs_contents0 (a0 :: bs_contents)) as Hinc.
        eapply dom_successors; eauto.
      rewrite <- HeqR. simpl.
      simpl in Hin. destruct Hin; try congruence.
      apply Hinc; auto.
    eapply IHHreach in J; eauto.
    simpl.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma sdom_is_sound : forall
  (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef f) (Hreach : reachable f l3)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : 
    In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3))),
  strict_domination f l' l3.
Proof. 
  intros.
  eapply dom_is_sound with (l':=l') in HBinF; simpl; eauto.
  split; auto.
  destruct (id_dec l' l3); subst; auto.
  unfold reachable, domination in *.
  remember (getEntryBlock f) as R.
  destruct R; try congruence.
  destruct b.
  destruct Hreach as [vl [al Hreach]].
  apply DWalk_to_dpath in Hreach.
  destruct Hreach as [vl0 [al0 Hp]].
  destruct (id_dec l3 l0); subst.
    symmetry in HeqR.
    apply dom_entrypoint in HeqR.
    rewrite HeqR in Hin. inv Hin.

    inv Hp; try congruence.
    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0, 
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    remember ((dom_analyze f) !! a0) as R.
    destruct R as [bs_contents bs_bounds].
    assert (In l3
      (a0 :: DomDS.L.bs_contents (bound_fdef f)
                (dom_analyze f) !! a0)) as J.
      remember ((dom_analyze f) !! l3) as R.
      destruct R.
      assert (incl bs_contents0 (a0 :: bs_contents)) as Hinc.
        destruct f. 
        assert (uniqBlocks b). inv HwfF. simpl in H11. auto.
        eapply dom_successors; eauto.
      rewrite <- HeqR0. simpl.
      simpl in Hin. 
      apply Hinc; auto.
    eapply dom_is_sound in J; eauto.
    unfold domination in J.
    rewrite <- HeqR in J.
    assert (Hw:=H).
    apply D_path_isa_walk in Hw.
    apply J in Hw.
    destruct Hw as [Hw | Hw]; subst; try congruence.
    apply H4 in Hw. inv Hw; try congruence.
Qed.

Lemma sdom_isnt_refl : forall
  (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef f) (Hreach : reachable f l3)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3))),
  l' <> l3.
Proof.
  intros.
  eapply sdom_is_sound in Hin; eauto.
  destruct Hin; auto.
Qed.

Lemma blockStrictDominates_isnt_refl : forall F1 block'
  (Hin : blockInFdefB block' F1)
  (HwfF : wf_fdef F1) (Hreach : isReachableFromEntry F1 block'),
  ~ blockStrictDominates F1 block' block'.
Proof.
  intros. destruct block'.
  unfold blockStrictDominates. intro J.
  remember ((dom_analyze F1) !! l0) as R.
  destruct R.
  simpl in Hreach.
  eapply sdom_isnt_refl in Hreach; eauto.
  rewrite <- HeqR. simpl. auto.
Qed.

Lemma dom_tran: forall (f:fdef) (l1 l2 l3:l),
  domination f l1 l2 -> domination f l2 l3 -> domination f l1 l3.
Proof.
  unfold domination.
  intros.
  destruct (getEntryBlock f); tinv H.
  destruct b.
  intros vl al Hw.
  destruct (id_dec l1 l3); auto.
  left.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst.
    apply DW_extract with (x:=index l2) in Hw; simpl; auto.
    destruct Hw as [al' Hw].
    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; auto.
    destruct (id_dec l1 l2); subst; auto.
    apply V_extract_spec in Hw''; try congruence.
    simpl in Hw''. destruct Hw'' as [Hw'' | Hw'']; congruence.

    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; congruence.
Qed.     

Lemma dom_acyclic: forall (f:fdef) (l1 l2:l) (HwfF:wf_fdef f),
  reachable f l2 ->
  strict_domination f l1 l2 -> ~ domination f l2 l1.
Proof.
  unfold reachable, strict_domination, domination. 
  intros. assert (HwfF':=HwfF). inv HwfF'.
  rewrite H1 in *. destruct block5.
  destruct H as [vl [al Hw]].
  apply DWalk_to_dpath in Hw.
  destruct Hw as [vl0 [al0 Hp]].
  assert (Hw:=Hp).
  apply D_path_isa_walk in Hw.
  destruct H0 as [J1 J2].
  assert (Hw':=Hw).
  apply J1 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst; try congruence.
  intros J.
  apply DW_extract with (x:=index l1) in Hw; simpl; auto.
  destruct Hw as [al' Hw].
  assert (Hw'':=Hw).
  apply J in Hw''.
  destruct Hw'' as [Hw'' | Hw'']; subst; auto.
  apply V_extract_spec' in Hw''; try congruence.
  inv Hp. 
    inv Hw'.

    simpl in Hw''. 
    destruct Hw'' as [Hw'' | Hw'']; subst; try congruence.
    apply H8 in Hw''. inv Hw''.
    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0, 
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) (fdef_intro blocks5) /\
      In l0 (successors_terminator tmn0)) as J'.
      eapply successors__blockInFdefB; eauto.
    destruct J' as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    eapply getEntryBlock_inv in H1; eauto.    
Qed.

Lemma sdom_reachable : forall f l1 l2,
  reachable f l2 -> strict_domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, strict_domination, domination.
  intros.
  destruct H0 as [J1 J2].
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply J1 in H'.
  assert (In (index l1) vl) as Hin.
    destruct H' as [H' | H']; subst; try congruence.
  apply DW_extract with (x:=index l1) in H; simpl; auto.
  destruct H as [al' H].
  exists (V_extract (index l1) (index l2 :: vl)). exists al'.
  auto.
Qed.
   
Lemma dom_reachable : forall f l1 l2,
  reachable f l2 -> domination f l1 l2 -> reachable f l1.
Proof.
  intros.
  destruct (id_dec l1 l2); subst; auto.
  eapply sdom_reachable; eauto. split; auto.
Qed.

Lemma sdom_dec : forall f l1 l2,
  strict_domination f l1 l2 \/ ~ strict_domination f l1 l2.
Proof. intros. tauto. Qed. (* classic logic *)

Lemma everything_dominates_unreachable_blocks : 
  forall f l1 l2 (Hreach: ~ reachable f l2) 
  (Hentry: getEntryBlock f <> None),
  domination f l1 l2.
Proof.
  unfold reachable, domination.
  intros. 
  destruct (getEntryBlock f); try congruence.
  destruct b.
  intros.
  contradict Hreach. eauto.
Qed.  

Lemma sdom_tran1: forall (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef f)
  (Hreach: reachable f l2),
  strict_domination f l1 l2 -> domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    apply dom_acyclic in H; auto.
    contradict H; auto.

    destruct H.
    split; eauto using dom_tran.
Qed.     

Lemma sdom_tran2: forall (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef f)
  (Hreach: reachable f l3),
  domination f l1 l2 -> strict_domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    apply dom_acyclic in H0; auto.
    contradict H0; auto.

    destruct H0.
    split; eauto using dom_tran.
Qed.     

Lemma sdom_tran: forall (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef f)
  (Hreach: reachable f l2),
  strict_domination f l1 l2 -> strict_domination f l2 l3 -> 
  strict_domination f l1 l3.
Proof.
  intros. destruct H0. eapply sdom_tran1; eauto.
Qed.     

Lemma tauto_helper : forall A B:Prop,
  A -> ~ (B /\ A) -> ~ B.
Proof. tauto. Qed.

Import Classical_Pred_Type.

Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination f l1 l3)
  (Hsdom': strict_domination f l2 l3),
  strict_domination f l1 l2 \/ strict_domination f l2 l1.
Proof.
  intros.
  destruct (sdom_dec f l1 l2); auto.
  destruct (sdom_dec f l2 l1); auto.
  contradict Hsdom'. intro Hsdom'.
  unfold strict_domination in *. 
  destruct Hsdom as [Hdom Hneq1].
  destruct Hsdom' as [Hdom' Hneq2].
  unfold domination, reachable in *.
  destruct (getEntryBlock f); auto.
  destruct b. 
  destruct Hreach as [vl [al Hreach]].
  assert (Hw:=Hreach).  
  apply Hdom in Hw.
  destruct Hw as [Hin | Heq]; try congruence.
  assert (Hw:=Hreach).  
  apply Hdom' in Hw.
  destruct Hw as [Hin' | Heq]; try congruence.

  (* on Hw, we need to figuire the closest one to l3 in l1 and l2,
     suppose l1 is, then we split hw at l1, so l2 cannot be in the part 
     from l3 to l1.
  *)
  assert (Hw:=Hreach).  
  assert (vl <> V_nil) as Hnqnil.
    destruct vl; auto.
      intro J. inv J.
  apply DW_cut with (x:=index l1) (w:=index l2) in Hw; try congruence; 
    simpl; auto.
  destruct Hw as [al1 [al2 [vl1 [vl2 
    [[J1 [J2 [J3 [J4 J5]]]]|[J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
  Case "1".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l1) (index l0) vl al /\
    ~ In (index l2) vl) as J.
    clear - Hneq H0.
    apply tauto_helper in H0; auto.
    apply not_all_ex_not in H0. (* can we remove the classic lemma? *)
    destruct H0 as [vl H0].
    apply not_all_ex_not in H0.
    destruct H0 as [al H0].
    exists vl. exists al.
    tauto.
  destruct J as [vl1' [al1' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0) 
    (vl1++vl1') (al1++al1') * ~ In (index l2) (vl1++vl1'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom' in J3.
  destruct J3 as [Hin'' | Heq]; try congruence.

  Case "2".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l2) (index l0) vl al /\
    ~ In (index l1) vl) as J.
    clear - Hneq H.
    apply tauto_helper in H; auto.
    apply not_all_ex_not in H.
    destruct H as [vl H].
    apply not_all_ex_not in H.
    destruct H as [al H].
    exists vl. exists al.
    tauto.
  destruct J as [vl2' [al2' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0) 
    (vl1++vl2') (al1++al2') * ~ In (index l1) (vl1++vl2'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom in J3.
  destruct J3 as [Hin'' | Heq]; try congruence.
Qed.

Lemma adom_acyclic: forall l1 l2 ps1 cs1 tmn1 ps2 cs2 tmn2 F,
  wf_fdef F ->
  reachable F l2 ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F = true ->
  blockInFdefB (block_intro l2 ps2 cs2 tmn2) F = true ->
  In l1 (DomDS.L.bs_contents (bound_fdef F) ((dom_analyze F) !! l2)) ->
  In l2 (DomDS.L.bs_contents (bound_fdef F) ((dom_analyze F) !! l1)) ->
  l1 <> l2 ->
  False.
Proof.
  intros. 
  assert (strict_domination F l1 l2) as Hdom12.
    eapply sdom_is_sound; eauto.
  assert (strict_domination F l2 l1) as Hdom21.
    eapply sdom_is_sound; eauto.
      apply sdom_reachable in Hdom12; auto.
  apply dom_acyclic in Hdom12; auto.
  apply Hdom12. destruct Hdom21; auto.
Qed.

Lemma blockStrictDominates_trans : forall f b1 b2 b3
  (HwfF: wf_fdef f)
  (HBinF1: blockInFdefB b1 f)
  (HBinF2: blockInFdefB b2 f)
  (HBinF3: blockInFdefB b3 f)
  (H1 : blockStrictDominates f b1 b2)
  (H2 : blockStrictDominates f b2 b3),
  blockStrictDominates f b1 b3.
Proof.
  unfold blockStrictDominates.
  intros. destruct b1, b2, b3.
  remember (Maps.AMap.get l1 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (reachable_dec f l2).
    assert (strict_domination f l1 l2) as Hsdom23.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    assert (reachable f l1) as Hreach1.
      apply sdom_reachable in Hsdom23; auto.
    assert (strict_domination f l0 l1) as Hsdom12.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR1. simpl. auto.
    assert (strict_domination f l0 l2) as Hsdom13.
      apply sdom_tran with (l2:=l1); auto.
    eapply sdom_is_complete in Hsdom13; eauto.
      rewrite <- HeqR2 in Hsdom13. simpl in *. auto.

      rewrite <- HeqR2. simpl. 
      destruct bs_contents0; auto.
        intro J. inv J.
    
    eapply dom_unreachable in H; eauto. 
      rewrite <- HeqR2 in H. simpl in H.
      destruct H. apply H0.
      apply blockInFdefB_in_vertexes in HBinF1.
      unfold vertexes_fdef in HBinF1. auto.

      rewrite <- HeqR2. simpl. intro J. subst. inv H2.
Qed.

Lemma blockDominates_trans : forall f b1 b2 b3
  (HwfF: wf_fdef f)
  (HBinF1: blockInFdefB b1 f)
  (HBinF2: blockInFdefB b2 f)
  (HBinF3: blockInFdefB b3 f)
  (H1 : blockDominates f b1 b2)
  (H2 : blockDominates f b2 b3),
  blockDominates f b1 b3.
Proof.
  unfold blockDominates.
  intros. destruct b1, b2, b3.
  remember (Maps.AMap.get l1 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (l_dec l0 l2); auto.
  destruct H2 as [H2 | H2]; subst; auto.
  Case "l1 in sdom(l2)".
    left.
    assert (domination f l1 l2) as Hdom23.
      eapply dom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    destruct H1 as [H1 | H1]; subst.
    SCase "l0 in sdom(l1)".
      assert (domination f l0 l1) as Hdom12.
        eapply dom_is_sound; eauto.
          rewrite <- HeqR1. simpl. auto.
      assert (strict_domination f l0 l2) as Hsdom13.
        split; auto.
          eapply dom_tran; eauto.
      eapply sdom_is_complete in Hsdom13; eauto.
        rewrite <- HeqR2 in Hsdom13. simpl in *. auto.

        rewrite <- HeqR2. simpl. 
        destruct bs_contents0; auto.
          intro J. inv J.

    SCase "l0=l1".
      assert (strict_domination f l1 l2) as Hsdom12.
        split; auto.
      eapply sdom_is_complete in Hsdom12; eauto.
        rewrite <- HeqR2. simpl. 
        destruct bs_contents0; auto.
          intro J. inv J.

  Case "l1=l2".
    rewrite <- HeqR2 in HeqR1. inv HeqR1; auto.
Qed.

Lemma idDominates_blockStrictDominates__blockStrictDominates : 
forall f id1 id2 b1 b2 b (Huniq: wf_fdef f) 
  (HBinF: blockInFdefB b f = true),
  idDominates f id1 id2 ->
  lookupBlockViaIDFromFdef f id1 = ret b1 ->
  lookupBlockViaIDFromFdef f id2 = ret b2 ->
  blockStrictDominates f b2 b ->
  blockStrictDominates f b1 b.
Proof.
  unfold idDominates, blockStrictDominates in *. intros.  
  remember (lookupBlockViaIDFromFdef f id2) as R1.
  destruct R1; tinv H.
  remember (inscope_of_id f b0 id2) as R2.
  destruct R2; tinv H.
  unfold inscope_of_id in *.
  destruct b1. destruct b. destruct b0. destruct b2.
  remember (Maps.AMap.get l3 (dom_analyze f)) as R.
  destruct R.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R.
  destruct R. inv H1.
  symmetry in HeqR2.  
  apply fold_left__spec in HeqR2.
  destruct HeqR2 as [J1 [J2 J3]].
  apply J3 in H. clear J3.
  destruct H as [H | [b1 [l1' [J1' [J2' J3']]]]].
    assert (block_intro l1 p c t = block_intro l4 p2 c2 t2) as J'.
      clear - H H0 HeqR1 Huniq. 
      symmetry in HeqR1.
      apply lookupBlockViaIDFromFdef__blockInFdefB in HeqR1.
      eapply block_eq1 in H0; eauto using wf_fdef__uniqFdef.
      simpl. apply cmds_dominates_cmd_spec' in H; auto.
    inv J'. auto.

    assert (block_intro l1 p c t = b1) as EQ.
      apply lookupBlockViaLabelFromFdef__blockInFdefB in J2'; 
        auto using wf_fdef__uniqFdef.
      eapply block_eq1 in H0; eauto using wf_fdef__uniqFdef.
    subst.
    apply lookupBlockViaLabelFromFdef_inv in J2'; auto using wf_fdef__uniqFdef.
    destruct J2' as [Heq J2']; subst.
    assert (blockStrictDominates f (block_intro l1 p c t) 
                                   (block_intro l4 p2 c2 t2)) as Hdom.
      clear - J1' HeqR Huniq. simpl. rewrite <- HeqR. 
      apply ListSet.set_diff_elim1 in J1'; auto.
    assert (blockStrictDominates f (block_intro l4 p2 c2 t2) 
                  (block_intro l2 p0 c0 t0)) as Hdom'.
      clear - H2 HeqR0 Huniq. simpl. rewrite <- HeqR0. auto.
    assert (blockStrictDominates f (block_intro l1 p c t) 
                  (block_intro l2 p0 c0 t0)) as Hdom''.
      eapply blockStrictDominates_trans with (b2:=block_intro l4 p2 c2 t2); 
        eauto.
        eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto.
    simpl in Hdom''. rewrite <- HeqR0 in Hdom''. auto.
Qed.

Module AnotherDominators.

Definition domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  forall vl al, 
    D_walk vertexes arcs (index l2) (index entry) vl al -> 
    (In (index l1) vl \/ l1 = l2)
| _ => False
end.

Definition strict_domination (f:fdef) (l1 l2:l) : Prop :=
match getEntryBlock f with
| Some (block_intro entry _ _ _) =>
  let vertexes := vertexes_fdef f in
  let arcs := arcs_fdef f in
  forall vl al, 
    D_walk vertexes arcs (index l2) (index entry) vl al -> 
    (In (index l1) vl /\ l1 <> l2)
| _ => False
end.

Lemma sdom_is_complete: forall
  (f : fdef) (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HwfF : wf_fdef f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: strict_domination f l' l3)
  (Hnempty: DomDS.L.bs_contents _ ((dom_analyze f) !! l3) <> nil),
  In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3)).
Proof.
  intros. unfold dom_analyze in *. destruct f as [bs].
  remember (entry_dom bs) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
    destruct start; tinv Hp.
    destruct bs_contents; tinv Hp. 
    destruct bs; tinv HeqR.
    destruct b; inv HeqR.
    remember (DomDS.fixpoint (bound_blocks (block_intro l0 p c t :: bs))
                  (successors_blocks (block_intro l0 p c t :: bs))
                  (transfer (bound_blocks (block_intro l0 p c t :: bs)))
                  ((l0,
                   {|
                   DomDS.L.bs_contents := nil;
                   DomDS.L.bs_bound := bs_bound |}) :: nil)) as R.
    destruct R.
      symmetry in HeqR.
      apply DomComplete.dom_non_sdomination with (entry:=l0) in HeqR; auto.
        Focus.
        unfold DomComplete.non_sdomination_prop in HeqR.
        destruct (in_dec eq_atom_dec l'
          (DomDS.L.bs_contents
            (bound_fdef (fdef_intro (block_intro l0 p c t :: bs))) 
            t0 !! l3)); auto.
        assert (vertexes_fdef (DomComplete.f (block_intro l0 p c t :: bs))
           (index l')) as J. 
          apply blockInFdefB_in_vertexes in HBinF'; auto.
        apply HeqR with (l2:=l3) in J.
          unfold DomComplete.non_sdomination in J.
          destruct J as [vl [al [J1 J2]]].
          unfold strict_domination in Hsdom.
          simpl in Hsdom.
          apply Hsdom in J1.
          destruct J1; subst; congruence.
         
          unfold Dominators.member. 
          unfold DomComplete.dt. unfold DomComplete.bound.
          destruct (t0!!l3). simpl in *; auto.
        Unfocus.

        assert (HwfF':=HwfF). inv HwfF'.
        split. 
           remember ((DomComplete.predecessors (block_intro l0 p c t :: bs)) 
             !!! l0) as R.
           destruct R; auto.
           assert (In a (DomComplete.predecessors (block_intro l0 p c t :: bs)) 
             !!! l0) as Hin. rewrite <- HeqR0. simpl; auto.
           unfold DomComplete.predecessors in Hin.
           apply make_predecessors_correct' in Hin.
           unfold DomComplete.f in Hin.
           apply successors__blockInFdefB in Hin.
           destruct Hin as [ps0 [cs0 [tmn0 [J1 J2]]]].
           eapply getEntryBlock_inv with (l3:=a)(a:=l0) in J2; simpl; eauto.
           congruence.

        split; auto.
               exists {| DomDS.L.bs_contents := nil; DomDS.L.bs_bound := bs_bound |}.
               split; auto. simpl. apply set_eq_refl. 

      simpl in Hnempty.
      destruct (id_dec l0 l3); subst.
        rewrite AMap.gss in *. simpl in *. auto.
        rewrite AMap.gso in *; auto. rewrite AMap.gi in *; auto. 
        simpl in *. auto.

    subst. inv HBinF.
Qed.

Lemma dom_is_sound : forall
  (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : 
    In l' (l3::(DomDS.L.bs_contents _ ((dom_analyze f) !! l3)))),
  domination f l' l3.
Proof. 
  unfold domination, strict_domination.
  intros. destruct f as [bs].
  assert (Huniq : uniqBlocks bs). 
    apply wf_fdef__uniqFdef in HwfF. simpl in HwfF. auto.
  assert (HwfF':=HwfF).
  inv HwfF'. rewrite H0 in *.
  destruct block5 as [l5 ps5 cs5 t5].
  clear H4. intros vl al Hreach.
  generalize dependent ps.
  generalize dependent cs.
  generalize dependent tmn.
  remember (vertexes_fdef (fdef_intro bs)) as Vs.
  remember (arcs_fdef (fdef_intro bs)) as As.
  remember (index l3) as v0.
  remember (index l5) as v1.
  generalize dependent bs.
  generalize dependent l3.
  generalize dependent l5.
  induction Hreach; intros; subst.
    inv Heqv0.
    apply dom_entrypoint in H0.
    rewrite H0 in Hin.
    simpl in Hin. destruct Hin as [Hin | Hin]; tinv Hin; auto.

    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0, 
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) (fdef_intro bs) /\
      In l3 (successors_terminator tmn0)) as J.
      eapply successors__blockInFdefB; eauto.
    destruct J as [ps0 [cs0 [tmn0 [HBinF'' Hinsucc]]]].
    remember ((dom_analyze (fdef_intro bs)) !! a0) as R.
    destruct R as [bs_contents bs_bounds].
    destruct (id_dec l' l3); subst; auto.
    left.
    assert (In l'
      (a0 :: DomDS.L.bs_contents (bound_fdef (fdef_intro bs))
                (dom_analyze (fdef_intro bs)) !! a0)) as J.
      remember ((dom_analyze (fdef_intro bs)) !! l3) as R.
      destruct R.
      assert (incl bs_contents0 (a0 :: bs_contents)) as Hinc.
        eapply dom_successors; eauto.
      rewrite <- HeqR. simpl.
      simpl in Hin. destruct Hin; try congruence.
      apply Hinc; auto.
    eapply IHHreach in J; eauto.
    simpl.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma sdom_is_sound : forall
  (f : fdef) (l3 : l) (l' : l) ps cs tmn
  (HwfF : wf_fdef f) 
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : 
    In l' (DomDS.L.bs_contents _ ((dom_analyze f) !! l3))),
  strict_domination f l' l3.
Proof. 
  intros.
  eapply dom_is_sound with (l':=l') in HBinF; simpl; eauto.
  unfold strict_domination, domination in *.
  remember (getEntryBlock f) as R.
  destruct R; try congruence.
  destruct b.
  intros vl al Hreach.
  assert (Hw':=Hreach).
  apply DWalk_to_dpath in Hreach.
  destruct Hreach as [vl0 [al0 Hp]].
  destruct (id_dec l' l3); subst; auto.
  Case "l'=l3".
    destruct (id_dec l3 l0); subst.
    SCase "l3=l0".
      symmetry in HeqR.
      apply dom_entrypoint in HeqR.
      rewrite HeqR in Hin. inv Hin.

    SCase "l3<>l0".
      inv Hp; try congruence.
      destruct y as [a0].
      assert (exists ps0, exists cs0, exists tmn0, 
        blockInFdefB (block_intro a0 ps0 cs0 tmn0) f /\
        In l3 (successors_terminator tmn0)) as J.
        eapply successors__blockInFdefB; eauto.
      destruct J as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
      remember ((dom_analyze f) !! a0) as R.
      destruct R as [bs_contents bs_bounds].
      assert (In l3
        (a0 :: DomDS.L.bs_contents (bound_fdef f)
                  (dom_analyze f) !! a0)) as J.
        remember ((dom_analyze f) !! l3) as R.
        destruct R.
        assert (incl bs_contents0 (a0 :: bs_contents)) as Hinc.
          destruct f. 
          assert (uniqBlocks b). inv HwfF. simpl in H11. auto.
          eapply dom_successors; eauto.
        rewrite <- HeqR0. simpl.
        simpl in Hin. 
        apply Hinc; auto.
      eapply dom_is_sound in J; eauto.
      unfold domination in J.
      rewrite <- HeqR in J.
      assert (Hw:=H).
      apply D_path_isa_walk in Hw.
      apply J in Hw.
      destruct Hw as [Hw | Hw]; subst; try congruence.
      apply H4 in Hw. inv Hw; try congruence.
  Case "l'<>l3".
    apply HBinF in Hw'.
    split; auto. destruct Hw'; subst; auto. congruence.
Qed.

Lemma dom_tran: forall (f:fdef) (l1 l2 l3:l),
  domination f l1 l2 -> domination f l2 l3 -> domination f l1 l3.
Proof.
  unfold domination.
  intros.
  destruct (getEntryBlock f); tinv H.
  destruct b.
  intros vl al Hw.
  destruct (id_dec l1 l3); auto.
  left.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [Hw' | Hw']; subst.
    apply DW_extract with (x:=index l2) in Hw; simpl; auto.
    destruct Hw as [al' Hw].
    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; auto.
    destruct (id_dec l1 l2); subst; auto.
    apply V_extract_spec in Hw''; try congruence.
    simpl in Hw''. destruct Hw'' as [Hw'' | Hw'']; congruence.

    assert (Hw'':=Hw).
    apply H in Hw''.
    destruct Hw'' as [Hw'' | Hw'']; subst; congruence.
Qed.     

Lemma dom_acyclic: forall (f:fdef) (l1 l2:l) (HwfF:wf_fdef f),
  reachable f l2 ->
  strict_domination f l1 l2 -> ~ domination f l2 l1.
Proof.
  unfold reachable, strict_domination, domination. 
  intros. assert (HwfF':=HwfF). inv HwfF'.
  rewrite H1 in *. destruct block5.
  destruct H as [vl [al Hw]].
  apply DWalk_to_dpath in Hw.
  destruct Hw as [vl0 [al0 Hp]].
  assert (Hw:=Hp).
  apply D_path_isa_walk in Hw.
  assert (Hw':=Hw).
  apply H0 in Hw'.
  destruct Hw' as [J1 J2].
  intros J.
  apply DW_extract with (x:=index l1) in Hw; simpl; auto.
  destruct Hw as [al' Hw].
  assert (Hw'':=Hw).
  apply J in Hw''.
  destruct Hw'' as [Hw'' | Hw'']; subst; auto.
  apply V_extract_spec' in Hw''; try congruence.
  inv Hp. 
    inv Hw''.

    simpl in Hw''. 
    destruct Hw'' as [Hw'' | Hw'']; subst; try congruence.
    apply H9 in Hw''. inv Hw''.
    destruct y as [a0].
    assert (exists ps0, exists cs0, exists tmn0, 
      blockInFdefB (block_intro a0 ps0 cs0 tmn0) (fdef_intro blocks5) /\
      In l0 (successors_terminator tmn0)) as J'.
      eapply successors__blockInFdefB; eauto.
    destruct J' as [ps0 [cs0 [tmn0 [HBinF' Hinsucc]]]].
    eapply getEntryBlock_inv in H1; eauto.    
Qed.

Lemma sdom_reachable : forall f l1 l2,
  reachable f l2 -> strict_domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, strict_domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply H0 in H'. destruct H' as [J1 J2].
  apply DW_extract with (x:=index l1) in H; simpl; auto.
  destruct H as [al' H].
  exists (V_extract (index l1) (index l2 :: vl)). exists al'.
  auto.
Qed.
   
Lemma dom_reachable : forall f l1 l2,
  reachable f l2 -> domination f l1 l2 -> reachable f l1.
Proof.
  unfold reachable, domination.
  intros.
  destruct (getEntryBlock f); try congruence.
  destruct b.
  destruct H as [vl [al H]].
  assert (H':=H).
  apply H0 in H'.
  apply DW_extract with (x:=index l1) in H; simpl; auto.
    destruct H as [al' H].
    exists (V_extract (index l1) (index l2 :: vl)). exists al'. auto.

    destruct H' as [H' | H']; subst; auto.
Qed.

Lemma everything_dominates_unreachable_blocks : 
  forall f l1 l2 (Hreach: ~ reachable f l2) 
  (Hentry: getEntryBlock f <> None),
  domination f l1 l2.
Proof.
  unfold reachable, domination.
  intros. 
  destruct (getEntryBlock f); try congruence.
  destruct b.
  intros.
  contradict Hreach. eauto.
Qed.  

Lemma everything_sdominates_unreachable_blocks : 
  forall f l1 l2 (Hreach: ~ reachable f l2) 
  (Hentry: getEntryBlock f <> None),
  strict_domination f l1 l2.
Proof.
  unfold reachable, strict_domination.
  intros. 
  destruct (getEntryBlock f); try congruence.
  destruct b.
  intros.
  contradict Hreach. eauto.
Qed.  

Lemma sdom_dom: forall f l1 l2,
  strict_domination f l1 l2 -> domination f l1 l2. 
Proof.
  unfold strict_domination, domination.
  intros. 
  destruct (getEntryBlock f); try congruence.
  destruct b. intros. apply H in H0. destruct H0; auto.
Qed.  

Lemma dom_sdom: forall f l1 l2,
  domination f l1 l2 -> l1 <> l2 -> strict_domination f l1 l2. 
Proof.
  unfold strict_domination, domination.
  intros. 
  destruct (getEntryBlock f); try congruence.
  destruct b. intros. apply H in H1. 
  destruct H1 as [H1 | H1]; subst; auto. 
    congruence.
Qed.  

Lemma sdom_tran1: forall (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef f),
  strict_domination f l1 l2 -> domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    destruct (@reachable_dec f l3).
      apply dom_acyclic in H; auto.
        contradict H; auto.
        apply dom_reachable in H0; auto.   

      apply everything_sdominates_unreachable_blocks; auto.
        apply wf_fdef__non_entry; auto.

    apply sdom_dom in H.
    apply dom_sdom; eauto using dom_tran.
Qed.

Lemma sdom_tran2: forall (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef f),
  domination f l1 l2 -> strict_domination f l2 l3 -> strict_domination f l1 l3.
Proof.
  intros.
  destruct (id_dec l1 l3); subst.
    destruct (@reachable_dec f l3).
      apply dom_acyclic in H0; auto.
      contradict H0; auto.

      apply everything_sdominates_unreachable_blocks; auto.
        apply wf_fdef__non_entry; auto.

    apply sdom_dom in H0.
    apply dom_sdom; eauto using dom_tran.
Qed.     

Lemma sdom_tran: forall (f:fdef) (l1 l2 l3:l) (HwfF:wf_fdef f),
  strict_domination f l1 l2 -> strict_domination f l2 l3 -> 
  strict_domination f l1 l3.
Proof.
  intros. apply sdom_dom in H0. eapply sdom_tran1; eauto.
Qed.     

Import Classical_Pred_Type.

Definition strict_domination' f l1 l2 := domination f l1 l2 /\ l1 <> l2.

Lemma sdom_sdom': forall f l1 l2,
  strict_domination f l1 l2 -> reachable f l2 -> strict_domination' f l1 l2.
Proof.
  intros.
  split. apply sdom_dom; auto.
    unfold reachable, strict_domination in *. intros.
    destruct (getEntryBlock f); tinv H.
    destruct b.
    destruct H0 as [vl [al H0]]. 
    apply H in H0; auto.
Qed.

Lemma sdom_dec' : forall f l1 l2,
  strict_domination' f l1 l2 \/ ~ strict_domination' f l1 l2.
Proof. intros. tauto. Qed. (* classic logic *)

Lemma sdom_ordered' : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination' f l1 l3)
  (Hsdom': strict_domination' f l2 l3),
  strict_domination' f l1 l2 \/ strict_domination' f l2 l1.
Proof.
  intros.
  destruct (sdom_dec' f l1 l2); auto.
  destruct (sdom_dec' f l2 l1); auto.
  contradict Hsdom'. intro Hsdom'.
  unfold strict_domination' in *. 
  destruct Hsdom as [Hdom Hneq1].
  destruct Hsdom' as [Hdom' Hneq2].
  unfold domination, reachable in *.
  destruct (getEntryBlock f); auto.
  destruct b. 
  destruct Hreach as [vl [al Hreach]].
  assert (Hw:=Hreach).  
  apply Hdom in Hw.
  destruct Hw as [Hin | Heq]; try congruence.
  assert (Hw:=Hreach).  
  apply Hdom' in Hw.
  destruct Hw as [Hin' | Heq]; try congruence.

  (* on Hw, we need to figuire the closest one to l3 in l1 and l2,
     suppose l1 is, then we split hw at l1, so l2 cannot be in the part 
     from l3 to l1.
  *)
  assert (Hw:=Hreach).  
  assert (vl <> V_nil) as Hnqnil.
    destruct vl; auto.
      intro J. inv J.
  apply DW_cut with (x:=index l1) (w:=index l2) in Hw; try congruence; 
    simpl; auto.
  destruct Hw as [al1 [al2 [vl1 [vl2 
    [[J1 [J2 [J3 [J4 J5]]]]|[J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
  Case "1".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l1) (index l0) vl al /\
    ~ In (index l2) vl) as J.
    clear - Hneq H0.
    apply tauto_helper in H0; auto.
    apply not_all_ex_not in H0. (* can we remove the classic lemma? *)
    destruct H0 as [vl H0].
    apply not_all_ex_not in H0.
    destruct H0 as [al H0].
    exists vl. exists al.
    tauto.
  destruct J as [vl1' [al1' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0) 
    (vl1++vl1') (al1++al1') * ~ In (index l2) (vl1++vl1'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom' in J3.
  destruct J3 as [Hin'' | Heq]; try congruence.

  Case "2".
  assert (exists vl:V_list, exists al:A_list,
    D_walk (vertexes_fdef f) (arcs_fdef f) (index l2) (index l0) vl al /\
    ~ In (index l1) vl) as J.
    clear - Hneq H.
    apply tauto_helper in H; auto.
    apply not_all_ex_not in H.
    destruct H as [vl H].
    apply not_all_ex_not in H.
    destruct H as [al H].
    exists vl. exists al.
    tauto.
  destruct J as [vl2' [al2' [J1' J2']]].

  assert ((D_walk (vertexes_fdef f) (arcs_fdef f) (index l3) (index l0) 
    (vl1++vl2') (al1++al2') * ~ In (index l1) (vl1++vl2'))%type) as J.
    split.
      eapply DWalk_append; eauto.

      clear - J2' J5.
      intro J. apply in_app_or in J.
      simpl in *.
      destruct J as [J | J]; auto.
  destruct J as [J3 J4].
  apply Hdom in J3.
  destruct J3 as [Hin'' | Heq]; try congruence.
Qed.

Lemma sdom_ordered : forall f l1 l2 l3
  (Hneq: l1 <> l2) (Hreach: reachable f l3)
  (Hsdom: strict_domination f l1 l3)
  (Hsdom': strict_domination f l2 l3),
  strict_domination f l1 l2 \/ strict_domination f l2 l1.
Proof.
  intros.
  apply sdom_sdom' in Hsdom; auto.
  apply sdom_sdom' in Hsdom'; auto.
  assert (J:=Hsdom').
  eapply sdom_ordered' in J; eauto.
  destruct J as [[J1 J2] | [J1 J2]].
    left. apply dom_sdom; auto.
    right. apply dom_sdom; auto.
Qed.

Lemma adom_acyclic: forall l1 l2 ps1 cs1 tmn1 ps2 cs2 tmn2 F,
  wf_fdef F ->
  reachable F l2 ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F = true ->
  blockInFdefB (block_intro l2 ps2 cs2 tmn2) F = true ->
  In l1 (DomDS.L.bs_contents (bound_fdef F) ((dom_analyze F) !! l2)) ->
  In l2 (DomDS.L.bs_contents (bound_fdef F) ((dom_analyze F) !! l1)) ->
  l1 <> l2 ->
  False.
Proof.
  intros. 
  assert (strict_domination F l1 l2) as Hdom12.
    eapply sdom_is_sound; eauto.
  assert (strict_domination F l2 l1) as Hdom21.
    eapply sdom_is_sound; eauto.
  apply dom_acyclic in Hdom12; auto.
  apply Hdom12. apply sdom_dom; auto.
Qed.

Lemma blockStrictDominates_trans : forall f b1 b2 b3
  (HwfF: wf_fdef f)
  (HBinF1: blockInFdefB b1 f)
  (HBinF2: blockInFdefB b2 f)
  (HBinF3: blockInFdefB b3 f)
  (H1 : blockStrictDominates f b1 b2)
  (H2 : blockStrictDominates f b2 b3),
  blockStrictDominates f b1 b3.
Proof.
  unfold blockStrictDominates.
  intros. destruct b1, b2, b3.
  remember (Maps.AMap.get l1 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (reachable_dec f l2).
    assert (strict_domination f l1 l2) as Hsdom23.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    assert (reachable f l1) as Hreach1.
      apply sdom_reachable in Hsdom23; auto.
    assert (strict_domination f l0 l1) as Hsdom12.
      eapply sdom_is_sound; eauto.
        rewrite <- HeqR1. simpl. auto.
    assert (strict_domination f l0 l2) as Hsdom13.
      apply sdom_tran with (l2:=l1); auto.
    eapply sdom_is_complete in Hsdom13; eauto.
      rewrite <- HeqR2 in Hsdom13. simpl in *. auto.

      rewrite <- HeqR2. simpl. 
      destruct bs_contents0; auto.
        intro J. inv J.
    
    eapply dom_unreachable in H; eauto. 
      rewrite <- HeqR2 in H. simpl in H.
      destruct H. apply H0.
      apply blockInFdefB_in_vertexes in HBinF1.
      unfold vertexes_fdef in HBinF1. auto.

      rewrite <- HeqR2. simpl. intro J. subst. inv H2.
Qed.

Lemma blockDominates_trans : forall f b1 b2 b3
  (HwfF: wf_fdef f)
  (HBinF1: blockInFdefB b1 f)
  (HBinF2: blockInFdefB b2 f)
  (HBinF3: blockInFdefB b3 f)
  (H1 : blockDominates f b1 b2)
  (H2 : blockDominates f b2 b3),
  blockDominates f b1 b3.
Proof.
  unfold blockDominates.
  intros. destruct b1, b2, b3.
  remember (Maps.AMap.get l1 (dom_analyze f)) as R1.
  remember (Maps.AMap.get l2 (dom_analyze f)) as R2.
  destruct R1. destruct R2.
  destruct (l_dec l0 l2); auto.
  destruct H2 as [H2 | H2]; subst; auto.
  Case "l1 in sdom(l2)".
    left.
    assert (domination f l1 l2) as Hdom23.
      eapply dom_is_sound; eauto.
        rewrite <- HeqR2. simpl. auto.
    destruct H1 as [H1 | H1]; subst.
    SCase "l0 in sdom(l1)".
      assert (domination f l0 l1) as Hdom12.
        eapply dom_is_sound; eauto.
          rewrite <- HeqR1. simpl. auto.
      assert (strict_domination f l0 l2) as Hsdom13.
        apply dom_sdom; auto.
        eapply dom_tran; eauto.
      eapply sdom_is_complete in Hsdom13; eauto.
        rewrite <- HeqR2 in Hsdom13. simpl in *. auto.

        rewrite <- HeqR2. simpl. 
        destruct bs_contents0; auto.
          intro J. inv J.

    SCase "l0=l1".
      assert (strict_domination f l1 l2) as Hsdom12.
        apply dom_sdom; auto.
      eapply sdom_is_complete in Hsdom12; eauto.
        rewrite <- HeqR2. simpl. 
        destruct bs_contents0; auto.
          intro J. inv J.

  Case "l1=l2".
    rewrite <- HeqR2 in HeqR1. inv HeqR1; auto.
Qed.

End AnotherDominators.

Lemma wf_insn_base__non_selfref: forall f b c0 id'
  (Hreach: isReachableFromEntry f b) (HwfF:wf_fdef f),
  wf_insn_base f b (insn_cmd c0) ->
  In id' (getCmdOperands c0) ->
  id' <> getCmdLoc c0.  
Proof.
  intros. inv H.
  assert (exists n, nth_list_id n id_list = Some id') as Hnth.
    eapply getCmdOperands__nth_list_id; eauto.
  destruct Hnth as [n Hnth]. 
  eapply wf_operand_list__wf_operand in Hnth; eauto.
  inv Hnth.
  destruct H8 as [H8 | [H8 | H8]]; auto.
    contradict H8. subst.
    assert (H':=H1).
    apply insnInFdefBlockB__blockInFdefB in H'.
    apply uniqFdef__uniqBlockLocs in H'; auto using wf_fdef__uniqFdef.
    apply insnInFdefBlockB__insnInBlockB in H1.
    apply insnDominates_spec1; auto.

    contradict H8. subst.
    assert (b = block') as EQ.
      eapply insnInFdefBlockB__lookupBlockViaIDFromFdef__eq; 
        eauto using wf_fdef__uniqFdef.
    subst.
    apply insnInFdefBlockB__blockInFdefB in H1.
    apply blockStrictDominates_isnt_refl; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
