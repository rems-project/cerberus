Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vminus.
Require Import Lattice.
Require Import subst.
Import AtomSet.

Definition isubst_fdef (id1 id2:id) : fdef -> fdef := 
subst_fdef id1 (value_id id2).

Definition isubst_block (id1 id2:id) : block -> block := 
subst_block id1 (value_id id2).

Definition isubst_phi (id1 id2:id) : phinode -> phinode := 
subst_phi id1 (value_id id2).

Definition isubst_cmd (id1 id2:id) : cmd -> cmd := 
subst_cmd id1 (value_id id2).

Definition isubst_tmn (id1 id2:id) : terminator -> terminator := 
subst_tmn id1 (value_id id2).

Definition isubst_insn (id1 id2:id) : insn -> insn := 
subst_insn id1 (value_id id2).

Definition isubst_value (id1 id2:id) : value -> value := 
subst_value id1 (value_id id2).

Hint Unfold isubst_fdef isubst_block isubst_insn.

(************** Preserving wellformedness **************************************)

Definition subst_id (id1 id2 : id) (id0:id) : id :=
if id_dec id0 id1 then id2 else id0.

Fixpoint subst_list_id (id1 id2 : id) (l0:list_id) : list_id :=
match l0 with
| Nil_list_id => Nil_list_id
| Cons_list_id id0 tl => 
    Cons_list_id (subst_id id1 id2 id0) (subst_list_id id1 id2 tl)
end.

Lemma isubst_values2ids : forall id2 id1 l0 id_list0,
  values2ids (list_prj1 value l (unmake_list_value_l l0)) =
    unmake_list_id id_list0 ->
  values2ids
     (list_prj1 value l
        (unmake_list_value_l (subst_list_value_l id2 (value_id id1) l0))) =
    unmake_list_id (subst_list_id id2 id1 id_list0).
Proof.
  induction l0; simpl; intros.
    destruct id_list0; inv H; auto.

    destruct v; simpl in *; auto.
      destruct (id_dec i0 id2); subst; destruct id_list0; inv H; 
        simpl; unfold subst_id.
        rewrite <- IHl0; auto.
        destruct (id_dec i0 i0); try congruence; auto.

        destruct (id_dec i1 id2); simpl; try congruence; f_equal; auto.
Qed.

Hint Resolve isubst_values2ids : ssa_subst.

Lemma isubst_getPhiNodeOperands : forall id2 id1 p id_list0,
  getPhiNodeOperands p = unmake_list_id id_list0 ->
  getPhiNodeOperands (subst_phi id2 (value_id id1) p) =
    unmake_list_id (subst_list_id id2 id1 id_list0).
Proof.
  destruct p; simpl; intros; auto with ssa_subst.
Qed.

Lemma isubst_getCmdOperands_helper : forall id1 id2 v v0 id_list0
  (H : getValueIDs v ++ getValueIDs v0 = unmake_list_id id_list0),
  getValueIDs (v {[value_id id1 // id2]}) ++
  getValueIDs (v0 {[value_id id1 // id2]}) =
   unmake_list_id (subst_list_id id2 id1 id_list0).
Proof.
  intros.
  destruct v; simpl in *.
    destruct id_list0; inv H.
    destruct v0; simpl in *.
      destruct id_list0; inv H2.
      destruct id_list0; inv H1; simpl. unfold subst_id.
      destruct (id_dec i1 id2); destruct (id_dec i2 id2); subst; auto. 
  
      destruct id_list0; inv H2. unfold subst_id.
      destruct (id_dec i1 id2); subst; auto.
    destruct v0; simpl in *.
      destruct id_list0; inv H.
      destruct id_list0; inv H2; simpl. unfold subst_id.
      destruct (id_dec i1 id2); subst; auto. 
  
      destruct id_list0; inv H; auto.
Qed.

Hint Resolve isubst_getCmdOperands_helper: ssa_subst.

Lemma isubst_getCmdOperands : forall id1 id2 c id_list0,
 getCmdOperands c = unmake_list_id id_list0 ->
 getCmdOperands (subst_cmd id2 (value_id id1) c) =
   unmake_list_id (subst_list_id id2 id1 id_list0).
Proof.
  destruct c; simpl; intros; auto with ssa_subst.
Qed.

Lemma isubst_getTerminatorOperands : forall id1 id2 t id_list0,
 getTerminatorOperands t = unmake_list_id id_list0 ->
 getTerminatorOperands (subst_tmn id2 (value_id id1) t) =
   unmake_list_id (subst_list_id id2 id1 id_list0).
Proof.
  destruct t; simpl; intros; try solve [destruct id_list0; inv H; simpl; auto].
    destruct v; simpl in *.
      destruct id_list0; inv H.
      destruct id_list0; inv H2; simpl. unfold subst_id.
      destruct (id_dec i2 id2); subst; auto. 
  
      destruct id_list0; inv H; auto.
    destruct v; simpl in *.
      destruct id_list0; inv H.
      destruct id_list0; inv H2; simpl. unfold subst_id.
      destruct (id_dec i2 id2); subst; auto. 
  
      destruct id_list0; inv H; auto.
Qed.

Hint Resolve isubst_getCmdOperands isubst_getPhiNodeOperands
  isubst_getTerminatorOperands: ssa_subst.

Lemma isubst_getInsnOperands : forall id1 id2 instr id_list0,
  getInsnOperands instr = unmake_list_id id_list0 ->
  getInsnOperands (isubst_insn id2 id1 instr) =
    unmake_list_id (subst_list_id id2 id1 id_list0).
Proof.
  destruct instr; simpl; intros; auto with ssa_subst.
Qed.

Hint Resolve isubst_getInsnOperands: ssa_subst.

Lemma isubst_In_values2ids : forall id1 id2 i0 l0 
  (H2 : ListSet.set_In i0 
    (values2ids (list_prj1 value l (unmake_list_value_l l0)))),
  ListSet.set_In (subst_id id2 id1 i0)
    (values2ids
      (list_prj1 value l
        (unmake_list_value_l (subst_list_value_l id2 (value_id id1) l0)))).
Proof.
  induction l0; simpl; intros; auto.
    destruct v; simpl in *; auto. 
    unfold subst_id.
    destruct H2 as [H2 | H2]; subst. 
      destruct (id_dec i0 id2); try congruence; simpl; auto.
      destruct (id_dec i1 id2); subst; simpl; auto.
Qed.     

Hint Resolve isubst_In_values2ids : ssa_subst.

Lemma isubst_In_getPhiNodeOperands : forall id1 id2 i0 p
  (H2 : ListSet.set_In i0 (getPhiNodeOperands p)),
  ListSet.set_In (subst_id id2 id1 i0) 
    (getPhiNodeOperands (subst_phi id2 (value_id id1) p)).
Proof.
  destruct p; simpl; intros; auto with ssa_subst.
Qed.

Lemma isubst_In_getCmdOperands_helper : forall id1 id2 v v0 i3
  (H2 : ListSet.set_In i3 (getValueIDs v ++ getValueIDs v0)),
  ListSet.set_In (subst_id id2 id1 i3) 
    (getValueIDs (v {[value_id id1 // id2]}) ++
     getValueIDs (v0 {[value_id id1 // id2]})).
Proof.
  intros.
  destruct v; simpl in *; unfold subst_id.
    destruct H2 as [H2 | H2]; subst.
      destruct v0; simpl in *; 
        destruct (id_dec i3 id2); try congruence; simpl; auto.
  
      destruct v0; simpl in *; try solve [inversion H2].
        destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
        destruct (id_dec i3 id2); destruct (id_dec i0 id2); simpl; auto.

    destruct v0; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      destruct (id_dec i3 id2); try congruence; simpl; auto.
Qed.

Hint Resolve isubst_In_getCmdOperands_helper: ssa_subst.

Lemma isubst_In_getCmdOperands : forall id1 id2 c i3
  (H2 : ListSet.set_In i3 (getCmdOperands c)),
  ListSet.set_In (subst_id id2 id1 i3) 
    (getCmdOperands (subst_cmd id2 (value_id id1) c)).
Proof.
  destruct c; simpl; intros; auto with ssa_subst.
Qed.

Lemma isubst_In_getTerminatorOperands : forall id1 id2 t i3
  (H2 : ListSet.set_In i3 (getTerminatorOperands t)),
  ListSet.set_In (subst_id id2 id1 i3) 
    (getTerminatorOperands(subst_tmn id2 (value_id id1) t)).
Proof.
  destruct t; simpl; intros; auto.
    destruct v; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      unfold subst_id.
      destruct (id_dec i3 id2); try congruence; simpl; auto.
    destruct v; simpl in *; try solve [inversion H2].
      destruct H2 as [H2 | H2]; subst; try solve [inversion H2].
      unfold subst_id.
      destruct (id_dec i3 id2); try congruence; simpl; auto.
Qed.

Hint Resolve isubst_In_getCmdOperands isubst_In_getPhiNodeOperands
  isubst_In_getTerminatorOperands: ssa_subst.

Lemma isubst_In_getInsnOperands : forall i0 id1 id2 instr 
  (H2 : ListSet.set_In i0 (getInsnOperands instr)),
  ListSet.set_In (subst_id id2 id1 i0)
     (getInsnOperands (isubst_insn id2 id1 instr)).
Proof.
  destruct instr; simpl; auto with ssa_subst.
Qed.

Hint Resolve isubst_In_getInsnOperands: ssa_subst.

Lemma isubst_wf_operand : forall instr id1 id2 f b i0
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2)
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f)
  (H1 : wf_operand f b instr i0) (Hdom : idDominates f id1 id2),
   wf_operand (isubst_fdef id2 id1 f) (isubst_block id2 id1 b)
     (isubst_insn id2 id1 instr) (subst_id id2 id1 i0).
Proof.
  intros.
  inv H1.
  apply isubst_In_getInsnOperands with (id1:=id1)(id2:=id2) in H2; auto.
  rewrite subst_isPhiNode with (id':=id2)(v':=value_id id1) in H4; auto.
  unfold subst_id in *.
  destruct (id_dec i0 id2); subst.
    assert (J:=Hdom).
    apply idDominates__lookupBlockViaIDFromFdef in J; auto.
    destruct J as [b1 J].
    eapply wf_operand_intro; try solve 
      [eauto with ssa_subst | autounfold; eauto with ssa_subst].   

      autounfold.
      rewrite <- subst_insnDominates; eauto 
        using insnInFdefBlockB__insnInBlockB.
      rewrite <- subst_blockStrictDominates.
      rewrite <- subst_isReachableFromEntry; auto.
      destruct H5 as [H5 | [H5 | H5]]; auto.
       apply insnInFdefBlockB__blockInFdefB in H.
       eapply idDominates_insnDominates__insnOrBlockStrictDominates in H5; 
         eauto.
       destruct H5 as [H5 | H5]; auto.

       apply insnInFdefBlockB__blockInFdefB in H.
       eapply idDominates_blockStrictDominates__blockStrictDominates in H5; 
         eauto.

    eapply wf_operand_intro; try solve 
      [eauto with ssa_subst | autounfold; eauto with ssa_subst].   
      autounfold.
      rewrite <- subst_insnDominates; eauto using insnInFdefBlockB__insnInBlockB.
      rewrite <- subst_blockStrictDominates.
      rewrite <- subst_isReachableFromEntry; auto.
Qed.

Hint Resolve isubst_wf_operand: ssa_subst.

Hint Constructors wf_operand_list.

Lemma isubst_wf_operand_list : forall instr id1 id2 f b id_list0
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2)
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f)
  (H2 : wf_operand_list
         (make_list_fdef_block_insn_id
            (map_list_id (fun id_ : id => (f, b, instr, id_)) id_list0)))
  (Hdom : idDominates f id1 id2),
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

Hint Resolve isubst_wf_operand_list: ssa_subst.

Lemma isubst_wf_insn_base : forall f b id1 id2 instr 
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2)
  (Huniq : NoDup (getBlockLocs b)) (HuniqF : wf_fdef f)
  (HwfI: wf_insn_base f b instr) (Hdom : idDominates f id1 id2),
  wf_insn_base (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) 
    (isubst_insn id2 id1 instr).
Proof.
  intros.
  inv HwfI.
  eapply subst_insnInFdefBlockB in H; eauto.
  eapply wf_insn_base_intro; eauto with ssa_subst.
Qed.

Hint Constructors wf_insn wf_value.

Lemma isubst_wf_value : forall f id1 id2 v (Hwfv: wf_value f v)
  (Hdom : idDominates f id1 id2) (Huniq:uniqFdef f),
  wf_value (isubst_fdef id2 id1 f) (isubst_value id2 id1 v).
Proof.
  intros.
  inv Hwfv; try constructor.
    simpl. 
    autounfold.
    destruct (id_dec id5 id2); subst; 
      constructor; rewrite <- subst_lookupIDFromFdef; auto.    
      eapply idDominates__lookupIDFromFdef; eauto.
Qed.

Hint Constructors wf_phi_operands.

Lemma isubst_wf_phi_operands : forall f b id1 id2 id' vls (HwfF: wf_fdef f)
  (Hwf_pnops: wf_phi_operands f b id' vls) (Hdom : idDominates f id1 id2),
  wf_phi_operands (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) id'
    (subst_list_value_l id2 (value_id id1) vls).
Proof.
  intros.
  induction Hwf_pnops; simpl; auto.
    assert (H0':=H0).
    apply subst_lookupBlockViaLabelFromFdef with (id':=id2)(v':=value_id id1) 
      in H0; auto.
    rewrite subst_isReachableFromEntry with (id':=id2)(v':=value_id id1) 
      in H1; auto.
    destruct (id_dec vid1 id2); subst.
      assert (J:=Hdom).
      apply idDominates__lookupBlockViaIDFromFdef in J; auto.
      destruct J as [vb1 J].
      eapply wf_phi_operands_cons_vid; eauto.
        eapply subst_lookupBlockViaIDFromFdef in J; eauto.
        autounfold.
        destruct H1 as [H1 | H1]; auto.
          rewrite <- subst_blockDominates; auto.
            left.
            apply blockDominates_trans with (b2:=vb); 
              eauto using lookupBlockViaIDFromFdef__blockInFdefB,
                          lookupBlockViaLabelFromFdef__blockInFdefB.
            eapply idDominates__blockDominates; eauto.
      
      eapply wf_phi_operands_cons_vid; eauto.
        eapply subst_lookupBlockViaIDFromFdef in H; eauto.
        autounfold.
        destruct H1 as [H1 | H1]; auto.
          rewrite <- subst_blockDominates; auto.
Qed.
     
Hint Resolve isubst_wf_phi_operands: ssa_subst.

Lemma isubst_wf_phinode : forall f b id1 id2 PN (HwfF: wf_fdef f) 
  (HwfPN: wf_phinode f b PN) (Hdom : idDominates f id1 id2),
  wf_phinode (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) 
    (isubst_phi id2 id1 PN).
Proof.
  intros. destruct PN as [id' vls].
  unfold wf_phinode in *. simpl.
  destruct HwfPN as [Hwf_pnops Hcl].
  split; auto with ssa_subst.
    autounfold. auto with ssa_subst.
Qed.

Hint Resolve isubst_wf_value : ssa_subst.

Lemma isubst_wf_value_list : forall
  (id1 id2 : id)
  (fdef5 : fdef) (Huniq: uniqFdef fdef5)
  (block5 : block)
  (value_l_list : list_value_l)
  (Hdom : idDominates fdef5 id1 id2)
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
    apply isubst_wf_value; auto.  
Qed.

Hint Resolve isubst_wf_value_list: ssa_subst.

Lemma isubst_wf_insn : forall f b id1 id2 instr (HwfF: wf_fdef f) 
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2)
  (HwfI: wf_insn f b instr)
  (Huniq : NoDup (getBlockLocs b)) (Hdom : idDominates f id1 id2),
  wf_insn (isubst_fdef id2 id1 f) (isubst_block id2 id1 b) 
    (isubst_insn id2 id1 instr).
Proof.
  intros.

  Ltac DONE := 
  eauto with ssa_subst; try match goal with
  | H : wf_insn_base _ _ _ |- wf_insn_base _ _ _ => 
    eapply isubst_wf_insn_base in H; eauto
  | H : wf_value _ ?v |- wf_value _ (?v {[ _ // _ ]}) => 
    eapply isubst_wf_value  in H; eauto
  | H : lookupBlockViaLabelFromFdef _ ?l = Some _ |- 
        lookupBlockViaLabelFromFdef _ ?l = Some _  =>
    eapply subst_lookupBlockViaLabelFromFdef in H; eauto
  | H : insnInFdefBlockB _ _ _ = _ |- insnInFdefBlockB _ _ _ = _ =>
    eapply subst_insnInFdefBlockB in H; eauto
  | H : wf_phinode _ _ _ |- wf_phinode _ _ _ =>
    eapply isubst_wf_phinode in H; eauto
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

Hint Resolve isubst_wf_insn : ssa_subst.
Hint Constructors wf_phinodes.

Lemma isubst_wf_phinodes : forall f b id1 id2 PNs (HwfF: wf_fdef f)
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2)
  (HwfPNs: wf_phinodes f b PNs)
  (Huniq : NoDup (getBlockLocs b)) (Hdom : idDominates f id1 id2),
  wf_phinodes (isubst_fdef id2 id1 f) (isubst_block id2 id1 b)
    (List.map (isubst_phi id2 id1) PNs).
Proof.
  intros. 
  induction HwfPNs; simpl; auto.
    eapply isubst_wf_insn in H; eauto.
Qed.

Hint Constructors wf_cmds.

Lemma isubst_wf_cmds : forall f b id1 id2 Cs (HwfF: wf_fdef f)
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2)
  (HwfCs: wf_cmds f b Cs)
  (Huniq : NoDup (getBlockLocs b)) (Hdom : idDominates f id1 id2),
  wf_cmds (isubst_fdef id2 id1 f) 
          (isubst_block id2 id1 b)
          (List.map (isubst_cmd id2 id1) Cs).
Proof.
  intros. 
  induction HwfCs; simpl; auto.
    eapply isubst_wf_insn in H; eauto.
Qed.

Lemma isubst_wf_block : forall f b id1 id2 (HwfF: wf_fdef f)
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2)
  (HwfB : wf_block f b)
  (Huniq : NoDup (getBlockLocs b)) (Hdom : idDominates f id1 id2),
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
     eapply isubst_wf_phinodes in HwfPNs; eauto;
     eapply isubst_wf_cmds in HwfCs; eauto;
     eapply isubst_wf_insn in Hwftmn; eauto
  end.
  apply wf_block_intro; eauto.
Qed.

Hint Resolve isubst_wf_block : ssa_subst.

Hint Constructors wf_blocks.

Lemma isubst_wf_blocks : forall f bs id1 id2 (HwfF: wf_fdef f)
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2)
  (HwfBs : wf_blocks f bs)
  (Huniq : uniqBlocks bs) (Hdom : idDominates f id1 id2),
  wf_blocks (isubst_fdef id2 id1 f) (List.map (isubst_block id2 id1) bs).
Proof.
  intros.
  induction HwfBs; simpl; auto.
    simpl_env in Huniq. apply uniqBlocks_inv in Huniq. inv Huniq.
    inv H0. simpl in *. simpl_env in H3.
    apply wf_blocks_cons; eauto with ssa_subst.
Qed.

Hint Resolve isubst_wf_blocks : ssa_subst.

Lemma isubst_wf_fdef : forall f id1 id2 (HwfF: wf_fdef f)
  (G : exists c2, lookupInsnViaIDFromFdef f id2 = ret insn_cmd c2),
  idDominates f id1 id2 ->
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
     eapply isubst_wf_blocks in HwfBs; eauto;
     eapply subst_uniqFdef in HuniqF; eauto
  end.
  eapply wf_fdef_intro; eauto.
Qed.

(************** Bisimulation for variable substituion **************************)

Definition gvnCmd (c c' : cmd) : Prop :=
match c, c' with
| insn_bop _ bop0 v1 v2, insn_bop _ bop0' v1' v2' =>
  bop0 = bop0' /\ v1 = v1' /\ v2 = v2'
| insn_icmp _ cnd0 v1 v2, insn_icmp _ cnd0' v1' v2' =>
  cnd0 = cnd0' /\ v1 = v1' /\ v2 = v2'
| _, _ => False
end.

Definition gvn_in_fdef (c1:cmd) (id2:id) (f:fdef) : Prop :=
idDominates f (getCmdLoc c1) id2 /\
lookupInsnViaIDFromFdef f (getCmdLoc c1) = Some (insn_cmd c1) /\
match lookupInsnViaIDFromFdef f id2 with
| Some (insn_cmd c2) => gvnCmd c1 c2
| _ => False
end.

Export Opsem.

Hint Resolve wf_fdef__uniqFdef.

Export OpsemProps.
Require Import Maps.

Lemma gvn_in_fdef__wf_insn_base : forall F c1 id2,
  wf_fdef F ->
  gvn_in_fdef c1 id2 F ->
  exists b1, wf_insn_base F b1 (insn_cmd c1).
Proof.
  intros F c1 id2 HwfF Hgvn. 
  destruct Hgvn as [J1 [J2 J3]].
  assert (Hlkb := J1).
  apply idDominates__lookupBlockViaIDFromFdef in Hlkb; auto.
  destruct Hlkb as [b1 Hlkb].
  assert (J:=Hlkb).
  apply lookupBlockViaIDFromFdef__blockInFdefB in J.
  destruct b1.
  apply wf_fdef__wf_cmd with (c:=c1) in J; auto.
    apply wf_insn__wf_insn_base in J; eauto.
      intro H. inv H.

    assert (J':=Hlkb).
    eapply lookupInsnViaIDFromFdef_lookupBlockViaIDFromFdef_In in J'; eauto.
Qed.

Lemma gvnCmd__eval_rhs : forall lc c1 c2,
  gvnCmd c1 c2 -> OpsemDom.eval_rhs lc c1 = OpsemDom.eval_rhs lc c2.
Proof.
  intros lc c1 c2 Hgvn.
  destruct c1; destruct c2; tinv Hgvn;
    destruct Hgvn as [Heq1 [Heq2 Heq3]]; subst; auto.
Qed.

Lemma gvn_spec2 : forall f (t : list atom) (l1 : l) (ps1 : phinodes)
  (cs1 cs: cmds) (tmn1 : terminator) (c1 c: cmd) (id2 : id) (HwfF: wf_fdef f)
  (HeqR: inscope_of_cmd f (block_intro l1 ps1 (cs1++c::cs) tmn1) c =
          ret t) 
  (Hreach: isReachableFromEntry f (block_intro l1 ps1 (cs1++c::cs) tmn1))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1++c::cs) tmn1) f = true)
  (Hgvn : gvn_in_fdef c1 id2 f)
  (Hid2InScope : In id2 t),
  In (getCmdLoc c1) t.
Proof.
  intros.
  destruct Hgvn as [J1 [J2 J3]].
  remember (lookupInsnViaIDFromFdef f id2) as R.
  destruct R as [[]|]; tinv J3.
  unfold inscope_of_cmd, inscope_of_id in HeqR.
  unfold idDominates in J1.
  remember (lookupBlockViaIDFromFdef f id2) as R.
  destruct R; tinv J1.
  remember (inscope_of_id f b id2) as R.
  destruct R; tinv J1.
  unfold inscope_of_id in HeqR2.  
  destruct b.
  remember ((dom_analyze f) !! l1) as R1.
  remember ((dom_analyze f) !! l2) as R2.
  destruct R1, R2. 
  assert (HeqR':=HeqR).
  apply fold_left__spec in HeqR.
  symmetry in HeqR2.
  assert (HeqR2':=HeqR2).
  apply fold_left__spec in HeqR2.
  destruct HeqR as [J4 [J5 J6]].
  destruct HeqR2 as [J7 [J8 J9]].
  apply J6 in Hid2InScope. 
  apply J9 in J1.
  destruct J1 as [J1 | [b1 [l1' [J10 [J11 J11']]]]].
  Case "1".
    destruct Hid2InScope as [J12 | [b2 [l2' [J13 [J14 J15]]]]].
    SCase "2.1".
      clear - HeqR1 HbInF J1 HwfF HeqR' J12 HeqR0.
      assert (block_intro l2 p c2 t0 = 
              block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) as EQ.
        eapply block_eq1 with (id0:=id2); eauto.
          simpl. eapply cmds_dominates_cmd_spec'; eauto.
      inv EQ.
      apply fold_left__init in HeqR'.
      apply HeqR'; auto.
        eapply cmds_dominates_cmd_trans; eauto.
          apply cmds_dominates_cmd_spec' in J12.
          eapply lookupCmdViaIDFromFdef_spec in HbInF; eauto.
          apply in_getCmdsIDs__in_getCmdsLocs; auto.

          apply uniqFdef__uniqBlockLocs in HbInF; auto.
          simpl in HbInF. 
          rewrite_env ((getPhiNodesIDs ps1 ++
             getCmdsLocs (cs1 ++ c :: cs)) ++ getTerminatorID tmn1 :: nil) 
          in HbInF.
          apply NoDup_inv in HbInF. destruct HbInF; auto.
     
    SCase "2.2".
      assert (block_intro l2 p c2 t0 = b2) as EQ.
        clear - HwfF HeqR1 J14 J15.
        apply lookupBlockViaLabelFromFdef__blockInFdefB in J14; auto.
        eapply block_eq1 with (id0:=id2); eauto.
      subst.
      assert (In (getCmdLoc c1) (getBlockIDs (block_intro l2 p c2 t0))) as Hin.
        clear - J1. simpl. eapply cmds_dominates_cmd_spec'; eauto.
      apply fold_left__intro with (l2:=l2')(B:=block_intro l2 p c2 t0) in HeqR';
        auto.
       
  Case "2".
    destruct Hid2InScope as [J12 | [b2 [l2' [J13 [J14 J15]]]]].
    SCase "2.1".
      clear - HeqR1 HbInF HwfF HeqR' J12 J10 J11 J11' HeqR3 HeqR4.   
      assert (block_intro l2 p c2 t0 = 
              block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) as EQ.
        eapply block_eq1 with (id0:=id2); eauto.
          simpl. eapply cmds_dominates_cmd_spec'; eauto.
      inv EQ.
      rewrite <- HeqR3 in HeqR4. inv HeqR4.
      apply fold_left__intro with (l2:=l1')(B:=b1) in HeqR'; auto.
  
    SCase "2.2".
      assert (block_intro l2 p c2 t0 = b2) as EQ.
        clear - HwfF HeqR1 J14 J15.
        apply lookupBlockViaLabelFromFdef__blockInFdefB in J14; auto.
        eapply block_eq1 with (id0:=id2); eauto.
      subst.
      apply lookupBlockViaLabelFromFdef_inv in J14; auto.
      destruct J14 as [Heq J14]; subst.
      destruct b1.
      apply lookupBlockViaLabelFromFdef_inv in J11; auto.
      destruct J11 as [Heq J11]; subst.

      assert (blockStrictDominates f (block_intro l3 p0 c3 t1) 
                                     (block_intro l2 p c2 t0)) as Hdom.
        clear - J10 HeqR4 HwfF. simpl. rewrite <- HeqR4. 
        apply ListSet.set_diff_elim1 in J10; auto.
      assert (blockStrictDominates f (block_intro l2 p c2 t0) 
                    (block_intro l1 ps1 (cs1 ++ c :: cs) tmn1)) as Hdom'.
        clear - J13 HeqR3 HwfF. simpl. rewrite <- HeqR3. 
        apply ListSet.set_diff_elim1 in J13; auto.
      assert (blockStrictDominates f (block_intro l3 p0 c3 t1) 
                    (block_intro l1 ps1 (cs1 ++ c :: cs) tmn1)) as Hdom''.
        eapply blockStrictDominates_trans; eauto.
      destruct (l_dec l3 l1); subst.
        assert (block_intro l1 p0 c3 t1 = 
                block_intro l1 ps1 (cs1 ++ c :: cs) tmn1) as EQ.
          clear - HbInF J11 HwfF. 
          eapply blockInFdefB_uniq in HbInF; eauto.
          destruct HbInF as [Heq1 [Heq2 Heq3]]; subst. auto.
        inv EQ.
        apply blockStrictDominates_isnt_refl in Hreach; auto.
          contradict Hdom''; auto.

        simpl in Hdom''. rewrite <- HeqR3 in Hdom''.
        apply fold_left__intro with (l2:=l3)(B:=block_intro l3 p0 c3 t1) 
          in HeqR'; auto.
          apply ListSet.set_diff_intro; auto.
             intro J. simpl in J. destruct J; auto.
          clear - J11 HwfF. 
          eapply blockInFdefB_lookupBlockViaLabelFromFdef; eauto.
Qed.

Lemma gvn_spec1 : forall f (t : list atom) (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator) (c1 : cmd) (id2 : id) (HwfF: wf_fdef f)
  (HeqR: inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 =
          ret t) (Hreach: isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (Hgvn : gvn_in_fdef c1 id2 f)
  (Hid2InScope : In id2 t),
  In (getCmdLoc c1) t.
Proof.
  intros.
  destruct Hgvn as [J1 [J2 J3]].
  remember (lookupInsnViaIDFromFdef f id2) as R.
  destruct R as [[]|]; tinv J3.
  unfold inscope_of_tmn in HeqR.
  unfold idDominates in J1.
  remember (lookupBlockViaIDFromFdef f id2) as R.
  destruct R; tinv J1.
  remember (inscope_of_id f b id2) as R.
  destruct R; tinv J1.
  unfold inscope_of_id in HeqR2.  
  destruct b.
  remember ((dom_analyze f) !! l1) as R1.
  remember ((dom_analyze f) !! l2) as R2.
  destruct R1, R2. 
  assert (HeqR':=HeqR).
  apply fold_left__spec in HeqR.
  symmetry in HeqR2.
  assert (HeqR2':=HeqR2).
  apply fold_left__spec in HeqR2.
  destruct HeqR as [J4 [J5 J6]].
  destruct HeqR2 as [J7 [J8 J9]].
  apply J6 in Hid2InScope. 
  apply J9 in J1.
  destruct J1 as [J1 | [b1 [l1' [J10 [J11 J11']]]]].
  Case "1".
    destruct Hid2InScope as [J12 | [b2 [l2' [J13 [J14 J15]]]]].
    SCase "2.1".
      clear - HeqR1 HbInF J1 HwfF HeqR' J12.   
      assert (block_intro l2 p c0 t0 = block_intro l1 ps1 cs1 tmn1) as EQ.
        eapply block_eq1 with (id0:=id2); eauto.
      inv EQ.
      apply fold_left__init in HeqR'.
      apply HeqR'; auto.
        eapply cmds_dominates_cmd_spec'; eauto.
     
    SCase "2.2".
      assert (block_intro l2 p c0 t0 = b2) as EQ.
        clear - HwfF HeqR1 J14 J15.
        apply lookupBlockViaLabelFromFdef__blockInFdefB in J14; auto.
        eapply block_eq1 with (id0:=id2); eauto.
      subst.
      assert (In (getCmdLoc c1) (getBlockIDs (block_intro l2 p c0 t0))) as Hin.
        clear - J1. simpl. eapply cmds_dominates_cmd_spec'; eauto.
      apply fold_left__intro with (l2:=l2')(B:=block_intro l2 p c0 t0) in HeqR';
        auto.
       
  Case "2".
    destruct Hid2InScope as [J12 | [b2 [l2' [J13 [J14 J15]]]]].
    SCase "2.1".
      clear - HeqR1 HbInF HwfF HeqR' J12 J10 J11 J11' HeqR3 HeqR4.   
      assert (block_intro l2 p c0 t0 = block_intro l1 ps1 cs1 tmn1) as EQ.
        eapply block_eq1 with (id0:=id2); eauto.
      inv EQ.
      rewrite <- HeqR3 in HeqR4. inv HeqR4.
      apply fold_left__intro with (l2:=l1')(B:=b1) in HeqR'; auto.
  
    SCase "2.2".
      assert (block_intro l2 p c0 t0 = b2) as EQ.
        clear - HwfF HeqR1 J14 J15. 
        apply lookupBlockViaLabelFromFdef__blockInFdefB in J14; auto.
        eapply block_eq1 with (id0:=id2); eauto.
      subst.
      apply lookupBlockViaLabelFromFdef_inv in J14; auto.
      destruct J14 as [Heq J14]; subst.
      destruct b1.
      apply lookupBlockViaLabelFromFdef_inv in J11; auto.
      destruct J11 as [Heq J11]; subst.
      assert (blockStrictDominates f (block_intro l3 p0 c2 t1) 
                                     (block_intro l2 p c0 t0)) as Hdom.
        clear - J10 HeqR4 HwfF. simpl. rewrite <- HeqR4. 
        apply ListSet.set_diff_elim1 in J10; auto.
      assert (blockStrictDominates f (block_intro l2 p c0 t0) 
                               (block_intro l1 ps1 cs1 tmn1)) as Hdom'.
        clear - J13 HeqR3 HwfF. simpl. rewrite <- HeqR3. 
        apply ListSet.set_diff_elim1 in J13; auto.
      assert (blockStrictDominates f (block_intro l3 p0 c2 t1) 
                                     (block_intro l1 ps1 cs1 tmn1)) as Hdom''.
        eapply blockStrictDominates_trans; eauto.
      destruct (l_dec l3 l1); subst.
        assert (block_intro l1 p0 c2 t1 = block_intro l1 ps1 cs1 tmn1) as EQ.
          clear - HbInF J11 HwfF. 
          eapply blockInFdefB_uniq in HbInF; eauto.
          destruct HbInF as [Heq1 [Heq2 Heq3]]; subst. auto.
        inv EQ.
        apply blockStrictDominates_isnt_refl in Hreach; auto.

        simpl in Hdom''. rewrite <- HeqR3 in Hdom''.
        apply fold_left__intro with (l2:=l3)(B:=block_intro l3 p0 c2 t1) 
          in HeqR'; auto.
          apply ListSet.set_diff_intro; auto.
             intro J. simpl in J. destruct J; auto.
          clear - J11 HwfF. 
          eapply blockInFdefB_lookupBlockViaLabelFromFdef; eauto.
Qed.

Lemma gvn_sim : forall f (lc : GVMap) (c1 : cmd) (id2 : id)
  (Hgvn : gvn_in_fdef c1 id2 f)
  (g1 : GenericValue) (g : GenericValue)
  (HeqR1 : OpsemDom.wf_GVs f lc (getCmdLoc c1) g)
  (HeqR4 : OpsemDom.wf_GVs f lc id2 g1),
  g1 = g.
Proof.
  intros.
  destruct Hgvn as [J1 [J2 J4]].
  remember (lookupInsnViaIDFromFdef f id2) as R.
  destruct R as [[]|]; tinv J4.
  symmetry in HeqR.
  apply HeqR4 in HeqR. destruct HeqR as [HeqR _].
  apply HeqR1 in J2.
  apply gvnCmd__eval_rhs with (lc:=lc) in J4.
  rewrite J4 in J2. destruct J2 as [J2 _].
  rewrite J2 in HeqR.
  inv HeqR. auto. 
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
  (l0 : list atom) c1 id2
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (Hinscope : OpsemDom.wf_defs f lc l0) (Hgvn : gvn_in_fdef c1 id2 f)
  (v : value)
  (Hvincs : valueInTmnOperands v tmn) gv gv'
  (Hget' : getOperandValue (v {[ value_id (getCmdLoc c1) // id2 ]}) lc 
    = Some gv')
  (Hget : getOperandValue v lc = Some gv),
  gv = gv'.
Proof.
  intros.
  destruct v as [vid | vc]; simpl in *; try congruence.
  destruct (id_dec vid id2); simpl in *; subst; try congruence.
    assert (HwfInstr:=HbInF).
    eapply wf_fdef__wf_tmn in HwfInstr; eauto.
    assert (OpsemDom.wf_GVs f lc id2 gv /\ In id2 l0) as Hwfg.
      eapply OpsemDom.state_tmn_typing; eauto. 
        apply valueInTmnOperands__InOps; auto.
    destruct Hwfg as [Hwfg Hin].
    assert (OpsemDom.wf_GVs f lc (getCmdLoc c1) gv') as Hwfg'.
      apply Hinscope; auto.
      eapply gvn_spec1; eauto.
    eapply gvn_sim; eauto.
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
  (c : cmd) c1 id2
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : OpsemDom.wf_defs f lc l0) (Hgvn : gvn_in_fdef c1 id2 f)
  (v : value)
  (Hvincs : valueInCmdOperands v c) gv gv'
  (Hget' : getOperandValue (v {[ value_id (getCmdLoc c1) // id2 ]} ) lc 
    = Some gv')
  (Hget : getOperandValue v lc = Some gv),
  gv = gv'.
Proof.
  intros.
  destruct v as [vid | vc]; simpl in Hget', Hget; try congruence.
  destruct (id_dec vid id2); simpl in Hget', Hget; subst; try congruence.
    assert (OpsemDom.wf_GVs f lc id2 gv /\ In id2 l0) as Hwfg.
      eapply OpsemDom.state_cmd_typing; eauto. 
        eapply wf_fdef__uniq_block; eauto.
        eapply wf_fdef__wf_cmd; eauto using In_middle.
        apply valueInCmdOperands__InOps; auto.
    destruct Hwfg as [Hwfg Hin].
    assert (OpsemDom.wf_GVs f lc (getCmdLoc c1) gv') as Hwfg'.
      apply Hinscope; auto.
      eapply gvn_spec2; eauto.
    eapply gvn_sim; eauto.
Qed.

Lemma getValueViaLabelFromValuels_getOperandValue_sim : forall
  (f : fdef) (l0 : l) (lc : GVMap) (t : list atom) (l1 : l) (ps1 : phinodes)
  (cs1 : cmds) (tmn1 : terminator) c1 id2
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : OpsemDom.wf_defs f lc t)
  (HwfF : wf_fdef f) (ps' : phinodes) (cs' : cmds) (tmn' : terminator)
  (i0 : id) (l2 : list_value_l) (ps2 : list phinode)
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true)
  (Hreach' : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (v0 : value) (Hgvn : gvn_in_fdef c1 id2 f)
  (HeqR3 : ret v0 = getValueViaLabelFromValuels l2 l1)
  (g1 : GenericValue) 
  (HeqR4 : ret g1 = getOperandValue v0 lc)
  (g2 : GVMap) (g : GenericValue) (g0 : GVMap)
  (H1 : wf_value_list
         (make_list_fdef_value
            (map_list_value_l (fun (value_ : value) (_ : l) => (f, value_))
               l2)))
  (H7 : wf_phinode f (block_intro l0 ps' cs' tmn') (insn_phi i0 l2))
  (HeqR1 : ret g = getOperandValue (v0 {[value_id (getCmdLoc c1) // id2]}) lc),
  g1 = g.
Proof.
  intros.
  destruct v0 as [vid | vc]; simpl in HeqR1, HeqR4; try congruence.
  destruct (id_dec vid id2); subst; simpl in HeqR1; try congruence.
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
    clear - Hlkb1 HbInF HwfF.
    apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
    rewrite HbInF in Hlkb1. inv Hlkb1; auto.
  subst.
  clear Hwfvls HwfV Hnth.
  destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
  clear Hreach.        
  unfold blockDominates in J3.         
  destruct vb. assert (HeqR':=HeqR).
  unfold inscope_of_tmn in HeqR.
  destruct f.
  remember ((dom_analyze (fdef_intro b)) !! l1) as R1.
  destruct R1.
  apply fold_left__spec in HeqR.
  destruct (eq_atom_dec l3 l1); subst.
  Case "l3=l1".
    destruct HeqR as [HeqR _].
    assert (In id2 t) as Hid2InScope.
      clear - HeqR3 HeqR Hlkb1 J3 Hlkvb HbInF HwfF.
      assert (J':=Hlkvb).
      apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
      apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto. 
      destruct Hlkb1 as [J1 J2].
      eapply blockInFdefB_uniq in J2; eauto.
      destruct J2 as [J2 [J4 J5]]; subst.
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
      simpl in J'.
      apply HeqR; auto.
    apply Hinscope in HeqR4; auto.
    assert (In (getCmdLoc c1) t) as Hc1InScope.
      eapply gvn_spec1; eauto.
    apply Hinscope in HeqR1; auto.
    eapply gvn_sim; eauto.
  
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
    assert (In id2 t) as Hid2InScope.
      clear - J1 HeqR Hlkb1 J3 Hlkvb HbInF HwfF.
      apply J1.
      apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
    apply Hinscope in HeqR4; auto.
    assert (In (getCmdLoc c1) t) as Hc1InScope.
      eapply gvn_spec1; eauto.
    apply Hinscope in HeqR1; auto.
    eapply gvn_sim; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_sim : forall
  (f : fdef)
  l0
  (lc : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1 c1 id2
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : OpsemDom.wf_defs f lc t)
  (HwfF : wf_fdef f)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (Hreach' : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block f (block_intro l1 ps1 cs1 tmn1))
  (Hgvn : gvn_in_fdef c1 id2 f)
  ps2
  (H8 : wf_phinodes f (block_intro l0 ps' cs' tmn') ps2)
  (Hin: exists ps1, ps' = ps1 ++ ps2) RVs RVs'
  (Hget : getIncomingValuesForBlockFromPHINodes ps2 (block_intro l1 ps1 cs1 tmn1)
    lc = ret RVs)
  (Hget' : getIncomingValuesForBlockFromPHINodes 
    (List.map (isubst_phi id2 (getCmdLoc c1)) ps2) 
    (isubst_block id2 (getCmdLoc c1) (block_intro l1 ps1 cs1 tmn1)) lc 
      = ret RVs'),
  RVs = RVs'.
Proof.
  induction ps2; intros; simpl in Hget, Hget'; try congruence.
    destruct a. inv H8. inv H3. simpl in Hget'.
    inv_mbind'. 
    app_inv.
    eapply getValueViaLabelFromValuels_sim in HeqR0; eauto. subst.
    assert (g1 = g) as Heq.
      eapply getValueViaLabelFromValuels_getOperandValue_sim with (l0:=l0); 
        eauto.
    subst. 
    eapply IHps2 with (RVs:=g2) in H4; eauto.
      congruence.

      destruct Hin as [ps3 Hin]. subst.
      exists (ps3++[insn_phi i0 l2]).
      simpl_env. auto.
Qed.

Lemma switchToNewBasicBlock_sim : forall
  (f : fdef) l2 (lc : GVMap) (t : list atom) l1 ps1 cs1 tmn1 c1 id2
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : OpsemDom.wf_defs f lc t)
  (HwfF : wf_fdef f) (Hgvn : gvn_in_fdef c1 id2 f)
  (ps2 : phinodes) (cs2 : cmds) (tmn2 : terminator)
  (Hsucc : In l2 (successors_terminator tmn1))
  (Hreach : isReachableFromEntry f (block_intro l2 ps2 cs2 tmn2))
  (Hreach' : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block f (block_intro l1 ps1 cs1 tmn1))
  lc0 lc0'
  (H8 : wf_phinodes f (block_intro l2 ps2 cs2 tmn2) ps2) 
  (Hget : switchToNewBasicBlock (block_intro l2 ps2 cs2 tmn2) 
    (block_intro l1 ps1 cs1 tmn1) lc = ret lc0)
  (Hget' : switchToNewBasicBlock 
    (isubst_block id2 (getCmdLoc c1) (block_intro l2 ps2 cs2 tmn2))
    (isubst_block id2 (getCmdLoc c1) (block_intro l1 ps1 cs1 tmn1)) lc 
      = ret lc0'),
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

Definition related_ECs c1 id2 (f1:fdef) (ec1 ec2:ExecutionContext) : Prop :=
let '(mkEC b1 cs1 tmn1 lc1) := ec1 in
let '(mkEC b2 cs2 tmn2 lc2) := ec2 in
isReachableFromEntry f1 b1 /\
blockInFdefB b1 f1 = true /\
lc1 = lc2 /\
isubst_block id2 (getCmdLoc c1) b1 = b2 /\
List.map (isubst_cmd id2 (getCmdLoc c1)) cs1 = cs2 /\
(exists l1, exists ps1, exists cs1', exists ps2, exists cs2',
b1 = block_intro l1 ps1 (cs1'++cs1) tmn1 /\
b2 = block_intro l1 ps2 (cs2'++cs2) tmn2).

Lemma bisimulation_cmd_updated_case : forall
  (F2 F1 : fdef) (B2 : block) lc1 lc2 (gv : GenericValue)
  (cs2 : list cmd) (tmn2 : terminator)
  id1 id2 c2 c1' id2' B1 c1 cs1 tmn1
  (Hid2 : Some id2 = getCmdID c2)
  (Hid1 : Some id1 = getCmdID c1)
  (HwfF1 : wf_fdef F1)
  (HgvnInF1 : gvn_in_fdef c1' id2' F1)
  (Htrans : isubst_fdef id2' (getCmdLoc c1') F1 = F2)
  (Hrel : related_ECs c1' id2' F1
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
  related_ECs c1' id2' F1
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
    [Hreach1 [HBinF1 [Heq1 [Hbtrans [Hcstrans
      [l3 [ps1 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]]; subst.
  inv Hcstrans. unfold isubst_cmd in Hid2.
  rewrite subst_getCmdID in Hid2. 
  trans_eq.
  assert (uniqFdef F1) as HuniqF1. auto.
  repeat (split; try solve [auto]).
    inv Heq3. rewrite List.map_app in H1. simpl in H1.
    apply app_inv_tail in H1. subst.
    exists l3. exists ps1. exists (cs1'++[c1]). 
    exists (List.map (isubst_phi id2' (getCmdLoc c1')) ps1). 
    exists (List.map (isubst_cmd id2' (getCmdLoc c1')) (cs1'++[c1])). 
    simpl. repeat rewrite List.map_app. simpl_env. auto.
Qed.

Ltac destruct_ctx :=
match goal with
| Hrel : related_ECs _ _ _ ?S1 _,
  HwfS1 : OpsemDom.wf_ExecutionContext _ _,
  HsInsn1 : sInsn _ ?S1 _ _ |- _ =>
  destruct S1 as [b1 cs1 tmn1 lc1];
  assert (J:=Hrel); simpl in J;
  destruct J as
    [Hreach1 [HBinF1 [Heq1 [Hbtrans [Hcstrans
      [l3 [ps1 [cs1' [ps2 [cs2' [Heq2 Heq3]]]]]]]]]]]; subst;
  match goal with
  | Hcstrans : List.map _ _ = _ :: _ |- _ =>
    destruct cs1; inv Hcstrans;
    match goal with
    | H1 : isubst_cmd _ _ ?c = _ |- _ => 
      destruct c; inv H1
    end
  | Heq3 : isubst_block _ _ _ = _ |- _ =>
    apply map_eq_nil in Hcstrans; auto; subst;
    inv Heq3;
    match goal with
    | H5 : subst_tmn _ _ ?tmn1 = _ |- _ =>
      destruct tmn1; inv H5
    end
  end;
  inv HsInsn1;
  destruct HwfS1 as [_ [_ [_ [Hinscope' _]]]];
  match goal with
  | Hinscope' : match inscope_of_cmd ?f ?b ?c with
                | ret _ => _
                | merror => False
                end |- _ => 
    remember (inscope_of_cmd f b c) as R1;
    destruct R1; tinv Hinscope'
  | Hinscope' : match inscope_of_tmn ?f ?b ?c with
                | ret _ => _
                | merror => False
                end |- _ => 
    remember (inscope_of_tmn f b c) as R1;
    destruct R1; tinv Hinscope'
  end
end.

Ltac bisimulation_cmd :=
match goal with
| H : _ ?lc _  (?v {[value_id (getCmdLoc ?c1) // ?id2]})
        (?v0 {[value_id (getCmdLoc ?c1) // ?id2]}) = ret ?gvs3,
  H11 : _ _ _ ?v ?v0 = ret ?gvs0,
  Hrel : related_ECs _ _ _ _ _ |-
  context [_ ?id1 _ ?v ?v0] =>
  assert (gvs0 = gvs3) as Heq;
    try (unfold ICMP, BOP in *;
    inv_mbind'; inv_mfalse; app_inv; symmetry_ctx;
    match goal with
    | HeqR : getOperandValue ?v _ = ret _, 
      HeqR' : getOperandValue (?v {[ _ // _ ]} )_ = ret _, 
      HeqR0 : getOperandValue ?v0 _ = ret _,
      HeqR0' : getOperandValue (?v0 {[ _ // _ ]} ) _ = ret _ |- _ => 
      eapply getOperandValue_inCmdOps_sim in HeqR; 
        try (eauto || simpl; auto);
      eapply getOperandValue_inCmdOps_sim in HeqR0; 
        try (eauto || simpl; auto);
      subst; auto
    end);
  split; try solve [auto |
    eapply bisimulation_cmd_updated_case in Hrel; try solve [simpl; eauto]]
end.

Lemma bisimulation : forall c1 id2 F1 F2 S1 S2 S1' S2' tr1 tr2,
  OpsemDom.wf_ExecutionContext F1 S1 -> 
  wf_fdef F1 ->
  gvn_in_fdef c1 id2 F1 ->
  isubst_fdef id2 (getCmdLoc c1) F1 = F2 ->
  related_ECs c1 id2 F1 S1 S2 ->
  sInsn F1 S1 S1' tr1 ->
  sInsn F2 S2 S2' tr2 ->
  related_ECs c1 id2 F1 S1' S2' /\ tr1 = tr2.
Proof.
  intros c1 id2 F1 F2 S1 S2 S1' S2' tr1 tr2 HwfS1 HwfF1 HgvnInF1 Htrans Hrel 
    HsInsn1 HsInsn2.
  (sInsn_cases (destruct HsInsn2) Case); destruct_ctx.
Focus.
Case "sBranch".
  assert (c0 = c) as Heq.
    eapply getOperandValue_inTmnOperans_sim; try solve [eauto | simpl; auto].
  subst.
  assert (isubst_block id2 (getCmdLoc c1) (block_intro l'0 ps'0 cs'0 tmn'0) 
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
    exists l'. exists ps'0. exists nil. 
    exists (List.map (isubst_phi id2 (getCmdLoc c1)) ps'0). exists nil.
    auto.
Unfocus.

Focus.
Case "sBranch_uncond". 
  assert (isubst_block id2 (getCmdLoc c1) (block_intro l'0 ps'0 cs'0 tmn'0) 
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
      exists l'. exists ps'0. exists nil. 
      exists (List.map (subst_phi id2 (value_id (getCmdLoc c1))) ps'0). 
      exists nil. auto.
Unfocus.

Case "sBop". abstract bisimulation_cmd.
Case "sIcmp". abstract bisimulation_cmd.
Qed.

Lemma related_finalstate_is_stuck : forall c1 id2 F1 F2 S1 S2 S2' tr2
  (Hrel : related_ECs c1 id2 F1 S1 S2)
  (Hfinal1 : s_isFinialState S1 = true)
  (HsInsn2 : sInsn F2 S2 S2' tr2),
  False.
Proof.
  intros.
  destruct S1. destruct CurCmds0; tinv Hfinal1. 
  destruct Terminator0; inv Hfinal1. destruct S2. 
  destruct Hrel as 
    [J1 [J2 [J3 [J4 [J6 [l1 [ps1 [cs1' [ps2 [cs2' [J7 J8]]]]]]]]]]]; 
    subst.
  inv J8. inv HsInsn2.
Qed.

Lemma backsimulation : forall c1 id2 F1 F2 S1 S2 S2' tr2,
  wf_fdef F1 ->
  gvn_in_fdef c1 id2 F1 ->
  isubst_fdef id2 (getCmdLoc c1) F1 = F2 ->
  related_ECs c1 id2 F1 S1 S2 ->
  OpsemPP.wf_ExecutionContext F1 S1 -> 
  OpsemDom.wf_ExecutionContext F1 S1 -> 
  sInsn F2 S2 S2' tr2 ->
  exists S1', exists tr1,
    sInsn F1 S1 S1' tr1 /\ related_ECs c1 id2 F1 S1' S2' /\ tr1 = tr2.
Proof.
  intros c1 id2 F1 F2 S1 S2 S2' tr2 HwfF1 HcInF1 Htrans Hrel HwfEC1 HwfEC1' 
    HsInsn2.
  assert (J:=HwfEC1).
  apply OpsemPP.progress in J; auto.
  destruct J as [Hfinal1 | [S1' [tr1 HsInsn1]]].
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
