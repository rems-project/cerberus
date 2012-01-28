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
Require Import promotable_props.
Require Import palloca_props.

Ltac zauto := auto with zarith.
Ltac zeauto := eauto with zarith.

Import Promotability.

(* Simulation *)

Definition DGVMap := @Opsem.GVsMap DGVs.

Definition reg_simulation (pinfo: PhiInfo) (f1:fdef) (lc1 lc2:DGVMap) : Prop :=  
  if (fdef_dec (PI_f pinfo) f1) then 
    (forall i0, 
      not_temporaries i0 (PI_newids pinfo) -> 
      lookupAL _ lc1 i0 = lookupAL _ lc2 i0) 
  else lc1 = lc2.

Definition fdef_simulation (pinfo: PhiInfo) f1 f2: Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    phinodes_placement f1 (PI_rd pinfo) (PI_id pinfo) (PI_typ pinfo) 
      (PI_align pinfo) (PI_succs pinfo) (PI_preds pinfo) = f2
  else f1 = f2.

Definition wf_tmp_value (pinfo: PhiInfo) TD (M2:mem) (lc2:DGVMap) (tid:id)   
  : Prop :=  
  exists gvsa, exists gv, 
    lookupAL _ lc2 (PI_id pinfo) = Some gvsa /\
    mload TD M2 gvsa (PI_typ pinfo) (PI_align pinfo) = Some gv /\
    lookupAL _ lc2 tid = Some gv.

Definition cmds_simulation (pinfo: PhiInfo) TD (M2:mem) lc2 (f1:fdef) (b1:block) 
  cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    let '(block_intro l1 _ cs _) := b1 in 
    match ATree.get l1 (PI_newids pinfo) with
    | Some (lid, pid', sid) =>
      let suffix := 
        match ATree.get l1 (PI_succs pinfo) with
        | Some (_::_) => 
            [insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) 
              (PI_align pinfo)]
        | _ => nil
        end in
      let prefix :=
        match ATree.get l1 (PI_preds pinfo) with
        | Some (_ :: _) => 
            [insn_store sid (PI_typ pinfo) (value_id pid') 
              (value_id (PI_id pinfo)) (PI_align pinfo)]
        | _ => nil
        end in
      (* If cs1 is at the beginning of b1, 
         then cs2 must be at the beginning of b2, or 
                       exactly after the inserted store in b2, or
                       exactly after the inserted load 
                         if both cs1/cs2 are at the end;
         moreover, if pid' is inserted, its value should be correct, which can
           only happen when cs = cs1. 
      *)
      (cs = cs1 ->          
       (cs2 = prefix ++ cs1 ++ suffix \/ 
        (prefix <> nil /\ cs2 = cs1 ++ suffix) \/
        (suffix <> nil /\ cs1 = nil /\ cs2 = nil)) /\ 
       (prefix <> nil -> 
        cs2 = prefix ++ cs1 ++ suffix ->
        wf_tmp_value pinfo TD M2 lc2 pid')) /\
      (* If cs1 isn't at the beginning of b1, 
         then cs2 matches cs1 with suffix, or both cs1 and cs2 reach the end *)
      (cs <> cs1 -> cs2 = cs1 ++ suffix \/ 
                    (suffix <> nil /\ cs1 = nil /\ cs2 = nil)) /\
      (* Moreover, when both cs1 and cs2 are at the end, and 
                        a load is inserted for b2, 
                   the value of the load shoule be correct. 
         This case can happen when cs = cs1 \/ cs <> cs1
      *)
      (suffix <> nil -> cs1 = nil -> cs2 = nil -> 
       wf_tmp_value pinfo TD M2 lc2 lid)
    | _ => cs1 = cs2
    end
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) f1 b1 b2: Prop :=
  if (fdef_dec (PI_f pinfo) f1) then
     phinodes_placement_block (PI_id pinfo) (PI_typ pinfo) (PI_align pinfo) 
       (PI_newids pinfo) (PI_succs pinfo) (PI_preds pinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) Ps1 Ps2: Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) S1 S2: Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo Ps1 Ps1
   end) S1 S2.

Definition EC_simulation_head (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (EC1 EC2:Opsem.ExecutionContext) (M2:mem) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(los, nts) := TD in
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\ als1 = als2 /\
       block_simulation pinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       reg_simulation pinfo f1 lc1 lc2 /\
       cmds_simulation pinfo TD M2 lc2 f1 b1 cs1 cs2
  end.

Definition EC_simulation_tail (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (EC1 EC2:Opsem.ExecutionContext) (M2:mem) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 ((insn_call _ _ _ _ _ _ as c2)::cs2) tmn2 lc2 als2) =>
       let '(los, nts) := TD in
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\ als1 = als2 /\
       block_simulation pinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++c2::cs2) tmn2) /\
       reg_simulation pinfo f1 lc1 lc2 /\
       cmds_simulation pinfo TD M2 lc2 f1 b1 cs1 (c2::cs2)
  | _ => False
  end.

Fixpoint ECs_simulation_tail (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (ECs1 ECs2:Opsem.ECStack) (M2:mem) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation_tail TD Ps1 pinfo EC1 EC2 M2 /\ 
    ECs_simulation_tail TD Ps1 pinfo ECs1' ECs2' M2
| _, _ => False
end.

Fixpoint ECs_simulation (TD:TargetData) Ps1 (pinfo: PhiInfo) 
  (ECs1 ECs2:Opsem.ECStack) (M2:mem) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation_head TD Ps1 pinfo EC1 EC2 M2 /\ 
    ECs_simulation_tail TD Ps1 pinfo ECs1' ECs2' M2
| _, _ => False
end.

Definition State_simulation (pinfo: PhiInfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    let '(los, nts) := TD1 in
    wf_system nil S1 /\
    moduleInSystemB (module_intro los nts Ps1) S1 = true /\
    system_simulation pinfo S1 S2 /\ 
    TD1 = TD2 /\ 
    products_simulation pinfo Ps1 Ps2 /\
    ECs_simulation TD1 Ps1 pinfo ECs1 ECs2 M2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

Notation "$ gv # t $" := (DGVs.(gv2gvs) gv t) (at level 41).

Lemma cmds_simulation_nil_inv: forall TD M2 lc2 F1 B1 cs1 pinfo
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 nil),
  cs1 = nil.
Proof.
  intros.
  unfold cmds_simulation in Htcmds. unfold wf_tmp_value in Htcmds. 
  destruct (fdef_dec (PI_f pinfo) F1); subst; auto.
  destruct B1.
  destruct ((PI_newids pinfo) ! l0) as [[[]]|]; auto.
  destruct Htcmds as [J1 [J2 _]].
  destruct (list_eq_dec cmd_dec c cs1).
    apply J1 in e. 
    destruct e as [[e | [[_ e] | [_ [e1 e2]]]] _]; auto;
      repeat match goal with
      | H : nil = _ ++ _ |- _ => symmetry in H
      | H : _ ++ _ = nil |- _ => apply app_eq_nil in H; destruct H; auto
      end.

    apply J2 in n.
    destruct n as [n | [_ [n _]]]; auto.
    repeat match goal with
    | H : nil = _ ++ _ |- _ => symmetry in H
    | H : _ ++ _ = nil |- _ => apply app_eq_nil in H; destruct H; auto
    end.
Qed.

Ltac cmds_simulation_cons_inv_tac1 :=
let foo cs2 e :=
    exists cs2;
    rewrite e; simpl_env;
    split; try solve 
      [auto |
       split; intros; try solve
         [split; auto |
          split; try solve [auto | intros; congruence]]
      ] in
match goal with
| e : ?c :: ?cs2 = ?cs1 ++ nil |- _ => foo cs2 e
| e : ?c :: ?cs2 = nil ++ ?cs1 ++ nil |- _ => foo cs2 e
end.

Definition isnt_inserted_ldst pinfo c : Prop :=
match c with
| insn_load id0 _ _ _ | insn_store id0 _ _ _ _ => 
    not_temporaries id0 (PI_newids pinfo)
| _ => True
end.

Ltac cmds_simulation_same_cons_inv_tac2 :=
let foo e cs1 Hnoldst l0 HeqR :=
    simpl_env in e;
    destruct cs1; inv e; 
      try solve [
        assert (J:=Hnoldst l0); simpl in J; rewrite <- HeqR in J;
        destruct J as [J7 [J8 J9]]; try congruence];
    exists cs1;
    split; try solve 
      [auto |
       split; intros; 
       split; auto; try solve [
         intros; subst;
         match goal with
         | H1 : nil ++ [_] = nil |- _ => inv H1
         end
         ]
      ] in
match goal with
| Hnoldst : isnt_inserted_ldst _ ?c,
  HeqR : Some (_, _, _) = _ ! ?l0 |- _ => 
  match goal with
  | e : ?c :: ?cs2 = nil ++ ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  | e : ?c :: ?cs2 = ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  end
end.

Ltac cmds_simulation_same_cons_inv_tac3 R2 :=
 let l2 := fresh "l2" in
 destruct R2 as [l2|]; try solve [
   destruct l2; try solve 
     [cmds_simulation_cons_inv_tac1|
      cmds_simulation_same_cons_inv_tac2] |
   cmds_simulation_cons_inv_tac1].

Hint Unfold cmds_simulation: ppbsim.

Lemma cmds_simulation_other_cons_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Hneq: F1 <> PI_f pinfo),
  exists cs1', 
    cs1 = c::cs1' /\   
    cmds_simulation pinfo TD M2 lc2 F1 B1 cs1' cs2.
Proof.
  intros. autounfold with ppbsim in *. unfold wf_tmp_value in *. 
  destruct (fdef_dec (PI_f pinfo) F1); subst; try congruence.
  eauto.
Qed.

Ltac cmds_simulation_cons_inv_tac1' :=
let foo cs2 e :=
    exists cs2;
    rewrite e; simpl_env;
    split; try solve [
      auto |
      split; intros; subst; try solve [
        split; try solve [
          auto |
          intros;
          match goal with
          | H0: ?cs2 = [_] ++ ?cs2 |- _ =>
            symmetry in H0; apply app_inv_tail_nil in H0; congruence
          end] | 
        split; try solve [auto | intros; congruence]
      ]
    ] in
match goal with
| e : ?c :: ?cs2 = ?cs1 ++ nil |- _ => foo cs2 e
| e : ?c :: ?cs2 = nil ++ ?cs1 ++ nil |- _ => foo cs2 e
end.

Ltac cmds_simulation_same_cons_inv_tac2' :=
let foo e cs1 Hnoldst l0 HeqR :=
    simpl_env in e;
    destruct cs1; inv e; 
      try solve [
        assert (J:=Hnoldst l0); simpl in J; rewrite <- HeqR in J;
        destruct J as [J7 [J8 J9]]; try congruence];
    exists cs1;
    split; try solve [
      auto |
      split; intros; subst; try solve [
        split; try solve [
          auto |
          intros;
          match goal with
          | H0: ?cs2 = [_] ++ ?cs2 |- _ =>
            symmetry in H0; apply app_inv_tail_nil in H0; congruence
          end] |
        split; try solve [
          auto | 
          intros; subst;
          match goal with
          | H1 : nil ++ [_] = nil |- _ => inv H1
          end
        ]
      ]
    ] in
match goal with
| Hnoldst : isnt_inserted_ldst _ ?c,
  HeqR : Some (_, _, _) = _ ! ?l0 |- _ => 
  match goal with
  | e : ?c :: ?cs2 = nil ++ ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  | e : ?c :: ?cs2 = ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  end
end.

Ltac cmds_simulation_same_cons_inv_tac3' R2 :=
 let l2 := fresh "l2" in
 destruct R2 as [l2|]; try solve [
   destruct l2; try solve 
     [cmds_simulation_cons_inv_tac1'|
      cmds_simulation_same_cons_inv_tac2'] |
   cmds_simulation_cons_inv_tac1'].

Lemma cmds_simulation_same_cons_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Heq: exists l0, exists ps0, exists cs0, exists tmn0, 
          B1 = block_intro l0 ps0 (cs0++cs1) tmn0)
  (Hnoldst: isnt_inserted_ldst pinfo c)
  (Heq': F1 = PI_f pinfo),
  exists cs1', 
    cs1 = c::cs1' /\   
    cmds_simulation pinfo TD M2 lc2 F1 B1 cs1' cs2.
Proof.
  intros.
  autounfold with ppbsim in *. unfold wf_tmp_value in *. 
  destruct (fdef_dec (PI_f pinfo) F1); subst F1; try congruence.
  destruct B1.
  remember ((PI_newids pinfo) ! l0) as R.
  destruct R as [[[]]|]; eauto.
  destruct Htcmds as [J1 [J2 J3]].
  remember ((PI_preds pinfo) ! l0) as R1.
  remember ((PI_succs pinfo) ! l0) as R2.
  destruct (list_eq_dec cmd_dec c0 cs1).
  Case "1".
    clear J2. apply_clear J1 in e. 
    destruct e as [[e | [[e1 e] | [e1 [e2 e3]]]] J4];
      try match goal with
      | H: _::_ = nil |- _ => inv H
      end;
      destruct R1 as [l1|]; try solve [
        destruct l1; try solve [
          cmds_simulation_same_cons_inv_tac3 R2 | 
          cmds_simulation_same_cons_inv_tac3' R2 | 
          inv e; assert (J:=Hnoldst l0); simpl in J; rewrite <- HeqR in J;
            destruct J as [J7 [J8 J9]]; try congruence ] | 
        cmds_simulation_same_cons_inv_tac3 R2 |
        cmds_simulation_same_cons_inv_tac3' R2].

  Case "2".
    assert (n':=n).
    apply J2 in n. 
    destruct n as [n | [_ [_ n]]]; try congruence.
    destruct R2 as [l2|].
    SCase "2.1".    
      destruct l2.
      SSCase "2.1.1".    
        exists cs2.
        simpl_env in n. subst cs1.
        split; auto.
        destruct R1 as [l1|].
         SSSCase "2.1.1.1".    
          destruct l1.
          SSSSCase "2.1.1.1.1".    
            simpl_env.
            split; intros;
              split; try solve [auto | intros; congruence].
            split; intros.
              subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
              inversion Heq.
              apply app_cons_is_larger in H2. inv H2.

          SSSSCase "2.1.1.1.2".    
             split; try solve [auto | intros; congruence].
        SSSCase "2.1.1.2".    
        split; intros.
          subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
          inversion Heq.
          apply app_cons_is_larger in H2. inv H2.

          split; try solve [auto | intros; congruence].
          
      SSCase "2.1.2".    
        destruct cs1; inversion n.
        SSSCase "2.1.2.1".    
          subst c. 
          assert (J:=Hnoldst l0); simpl in J; rewrite <- HeqR in J;
            destruct J as [J7 [J8 J9]]; try congruence.

        SSSCase "2.1.2.2".    
          exists cs1.
          split; auto.
          destruct R1 as [l3|].
          SSSSCase "2.1.2.2.1".    
            destruct l3.
            SSSSSCase "2.1.2.2.1.1".    
              split; intros;
                split; try solve [auto | intros; congruence].
              intros. subst. inv H3.

            SSSSSCase "2.1.2.2.1.2".    
              split; intros.
                subst. destruct Heq as [l5 [ps3 [cs3 [tmn3 Heq]]]].
                inversion Heq.
                apply app_cons_is_larger in H2. inv H2.
              split; auto.
                intros. subst. inv H3.

          SSSSCase "2.1.2.2.2".    
            split; intros; auto.
            split; intros; auto.
              congruence.
            split; intros; auto.
              subst. inv H3.

    SCase "2.2".    
        exists cs2.
        simpl_env in n. subst cs1.
        split; auto.
        destruct R1 as [l1|].
        SSCase "2.2.1".    
          destruct l1.
          SSSCase "2.2.1.1".    
            simpl_env.
            split; intros;
              split; try solve [auto | intros; congruence].
          SSSCase "2.2.1.2".    
            split; intros.
              subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
              inversion Heq.
              apply app_cons_is_larger in H2. inv H2.

              split; try solve [auto | intros; congruence].
        SSCase "2.2.2".    
          split; intros.
            subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
            inversion Heq.
            apply app_cons_is_larger in H2. inv H2.

            split; try solve [auto | intros; congruence].
Qed.

Definition is_inserted_ld pinfo c : Prop :=
match c with
| insn_load id0 _ _ _ => is_temporary id0 (PI_newids pinfo)
| _ => False
end.

Definition is_inserted_st pinfo c : Prop :=
match c with
| insn_store id0 _ _ _ _ => is_temporary id0 (PI_newids pinfo)  
| _ => False
end.

Ltac solve_is_temporary :=
  match goal with
  | Hin : blockInFdefB _ _ = true |- _ =>
    eapply temporary_must_be_fresh in Hin; try solve [
      inv Hin |
      eauto ];
      simpl in *;
      match goal with
      | Htmp : is_temporary ?i0 ?A, EQ : ?A = ?B |- is_temporary ?i0 ?B => 
          rewrite <-EQ; auto
      end
  end.

Ltac cmds_simulation_same_head_inv_tac :=
match goal with 
| J1 : insn_store ?i0 ?t ?v ?v0 ?a :: _ = 
       ?cs1 ++ 
       match ?R2 with
       | ret _ => _
       | merror => _
       end |- _ => 
  assert (exists cs1', cs1 = insn_store i0 t v v0 a :: cs1') as EQ;
    destruct cs1; try solve [
      destruct R2 as [[]|]; inv J1 |
      inv J1; eauto];
  destruct EQ as [cs1' EQ]; inv EQ; subst;
  solve_is_temporary
end.

Lemma cmds_simulation_same_head_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Hin: blockInFdefB B1 F1 = true) (Hwfpi: WF_PhiInfo pinfo)
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Heq: exists l0, exists ps0, exists cs0, exists tmn0, 
          B1 = block_intro l0 ps0 (cs0++cs1) tmn0)
  (Hld: is_inserted_st pinfo c)
  (Heq': F1 = PI_f pinfo),
  exists l1, exists ps1, exists tmn1, exists lid, exists pid, exists sid, 
    B1 = block_intro l1 ps1 cs1 tmn1 /\
    ATree.get l1 (PI_newids pinfo) = Some (lid, pid, sid) /\
    c = insn_store sid (PI_typ pinfo) (value_id pid) (value_id (PI_id pinfo)) 
          (PI_align pinfo) /\
    ATree.get l1 (PI_preds pinfo) <> Some nil /\
    ATree.get l1 (PI_preds pinfo) <> None /\
    wf_tmp_value pinfo TD M2 lc2 pid.
Proof.
  intros. subst.
  destruct c; tinv Hld.
  destruct Heq as [l0 [ps0 [cs0 [tmn0 Heq]]]]; subst.
  autounfold with ppbsim in *. unfold wf_tmp_value in *. 
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  destruct Hwfpi as [_ [_ [_ [_ Hwfpi]]]].
  remember ((PI_newids pinfo) ! l0) as R.

  destruct R as [[[]]|]; subst; try solve [solve_is_temporary].
  destruct Htcmds as [J1 [J2 _]].
  exists l0. exists ps0. exists tmn0. exists i1. exists i2. exists i3.
  remember ((PI_preds pinfo) ! l0) as R1.
  remember ((PI_succs pinfo) ! l0) as R2.

  destruct (list_eq_dec cmd_dec (cs0++cs1) cs1).
  Case "1".
    apply app_inv_tail_nil in e0; subst cs0.
    split; auto.
    split; auto.
    clear J2.
    destruct J1 as [J1 J3]; auto.
    destruct J1 as [J1 | [[_ J1] | [_ [_ J1]]]].
      destruct R1; simpl in J1.
        destruct l1; simpl in J1.
          cmds_simulation_same_head_inv_tac.

          inv J1.
          split; auto.
          split; try solve [intros; congruence].
          split; try solve [intros; congruence].
            apply J3; auto.
              intro J. inv J.

        cmds_simulation_same_head_inv_tac.
      cmds_simulation_same_head_inv_tac.
      inv J1.

  Case "2".
    clear J1.
    apply_clear J2 in n.
    destruct n as [n | [_ [_ n]]]; try congruence.
    cmds_simulation_same_head_inv_tac.
Qed.

Ltac cmds_simulation_same_tail_inv_tac :=
match goal with 
| J1 : insn_load ?i0 ?t ?v ?a :: _ = 
       ?cs1 ++ 
       match ?R2 with
       | ret _ => _
       | merror => _
       end |- _ => 
    destruct cs1; try solve [
      inv J1; solve_is_temporary |
      destruct R2 as [[]|]; inv J1;
        repeat split; try solve [auto | intros; congruence]
      ]
end.

Lemma cmds_simulation_same_tail_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Hin: blockInFdefB B1 F1 = true) (Hwfpi: WF_PhiInfo pinfo)
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Heq: exists l0, exists ps0, exists cs0, exists tmn0, 
          B1 = block_intro l0 ps0 (cs0++cs1) tmn0)
  (Hld: is_inserted_ld pinfo c)
  (Heq': F1 = PI_f pinfo),
  exists lid, exists pid, exists sid, 
    cs1 = nil /\ cs2 = nil /\
    ATree.get (getBlockLabel B1) (PI_newids pinfo) = Some (lid, pid, sid) /\
    c = insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) (PI_align pinfo) /\
    ATree.get (getBlockLabel B1) (PI_succs pinfo) <> Some nil /\
    ATree.get (getBlockLabel B1) (PI_succs pinfo) <> None.
Proof.
  intros. subst.
  destruct c; tinv Hld.
  destruct Heq as [l0 [ps0 [cs0 [tmn0 Heq]]]]; subst.
  autounfold with ppbsim in *. unfold wf_tmp_value in *. simpl.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  destruct Hwfpi as [_ [_ [_ [_ Hwfpi]]]].
  remember ((PI_newids pinfo) ! l0) as R.
  destruct R as [[[]]|]; subst; try solve [solve_is_temporary].
  destruct Htcmds as [J1 [J2 J3]].
  exists i1. exists i2. exists i3.
  remember ((PI_preds pinfo) ! l0) as R1.
  remember ((PI_succs pinfo) ! l0) as R2.
  destruct (list_eq_dec cmd_dec (cs0++cs1) cs1).
  Case "1".
    apply app_inv_tail_nil in e0; subst cs0.
    destruct J1 as [J1 _]; auto.
    destruct J1 as [J1 | [[_ J1] | [_ [_ J1]]]].
      destruct R1; simpl in J1.
        destruct l1; tinv J1.
          destruct cs1.
            destruct R2; tinv J1.
              destruct l1; inv J1.
              repeat split; try solve [auto | intros; congruence]. 
            inv J1. solve_is_temporary.
        cmds_simulation_same_tail_inv_tac.
      cmds_simulation_same_tail_inv_tac.
      inv J1.

  Case "2".
    clear J1.
    apply_clear J2 in n.
    destruct n as [n | [_ [_ n]]]; try congruence.
    cmds_simulation_same_tail_inv_tac.
Qed.

Definition isnt_ldst c : Prop :=
match c with
| insn_load _ _ _ _ | insn_store _ _ _ _ _ => False
| _ => True
end.

Ltac cmds_simulation_non_ldst_cons_inv_tac2 :=
let foo e cs1 Hnoldst l0 HeqR :=
    simpl_env in e;
    destruct cs1; inv e; tinv Hnoldst;
    exists cs1;
    split; try solve 
      [auto |
       split; intros; 
       split; auto; try solve [
         intros; subst;
         match goal with
         | H1 : nil ++ [_] = nil |- _ => inv H1
         end
         ]
      ] in
match goal with
| Hnoldst : isnt_ldst ?c,
  HeqR : Some (_, _, _) = _ ! ?l0 |- _ => 
  match goal with
  | e : ?c :: ?cs2 = nil ++ ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  | e : ?c :: ?cs2 = ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  end
end.

Ltac cmds_simulation_non_ldst_cons_inv_tac2' :=
let foo e cs1 Hnoldst l0 HeqR :=
    simpl_env in e;
    destruct cs1; inv e; tinv Hnoldst;
    exists cs1;
    split; try solve [
      auto |
      split; intros; subst; try solve [
        split; try solve [
          auto |
          intros;
          match goal with
          | H0: ?cs2 = [_] ++ ?cs2 |- _ =>
            symmetry in H0; apply app_inv_tail_nil in H0; congruence
          end] |
        split; try solve [
          auto | 
          intros; subst;
          match goal with
          | H1 : nil ++ [_] = nil |- _ => inv H1
          end
        ]
      ]
    ] in
match goal with
| Hnoldst : isnt_ldst ?c,
  HeqR : Some (_, _, _) = _ ! ?l0 |- _ => 
  match goal with
  | e : ?c :: ?cs2 = nil ++ ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  | e : ?c :: ?cs2 = ?cs1 ++ [insn_load _ _ _ _] |- _ => 
      foo e cs1 Hnoldst l0 HeqR
  end
end.

Ltac cmds_simulation_non_ldst_cons_inv_tac3 R2 :=
 let l2 := fresh "l2" in
 destruct R2 as [l2|]; try solve [
   destruct l2; try solve 
     [cmds_simulation_cons_inv_tac1|
      cmds_simulation_non_ldst_cons_inv_tac2] |
   cmds_simulation_cons_inv_tac1].

Ltac cmds_simulation_non_ldst_cons_inv_tac3' R2 :=
 let l2 := fresh "l2" in
 destruct R2 as [l2|]; try solve [
   destruct l2; try solve 
     [cmds_simulation_cons_inv_tac1'|
      cmds_simulation_non_ldst_cons_inv_tac2'] |
   cmds_simulation_cons_inv_tac1'].

Lemma cmds_simulation_non_ldst_cons_inv: forall pinfo TD M2 lc2 F1 B1 cs1 c cs2
  (Htcmds: cmds_simulation pinfo TD M2 lc2 F1 B1 cs1 (c::cs2))
  (Heq: exists l0, exists ps0, exists cs0, exists tmn0, 
          B1 = block_intro l0 ps0 (cs0++cs1) tmn0)
  (Hnoldst: isnt_ldst c),
  exists cs1', 
    cs1 = c::cs1' /\   
    cmds_simulation pinfo TD M2 lc2 F1 B1 cs1' cs2.
Proof.
  intros.
  autounfold with ppbsim in *. unfold wf_tmp_value in *.
  destruct (fdef_dec (PI_f pinfo) F1); subst; eauto.
  destruct B1.
  remember ((PI_newids pinfo) ! l0) as R.
  destruct R as [[[]]|]; eauto.
  destruct Htcmds as [J1 [J2 J3]].
  remember ((PI_preds pinfo) ! l0) as R1.
  remember ((PI_succs pinfo) ! l0) as R2.
  destruct (list_eq_dec cmd_dec c0 cs1).
  Case "1".
    clear J2. apply_clear J1 in e. 
    destruct e as [[e | [[e1 e] | [_ [_ e]]]] J4];
      try match goal with  
      | H: _::_ = nil |- _ => inv H
      end;
      destruct R1 as [l1|]; try solve [
        destruct l1; try solve [
          cmds_simulation_non_ldst_cons_inv_tac3 R2 | 
          cmds_simulation_non_ldst_cons_inv_tac3' R2 | 
          inv e; inv Hnoldst ] | 
        cmds_simulation_non_ldst_cons_inv_tac3 R2 |
        cmds_simulation_non_ldst_cons_inv_tac3' R2].

  Case "2".
    assert (n':=n).
    apply J2 in n. 
    destruct n as [n | [_ [_ n]]]; try congruence.
    destruct R2 as [l2|].
    SCase "2.1".    
      destruct l2.
      SSCase "2.1.1".    
        exists cs2.
        simpl_env in n. subst cs1.
        split; auto.
        destruct R1 as [l1|].
         SSSCase "2.1.1.1".    
          destruct l1.
          SSSSCase "2.1.1.1.1".    
            simpl_env.
            split; intros;
              split; try solve [auto | intros; congruence].
            split; intros.
              subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
              inversion Heq.
              apply app_cons_is_larger in H2. inv H2.

          SSSSCase "2.1.1.1.2".    
             split; try solve [auto | intros; congruence].
        SSSCase "2.1.1.2".    
        split; intros.
          subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
          inversion Heq.
          apply app_cons_is_larger in H2. inv H2.

          split; try solve [auto | intros; congruence].
          
      SSCase "2.1.2".    
        destruct cs1; inversion n.
        SSSCase "2.1.2.1".    
          subst c. inv Hnoldst.

        SSSCase "2.1.2.2".    
          exists cs1.
          split; auto.
          destruct R1 as [l3|].
          SSSSCase "2.1.2.2.1".    
            destruct l3.
            SSSSSCase "2.1.2.2.1.1".    
              split; intros;
                split; try solve [auto | intros; congruence].
              intros. subst. inv H3.

            SSSSSCase "2.1.2.2.1.2".    
              split; intros.
                subst. destruct Heq as [l5 [ps3 [cs3 [tmn3 Heq]]]].
                inversion Heq.
                apply app_cons_is_larger in H2. inv H2.
              split; auto.
                intros. subst. inv H3.

          SSSSCase "2.1.2.2.2".    
            split; intros; auto.
            split; intros; auto.
              congruence.
            split; intros; auto.
              subst. inv H3.

    SCase "2.2".    
        exists cs2.
        simpl_env in n. subst cs1.
        split; auto.
        destruct R1 as [l1|].
        SSCase "2.2.1".    
          destruct l1.
          SSSCase "2.2.1.1".    
            simpl_env.
            split; intros;
              split; try solve [auto | intros; congruence].
          SSSCase "2.2.1.2".    
            split; intros.
              subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
              inversion Heq.
              apply app_cons_is_larger in H2. inv H2.

              split; try solve [auto | intros; congruence].
        SSCase "2.2.2".    
          split; intros.
            subst. destruct Heq as [l3 [ps3 [cs3 [tmn3 Heq]]]].
            inversion Heq.
            apply app_cons_is_larger in H2. inv H2.

            split; try solve [auto | intros; congruence].
Qed.

Lemma simulation__lookupAL: forall pinfo vid lc lc2 F
  (Hntmp: if fdef_dec (PI_f pinfo) F then not_temporaries vid (PI_newids pinfo) else True)
  (Hrsim : reg_simulation pinfo F lc lc2),
  lookupAL _ lc vid = lookupAL _ lc2 vid.
Proof.
  intros.
  unfold reg_simulation in Hrsim.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
Qed.

Lemma simulation__getOperandValue: forall pinfo TD v lc gl2 lc2 F
  (Hntmp: if fdef_dec (PI_f pinfo) F then value_has_no_tmps pinfo v else True)
  (Hrsim : reg_simulation pinfo F lc lc2),
  Opsem.getOperandValue TD v lc gl2 = Opsem.getOperandValue TD v lc2 gl2.
Proof.
  intros.
  destruct v; auto.
    simpl. eapply simulation__lookupAL; eauto.
Qed.

Lemma returnUpdateLocals_rsim : forall pinfo TD i0 n c t v p Result lc2 lc2' gl2 
  lc2'' F F' lc1' lc1
  (Hntmp: if fdef_dec (PI_f pinfo) F then value_has_no_tmps pinfo Result 
          else True)
  (H1 : Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc2
         lc2' gl2 = ret lc2'')
  (Hrsim : reg_simulation pinfo F lc1 lc2)
  (Hrsim' : reg_simulation pinfo F' lc1' lc2'),
  exists lc1'',
    Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc1 lc1' gl2 
      = ret lc1'' /\ reg_simulation pinfo F' lc1'' lc2''.
Proof.
  unfold Opsem.returnUpdateLocals in *.
  intros.
  inv_mbind'.
  erewrite simulation__getOperandValue; eauto. 
  rewrite <- HeqR. 
  destruct n; inv H0; eauto.
    destruct t; tinv H1.
    inv_mbind'.
    exists (updateAddAL (GVsT DGVs) lc1' i0 g0).
    split; auto.
      unfold reg_simulation in *.
      destruct (fdef_dec (PI_f pinfo) F'); subst; auto.
        intros.
        apply Hrsim' in H.
        destruct (id_dec i0 i1); subst.
          repeat rewrite lookupAL_updateAddAL_eq. auto.
          repeat rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Ltac solve_tmnInFdefBlockB :=
match goal with
| Heqb1 : exists _, exists _, exists _,
            ?B1 = block_intro _ _ _ ?tmn,
  HBinF : blockInFdefB ?B1 ?F1 = true |- 
  terminatorInBlockB ?tmn ?B1 && blockInFdefB ?B1 ?F1 = true =>
    destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst;
    simpl;
    apply andb_true_iff;
    split; try solve [auto | apply terminatorEqB_refl]
end.

Ltac destruct_ctx_return :=
match goal with
| [Hsim : State_simulation _ ?Cfg1 ?St1 
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           Opsem.ECS := {|
                          Opsem.CurFunction := ?F;
                          Opsem.CurBB := _;
                          Opsem.CurCmds := nil;
                          Opsem.Terminator := _;
                          Opsem.Locals := _;
                          Opsem.Allocas := _ |}
                          :: {|
                             Opsem.CurFunction := ?F';
                             Opsem.CurBB := _;
                             Opsem.CurCmds := ?c' :: _;
                             Opsem.Terminator := _;
                             Opsem.Locals := _;
                             Opsem.Allocas := _ |} :: _;
           Opsem.Mem := _ |} |- _] =>
  destruct Cfg1 as [S1 TD1 Ps1 gl1 fs1];
  destruct St1 as [ECs1 M1];
  destruct TD1 as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs1 as [|[F1 B1 cs1 tmn1 lc1 als1] ECs1];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct ECs1 as [|[F1' B1' cs1' tmn1' lc1' als1'] ECs1];
    try solve [inversion HsimECs];
  destruct HsimECs as [HsimEC' HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hbsim [Heqb1 [Heqb2     
    [Hrsim Htcmds]]]]]]]]]; subst;
  destruct c'; try solve [inversion HsimEC'];
  destruct HsimEC' as [HBinF' [HFinPs' [Htfdef' [Heq0' [Heq1' [Hbsim' 
    [Heqb1' [Heqb2' [Hrsim' Htcmds']]]]]]]]]; subst;
  fold ECs_simulation_tail in HsimECs
end.

Ltac cmds_simulation_stable_tac :=
match goal with
| H3 : _ ++ [_] = _ ++ _ :: nil |- _ =>
      apply app_inj_tail in H3;
      destruct H3; subst; solve_is_temporary
end.

Hint Unfold block_simulation: ppbsim.

Lemma cmds_simulation_stable: forall pinfo TD Mem lc' F1' l1 ps1 cs11 c cs1'0 
  tmn' cs' lc'' Mem' l2 ps2 cs21 (Hwfpi: WF_PhiInfo pinfo)
  (Hin : blockInFdefB (block_intro l1 ps1 (cs11 ++ c :: cs1'0) tmn') F1' = true)
  (Hbsim: block_simulation pinfo F1' 
    (block_intro l1 ps1 (cs11 ++ c :: cs1'0) tmn') 
    (block_intro l2 ps2 (cs21 ++ c :: cs') tmn')),
  cmds_simulation pinfo TD Mem lc' F1' 
    (block_intro l1 ps1 (cs11 ++ c :: cs1'0) tmn') 
    cs1'0 cs' ->
  cmds_simulation pinfo TD Mem' lc'' F1' 
    (block_intro l1 ps1 (cs11 ++ c :: cs1'0) tmn') 
    cs1'0 cs'.
Proof.
  autounfold with ppbsim. simpl.
  intros.
  destruct (fdef_dec (PI_f pinfo) F1'); subst; auto.
  remember ((PI_newids pinfo) ! l1) as R.
  destruct R as [[[]]|]; auto.
  destruct H as [J1 [J2 J3]].
  split; intros.
    symmetry in H.
    apply app_cons_is_larger in H. inv H.
  split; auto.
    intros; subst.
    destruct ((PI_succs pinfo) ! l1) as [succs|]; try congruence.
    destruct succs; try congruence.
    destruct Hwfpi as [Hwfpi1 [Hwfpi2 [Hwfpi3 [Hwfpi4 Hwfpi5]]]]; subst.
    assert (Hit: is_temporary
      (getCmdLoc (insn_load i0 (PI_typ pinfo) (value_id (PI_id pinfo)) 
        (PI_align pinfo)))
      (fst (gen_fresh_ids (PI_rd pinfo) (getFdefLocs (PI_f pinfo))))).
      simpl.
      exists l1. rewrite <- Hwfpi5. rewrite <- HeqR.
      left.
      destruct (i0 == i0); simpl; auto; try congruence.

    destruct ((PI_preds pinfo) ! l1)
      as [[]|]; inv Hbsim; try cmds_simulation_stable_tac.

      rewrite_env 
        ((insn_store i2 (PI_typ pinfo) (value_id i1) (value_id (PI_id pinfo))
         (PI_align pinfo) ::
         cs11 ++ c :: nil) ++
        [insn_load i0 (PI_typ pinfo) (value_id (PI_id pinfo)) (PI_align pinfo)]) 
        in H3.
      cmds_simulation_stable_tac.
Qed.     

Lemma cmds_simulation_tail_stable: forall pinfo TD Mem lc' F1' l1 ps1 cs11 c 
  cs12 tmn' cs' lc'' Mem' l2 ps2 cs21 (Hwfpi: WF_PhiInfo pinfo)
  (Hnt : isnt_ldst c)
  (Hin : blockInFdefB (block_intro l1 ps1 (cs11 ++ cs12) tmn') F1' = true)
  (Hbsim: block_simulation pinfo F1' 
    (block_intro l1 ps1 (cs11 ++ cs12) tmn') 
    (block_intro l2 ps2 (cs21 ++ c :: cs') tmn')),
  cmds_simulation pinfo TD Mem lc' F1' 
    (block_intro l1 ps1 (cs11 ++ cs12) tmn') 
    cs12 (c::cs') ->
  cmds_simulation pinfo TD Mem' lc'' F1' 
    (block_intro l1 ps1 (cs11 ++ cs12) tmn') 
    cs12 (c::cs').
Proof.
  autounfold with ppbsim. simpl.
  intros.
  destruct (fdef_dec (PI_f pinfo) F1'); subst; auto.
  remember ((PI_newids pinfo) ! l1) as R.
  destruct R as [[[]]|]; auto.
  destruct H as [J1 [J2 J3]].
  split; intros.
    assert (W:=H).
    apply app_inv_tail_nil in H. subst cs11.
    apply J1 in W. clear J1.
    destruct W as [W1 W2].
    split; auto.
      intros W3 W4.
      destruct ((PI_preds pinfo) ! l1) as [[]|]; try congruence.
      clear J2 J3.
      destruct W1 as [W1 | [[ W1' W1] | [_ [_ W1]]]].
        inv W1. inv Hnt.

        rewrite W1 in Hbsim.
        simpl_env in Hbsim.
        inv Hbsim.
        simpl_env in H2.
        apply app_inv_tail in H2; subst.    
        inv W4. inv Hnt.

        inv W1.

  split; auto.
    intros; subst.
    destruct ((PI_succs pinfo) ! l1) as [succs|]; try congruence.
Qed.     

Lemma EC_simulation_tail_stable: forall TD Ps1 pinfo Mem Mem' EC1 EC2
  (Hwfpi: WF_PhiInfo pinfo)
  (H: EC_simulation_tail TD Ps1 pinfo EC1 EC2 Mem),
  EC_simulation_tail TD Ps1 pinfo EC1 EC2 Mem'.
Proof.
  destruct EC1. destruct EC2. destruct TD. intros.
  destruct CurCmds0 as [|[]]; simpl; auto.
  destruct H as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
  repeat split; auto.
    destruct J7 as [l1 [ps1 [cs11 J7]]]; subst.
    destruct J8 as [l2 [ps2 [cs21 J8]]]; subst.
    eapply cmds_simulation_tail_stable; simpl; eauto.
Qed.

Lemma ECs_simulation_tail_stable: forall TD Ps1 pinfo Mem Mem' ECs1 ECs2
  (Hwfpi: WF_PhiInfo pinfo),
  ECs_simulation_tail TD Ps1 pinfo ECs1 ECs2 Mem ->
  ECs_simulation_tail TD Ps1 pinfo ECs1 ECs2 Mem'.
Proof.
  induction ECs1; destruct ECs2; simpl; intros; auto.
    destruct H.
    split; eauto.
      eapply EC_simulation_tail_stable; eauto.
Qed.

Definition noalias_EC (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (ec:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
if (fdef_dec (PI_f pinfo) f) then wf_defs maxb pinfo TD M lc als else True.

Lemma noalias_State__noalias_EC: forall maxb pinfo Cfg EC ECs Mem,
  Promotability.wf_State maxb pinfo Cfg 
    {| Opsem.ECS := EC :: ECs; Opsem.Mem := Mem |} ->
  noalias_EC maxb pinfo (OpsemAux.CurTargetData Cfg) Mem EC.
Proof.
  intros. destruct Cfg.
  destruct H as [[J1 _] _].
  destruct EC. destruct J1 as [J1 _].
  simpl. auto.
Qed.

Ltac destruct_ctx_br :=
match goal with
| [Hsim : State_simulation _ ?Cfg1 ?St1
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           Opsem.ECS := {|
                          Opsem.CurFunction := ?F;
                          Opsem.CurBB := _;
                          Opsem.CurCmds := nil;
                          Opsem.Terminator := _;
                          Opsem.Locals := _;
                          Opsem.Allocas := _ |} :: _;
           Opsem.Mem := _ |} |- _] =>
  destruct Cfg1 as [S1 TD1 Ps1 gl1 fs1];
  destruct St1 as [ECs1 M1];
  destruct TD1 as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs1 as [|[F1 B1 cs1 tmn1 lc1 als1] ECs1];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hbsim [Heqb1 [Heqb2
    [Hrsim Htcmds]]]]]]]]]; subst
end.

Lemma blockInFdefB_sim__block_sim : forall pinfo f1 f2 b2 
  (Hwfpi: WF_PhiInfo pinfo),
  fdef_simulation pinfo f1 f2 ->
  blockInFdefB b2 f2 ->
  exists b1,
    blockInFdefB b1 f1 /\ block_simulation pinfo f1 b1 b2.
Proof.
  unfold fdef_simulation, block_simulation.
  destruct f1, f2. simpl.
  intros.
  destruct (fdef_dec (PI_f pinfo) (fdef_intro f b)).
    destruct f. 
    remember (gen_fresh_ids (PI_rd pinfo) (getArgsIDs a ++ getBlocksLocs b)) 
      as R.
    destruct R. inv H.
    destruct Hwfpi as [J1 [J2 [J3 [J4 J5]]]].
    rewrite e in J5. simpl in J5.
    rewrite <- HeqR in J5. simpl in J5. subst.
    clear e HeqR.
    unfold phinodes_placement_blocks in H0.
    clear f t i0 a v l0.
    induction b; simpl in *.
      congruence. 

      apply orb_true_iff in H0.
      destruct H0 as [H0 | H0].
        apply blockEqB_inv in H0. subst.
        exists a.
        split; auto.
          apply orb_true_iff. left. apply blockEqB_refl.
      
        apply IHb in H0.
        destruct H0 as [b1 [J5 J6]].
        subst.
        exists b1.
        split; auto.
          apply orb_true_iff; auto.

    inv H. eauto.
Qed.

Hint Unfold phinodes_placement_block : ppbsim.

Lemma block_simulation__inv: forall pinfo f l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2,
  block_simulation pinfo f (block_intro l1 ps1 cs1 tmn1)
     (block_intro l2 ps2 cs2 tmn2) ->
  l1 = l2 /\ tmn1 = tmn2.
Proof.
  unfold block_simulation, phinodes_placement_block.
  intros.
  destruct (fdef_dec (PI_f pinfo) f).
    destruct (PI_newids pinfo) ! l1 as [[[]]|]; inv H; auto.
    destruct (PI_preds pinfo) ! l1 as [[]|]; inv H1; auto.

    inv H. auto.
Qed.

Lemma phinodes_placement_blocks__getBlocksLabels: forall pid t al nids succs 
  preds bs,
  getBlocksLabels bs = 
  getBlocksLabels (phinodes_placement_blocks bs pid t al nids succs preds).
Proof.
  induction bs as [|[]]; simpl; intros; auto.
    rewrite <- IHbs.
    destruct (nids ! l0) as [[[]]|]; auto.
    destruct (preds ! l0) as [[]|]; auto.
Qed.

Lemma phinodes_placement_block__getBlockLocs_aux: forall pid t al nids succs 
  preds
  (Hprop1: forall l0 lib pid sid, nids ! l0 = Some (lib, pid, sid) -> 
           lib <> pid /\ lib <> sid /\ pid <> sid)
  b prefix suffix
  (Hprop2: forall i0, is_temporary i0 nids -> 
           ~ In i0 (prefix ++ getBlockLocs b ++ suffix))
  (Hndup: NoDup (prefix ++ getBlockLocs b ++ suffix)),
  NoDup (prefix ++ 
         getBlockLocs (phinodes_placement_block pid t al nids succs preds b) ++
         suffix).
Proof.
  intros.
  unfold phinodes_placement_block.
  destruct b as [l0 p c t0]. simpl in Hndup, Hprop2.
  simpl_env in Hndup. simpl_env in Hprop2.
  remember (nids ! l0) as R.
  destruct R as [[[i1 i2] i3]|]; simpl; simpl_env; auto.
  assert (HeqR' := HeqR).
  symmetry in HeqR'.
  apply Hprop1 in HeqR'.
  destruct HeqR' as [Hneq1 [Hneq2 Hneq3]].
 
  assert (~ In i1 (prefix ++ getPhiNodesIDs p ++ getCmdsLocs c ++ 
                   [getTerminatorID t0] ++ suffix)) as Hnotin1.
    apply Hprop2.
    exists l0. rewrite <- HeqR.
    destruct (i1 == i1); try congruence.
      simpl. left. reflexivity.

  assert (~ In i2 (prefix ++ getPhiNodesIDs p ++ getCmdsLocs c ++ 
                   [getTerminatorID t0] ++ suffix)) as Hnotin2.
    apply Hprop2. 
    exists l0. rewrite <- HeqR.
    destruct (i2 == i2); try congruence.
      simpl. right. left. reflexivity.

  assert (~ In i3 (prefix ++ getPhiNodesIDs p ++ getCmdsLocs c ++ 
                   [getTerminatorID t0] ++ suffix)) as Hnotin3.
    apply Hprop2. 
    exists l0. rewrite <- HeqR.
    destruct (i3 == i3); try congruence.
      simpl. right. right. reflexivity.

  assert (NoDup
     (prefix ++ getPhiNodesIDs p ++
      getCmdsLocs c ++ i1 :: [getTerminatorID t0] ++ suffix)) as Hnodup1.
    rewrite_env 
      ((prefix ++ getPhiNodesIDs p ++ getCmdsLocs c) ++ 
       i1 :: [getTerminatorID t0] ++ suffix).
    apply NoDup_insert; simpl_env; auto.

  assert(~ In i3
     (prefix ++ [i2] ++ getPhiNodesIDs p ++
      getCmdsLocs c ++ [getTerminatorID t0] ++ suffix)) as Hnotin4.
      intro G. simpl_env in G.
      apply Hnotin3.
      apply in_or_app.
      apply in_app_or in G.
      destruct G as [G | G]; auto.
      right.
      simpl in G.
      destruct G as [G | G]; subst; try congruence.
      auto.

  assert (NoDup (prefix ++ [i2] ++
      getPhiNodesIDs p ++ [i3] ++ getCmdsLocs c ++ 
      [getTerminatorID t0] ++ suffix)) as Hnodup2.
    rewrite_env 
        ((prefix ++ [i2] ++ getPhiNodesIDs p) ++ 
          i3 :: getCmdsLocs c ++ [getTerminatorID t0] ++ suffix).
    apply NoDup_insert; simpl_env; auto.
      simpl.
      rewrite_env 
        (prefix ++ i2 :: getPhiNodesIDs p ++ 
           getCmdsLocs c ++ [getTerminatorID t0] ++ suffix).
      apply NoDup_insert; auto.

  remember (preds ! l0) as R1.
  remember (succs ! l0) as R2.

  assert (
   NoDup
     (prefix ++ getBlockLocs
        (block_intro l0 p
           (c ++
            match R2 with
            | ret nil => nil
            | ret (_ :: _) => [insn_load i1 t (value_id pid) al]
            | merror => nil
            end) t0) ++ suffix)) as Hnodup3.
    destruct R2 as [[]|]; simpl; simpl_env; auto.
      rewrite getCmdsLocs_app. simpl. simpl_env. auto.

  destruct R1 as [[]|]; auto.
    destruct R2 as [[]|]; simpl; simpl_env; auto.

      rewrite getCmdsLocs_app. simpl. simpl_env.
      rewrite_env 
        ((prefix ++ [i2] ++ getPhiNodesIDs p) ++ 
          i3 :: getCmdsLocs c ++ [i1] ++ [getTerminatorID t0] ++ suffix).
      apply NoDup_insert.
        simpl in Hnodup3.
        rewrite getCmdsLocs_app in Hnodup3. simpl in Hnodup3.
        simpl_env in Hnodup3. 
        rewrite_env 
          (prefix ++ i2:: getPhiNodesIDs p ++ 
             getCmdsLocs c ++ [i1] ++ [getTerminatorID t0] ++ suffix).
        apply NoDup_insert; simpl_env; auto.
          intro G.
          apply Hnotin2.
          apply in_or_app.
          apply in_app_or in G.
          destruct G as [G | G]; auto. 
          right.
          apply in_or_app.
          apply in_app_or in G.
          destruct G as [G | G]; auto. 
          right. 
          apply in_or_app.
          apply in_app_or in G.
          destruct G as [G | G]; auto. 
          right. 
          apply in_or_app.
          simpl in G.
          destruct G as [G | G]; try congruence.
          simpl.
          destruct G as [G | G]; auto. 

        simpl_env.
        intro G.
        apply Hnotin3. 
        apply in_or_app.
        apply in_app_or in G.
        destruct G as [G | G]; auto. 
        right. 
        simpl in G.
        destruct G as [G | G]; try congruence.
        apply in_or_app.
        apply in_app_or in G.
        destruct G as [G | G]; auto. 
        right.
        apply in_or_app.
        apply in_app_or in G.
        destruct G as [G | G]; auto. 
        right. inv G; auto. congruence.
Qed.

Lemma phinodes_placement_block__getBlockLocs: forall pid t al nids succs 
  preds
  (Hprop1: forall l0 lib pid sid, nids ! l0 = Some (lib, pid, sid) -> 
           lib <> pid /\ lib <> sid /\ pid <> sid)
  b
  (Hprop2: forall i0, is_temporary i0 nids -> ~ In i0 (getBlockLocs b))
  (Hndup: NoDup (getBlockLocs b)),
  NoDup (getBlockLocs (phinodes_placement_block pid t al nids succs preds b)).
Proof.
  intros.
  rewrite_env (nil ++ 
    getBlockLocs (phinodes_placement_block pid t al nids succs preds b) ++ nil).
  apply phinodes_placement_block__getBlockLocs_aux; simpl_env; auto.
Qed.

Lemma uniqFdef__block_simulation__uniqBlockLocs: forall pinfo F b1 b2,
  WF_PhiInfo pinfo ->
  uniqFdef F ->
  blockInFdefB b1 F = true ->
  block_simulation pinfo F b1 b2 ->
  NoDup (getBlockLocs b2).
Proof.
  intros.
  assert (H1':=H1).
  destruct H as [J1 [J2 [J3 [J4 J5]]]].
  apply uniqFdef__uniqBlockLocs in H1; auto.
  unfold block_simulation in H2.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  assert(
    forall (i0 : id),
      is_temporary i0 (PI_newids pinfo) -> ~ In i0 (getFdefLocs (PI_f pinfo))
    ) as J.
    replace (PI_newids pinfo) with
        (fst (gen_fresh_ids (PI_rd pinfo) (getFdefLocs (PI_f pinfo)))).
    intros. apply gen_fresh_ids__spec in H; auto.
  assert (forall l0 lib pid sid, 
          (PI_newids pinfo) ! l0 = Some (lib, pid, sid) -> 
          lib <> pid /\ lib <> sid /\ pid <> sid) as Hprop1.
    replace (PI_newids pinfo) with
        (fst (gen_fresh_ids (PI_rd pinfo) (getFdefLocs (PI_f pinfo)))).
    intros. eapply gen_fresh_ids__spec3; eauto.
  destruct (PI_f pinfo) as [[] bs]. simpl in *.
  assert (forall i0,
     ~ In i0 (getArgsIDs a ++ getBlocksLocs bs) ->  ~ In i0 (getBlockLocs b1)
    ) as J'.
    intros.
    eapply notin_getBlocksLocs__notin_getBlockLocs; eauto.
    intro W. apply H. apply in_or_app. auto.
  apply phinodes_placement_block__getBlockLocs; auto.
Qed.

Lemma phinodes_placement_blocks__getBlocksLocs: forall pid t al nids succs 
  preds rds exids (Heq: fst (gen_fresh_ids rds exids) = nids)
  (Hprop1: forall l0 lib pid sid, nids ! l0 = Some (lib, pid, sid) -> 
           lib <> pid /\ lib <> sid /\ pid <> sid)
  bs prefix (Huniq: NoDup (getBlocksLabels bs))
  (Hprop2: forall i0, is_temporary i0 nids -> 
           ~ In i0 (prefix ++ getBlocksLocs bs)),
  NoDup (prefix ++ getBlocksLocs bs) -> 
  NoDup (prefix ++ 
         getBlocksLocs (phinodes_placement_blocks bs pid t al nids succs preds)).
Proof.
  induction bs; simpl; intros; auto.

  rewrite_env ((prefix ++ getBlockLocs a) ++ getBlocksLocs bs) in H.
  rewrite_env ((prefix ++ getBlockLocs a) ++ getBlocksLocs bs) in Hprop2.
  destruct a as [l0 p c t0]. simpl in H, Hprop2.
  inv Huniq.
  apply IHbs in H; auto. clear IHbs.
  simpl_env in H.

  unfold phinodes_placement_block.
  simpl_env in H. simpl_env in Hprop2.
  remember ((fst (gen_fresh_ids rds exids)) ! l0) as R.
  destruct R as [[[i1 i2] i3]|]; simpl; simpl_env; auto.
  assert (HeqR' := HeqR).
  symmetry in HeqR'.
  apply Hprop1 in HeqR'.
  destruct HeqR' as [Hneq1 [Hneq2 Hneq3]].
 
  assert (~ In i1 (prefix ++ getPhiNodesIDs p ++ getCmdsLocs c ++ 
    [getTerminatorID t0] ++ 
    getBlocksLocs (phinodes_placement_blocks bs pid t al 
      (fst (gen_fresh_ids rds exids)) succs preds)
    )) as Hnotin1.
    assert (is_temporary i1 (fst (gen_fresh_ids rds exids))) as Histmp.
      exists l0. rewrite <- HeqR.
      destruct (i1 == i1); try congruence.
        simpl. left. reflexivity.
    apply Hprop2 in Histmp.
    intro G.
    apply Histmp. 
    solve_in_prefix.
    eapply phinodes_placement_blocks__disjoint_tmps in G; eauto.
      eapply gen_fresh_ids__spec4; eauto.

  assert (~ In i2 (prefix ++ getPhiNodesIDs p ++ getCmdsLocs c ++ 
    [getTerminatorID t0] ++
    getBlocksLocs (phinodes_placement_blocks bs pid t al 
      (fst (gen_fresh_ids rds exids)) succs preds))) 
    as Hnotin2.
    assert (is_temporary i2 (fst (gen_fresh_ids rds exids))) as Histmp.
      exists l0. rewrite <- HeqR.
      destruct (i2 == i2); try congruence.
        simpl. right. left. reflexivity.
    apply Hprop2 in Histmp.
    intro G.
    apply Histmp. 
    solve_in_prefix.
    eapply phinodes_placement_blocks__disjoint_tmps in G; eauto.
      eapply gen_fresh_ids__spec4; eauto.

  assert (~ In i3 (prefix ++ getPhiNodesIDs p ++ getCmdsLocs c ++ 
    [getTerminatorID t0] ++ 
    getBlocksLocs (phinodes_placement_blocks bs pid t al 
      (fst (gen_fresh_ids rds exids)) succs preds))) 
    as Hnotin3.
    assert (is_temporary i3 (fst (gen_fresh_ids rds exids))) as Histmp.
      exists l0. rewrite <- HeqR.
      destruct (i3 == i3); try congruence.
        simpl. right. right. reflexivity.
    apply Hprop2 in Histmp.
    intro G.
    apply Histmp. 
    solve_in_prefix.
    eapply phinodes_placement_blocks__disjoint_tmps in G; eauto.
      eapply gen_fresh_ids__spec4; eauto.

  assert (NoDup
     (prefix ++ getPhiNodesIDs p ++
      getCmdsLocs c ++ i1 :: [getTerminatorID t0] ++ 
      getBlocksLocs (phinodes_placement_blocks bs pid t al 
        (fst (gen_fresh_ids rds exids)) succs preds))) 
    as Hnodup1.
    rewrite_env 
      ((prefix ++ getPhiNodesIDs p ++ getCmdsLocs c) ++ 
       i1 :: [getTerminatorID t0] ++ 
       getBlocksLocs (phinodes_placement_blocks bs pid t al 
         (fst (gen_fresh_ids rds exids)) succs preds)).
    apply NoDup_insert; simpl_env; auto.

  assert(~ In i3
     (prefix ++ [i2] ++ getPhiNodesIDs p ++
      getCmdsLocs c ++ [getTerminatorID t0] ++ 
      getBlocksLocs (phinodes_placement_blocks bs pid t al 
        (fst (gen_fresh_ids rds exids)) succs preds)))
    as Hnotin4.
    intro G. simpl_env in G.
    apply Hnotin3.
    solve_in_prefix.
    simpl in G.
    destruct G as [G | G]; subst; try congruence.
    auto.

  assert (NoDup (prefix ++ [i2] ++
      getPhiNodesIDs p ++ [i3] ++ getCmdsLocs c ++ 
      [getTerminatorID t0] ++ 
      getBlocksLocs (phinodes_placement_blocks bs pid t al 
        (fst (gen_fresh_ids rds exids)) succs preds))) 
    as Hnodup2.
    rewrite_env 
      ((prefix ++ [i2] ++ getPhiNodesIDs p) ++ 
        i3 :: getCmdsLocs c ++ [getTerminatorID t0] ++
        getBlocksLocs (phinodes_placement_blocks bs pid t al 
          (fst (gen_fresh_ids rds exids)) succs preds)).
    apply NoDup_insert; simpl_env; auto.
      simpl.
      rewrite_env 
        (prefix ++ i2 :: getPhiNodesIDs p ++ 
         getCmdsLocs c ++ [getTerminatorID t0] ++ 
         getBlocksLocs (phinodes_placement_blocks bs pid t al 
           (fst (gen_fresh_ids rds exids)) succs preds)).
      apply NoDup_insert; auto.

  remember (preds ! l0) as R1.
  remember (succs ! l0) as R2.

  assert (
   NoDup
     (prefix ++ getBlockLocs
        (block_intro l0 p
           (c ++
            match R2 with
            | ret nil => nil
            | ret (_ :: _) => [insn_load i1 t (value_id pid) al]
            | merror => nil
            end) t0) ++ 
      getBlocksLocs (phinodes_placement_blocks bs pid t al 
        (fst (gen_fresh_ids rds exids)) succs preds))) 
    as Hnodup3.
    destruct R2 as [[]|]; simpl; simpl_env; auto.
      rewrite getCmdsLocs_app. simpl. simpl_env. auto.

  destruct R1 as [[]|]; auto.
    destruct R2 as [[]|]; simpl; simpl_env; auto.

      rewrite getCmdsLocs_app. simpl. simpl_env.
      rewrite_env 
        ((prefix ++ [i2] ++ getPhiNodesIDs p) ++ 
          i3 :: getCmdsLocs c ++ [i1] ++ [getTerminatorID t0] ++
          getBlocksLocs (phinodes_placement_blocks bs pid t al 
            (fst (gen_fresh_ids rds exids)) succs preds
        )).
      apply NoDup_insert.
        simpl in Hnodup3.
        rewrite getCmdsLocs_app in Hnodup3. simpl in Hnodup3.
        simpl_env in Hnodup3. 
        rewrite_env 
         (prefix ++ i2:: getPhiNodesIDs p ++ 
         getCmdsLocs c ++ [i1] ++ [getTerminatorID t0] ++ 
         getBlocksLocs (phinodes_placement_blocks bs pid t al 
           (fst (gen_fresh_ids rds exids)) succs preds)).
        apply NoDup_insert; simpl_env; auto.
          intro G.
          apply Hnotin2.
          solve_in_prefix.
          simpl in G.
          destruct G as [G | G]; try congruence.
          simpl. auto.

        simpl_env.
        intro G.
        apply Hnotin3. 
        solve_in_prefix.
        simpl in G.
        destruct G as [G | G]; try congruence.
        solve_in_prefix.
        simpl. simpl in G.
        destruct G as [G | G]; try congruence.
Qed.

Lemma fdef_simulation__uniqFdef : forall pinfo f1 f2 (Hwfpi: WF_PhiInfo pinfo),
  uniqFdef f1 -> fdef_simulation pinfo f1 f2 -> uniqFdef f2.
Proof.
  unfold fdef_simulation.
  destruct f1 as [[fa1 t1 fid1 la1 va1] bs1], 
           f2 as [[fa2 t2 fid2 la2 va2] bs2]. 
  simpl.
  intros.
  destruct (fdef_dec (PI_f pinfo) 
             (fdef_intro (fheader_intro fa1 t1 fid1 la1 va1) bs1)).
    remember (gen_fresh_ids (PI_rd pinfo) 
      (getArgsIDs la1 ++ getBlocksLocs bs1)) as R.
    destruct R. inv H0.
    destruct Hwfpi as [J1 [J2 [J3 [J4 J5]]]].
    rewrite e in J5. simpl in J5.
    rewrite <- HeqR in J5. simpl in J5. subst.
    unfold uniqBlocks in *.
    destruct H as [[H1 H2] H3].
    rewrite <- phinodes_placement_blocks__getBlocksLabels; auto.
    assert (forall l0 lib pid sid, 
              (fst (gen_fresh_ids (PI_rd pinfo) 
                 (getArgsIDs la2 ++ getBlocksLocs bs1))) ! l0 = 
                    Some (lib, pid, sid) -> 
              lib <> pid /\ lib <> sid /\ pid <> sid) as Hprop1.
      intros. eapply gen_fresh_ids__spec3; eauto.
    assert (forall i0, 
              is_temporary i0 (fst (gen_fresh_ids (PI_rd pinfo) 
                 (getArgsIDs la2 ++ getBlocksLocs bs1))) -> 
              ~ In i0 (getArgsIDs la2 ++ getBlocksLocs bs1)) as Hprop2.
      intros. eapply gen_fresh_ids__spec; eauto.
    eapply phinodes_placement_blocks__getBlocksLocs in H3; eauto.
    replace (PI_newids pinfo) with
      (fst (gen_fresh_ids (PI_rd pinfo) 
        (getArgsIDs la2 ++ getBlocksLocs bs1))).
      split; eauto.
      apply NoDup_inv in H3. destruct H3.
      split; auto.

      rewrite <- HeqR. auto.

    inv H0. auto.
Qed.

Lemma lookup_fdef_sim__block_sim : forall pinfo f1 f2 l0 b2 (Huniq: uniqFdef f1)
  (Hwfpi: WF_PhiInfo pinfo),
  fdef_simulation pinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  exists b1,
    lookupBlockViaLabelFromFdef f1 l0 = Some b1 /\
    block_simulation pinfo f1 b1 b2.
Proof.
  intros.
  destruct b2.
  apply lookupBlockViaLabelFromFdef_inv in H0; 
    eauto using fdef_simulation__uniqFdef.
  destruct H0 as [J1 J2]; subst.
  eapply blockInFdefB_sim__block_sim in J2; eauto.
  destruct J2 as [b1 [J1 J2]].
  exists b1.
  split; auto.
    destruct b1.
    apply block_simulation__inv in J2.
    destruct J2 as [J21 J22]; subst.
    apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.  
Qed.

Lemma block_simulation_neq_refl: forall pinfo F b,
  PI_f pinfo <> F ->
  block_simulation pinfo F b b.
Proof.
  intros.
  autounfold with ppbsim.
  destruct (fdef_dec (PI_f pinfo) F); try congruence.
Qed.

Lemma cmds_simulation_neq_refl: forall pinfo td M lc F b cs,
  PI_f pinfo <> F ->
  cmds_simulation pinfo td M lc F b cs cs.
Proof.
  intros.
  autounfold with ppbsim.
  destruct (fdef_dec (PI_f pinfo) F); try congruence.
Qed.

Lemma reg_simulation__getIncomingValuesForBlockFromPHINodes_helper_aux: forall
  (pinfo : PhiInfo) (lc1 : DGVMap) (lc2 : DGVMap) (td : TargetData)
  (l1 : l) (t0 : terminator) (l3 : l) (p2 : phinodes) 
  (c2 : cmds) (t2 : terminator) (gl : GVMap) 
  (c : cmds) (p1 : phinodes) (c1 : cmds) (Hwfpi : WF_PhiInfo pinfo)
  ifs S m (HwfF: wf_fdef ifs S m (PI_f pinfo))
  (H : forall i0 : id,
       not_temporaries i0 (PI_newids pinfo) ->
       lookupAL (GVsT DGVs) lc1 i0 = lookupAL (GVsT DGVs) lc2 i0)
  (p0 ps : phinodes) (lc2' : list (id * GVsT DGVs))
  (H0 : Opsem.getIncomingValuesForBlockFromPHINodes td p0
         (block_intro l3 p2 c2 t2) gl lc2 = ret lc2')
  (HBinF : blockInFdefB (block_intro l1 (ps++p0) c t0) (PI_f pinfo) = true),
  exists lc1' : list (id * GVsT DGVs),
    Opsem.getIncomingValuesForBlockFromPHINodes td p0
      (block_intro l3 p1 c1 t2) gl lc1 = ret lc1' /\
    (forall i3 : id,
     not_temporaries i3 (PI_newids pinfo) ->
     lookupAL (GVsT DGVs) lc1' i3 = lookupAL (GVsT DGVs) lc2' i3).
Proof.
    induction p0 as [|[]]; simpl; intros.
      inv H0.
      exists nil. split; auto.

      inv_mbind'.
      rewrite_env ((ps ++ [insn_phi i0 t l0]) ++ p0) in HBinF.
      edestruct IHp0 with (ps:=ps++[insn_phi i0 t l0]) as [lc1' [J1 J2]]; eauto.
      rewrite J1.
      destruct v; simpl in *.
        rewrite H.
          rewrite <- HeqR0.
          exists ((i0,g)::lc1').
          split; auto.
            intros.
            simpl.
            destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i3 i0); 
              auto.

          eapply original_ids_in_phi_arent_temporaries in HBinF; eauto.
            simpl_env. simpl. eapply in_middle.

        rewrite <- HeqR0.
        exists ((i0,g)::lc1').
        split; auto.
          intros.
          simpl.
          destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i3 i0); 
            auto.
Qed.

Lemma reg_simulation__getIncomingValuesForBlockFromPHINodes_helper: forall
  (pinfo : PhiInfo) (lc1 : DGVMap) (lc2 : DGVMap) (td : TargetData)
  (l1 : l) (p0 : phinodes) (t0 : terminator) (l3 : l) (p2 : phinodes) 
  (c2 : cmds) (t2 : terminator) (gl : GVMap) (lc2' : list (id * GVsT DGVs))
  (c : cmds) (p1 : phinodes) (c1 : cmds) (Hwfpi : WF_PhiInfo pinfo)
  ifs S m (HwfF: wf_fdef ifs S m (PI_f pinfo))
  (H : forall i0 : id,
       not_temporaries i0 (PI_newids pinfo) ->
       lookupAL (GVsT DGVs) lc1 i0 = lookupAL (GVsT DGVs) lc2 i0)
  (H0 : Opsem.getIncomingValuesForBlockFromPHINodes td p0
         (block_intro l3 p2 c2 t2) gl lc2 = ret lc2')
  (HBinF : blockInFdefB (block_intro l1 p0 c t0) (PI_f pinfo) = true),
  exists lc1' : list (id * GVsT DGVs),
    Opsem.getIncomingValuesForBlockFromPHINodes td p0
      (block_intro l3 p1 c1 t2) gl lc1 = ret lc1' /\
    (forall i3 : id,
     not_temporaries i3 (PI_newids pinfo) ->
     lookupAL (GVsT DGVs) lc1' i3 = lookupAL (GVsT DGVs) lc2' i3).
Proof.
  intros.
  eapply reg_simulation__getIncomingValuesForBlockFromPHINodes_helper_aux
    with (ps:=nil); eauto.
Qed.

Lemma reg_simulation__getIncomingValuesForBlockFromPHINodes: forall pinfo F1 lc1 
  lc2 td b2 B2 gl lc2' b1 B1 (HBinF: blockInFdefB b1 F1 = true) 
  ifs S m (HwfF: wf_fdef ifs S m F1) (Hwfpi:WF_PhiInfo pinfo),
  reg_simulation pinfo F1 lc1 lc2 ->
  Opsem.getIncomingValuesForBlockFromPHINodes td (getPHINodesFromBlock b2) B2 gl 
    lc2 = ret lc2' ->
  block_simulation pinfo F1 b1 b2 ->
  block_simulation pinfo F1 B1 B2 ->
  exists lc1', 
    Opsem.getIncomingValuesForBlockFromPHINodes td (getPHINodesFromBlock b1) B1 
      gl lc1 = ret lc1' /\ reg_simulation pinfo F1 lc1' lc2'.
Proof.
  destruct b1, b2, B1, B2. simpl.  
  intros.
  apply block_simulation__inv in H2.
  destruct H2; subst.
  unfold block_simulation in H1.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F1); try subst F1.
    simpl in H1.
    remember ((PI_newids pinfo) ! l0) as R.
    destruct R as [[[]]|].
      destruct ((PI_preds pinfo) ! l0) as [[]|]; inv H1; try 
        eauto using reg_simulation__getIncomingValuesForBlockFromPHINodes_helper.

      simpl in H0.
      inv_mbind'.      
      eapply reg_simulation__getIncomingValuesForBlockFromPHINodes_helper 
        with (lc2':=l0) in H; eauto.
      destruct H as [lc1' [J1 J2]].
      exists lc1'.
      split; eauto.
        intros.
        simpl.
        destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i3 i1); auto.
          subst.
          assert (J := @H l1).
          rewrite <- HeqR in J. 
          destruct J. destruct H1; congruence.
      
      inv H1.
      eauto using reg_simulation__getIncomingValuesForBlockFromPHINodes_helper.
        
    inv H1.
    exists lc2'. 
    split; auto.
      rewrite <- H0.
      erewrite OpsemProps.getIncomingValuesForBlockFromPHINodes_eq; eauto.
Qed.

Lemma reg_simulation_refl: forall pinfo f lc,
  reg_simulation pinfo f lc lc.
Proof.
  unfold reg_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f); auto.
Qed.

Lemma reg_simulation__updateValuesForNewBlock: forall pinfo F1 lc1' lc2'
  (Hrsim': reg_simulation pinfo F1 lc1' lc2') lc1 lc2
  (Hrsim: reg_simulation pinfo F1 lc1 lc2),
  reg_simulation pinfo F1 (Opsem.updateValuesForNewBlock lc1 lc1')
    (Opsem.updateValuesForNewBlock lc2 lc2').
Proof.
  intros.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F1); subst; auto.
  intros i0 Hntmp.
  assert (Hntmp':=Hntmp).
  apply Hrsim in Hntmp.    
  apply Hrsim' in Hntmp'.
  clear Hrsim Hrsim'.
  generalize dependent lc2.
  generalize dependent lc2'.
  generalize dependent lc1'.
  induction lc1 as [|[]]; simpl; intros; auto.
    apply OpsemProps.updateValuesForNewBlock_spec5; auto.

    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i1); subst.
      rewrite lookupAL_updateAddAL_eq; auto.
      symmetry.
      apply OpsemProps.updateValuesForNewBlock_spec4; auto.

      rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma reg_simulation__switchToNewBasicBlock: forall pinfo F1 lc1 lc2 td b2 B2 gl
  lc2' b1 B1 (Hwfpi: WF_PhiInfo pinfo) (HBinF: blockInFdefB b1 F1 = true)
  ifs S m (HwfF: wf_fdef ifs S m F1),
  reg_simulation pinfo F1 lc1 lc2 ->
  Opsem.switchToNewBasicBlock td b2 B2 gl lc2 = ret lc2' ->
  block_simulation pinfo F1 b1 b2 ->
  block_simulation pinfo F1 B1 B2 ->
  exists lc1', 
    Opsem.switchToNewBasicBlock td b1 B1 gl lc1 = ret lc1' /\
    reg_simulation pinfo F1 lc1' lc2'.
Proof.
  intros.
  unfold Opsem.switchToNewBasicBlock in *.
  inv_mbind'. symmetry_ctx.
  eapply reg_simulation__getIncomingValuesForBlockFromPHINodes in HeqR; eauto.
  destruct HeqR as [lc1' [J1 J2]].
  rewrite J1.
  exists (Opsem.updateValuesForNewBlock lc1' lc1).
  split; auto using reg_simulation__updateValuesForNewBlock.
Qed.

Lemma phinodes_placement_is_correct__dsBranch: forall 
  (pinfo : PhiInfo) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (S : system) (TD : TargetData) (Ps : list product) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (bid : id) (Cond : value)
  (l1 : l) (l2 : l) (ECs : list Opsem.ExecutionContext) (Mem : mem) 
  (als : list mblock) maxb EC1 Cfg1 Cfg2 (Hwfpi: WF_PhiInfo pinfo)
  (Heq1: Cfg2 = {| OpsemAux.CurSystem := S;
                   OpsemAux.CurTargetData := TD;
                   OpsemAux.CurProducts := Ps;
                   OpsemAux.Globals := gl;
                   OpsemAux.FunTable := fs |})
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Heq2: EC1 = {| Opsem.CurFunction := F;
                  Opsem.CurBB := B;
                  Opsem.CurCmds := nil;
                  Opsem.Terminator := insn_br bid Cond l1 l2;
                  Opsem.Locals := lc;
                  Opsem.Allocas := als |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
            {| Opsem.ECS := EC1 :: ECs;
               Opsem.Mem := Mem |})
  (conds : GVsT DGVs) (c : GenericValue) (l' : l) (ps' : phinodes)
  (cs' : cmds) (tmn' : terminator) (lc' : Opsem.GVsMap)
  (H : Opsem.getOperandValue TD Cond lc gl = ret conds)
  (H0 : c @ conds)
  (H1 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (H2 : Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc =
       ret lc'),
  exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' trace_nil /\
     State_simulation pinfo Cfg1 St1' Cfg2
     {|Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := (block_intro l' ps' cs' tmn');
                       Opsem.CurCmds := cs';
                       Opsem.Terminator := tmn';
                       Opsem.Locals := lc';
                       Opsem.Allocas := als |} :: ECs;
       Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct_ctx_br.
  destruct Hwfpp as [_ [_ [_ [_ [[Hreachb _] _]]]]]; auto.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.

  assert (exists b1,
    (if isGVZero (los, nts) c
     then lookupBlockViaLabelFromFdef F1 l2
     else lookupBlockViaLabelFromFdef F1 l1) = Some b1 /\
    block_simulation pinfo F1 b1 (block_intro l' ps' cs' tmn')) as Hfind.
    symmetry in H1.
    destruct (isGVZero (los, nts) c); 
      eapply lookup_fdef_sim__block_sim in H1; eauto.
  destruct Hfind as [b1 [Hfind Htblock]].

  destruct Heqb1 as [l3 [ps3 [cs11 Heqb1]]]; subst.

  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.

  assert (isReachableFromEntry F1 b1) as Hreachb1.
    unfold isReachableFromEntry in *.
    destruct b1.
    destruct (isGVZero (los, nts) c); try solve [
      apply lookupBlockViaLabelFromFdef_inv in Hfind; auto;
      destruct Hfind as [Hfind _]; subst;
      eapply reachable_successors; eauto; simpl; auto].

  assert (Htcmds':=Htcmds).
  apply cmds_simulation_nil_inv in Htcmds'. subst.
  unfold cmds_simulation in Htcmds.

  assert (blockInFdefB b1 F1)as HBinF'.
    destruct F1 as [[f t i0 a v] bs]. 
    destruct HuniqF as [HuniqBlocks HuniqArgs].
    destruct b1.
    destruct (isGVZero (los,nts) c);
      apply genLabel2Block_blocks_inv with (f:=fheader_intro f t i0 a v) 
        in Hfind; auto; destruct Hfind; eauto.

  assert (exists lc1', 
    Opsem.switchToNewBasicBlock (los, nts) b1
      (block_intro l3 ps3 (cs11 ++ nil) (insn_br bid Cond l1 l2)) gl 
      lc1 = ret lc1' /\
    reg_simulation pinfo F1 lc1' lc') as Hswitch1.
    eapply reg_simulation__switchToNewBasicBlock; eauto.

  destruct Hswitch1 as [lc1' [Hswitch1 Hrsim']].

  unfold block_simulation, phinodes_placement_block in *.

  assert (Opsem.getOperandValue (los, nts) Cond lc1 gl = ret conds) as Hget.
    erewrite simulation__getOperandValue with (lc2:=lc); eauto.
    apply original_values_arent_tmps with 
      (instr:=insn_terminator (insn_br bid Cond l1 l2))
      (B:=block_intro l3 ps3 (cs11 ++ nil) (insn_br bid Cond l1 l2))
      (ifs:=nil) (S:=S1) (m:=module_intro los nts Ps1); simpl; auto.
      apply andb_true_iff.
      split; auto.
        apply terminatorEqB_refl.

  destruct (fdef_dec (PI_f pinfo) F1) as [ e | n]; try subst F1.
  SCase "F is tranformed".
    assert ((PI_newids pinfo) ! l3 <> None) as Hreach.
      apply reachable_blk_has_newids; subst; simpl; auto.

    remember ((PI_newids pinfo) ! l3) as R.
    destruct R as [[[lid pid] sid]|]; try congruence.
    destruct Htcmds as [_ [_ Htcmds]].
    assert (exists sc, exists scs, (PI_succs pinfo) ! l3 = Some (sc::scs)) 
      as R2.
      apply WF_PhiInfo__succs in HBinF; subst; simpl; auto; congruence.

    destruct R2 as [sc [scs Heq]].
    rewrite Heq in *.
    assert ([insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) 
               (PI_align pinfo)] <> nil) as Hwft.
      intro J. inv J.
    apply_clear Htcmds in Hwft.

    destruct b1 as [l0 ps0 cs0 tmn0].
    unfold phinodes_placement_block in Htblock.
    assert ((PI_newids pinfo) ! l0 <> None) as Hreach'.
      apply reachable_blk_has_newids; subst; simpl; auto.
    remember ((PI_newids pinfo) ! l0) as R1.
    destruct R1 as [[[lid' pid'] sid']|]; try congruence.
    assert (exists prd, exists prds, (PI_preds pinfo) ! l0 = Some (prd::prds))
      as R2.
      eapply WF_PhiInfo__preds in HBinF; subst; simpl; eauto.
        simpl in HBinF.
        destruct (PI_f pinfo) as [[f t i0 a v] bs]. 
        destruct HuniqF as [HuniqBlocks HuniqArgs].
        destruct (isGVZero (los,nts) c);
          apply genLabel2Block_blocks_inv 
            with (f:=fheader_intro f t i0 a v) in Hfind; auto;
            destruct Hfind; auto.

    destruct R2 as [prd [prds Heq']].
    simpl in H.
    rewrite Heq' in *. 
    inversion Htblock; subst l' ps' cs' tmn'. clear Htblock.

    unfold wf_tmp_value in Hwft. simpl in Hwft.
    destruct Hwft as [gvsa [gv [Hlkp1 [Hld Hlk2]]]].

    assert (lookupAL _ lc' pid' = Some gv /\
            lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa) as Hswitch2. 

      clear - Hbsim H2 Hrsim' Hlk2 HBinF' HuniqF Hwfpi HeqR1 Heq' HeqR Hfind 
        HBinF Hlkp1.

      assert (exists ps3', exists cs3', 
            B = block_intro l3 ps3' 
                  (cs3'++[insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) 
                  (PI_align pinfo)])
                  (insn_br bid Cond l1 l2)) as EQ.
        clear - Hbsim.
        subst.
        destruct ((PI_preds pinfo) ! l3) as [[]|]; simpl_env; eauto.
        simpl.
        exists ([gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) 
          ([l0] ++ l4)] ++ ps3).
        exists 
          ([insn_store sid (PI_typ pinfo) (value_id pid) (value_id (PI_id pinfo))
             (PI_align pinfo)] ++ cs11).
        simpl_env. auto.

      clear Hbsim.
      destruct EQ as [ps3' [cs3' EQ]]; subst B.
      eapply WF_PhiInfo_spec8 in Hfind; eauto.
      destruct Hfind as [succs [J1 J2]].
      eapply WF_PhiInfo__switchToNewBasicBlock; eauto.

    destruct Hswitch2 as [Hlka Hlkb].

    exists (Opsem.mkState 
             ((Opsem.mkEC (PI_f pinfo) (block_intro l0 ps0 cs0 tmn0) cs0 tmn0 
                lc1' als)::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_star.
      econstructor; eauto.

    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      SSSCase "bsim".
        autounfold with ppbsim. simpl.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite <- HeqR1. rewrite Heq'. auto.

      SSSCase "eq".
        exists l0. exists ps0. exists nil. auto.

      SSSCase "eq".
        exists l0. 
        exists (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo) (prd :: prds) 
                :: ps0).
        exists nil. simpl_env. auto.

      SSSCase "csim".
        autounfold with ppbsim.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite <- HeqR1. rewrite Heq'.
        split; intros.
          split; auto.
            intros. 
            unfold wf_tmp_value. simpl.
            exists gvsa. exists gv. repeat split; auto.
        split; intros; congruence.
        
  SCase "F isnt tranformed".
    subst b1.

    exists (Opsem.mkState 
             ((Opsem.mkEC F1 (block_intro l' ps' cs' tmn') cs' tmn' lc1' als)
              ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_star.
      econstructor; eauto.

    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      SSSCase "bsim".
        apply block_simulation_neq_refl; auto.

      SSSCase "eq".
        exists l'. exists ps'. exists nil. auto.

      SSSCase "eq".
        exists l'. exists ps'. exists nil. simpl_env. auto.

      SSSCase "csim".
        apply cmds_simulation_neq_refl; auto.
Qed.

Lemma phinodes_placement_is_correct__dsBranch_uncond: forall 
  (pinfo : PhiInfo) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (S : system) (TD : TargetData) (Ps : list product) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (bid : id) 
  (l0 : l) (ECs : list Opsem.ExecutionContext) (Mem : mem) 
  (als : list mblock) maxb EC1 Cfg1 Cfg2 (Hwfpi: WF_PhiInfo pinfo)
  (Heq1: Cfg2 = {| OpsemAux.CurSystem := S;
                   OpsemAux.CurTargetData := TD;
                   OpsemAux.CurProducts := Ps;
                   OpsemAux.Globals := gl;
                   OpsemAux.FunTable := fs |})
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Heq2: EC1 = {| Opsem.CurFunction := F;
                  Opsem.CurBB := B;
                  Opsem.CurCmds := nil;
                  Opsem.Terminator := insn_br_uncond bid l0;
                  Opsem.Locals := lc;
                  Opsem.Allocas := als |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
            {| Opsem.ECS := EC1 :: ECs;
               Opsem.Mem := Mem |})
  (l' : l) (ps' : phinodes)
  (cs' : cmds) (tmn' : terminator) (lc' : Opsem.GVsMap)
  (H1 : ret block_intro l' ps' cs' tmn' = lookupBlockViaLabelFromFdef F l0)
  (H2 : Opsem.switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc =
       ret lc'),
  exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' trace_nil /\
     State_simulation pinfo Cfg1 St1' Cfg2
     {|Opsem.ECS := {| Opsem.CurFunction := F;
                       Opsem.CurBB := (block_intro l' ps' cs' tmn');
                       Opsem.CurCmds := cs';
                       Opsem.Terminator := tmn';
                       Opsem.Locals := lc';
                       Opsem.Allocas := als |} :: ECs;
       Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct_ctx_br.
  destruct Hwfpp as [_ [_ [_ [_ [[Hreachb _] _]]]]]; auto.

  assert (HuniqF:=HFinPs).
  eapply wf_system__uniqFdef in HuniqF; eauto.

  assert (exists b1,
    lookupBlockViaLabelFromFdef F1 l0 = Some b1 /\
    block_simulation pinfo F1 b1 (block_intro l' ps' cs' tmn')) as Hfind.
    symmetry in H1.
    eapply lookup_fdef_sim__block_sim in H1; eauto.
  destruct Hfind as [b1 [Hfind Htblock]].

  destruct Heqb1 as [l3 [ps3 [cs11 Heqb1]]]; subst.

  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.

  assert (isReachableFromEntry F1 b1) as Hreachb1.
    unfold isReachableFromEntry in *.
    destruct b1.
    apply lookupBlockViaLabelFromFdef_inv in Hfind; auto.
    destruct Hfind as [Hfind _]; subst.
    eapply reachable_successors; eauto; simpl; auto.

  assert (Htcmds':=Htcmds).
  apply cmds_simulation_nil_inv in Htcmds'. subst.
  unfold cmds_simulation in Htcmds.
  unfold block_simulation, phinodes_placement_block in *.

  assert (blockInFdefB b1 F1)as HBinF'.
    destruct F1 as [[f t i0 a v] bs]. 
    destruct HuniqF as [HuniqBlocks HuniqArgs].
    destruct b1.
    apply genLabel2Block_blocks_inv with (f:=fheader_intro f t i0 a v) 
      in Hfind; auto; destruct Hfind; eauto.

  assert (exists lc1', 
    Opsem.switchToNewBasicBlock (los, nts) b1
      (block_intro l3 ps3 (cs11 ++ nil) (insn_br_uncond bid l0)) gl 
      lc1 = ret lc1' /\
    reg_simulation pinfo F1 lc1' lc') as Hswitch1.
    eapply reg_simulation__switchToNewBasicBlock; eauto.

  destruct Hswitch1 as [lc1' [Hswitch1 Hrsim']].

  destruct (fdef_dec (PI_f pinfo) F1) as [ e | n]; try subst F1.
  SCase "F is tranformed".
    assert ((PI_newids pinfo) ! l3 <> None) as Hreach.
      apply reachable_blk_has_newids; subst; simpl; auto.

    remember ((PI_newids pinfo) ! l3) as R.
    destruct R as [[[lid pid] sid]|]; try congruence.
    destruct Htcmds as [_ [_ Htcmds]].
    assert (exists sc, exists scs, (PI_succs pinfo) ! l3 = Some (sc::scs)) 
      as R2.
      apply WF_PhiInfo__succs in HBinF; subst; simpl; auto; congruence.

    destruct R2 as [sc [scs Heq]].
    rewrite Heq in *.
    assert ([insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) 
              (PI_align pinfo)] <> nil) as Hwft.
      intro J. inv J.
    apply_clear Htcmds in Hwft.

    destruct b1 as [l1 ps1 cs1 tmn1].
    unfold phinodes_placement_block in Htblock.
    assert ((PI_newids pinfo) ! l1 <> None) as Hreach'.
      apply reachable_blk_has_newids; subst; simpl; auto.

    remember ((PI_newids pinfo) ! l1) as R1.
    destruct R1 as [[[lid' pid'] sid']|]; try congruence.
    assert (exists prd, exists prds, (PI_preds pinfo) ! l1 = Some (prd::prds)) 
      as R2.
      eapply WF_PhiInfo__preds in HBinF; subst; simpl; eauto.
        simpl in HBinF.
        destruct (PI_f pinfo) as [[f t i0 a v] bs]. 
        destruct HuniqF as [HuniqBlocks HuniqArgs].
        apply genLabel2Block_blocks_inv 
          with (f:=fheader_intro f t i0 a v) in Hfind; auto;
          destruct Hfind; auto.

    destruct R2 as [prd [prds Heq']].
    rewrite Heq' in *. 
    inversion Htblock; subst l' ps' cs' tmn'. clear Htblock.

    unfold wf_tmp_value in Hwft. simpl in Hwft.
    destruct Hwft as [gvsa [gv [Hlkp1 [Hld Hlk2]]]].

    assert (lookupAL _ lc' pid' = Some gv /\
            lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa) as Hswitch2.

      clear - Hbsim H2 Hrsim' Hlk2 HBinF' HuniqF Hwfpi HeqR1 Heq' HeqR Hfind 
        HBinF Hlkp1.

      assert (exists ps3', exists cs3', 
            B = block_intro l3 ps3' 
                  (cs3'++[insn_load lid (PI_typ pinfo) (value_id (PI_id pinfo)) 
                  (PI_align pinfo)])
                  (insn_br_uncond bid l0)) as EQ.
        clear - Hbsim.
        subst.
        destruct ((PI_preds pinfo) ! l3) as [[]|]; simpl_env; eauto.
        simpl.
        exists ([gen_phinode pid (PI_typ pinfo) (PI_newids pinfo) 
          ([l1] ++ l2)] ++ ps3).
        exists 
          ([insn_store sid (PI_typ pinfo) (value_id pid) (value_id (PI_id pinfo))
             (PI_align pinfo)] ++ cs11).
        simpl_env. auto.

      clear Hbsim.
      destruct EQ as [ps3' [cs3' EQ]]; subst B.

      eapply WF_PhiInfo_spec9 in Hfind; eauto.
      destruct Hfind as [succs [J1 J2]].
      eapply WF_PhiInfo__switchToNewBasicBlock; eauto.

    destruct Hswitch2 as [Hlka Hlkb].

    exists (Opsem.mkState 
             ((Opsem.mkEC (PI_f pinfo) (block_intro l1 ps1 cs1 tmn1) cs1 tmn1 
              lc1' als)::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_star.
      econstructor; eauto.

    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      SSSCase "bsim".
        autounfold with ppbsim. simpl.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite <- HeqR1. rewrite Heq'. auto.

      SSSCase "eq".
        exists l1. exists ps1. exists nil. auto.

      SSSCase "eq".
        exists l1. 
        exists (gen_phinode pid' (PI_typ pinfo) (PI_newids pinfo) (prd :: prds) 
                  :: ps1).
        exists nil. simpl_env. auto.

      SSSCase "csim".
        autounfold with ppbsim. 
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite <- HeqR1. rewrite Heq'.
        split; intros.
          split; auto.
            intros. 
            unfold wf_tmp_value. simpl.
            exists gvsa. exists gv. repeat split; auto.
        split; intros; congruence.
        
  SCase "F isnt tranformed".
    subst b1.

    exists (Opsem.mkState 
             ((Opsem.mkEC F1 (block_intro l' ps' cs' tmn') cs' tmn' lc1' als)
              ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_star.
      econstructor; eauto.

    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      SSSCase "bsim".
        apply block_simulation_neq_refl; auto.

      SSSCase "eq".
        exists l'. exists ps'. exists nil. auto.

      SSSCase "eq".
        exists l'. exists ps'. exists nil. simpl_env. auto.

      SSSCase "csim".
        apply cmds_simulation_neq_refl; auto.
Qed.

Ltac destruct_ctx_other :=
match goal with
| [Hsim : State_simulation _ ?Cfg1 ?St1
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           Opsem.ECS := {|
                          Opsem.CurFunction := ?F;
                          Opsem.CurBB := _;
                          Opsem.CurCmds := _::_;
                          Opsem.Terminator := _;
                          Opsem.Locals := _;
                          Opsem.Allocas := _ |} :: _;
           Opsem.Mem := _ |} |- _] =>
  destruct Cfg1 as [S1 TD1 Ps1 gl1 fs1];
  destruct St1 as [ECs1 M1];
  destruct TD1 as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Heq2 
    [Heq3 Heq4]]]]]]]]; subst;
  destruct ECs1 as [|[F1 B1 cs1 tmn1 lc1 als1] ECs1];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct HsimEC as [HBinF [HFinPs [Htfdef [Heq0 [Heq1 [Hbsim [Heqb1 [Heqb2
    [Hrsim Htcmds]]]]]]]]]; subst
end.

Lemma reg_simulation__updateAddAL_tmp : forall pinfo lc1 lc2 lid gv2,
  reg_simulation pinfo (PI_f pinfo) lc1 lc2 ->
  is_temporary lid (PI_newids pinfo) ->
  reg_simulation pinfo (PI_f pinfo) lc1 (updateAddAL (GVsT DGVs) lc2 lid gv2).
Proof.
  intros.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  intros.
  destruct (id_dec lid i0); subst.
    apply temporaries_exclusive in H1; auto. 
    inv H1.
    
    rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma mload_gv2gvs: forall TD Mem mp PI_typ0 PI_align0 gv,
  mload TD Mem mp PI_typ0 PI_align0 = ret gv ->
  ($ gv # PI_typ0 $) = gv.
Admitted.

Lemma reg_simulation__updateAddAL : forall pinfo F lc1 lc2 lid gv,
  reg_simulation pinfo F lc1 lc2 ->
  reg_simulation pinfo F 
    (updateAddAL (GVsT DGVs) lc1 lid gv) (updateAddAL (GVsT DGVs) lc2 lid gv).
Proof.
  intros.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
    intros.
    apply H in H0.
    destruct (id_dec lid i0); subst.
      repeat rewrite lookupAL_updateAddAL_eq. auto.
      repeat rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma cmds_simulation_other_stable: forall pinfo TD Mem lc F1 B1 cs1 cs2 Mem' 
  lc', 
  PI_f pinfo <> F1 ->
  cmds_simulation pinfo TD Mem lc F1 B1 cs1 cs2 ->
  cmds_simulation pinfo TD Mem' lc' F1 B1 cs1 cs2.
Proof.
  intros.
  autounfold with ppbsim in *.
  destruct (fdef_dec (PI_f pinfo) F1); subst; try congruence; auto.
Qed.

Lemma wf_tmp_value__updateAddAL_neq: forall pinfo TD M lc pid id0 gv,
  wf_tmp_value pinfo TD M lc pid ->
  PI_id pinfo <> id0 -> id0 <> pid ->
  wf_tmp_value pinfo TD M (updateAddAL (GVsT DGVs) lc id0 gv) pid.
Proof.
  intros.
  unfold wf_tmp_value in *. simpl in *.
  destruct H as [gvsa [gv1 [W11 [W12 W13]]]].
  exists gvsa. exists gv1.
  split.
    rewrite <- lookupAL_updateAddAL_neq; auto.
  split; auto.
    rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma cmds_simulation__updateAddAL_neq: forall pinfo TD Mem lc l1 ps1 cs11 c 
  cs1' cs1 cs2 tmn gv
  (Htcmds : cmds_simulation pinfo TD Mem lc 
             (PI_f pinfo)
             (block_intro l1 ps1 (cs11 ++ c :: cs1')
                tmn) cs1 cs2)
  (Hneq: PI_id pinfo <> (getCmdLoc c)) 
  (Hnt: not_temporaries (getCmdLoc c) (PI_newids pinfo)),
  cmds_simulation pinfo TD Mem
     (updateAddAL (GVsT DGVs) lc (getCmdLoc c) gv) 
     (PI_f pinfo) (block_intro l1 ps1 (cs11 ++ c :: cs1') tmn) cs1 cs2.
Proof.
  intros.
  autounfold with ppbsim in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); subst; try congruence; auto.
  remember ((PI_newids pinfo) ! l1) as R.
  destruct R as [[[lid pid] sid]|]; auto.
  destruct Htcmds as [J1 [J2 J3]].
  split.
    clear J2 J3.
    intros H4.
    apply J1 in H4. clear J1.
    destruct H4 as [J1 J2].
    split; auto.
      clear J1.
      intros W1 W2.
      apply J2 in W1; auto. clear J2.
      assert (getCmdLoc c <> pid) as Hneq2.
        clear - HeqR Hnt.
        assert (J:=Hnt l1).
        rewrite <- HeqR in J.
        destruct J as [_ [J _]]; auto.
      eapply wf_tmp_value__updateAddAL_neq; eauto.
  split; auto.
    clear J1 J2.
    intros. subst.
    apply J3 in H; auto. clear J3.
      assert (getCmdLoc c <> lid) as Hneq2.
        clear - HeqR Hnt.
        assert (J:=Hnt l1).
        rewrite <- HeqR in J.
        destruct J as [J _]; auto.
      eapply wf_tmp_value__updateAddAL_neq; eauto.
Qed.

Lemma phinodes_placement_is_correct__dsLoad: forall (maxb : Values.block) 
  (pinfo : PhiInfo)
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hnoalias : wf_State maxb pinfo Cfg1 St1) (S : system) (TD : TargetData)
  (Ps : list product) (F : fdef) (B : block) (lc : Opsem.GVsMap) (gl : GVMap)
  (fs : GVMap) (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (als : list mblock) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_load id0 t v align0 :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (mps : GVsT DGVs) (mp : GenericValue) (gv : GenericValue)
  (H : Opsem.getOperandValue TD v lc gl = ret mps)
  (H0 : mp @ mps) (H1 : mload TD Mem mp t align0 = ret gv),
  exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' trace_nil /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                                      ($ gv # t $);
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct_ctx_other.
  assert (Heqb1':=Heqb1).    
  destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  destruct (fdef_dec (PI_f pinfo) F1).
  Case "PI_f pinfo = F1".

    destruct (is_temporary_dec id0 (PI_newids pinfo)).
    SCase "is_temporary".
      apply cmds_simulation_same_tail_inv in Htcmds; eauto.
      destruct Htcmds as [lid [pid [sid [Heq1 [Heq2 [J1 [J2 [J3 J4]]]]]]]]; 
        subst.
      inv J2.

      exists 
        {| Opsem.ECS := {|
                    Opsem.CurFunction := PI_f pinfo;
                    Opsem.CurBB := block_intro l1 ps1 (cs11 ++ nil) tmn;
                    Opsem.CurCmds := nil;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := lc1;
                    Opsem.Allocas := als |} :: ECs1;
           Opsem.Mem := Mem |}.
      split.
      SSCase "opsem".
        constructor.
      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).

        apply reg_simulation__updateAddAL_tmp; auto.

        unfold cmds_simulation. simpl in *.
        destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
        rewrite J1 in *.
        destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
        split.
        SSSCase "1".
          intros H3.
          apply app_eq_nil in H3.
          destruct H3; subst.
          split.
          SSSSCase "1.1".
            destruct ((PI_preds pinfo) ! l1) as [[]|];
              destruct ((PI_succs pinfo) ! l1) as [[]|]; try solve [
                auto | 
                right; right; split; try solve [auto | intro J; inv J]
              ].
          SSSSCase "1.2".
            intros H3 H5.
            symmetry in H5.
            apply app_eq_nil in H5.
            destruct H5 as [J5 J6].
            rewrite J5 in H3. congruence.
        SSSCase "2".
          split.
          SSSSCase "2.1".
            intros H3.
            destruct ((PI_succs pinfo) ! l1) as [[]|]; auto.
              right; split; try solve [auto | intro J; inv J].
          SSSSCase "2.2".
            intros H3. intros.
            unfold wf_tmp_value. simpl.
            exists mp. exists gv.
            split.
              inv H0.
              assert ((PI_id pinfo) <> lid) as Hneq.
                eapply wf_system__uniqFdef with (f:=PI_f pinfo) in Hwfs; eauto.
                symmetry in J1.
                apply WF_PhiInfo_fresh in J1; auto.
                destruct J1; auto.

              rewrite <- lookupAL_updateAddAL_neq; auto.
            split; auto.
              rewrite lookupAL_updateAddAL_eq.
              erewrite mload_gv2gvs; eauto.

    SCase "isnt_temporary".
      apply cmds_simulation_same_cons_inv in Htcmds; eauto.
      destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC (PI_f pinfo) 
            (block_intro l1 ps1 (cs11 ++ insn_load id0 t v align0 :: cs1') tmn) 
            cs1' tmn (updateAddAL (GVsT DGVs) lc1 id0 ($ gv # t $)) als)
         ::ECs1) Mem).
      split.
      SSCase "opsem".
        apply OpsemProps.sInsn__implies__sop_star.
        econstructor; eauto.
          erewrite simulation__getOperandValue; eauto.
            eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).
        apply reg_simulation__updateAddAL; auto.
        apply cmds_simulation__updateAddAL_neq; auto.
          eapply wf_system__uniqFdef with (f:=PI_f pinfo) in Hwfs; eauto.
          apply WF_PhiInfo_spec10 in HBinF; auto.

  Case "PI_f pinfo <> F1".
    apply cmds_simulation_other_cons_inv in Htcmds; auto.
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
    exists 
      (Opsem.mkState 
        ((Opsem.mkEC F1
          (block_intro l1 ps1 (cs11 ++ insn_load id0 t v align0 :: cs1') tmn) 
          cs1' tmn (updateAddAL (GVsT DGVs) lc1 id0 ($ gv # t $)) als)
       ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_star.
      econstructor; eauto.
        erewrite simulation__getOperandValue; eauto.
          eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
    SSCase "sim".
      repeat (split; eauto 2 using cmds_at_block_tail_next).
      apply reg_simulation__updateAddAL; auto.
      eapply cmds_simulation_other_stable; eauto.
Qed.

Lemma load_store_same: forall a Mem b0 ofs0 v Mem',
  ret v = Mem.load a Mem b0 ofs0 ->
  ret Mem' = Mem.store a Mem b0 ofs0 v ->
  Mem = Mem'.
Proof.
  intros.
Local Transparent Mem.store Mem.load.
  unfold Mem.store in H0.
  unfold Mem.load in H.
  remember (Mem.valid_access_dec Mem a b0 ofs0 Readable) as R1.
  destruct R1; inv H.
  remember (Mem.valid_access_dec Mem a b0 ofs0 Writable) as R2.
  destruct R2; inv H0.

Global Opaque Mem.store Mem.load.
Admitted.

Lemma mload_aux_mstore_aux_same: forall b0 mc Mem gv1 ofs0 Mem',
  mstore_aux Mem gv1 b0 ofs0 = ret Mem' ->
  mload_aux Mem mc b0 ofs0 = ret gv1 ->
  Mem = Mem'.
Proof.
  induction mc; simpl; intros.
    inv H0. inv H. auto.

    inv_mbind'.
    simpl in *.
    inv_mbind'.
    apply load_store_same in HeqR1; auto. subst.
    apply IHmc in H1; auto.
Qed.

Lemma mload_mstore_same: forall pinfo td Mem lc pid Mem' gv1 gvs1 mp2 mps2 gl,  
  wf_tmp_value pinfo td Mem lc pid ->
  Opsem.getOperandValue td (value_id (PI_id pinfo)) lc gl = ret mps2 ->
  Opsem.getOperandValue td (value_id pid) lc gl = ret gvs1 ->
  gv1 @ gvs1 ->
  mp2 @ mps2 ->
  mstore td Mem mp2 (PI_typ pinfo) gv1 (PI_align pinfo) = ret Mem' ->
  Mem = Mem'.
Proof.
  simpl. intros.
  inv H2. inv H3.
  destruct H as [gvsa [gv2 [J1 [J2 J3]]]].
  rewrite J1 in H0. inv H0.
  rewrite J3 in H1. inv H1.
  clear - H4 J2.
  apply genericvalues.LLVMgv.mload_inv in J2.
  destruct J2 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  apply genericvalues.LLVMgv.store_inv in H4.
  destruct H4 as [b0 [ofs0 [J1 J4]]].
  clear J2.
  inv J1. clear m.
  eapply mload_aux_mstore_aux_same in J3; eauto.
Qed.

Lemma phinodes_placement_is_correct__dsStore: forall (maxb : Values.block) 
  (pinfo : PhiInfo)
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hnoalias : wf_State maxb pinfo Cfg1 St1) (S : system) (TD : TargetData)
  (Ps : list product) (F : fdef) (B : block) (lc : Opsem.GVsMap) (gl : GVMap)
  (fs : GVMap) (sid : id) (t : typ) (align0 : align) (v1 v2 : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (als : list mblock) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_store sid t v1 v2 align0 :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (mp2 : GenericValue) (gv1 : GenericValue) (Mem' : mem) (gvs1 : GVsT DGVs)
  (mps2 : GVsT DGVs) (H : Opsem.getOperandValue TD v1 lc gl = ret gvs1)
  (H0 : Opsem.getOperandValue TD v2 lc gl = ret mps2) (H1 : gv1 @ gvs1)
  (H2 : mp2 @ mps2) (H3 : mstore TD Mem mp2 t gv1 align0 = ret Mem'),
  exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' trace_nil /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := lc;
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem' |}.
Proof.
  intros. subst.
  destruct_ctx_other.
  assert (Heqb1':=Heqb1).    
  destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  destruct (fdef_dec (PI_f pinfo) F1).
  Case "PI_f pinfo = F1".

    destruct (is_temporary_dec sid (PI_newids pinfo)).
    SCase "is_temporary".
      apply cmds_simulation_same_head_inv in Htcmds; eauto.
      destruct Htcmds as [l2 [ps2 [tmn1 [lid [pid [sid0 [Heq1 [Heq2 
                           [J1 [J2 [J3 J4]]]]]]]]]]]; subst.
      inv J1. inversion Heq1; subst l1 ps1 tmn.
      apply app_inv_tail_nil in H8; subst. simpl.
      exists 
        {| Opsem.ECS := {|
                    Opsem.CurFunction := PI_f pinfo;
                    Opsem.CurBB := block_intro l2 ps2 cs1 tmn1;
                    Opsem.CurCmds := cs1;
                    Opsem.Terminator := tmn1;
                    Opsem.Locals := lc1;
                    Opsem.Allocas := als |} :: ECs1;
           Opsem.Mem := Mem |}.
      split.
      SSCase "opsem".
        constructor.
      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).

        SSSCase "cs sim".
          assert (NoDup (getBlockLocs B)) as Huniq.
           apply uniqFdef__block_simulation__uniqBlockLocs in Hbsim; auto.
             eapply wf_system__uniqFdef; eauto.

          autounfold with ppbsim in *.
          unfold phinodes_placement_block in Hbsim.
          destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
          destruct Heqb2 as [l2' [ps2' [cs21 Heqb2]]]; subst.
          rewrite Heq2 in *.
          destruct ((PI_preds pinfo) ! l2) as [[]|]; try congruence.
          inv Hbsim. 
          assert (cs21 = nil) as EQ. 
            clear - H8 Huniq.
            simpl in Huniq.
            simpl_env in Huniq.
            apply NoDup_split in Huniq.
            destruct Huniq as [_ Huniq].
            apply NoDup_split in Huniq.
            destruct Huniq as [_ Huniq].
            apply NoDup_split in Huniq.
            destruct Huniq as [Huniq _].
            rewrite getCmdsLocs_app in Huniq.
            apply infrastructure_props.NoDup_disjoint with (i0:=sid0) in Huniq; 
              simpl; auto.
            destruct cs21; auto.
            inv H8. 
            contradict Huniq; simpl; auto.

          subst.
          inv H8. 
          split.
          SSSSCase "1".
            intros H5.
            split.
            SSSSSCase "1.1".
              right. left. split; auto. intro J; inv J.
          
            SSSSSCase "1.2".
              intros H6 H7. 
              symmetry in H7. apply app_inv_tail_nil in H7. inv H7.
          
          SSSSCase "2".
            split.
            SSSSSCase "2.1".
              intros H5. congruence.
            SSSSSCase "2.2".
              intros H5 EQ1 EQ2. 
              destruct ((PI_succs pinfo) ! l2') as [[]|]; try congruence.
              apply app_eq_nil in EQ2.
              destruct EQ2 as [_ EQ2]. congruence.

        SSSCase "tail sim".
        eapply ECs_simulation_tail_stable; eauto.
 
        SSSCase "Mem sim".
        eapply mload_mstore_same; eauto.

    SCase "isnt_temporary".
      apply cmds_simulation_same_cons_inv in Htcmds; eauto.
      destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC (PI_f pinfo) 
            (block_intro l1 ps1 (cs11 ++ insn_store sid t v1 v2 align0 :: cs1') 
              tmn) 
            cs1' tmn lc1 als)
         ::ECs1) Mem').
      split.
      SSCase "opsem".
        apply OpsemProps.sInsn__implies__sop_star.
        erewrite <- simulation__getOperandValue in H; eauto.
        erewrite <- simulation__getOperandValue in H0; eauto.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.

      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).

        destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
        eapply cmds_simulation_stable; eauto.

        eapply ECs_simulation_tail_stable; eauto.

  Case "PI_f pinfo <> F1".
      apply cmds_simulation_other_cons_inv in Htcmds; eauto.
      destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC F1
            (block_intro l1 ps1 (cs11 ++ insn_store sid t v1 v2 align0 :: cs1') 
              tmn) 
            cs1' tmn lc1 als)
         ::ECs1) Mem').
      split.
      SSCase "opsem".
        apply OpsemProps.sInsn__implies__sop_star.
        erewrite <- simulation__getOperandValue in H; eauto.
        erewrite <- simulation__getOperandValue in H0; eauto.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.

      SSCase "sim".
        repeat (split; eauto 2 using cmds_at_block_tail_next).

        eapply cmds_simulation_other_stable; eauto.

        eapply ECs_simulation_tail_stable; eauto.
Qed.

Ltac next_state :=
match goal with
| Hrsim: reg_simulation ?pinfo ?F1 ?lc1 ?lc |-
     exists St1' : Opsem.State,
     Opsem.sop_star _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := ?F1;
                    Opsem.CurBB := ?B1;
                    Opsem.CurCmds := _ :: ?cs1';
                    Opsem.Terminator := ?tmn;
                    Opsem.Locals := ?lc1;
                    Opsem.Allocas := _ |} :: ?ECs1;
       Opsem.Mem := _ |} St1' _ /\
     State_simulation ?pinfo _ St1' _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := _;
                    Opsem.CurBB := _;
                    Opsem.CurCmds := _;
                    Opsem.Terminator := _;
                    Opsem.Locals := ?lc;
                    Opsem.Allocas := ?als' |} :: _;
       Opsem.Mem := ?Mem' |} =>
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC F1 B1 cs1' tmn lc1 als')
         ::ECs1) Mem')

| Hrsim: reg_simulation ?pinfo ?F1 ?lc1 ?lc |-
     exists St1' : Opsem.State,
     Opsem.sop_star _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := ?F1;
                    Opsem.CurBB := ?B1;
                    Opsem.CurCmds := _ :: ?cs1';
                    Opsem.Terminator := ?tmn;
                    Opsem.Locals := ?lc1;
                    Opsem.Allocas := _ |} :: ?ECs1;
       Opsem.Mem := _ |} St1' _ /\
     State_simulation ?pinfo _ St1' _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := _;
                    Opsem.CurBB := _;
                    Opsem.CurCmds := _;
                    Opsem.Terminator := _;
                    Opsem.Locals := updateAddAL (GVsT DGVs) ?lc ?id0 ?gv;
                    Opsem.Allocas := ?als' |} :: _;
       Opsem.Mem := ?Mem' |} =>
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC F1 B1 cs1' tmn 
            (updateAddAL (GVsT DGVs) lc1 id0 gv) als')
         ::ECs1) Mem')

| Hrsim: reg_simulation ?pinfo ?F1 ?lc1 ?lc |-
     exists St1' : Opsem.State,
     Opsem.sop_star _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := ?F1;
                    Opsem.CurBB := ?B1;
                    Opsem.CurCmds := _ :: ?cs1';
                    Opsem.Terminator := ?tmn;
                    Opsem.Locals := ?lc1;
                    Opsem.Allocas := _ |} :: ?ECs1;
       Opsem.Mem := _ |} St1' _ /\
     State_simulation ?pinfo _ St1' _
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := _;
                    Opsem.CurBB := _;
                    Opsem.CurCmds := _;
                    Opsem.Terminator := _;
                    Opsem.Locals := (if ?c
                                    then updateAddAL (GVsT DGVs) ?lc ?id0 ?gvs2
                                    else updateAddAL (GVsT DGVs) ?lc ?id0 ?gvs1);
                    Opsem.Allocas := ?als' |} :: _;
       Opsem.Mem := ?Mem' |} =>
      exists 
        (Opsem.mkState 
          ((Opsem.mkEC F1 B1 cs1' tmn 
            (if c
             then updateAddAL (GVsT DGVs) lc1 id0 gvs2
             else updateAddAL (GVsT DGVs) lc1 id0 gvs1) als')
         ::ECs1) Mem')
end.

Lemma values2GVs__simulation: forall pinfo lc1 lc2 gl F1 td idxs
  (Hntmp: 
   if fdef_dec (PI_f pinfo) F1 then
     forall nth sz0 v0,
       nth_list_sz_value nth idxs = Some (sz0, v0) ->
       value_has_no_tmps pinfo v0
   else True),
  reg_simulation pinfo F1 lc1 lc2 ->
  Opsem.values2GVs td idxs lc1 gl = Opsem.values2GVs td idxs lc2 gl.
Proof.
  intros.
  induction idxs as [|[]]; simpl; intros; auto.
    assert (if fdef_dec (PI_f pinfo) F1 then
              forall (nth : nat) (sz0 : sz) (v0 : value),
                nth_list_sz_value nth idxs = ret (sz0, v0) -> 
                value_has_no_tmps pinfo v0
            else True) as J.
      destruct (fdef_dec (PI_f pinfo) F1); auto.
      intros. 
      apply Hntmp with (nth:=S nth)(sz0:=sz0)(v0:=v0); auto.
    rewrite IHidxs; auto.
    assert (if fdef_dec (PI_f pinfo) F1
            then value_has_no_tmps pinfo v else True) as Hnt.
      destruct (fdef_dec (PI_f pinfo) F1); auto.
      apply Hntmp with (nth:=O)(sz0:=0%nat)(v0:=v); auto.
    erewrite simulation__getOperandValue; eauto.

    assert (if fdef_dec (PI_f pinfo) F1 then
              forall (nth : nat) (sz0 : sz) (v0 : value),
                nth_list_sz_value nth idxs = ret (sz0, v0) -> 
                value_has_no_tmps pinfo v0
            else True) as J.
      destruct (fdef_dec (PI_f pinfo) F1); auto.
      intros. 
      apply Hntmp with (nth:=S nth)(sz0:=sz0)(v0:=v0); auto.
    rewrite IHidxs; auto.
    assert (if fdef_dec (PI_f pinfo) F1
            then value_has_no_tmps pinfo v else True) as Hnt.
      destruct (fdef_dec (PI_f pinfo) F1); auto.
      apply Hntmp with (nth:=O)(sz0:=S n)(v0:=v); auto.
    erewrite simulation__getOperandValue; eauto.
Qed.

Ltac solve_step :=
match goal with
| Hrsim: reg_simulation ?pinfo ?F1 ?lc1 ?lc, 
  H0: Opsem.getOperandValue _ _ ?lc _ = ret _ |- _ =>
  erewrite <- simulation__getOperandValue in H0; try solve [
    eauto | 
    eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto
  ]
end.

Ltac solve_opsem :=
  apply OpsemProps.sInsn__implies__sop_star; 
  econstructor; try solve [
    eauto |
    match goal with
    | Hrsim: reg_simulation _ _ ?lc1 ?lc2,
      H: Opsem.values2GVs ?td ?idxs ?lc2 ?gl = Some _ |- 
         Opsem.values2GVs ?td ?idxs ?lc1 ?gl = Some _ =>
         erewrite values2GVs__simulation; 
         try solve [eauto | eapply original_indxs_arent_tmps; eauto]
    end |
    unfold Opsem.BOP, Opsem.FBOP, Opsem.TRUNC, Opsem.EXT, Opsem.CAST, 
      Opsem.ICMP, Opsem.FCMP in *;
    inv_mbind';
    symmetry_ctx;
    repeat solve_step;
    repeat match goal with
           | H : Opsem.getOperandValue ?td ?v ?lc ?gl = Some _ |-
             match Opsem.getOperandValue ?td ?v ?lc ?gl with
             | Some _ => _
             | None => _
             end = _ => rewrite H
           end; auto
  ].

Ltac solve_if_rsim :=
  match goal with
  | Hrsim : reg_simulation ?pinfo ?F1 ?lc1 ?lc2 |-
    reg_simulation ?pinfo ?F1 
           (if ?c
            then updateAddAL (GVsT DGVs) ?lc1 ?id0 ?gvs2
            else updateAddAL (GVsT DGVs) ?lc1 ?id0 ?gvs1)
           (if ?c
            then updateAddAL (GVsT DGVs) ?lc2 ?id0 ?gvs2
            else updateAddAL (GVsT DGVs) ?lc2 ?id0 ?gvs1) =>
        destruct c; 
          apply reg_simulation__updateAddAL; auto
  end.

Ltac solve_other_fun_case :=
match goal with
| n : PI_f ?pinfo <> ?F1, 
  Htcmds : cmds_simulation ?pinfo _ _ _ ?F1 _ _ _ |- _ =>
    apply cmds_simulation_other_cons_inv in Htcmds; eauto;
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst;
    next_state;
    split; try solve [
      solve_opsem |
      repeat (split; eauto 2 using cmds_at_block_tail_next); try solve [
        solve_if_rsim |
        apply reg_simulation__updateAddAL; auto |
        eapply cmds_simulation_other_stable; eauto |
        eapply ECs_simulation_tail_stable; eauto]
      ]
end.

Ltac solve_same_fun_ntmp_case :=
match goal with
| e : PI_f ?pinfo = ?F1, 
  Htcmds : cmds_simulation ?pinfo _ _ _ ?F1 _ _ _ |- _ =>
    apply cmds_simulation_same_cons_inv in Htcmds; try solve [simpl; eauto];
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst;
    next_state;
    split; try solve [
      solve_opsem |
      repeat (split; eauto 2 using cmds_at_block_tail_next); try solve [
        solve_if_rsim |
        apply reg_simulation__updateAddAL; auto |
        match goal with
        | Heqb2 : exists _, exists _, exists _, ?B = _,
          Hbsim : block_simulation _ _ _ ?B |- 
          cmds_simulation _ _ _ _ _ _ _ _ =>
          destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst;
          eapply cmds_simulation_stable;
            eauto using original_ids_in_phi_arent_temporaries
        end | 
        eapply ECs_simulation_tail_stable; eauto]
    ]
end.

Ltac phinodes_placement_is_correct__common :=
  destruct_ctx_other;
  match goal with
  | Heqb1 : exists _, exists _, exists _,
                ?B1 = block_intro _ _ (_ ++ ?cs1) ?tmn,
    HBinF : blockInFdefB ?B1 ?F1 = true,
    Hwfpi : WF_PhiInfo ?pinfo,
    Hwfs : wf_system _ _ |- _ =>
    assert (Heqb1':=Heqb1);
    destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst;
    assert (HwfF := Hwfs);
    eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto;
    destruct (fdef_dec (PI_f pinfo) F1); try solve [
      solve_same_fun_ntmp_case | 
      solve_other_fun_case
    ]
  end.

Lemma phinodes_placement_is_correct__dsAlloca: forall (maxb: Values.block) 
  (pinfo: PhiInfo)
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hnoalias : wf_State maxb pinfo Cfg1 St1) (S : system) (TD : TargetData)
  (Ps : list product) (F : fdef) (B : block) (lc : Opsem.GVsMap) (gl : GVMap)
  (fs : GVMap) (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (als : list mblock) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_alloca id0 t v align0 :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (gns : GVsT DGVs) (gn : GenericValue) (Mem' : mem) (tsz : sz) (mb : mblock)
  (H : getTypeAllocSize TD t = ret tsz) 
  (H0 : Opsem.getOperandValue TD v lc gl = ret gns)
  (H1 : gn @ gns) (H2 : malloc TD Mem tsz gn align0 = ret (Mem', mb)),
  exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' trace_nil /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                                      ($ blk2GV TD mb # typ_pointer t $);
                    Opsem.Allocas := mb :: als |} :: EC;
       Opsem.Mem := Mem' |}.
Proof.
  intros. subst.
  phinodes_placement_is_correct__common.
Qed.

Lemma phinodes_placement_is_correct__dsMalloc: forall (maxb: Values.block) 
  (pinfo: PhiInfo)
  (Cfg1 : OpsemAux.Config) (St1 : Opsem.State) (Hwfpi : WF_PhiInfo pinfo)
  (Hnoalias : wf_State maxb pinfo Cfg1 St1) (S : system) (TD : TargetData)
  (Ps : list product) (F : fdef) (B : block) (lc : Opsem.GVsMap) (gl : GVMap)
  (fs : GVMap) (id0 : id) (t : typ) (align0 : align) (v : value)
  (EC : list Opsem.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (als : list mblock) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_malloc id0 t v align0 :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (gns : GVsT DGVs) (gn : GenericValue) (Mem' : mem) (tsz : sz) (mb : mblock)
  (H : getTypeAllocSize TD t = ret tsz) 
  (H0 : Opsem.getOperandValue TD v lc gl = ret gns)
  (H1 : gn @ gns) (H2 : malloc TD Mem tsz gn align0 = ret (Mem', mb)),
  exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' trace_nil /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := updateAddAL (GVsT DGVs) lc id0
                                      ($ blk2GV TD mb # typ_pointer t $);
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem' |}.
Proof.
  intros. subst.
  phinodes_placement_is_correct__common.
Qed.

Lemma fdef_simulation__inv: forall pinfo f1 f2, 
  fdef_simulation pinfo f1 f2 -> getFdefID f1 = getFdefID f2.
Proof.
  unfold fdef_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f1); inv H; auto.
    destruct (PI_f pinfo) as [[]]; simpl.
    destruct (gen_fresh_ids (PI_rd pinfo) (getArgsIDs a ++ getBlocksLocs b)).
    auto. 
Qed.

Lemma products_simulation__fdef_simulation : forall pinfo fid f2 Ps1 Ps2,
  products_simulation pinfo Ps1 Ps2 ->
  lookupFdefViaIDFromProducts Ps2 fid = ret f2 ->
  exists f1, 
    lookupFdefViaIDFromProducts Ps1 fid = ret f1 /\
    fdef_simulation pinfo f1 f2.
Proof.
  induction Ps1; simpl; intros Ps2 J1 J2.
    inv J1. inv J2.

    inv J1. simpl in J2.
    remember (lookupFdefViaIDFromProduct y fid) as R.     
    destruct R; inv J2.
      destruct a; subst; tinv HeqR.
      destruct y; subst; tinv HeqR.
      simpl in HeqR. simpl.
      destruct (getFdefID f0 == fid); inv HeqR.
      exists f.
      split; auto.
        apply fdef_simulation__inv in H1.
        destruct (getFdefID f == getFdefID f0); auto.
        rewrite H1 in n. congruence.

      destruct a; subst; simpl; try eapply IHPs1; eauto.  
      destruct y; subst; tinv H1.
      simpl in *.
      destruct (getFdefID f0 == fid); inv HeqR.
      eapply IHPs1 in H0; eauto.
      destruct H0 as [f1 [J1 J2]].
      exists f1. 
      split; auto.
        apply fdef_simulation__inv in H1.
        rewrite H1.
        destruct (getFdefID f0 == fid); auto.
          subst. congruence.
Qed.

Lemma lookupFdefViaPtr__simulation : forall TD gl F1 lc1 lc2 f2 fv Ps1 Ps2 fptr
  fs pinfo
  (Hntmp:if fdef_dec (PI_f pinfo) F1 then value_has_no_tmps pinfo fv else True),
  reg_simulation pinfo F1 lc1 lc2 ->
  getOperandValue TD fv lc2 gl = Some fptr ->
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 ->
  products_simulation pinfo Ps1 Ps2 ->
  exists f1,
    getOperandValue TD fv lc1 gl = Some fptr /\
    OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 /\
    fdef_simulation pinfo f1 f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; inv H1.
  erewrite <- simulation__getOperandValue in H0; eauto.
  simpl.
  eapply products_simulation__fdef_simulation in H4; eauto.
  destruct H4 as [f1 [J3 J4]].
  eauto.
Qed.

Lemma getEntryBlock__simulation: forall pinfo f1 f2 b2 
  (Hwfpi: WF_PhiInfo pinfo),
  getEntryBlock f2 = Some b2 ->
  fdef_simulation pinfo f1 f2 ->
  exists b1, getEntryBlock f1 = Some b1 /\ block_simulation pinfo f1 b1 b2.
Proof.
  unfold fdef_simulation.
  unfold block_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f1); inv H; eauto.
    destruct Hwfpi as [J1 [J2 [J3 [J4 J5]]]].
    destruct (PI_f pinfo) as [[]]; simpl in *.
    destruct (gen_fresh_ids (PI_rd pinfo) (getArgsIDs a ++ getBlocksLocs b)).
    rewrite J5.
    destruct b; simpl in *; inv H2.
    exists b.
    split; auto.
Qed.

Lemma params2GVs__simulation: forall pinfo lc1 lc2 td lp gl F1
  (Hntmp: 
   if fdef_dec (PI_f pinfo) F1 then
     List.fold_left 
       (fun acc p => let '(_, v):=p in value_has_no_tmps pinfo v /\ acc) 
       lp True 
   else True),
  reg_simulation pinfo F1 lc1 lc2 ->
  Opsem.params2GVs td lp lc1 gl = Opsem.params2GVs td lp lc2 gl. 
Proof.
  intros.
  induction lp as [|[]]; simpl; intros; auto.
    assert (if fdef_dec (PI_f pinfo) F1
            then value_has_no_tmps pinfo v else True) as Hnt.
      destruct (fdef_dec (PI_f pinfo) F1); auto.
      simpl in Hntmp.
      apply fold_left_prop in Hntmp.
        destruct Hntmp; auto.  
        destruct b. tauto.
        destruct c. tauto.
    erewrite simulation__getOperandValue; eauto.
    destruct (Opsem.getOperandValue td v lc2 gl); auto.
    rewrite IHlp; auto.
    simpl in Hntmp.
    destruct (fdef_dec (PI_f pinfo) F1); auto.
    apply fold_left_congruence with (b:=True) in Hntmp; auto.
    destruct c. tauto.
Qed.

Lemma fdef_simulation__inv' : forall pinfo f1 fa rt fid la va lb2,
  fdef_simulation pinfo f1 (fdef_intro (fheader_intro fa rt fid la va) lb2) ->
  exists lb1, f1 = fdef_intro (fheader_intro fa rt fid la va) lb1.
Proof.
  unfold fdef_simulation.
  intros.
  destruct (fdef_dec (PI_f pinfo) f1); inv H; eauto.
    destruct (PI_f pinfo) as [[]]; simpl in *.
    destruct (gen_fresh_ids (PI_rd pinfo) (getArgsIDs a ++ getBlocksLocs b)).
    inv H1. eauto. 
Qed.

Lemma entry_cmds_simulation: forall f l' ps0 cs0 tmn' pinfo ps' cs' ifs S los
  nts lc' Mem Ps (Hwfpi: WF_PhiInfo pinfo)
  (HwfF: wf_fdef ifs S (module_intro los nts Ps) f)
  (Hgetentry1 : getEntryBlock f = ret block_intro l' ps0 cs0 tmn')
  (Hbsim1 : block_simulation pinfo f
             (block_intro l' ps0 cs0 tmn') (block_intro l' ps' cs' tmn')),
  cmds_simulation pinfo (los, nts) Mem lc' f (block_intro l' ps0 cs0 tmn') 
    cs0 cs'.
Proof.
  intros.
  repeat autounfold with ppbsim in *.
  destruct (fdef_dec (PI_f pinfo) f); subst; inv Hbsim1; auto.
  destruct Hwfpi as [J1 [J2 [J3 [J4 J5]]]].
  assert (exists lid1, exists pid1, exists sid1, 
    (PI_newids pinfo) ! l' = Some (lid1, pid1, sid1)) as HeqR.
    symmetry in J5.
    apply gen_fresh_ids__spec2 with (l1:=l') in J5; auto.
    destruct (PI_newids pinfo) ! l' as [[[]]|]; eauto; try congruence.
    apply reachable_entrypoint in Hgetentry1.
    eapply reachable__reachablity_analysis in Hgetentry1; eauto.

  destruct HeqR as [lid1 [pid1 [sid1 HeqR]]].
  rewrite HeqR in *.
  assert (forall pd pds, (PI_preds pinfo) ! l' <> Some (pd::pds)) as Hprds.
    rewrite J4.
    intros. intro J.
    assert (In pd (make_predecessors (PI_succs pinfo))!!!l') as G.
      unfold successors_list. unfold l in J. rewrite J. simpl. auto.
    apply make_predecessors_correct' in G.
    rewrite J3 in G.
    apply successors__blockInFdefB in G.
    destruct G as [ps1 [cs1 [tmn1 [G1 G2]]]].
    destruct (PI_f pinfo) as [fh bs]. 
    simpl in G1.
    eapply getEntryBlock_inv in G1; eauto.

  destruct ((PI_preds pinfo) ! l') as [[]|]; try congruence.
    inv H0.
    split.
      intros.
      split; auto.
        intros. congruence.
    split.
      intros. congruence.

      intros. subst.
      destruct ((PI_succs pinfo) ! l') as [[]|]; try congruence.
      inv H1.

    assert (J:=@Hprds l0 l1). congruence.

    inv H0.
    split.
      intros.
      split; auto.
        intros. congruence.
    split.
      intros. congruence.

      intros. subst.
      destruct ((PI_succs pinfo) ! l') as [[]|]; try congruence.
      inv H1.
Qed.

Lemma phinodes_placement_is_correct__dsCall: forall (maxb : Values.block)
  (pinfo : PhiInfo) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (Hwfpi : WF_PhiInfo pinfo) (Hnoalias : wf_State maxb pinfo Cfg1 St1)
  (S : system) (TD : TargetData) (Ps : products) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (rid : id) (noret0 : noret)
  (ca : clattrs) (fv : value) (lp : params) (cs : list cmd) (tmn : terminator)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (als : list mblock) (ft : typ)
  Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2           
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_call rid noret0 ca ft fv lp
                                         :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (fid : id) (fptrs : GVsT DGVs) (fptr : GenericValue) (lc' : Opsem.GVsMap)
  (l' : l) (ps' : phinodes) (cs' : cmds) (tmn' : terminator) (rt : typ)
  (la : args) (va : varg) (lb : blocks) (fa : fnattrs) (gvs : list (GVsT DGVs))
  (H : Opsem.getOperandValue TD fv lc gl = ret fptrs)
  (H0 : fptr @ fptrs) 
  (H1 : OpsemAux.lookupFdefViaPtr Ps fs fptr =
        ret fdef_intro (fheader_intro fa rt fid la va) lb)
  (H2 : getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
        ret block_intro l' ps' cs' tmn')
  (H3 : Opsem.params2GVs TD lp lc gl = ret gvs)
  (H4 : Opsem.initLocals TD la gvs = ret lc'),
  exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' trace_nil /\
     State_simulation pinfo Cfg1 St1' Cfg2
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := fdef_intro
                                           (fheader_intro fa rt fid la va) lb;
                    Opsem.CurBB := block_intro l' ps' cs' tmn';
                    Opsem.CurCmds := cs';
                    Opsem.Terminator := tmn';
                    Opsem.Locals := lc';
                    Opsem.Allocas := nil |}
                    :: {|
                       Opsem.CurFunction := F;
                       Opsem.CurBB := B;
                       Opsem.CurCmds := insn_call rid noret0 ca ft fv lp
                                        :: cs;
                       Opsem.Terminator := tmn;
                       Opsem.Locals := lc;
                       Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem |}.
Proof.
  intros. subst.
  destruct_ctx_other.
  assert (Heqb1':=Heqb1).    
  destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  destruct (fdef_dec (PI_f pinfo) F1).
  SCase "PI_f pinfo = F1".
    assert (Htcmds':=Htcmds).
    apply cmds_simulation_same_cons_inv in Htcmds'; try solve [simpl; eauto].
    destruct Htcmds' as [cs1' [Heq Htcmds']]; subst.

    assert (not_temporaries rid (PI_newids pinfo)) as Hnt.
      eapply WF_PhiInfo_spec11 in HBinF ; eauto.

    assert (if fdef_dec (PI_f pinfo) (PI_f pinfo)
            then value_has_no_tmps pinfo fv else True) as Hntmp.
      eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
    inv H0.
    eapply lookupFdefViaPtr__simulation with (TD:=(los,nts))(gl:=gl) in H1; 
      eauto.
    destruct H1 as [f1 [J1 [J2 J3]]].
    eapply getEntryBlock__simulation in H2; eauto.
    destruct H2 as [[l0 ps0 cs0 tmn0] [Hgetentry1 Hbsim1]].
    assert (
      if fdef_dec (PI_f pinfo) (PI_f pinfo) then
        fold_left
          (fun (acc : Prop) (p : typ * attributes * value) =>
           let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp True
      else True) as Hntmp'.
      eapply WF_PhiInfo_spec12; eauto.

    erewrite <- params2GVs__simulation in H3; eauto.
    assert (J3':=J3).
    apply fdef_simulation__inv' in J3'.
    destruct J3' as [lb1' J3']; subst.
    exists 
      (Opsem.mkState 
        (
         (Opsem.mkEC (fdef_intro (fheader_intro fa rt fid la va) lb1')
           (block_intro l0 ps0 cs0 tmn0)
           cs0 tmn0 lc' nil)
         ::
         (Opsem.mkEC (PI_f pinfo) 
           (block_intro l1 ps1 
             (cs11 ++ insn_call rid noret0 ca ft fv lp :: cs1') tmn)
           (insn_call rid noret0 ca ft fv lp :: cs1') tmn lc1 als)
         ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_star. 
      econstructor; eauto.

    SSCase "sim".
      assert (Hbsim1':=Hbsim1).
      apply block_simulation__inv in Hbsim1'.
      destruct Hbsim1' as [Heq1 Heq2]; subst; auto.
      assert (
        InProductsB
          (product_fdef (fdef_intro (fheader_intro fa rt fid la va) lb1')) Ps1 =
          true) as Hin.
        eapply OpsemAux.lookupFdefViaPtr_inv; eauto.
      repeat (split; eauto 2 using cmds_at_block_tail_next).
        apply entryBlockInFdef; auto.
        exists l'. exists ps0. exists nil. auto.
        exists l'. exists ps'. exists nil. auto.
        apply reg_simulation_refl.
        eapply wf_system__wf_fdef in Hin; eauto.
        eapply entry_cmds_simulation; eauto.
        
  SCase "PI_f pinfo <> F1".
    assert (Htcmds':=Htcmds).
    apply cmds_simulation_other_cons_inv in Htcmds'; try solve [simpl; eauto].
    destruct Htcmds' as [cs1' [Heq Htcmds']]; subst.
    assert (if fdef_dec (PI_f pinfo) F1
            then value_has_no_tmps pinfo fv else True) as Hntmp.
      destruct (fdef_dec (PI_f pinfo) F1); auto; subst; try congruence.
    inv H0.
    eapply lookupFdefViaPtr__simulation with (TD:=(los,nts))(gl:=gl) in H1; 
      eauto.
    destruct H1 as [f1 [J1 [J2 J3]]].
    eapply getEntryBlock__simulation in H2; eauto.
    destruct H2 as [[l0 ps0 cs0 tmn0] [Hgetentry1 Hbsim1]].
    assert (
      if fdef_dec (PI_f pinfo) F1 then
        fold_left
          (fun (acc : Prop) (p : typ * attributes * value) =>
           let '(_, v) := p in value_has_no_tmps pinfo v /\ acc) lp True
      else True) as Hntmp'.
      eapply WF_PhiInfo_spec12; eauto.

    erewrite <- params2GVs__simulation in H3; eauto.
    assert (J3':=J3).
    apply fdef_simulation__inv' in J3'.
    destruct J3' as [lb1' J3']; subst.
    exists 
      (Opsem.mkState 
        (
         (Opsem.mkEC (fdef_intro (fheader_intro fa rt fid la va) lb1')
           (block_intro l0 ps0 cs0 tmn0)
           cs0 tmn0 lc' nil)
         ::
         (Opsem.mkEC F1
           (block_intro l1 ps1 
             (cs11 ++ insn_call rid noret0 ca ft fv lp :: cs1') tmn)
           (insn_call rid noret0 ca ft fv lp :: cs1') tmn lc1 als)
         ::ECs1) Mem).
    split.
    SSCase "opsem".
      apply OpsemProps.sInsn__implies__sop_star. 
      econstructor; eauto.

    SSCase "sim".
      assert (Hbsim1':=Hbsim1).
      apply block_simulation__inv in Hbsim1'.
      destruct Hbsim1' as [Heq1 Heq2]; subst; auto.
      assert (
        InProductsB
          (product_fdef (fdef_intro (fheader_intro fa rt fid la va) lb1')) Ps1 =
          true) as Hin.
        eapply OpsemAux.lookupFdefViaPtr_inv; eauto.
      repeat (split; eauto 2 using cmds_at_block_tail_next).
        apply entryBlockInFdef; auto.
        exists l'. exists ps0. exists nil. auto.
        exists l'. exists ps'. exists nil. auto.
        apply reg_simulation_refl.
        eapply wf_system__wf_fdef in Hin; eauto.
        eapply entry_cmds_simulation; eauto.
Qed.

Lemma simulation__exCallUpdateLocals: forall pinfo F1 lc1 lc2 td ft noret0 rid  
  oresult lc2' (Hrsim: reg_simulation pinfo F1 lc1 lc2)
  (Hexcall: Opsem.exCallUpdateLocals td ft noret0 rid oresult lc2 = ret lc2'),
  exists lc1', 
    Opsem.exCallUpdateLocals td ft noret0 rid oresult lc1 = ret lc1' /\
    reg_simulation pinfo F1 lc1' lc2'.
Proof.
  unfold Opsem.exCallUpdateLocals in *.
  intros.
  destruct noret0; inv Hexcall; eauto.
  inv_mbind'.
  destruct ft; tinv H1. 
  inv_mbind'.
  exists (updateAddAL (GVsT DGVs) lc1 rid ($ g0 # ft $)).
  split; auto.
    apply reg_simulation__updateAddAL; auto.
Qed.

Lemma products_simulation__fdef_None : forall pinfo fid Ps1 Ps2,
  products_simulation pinfo Ps1 Ps2 ->
  lookupFdefViaIDFromProducts Ps2 fid = merror ->
  lookupFdefViaIDFromProducts Ps1 fid = merror.
Proof.
  induction Ps1; simpl; intros Ps2 J1 J2; auto.
    inv J1. simpl in J2.
    remember (lookupFdefViaIDFromProduct y fid) as R.
    destruct R; inv J2.
    rewrite H0.
    apply IHPs1 in H0; auto.
    rewrite H0.
    destruct a; subst; simpl in *; auto.
    destruct (getFdefID f == fid); subst; auto.
    destruct y; subst; tinv H1.
    simpl in *.
    apply fdef_simulation__inv in H1.
    destruct (getFdefID f0 == getFdefID f); try congruence.
Qed.

Lemma products_simulation__fdec : forall pinfo fid f Ps1 Ps2,
  products_simulation pinfo Ps1 Ps2 ->
  lookupFdecViaIDFromProducts Ps2 fid = ret f ->
  lookupFdecViaIDFromProducts Ps1 fid = ret f.
Proof.
  induction Ps1; simpl; intros Ps2 J1 J2.
    inv J1. inv J2.

    inv J1. simpl in J2.
    remember (lookupFdecViaIDFromProduct y fid) as R.
    destruct R; inv J2.
      destruct a; subst; tinv HeqR.
        rewrite <- HeqR. auto.
      destruct y; subst; tinv HeqR.
      inv H1.

      assert (H0':=H0).
      apply IHPs1 in H0; auto.
      rewrite H0.
      destruct a; subst; simpl in *; auto.
      destruct (getFdecID f0 == fid); inv HeqR.
      auto.
Qed.

Lemma lookupExFdecViaPtr__simulation: forall TD gl F1 lc1 lc2 f fv Ps1 Ps2 fptr
  fs pinfo
  (Hntmp:if fdef_dec (PI_f pinfo) F1 then value_has_no_tmps pinfo fv else True),
  reg_simulation pinfo F1 lc1 lc2 ->
  getOperandValue TD fv lc2 gl = Some fptr ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs fptr = Some f ->
  products_simulation pinfo Ps1 Ps2 ->
  getOperandValue TD fv lc1 gl = Some fptr /\
  OpsemAux.lookupExFdecViaPtr Ps1 fs fptr = Some f.
Proof.  
  intros.
  unfold OpsemAux.lookupExFdecViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; inv H1.
  erewrite <- simulation__getOperandValue in H0; eauto.
  simpl.
  split; auto.
  remember (lookupFdefViaIDFromProducts Ps2 fid) as R.
  destruct R; tinv H4.
  symmetry in HeqR.
  erewrite products_simulation__fdef_None; eauto.
  rewrite H4. 
  eapply products_simulation__fdec; eauto.
Qed.

Lemma phinodes_placement_is_correct__dsExCall: forall (maxb : Values.block)
  (pinfo : PhiInfo) (Cfg1 : OpsemAux.Config) (St1 : Opsem.State)
  (Hwfpi : WF_PhiInfo pinfo) (Hnoalias : wf_State maxb pinfo Cfg1 St1)
  (S : system) (TD : TargetData) (Ps : products) (F : fdef) (B : block)
  (lc : Opsem.GVsMap) (gl : GVMap) (fs : GVMap) (rid : id) (noret0 : bool)
  (ca : clattrs) (fv : value) (lp : params) (cs : list cmd) (tmn : terminator)
  (EC : list Opsem.ExecutionContext) (Mem : mem) (als : list mblock)
  (ft : typ) Cfg2
  (EQ : Cfg2 = {| OpsemAux.CurSystem := S;
                  OpsemAux.CurTargetData := TD;
                  OpsemAux.CurProducts := Ps;
                  OpsemAux.Globals := gl;
                  OpsemAux.FunTable := fs |})
  (Hsim : State_simulation pinfo Cfg1 St1 Cfg2
           {|
           Opsem.ECS := {|
                        Opsem.CurFunction := F;
                        Opsem.CurBB := B;
                        Opsem.CurCmds := insn_call rid noret0 ca ft fv lp
                                         :: cs;
                        Opsem.Terminator := tmn;
                        Opsem.Locals := lc;
                        Opsem.Allocas := als |} :: EC;
           Opsem.Mem := Mem |})
  (fid : id) (rt : typ) (la : args) (oresult : monad GenericValue) (Mem' : mem)
  (lc' : Opsem.GVsMap) (va : varg) (fa : fnattrs) (gvs : list GenericValue)
  (fptr : GenericValue) (fptrs : GVsT DGVs) (gvss : list (GVsT DGVs))
  (H : Opsem.getOperandValue TD fv lc gl = ret fptrs) (H0 : fptr @ fptrs)
  (H1 : OpsemAux.lookupExFdecViaPtr Ps fs fptr =
        ret fdec_intro (fheader_intro fa rt fid la va))
  (H2 : Opsem.params2GVs TD lp lc gl = ret gvss)
  (H3 : gvs @@ gvss)
  (H4 : OpsemAux.callExternalFunction Mem fid gvs = ret (oresult, Mem'))
  (H5 : Opsem.exCallUpdateLocals TD ft noret0 rid oresult lc = ret lc'),
  exists St1' : Opsem.State,
     Opsem.sop_star Cfg1 St1 St1' trace_nil /\
     State_simulation pinfo Cfg1 St1' Cfg2       
       {|
       Opsem.ECS := {|
                    Opsem.CurFunction := F;
                    Opsem.CurBB := B;
                    Opsem.CurCmds := cs;
                    Opsem.Terminator := tmn;
                    Opsem.Locals := lc';
                    Opsem.Allocas := als |} :: EC;
       Opsem.Mem := Mem' |}.
Proof.
  intros. subst.
  destruct_ctx_other.
  assert (Heqb1':=Heqb1);
  destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  eapply simulation__exCallUpdateLocals in H5; eauto.
  destruct H5 as [lc1' [J1 J2]].
  destruct (fdef_dec (PI_f pinfo) F1).
  Case "=".
    apply cmds_simulation_same_cons_inv in Htcmds; try solve [simpl; eauto];
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst.
    exists 
      (Opsem.mkState 
        ((Opsem.mkEC 
           (PI_f pinfo)
           (block_intro l1 ps1
             (cs11 ++ insn_call rid noret0 ca ft fv lp :: cs1') 
             tmn)
           cs1' tmn lc1' als)::ECs1) Mem').
    split.

      assert (if fdef_dec (PI_f pinfo) (PI_f pinfo)
            then value_has_no_tmps pinfo fv else True) as Hntmp.
        eapply original_values_in_cmd_arent_tmps; eauto; simpl; auto.
      inv H0.
      eapply lookupExFdecViaPtr__simulation with (TD:=(los,nts))(gl:=gl)
        (lc1:=lc1)(lc2:=lc) in H1; eauto.
      destruct H1 as [J3 J4].
      apply OpsemProps.sInsn__implies__sop_star.
      econstructor; eauto.
        erewrite params2GVs__simulation with (lc2:=lc); eauto.
          eapply WF_PhiInfo_spec12; eauto.

      repeat (split; eauto 2 using cmds_at_block_tail_next); try solve [
        solve_if_rsim |
        apply reg_simulation__updateAddAL; auto |
        match goal with
        | Heqb2 : exists _, exists _, exists _, ?B = _,
          Hbsim : block_simulation _ _ _ ?B |- 
          cmds_simulation _ _ _ _ _ _ _ _ =>
          destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst;
          eapply cmds_simulation_stable;
            eauto using original_ids_in_phi_arent_temporaries
        end | 
        eapply ECs_simulation_tail_stable; eauto].
   
  Case "<>".
    apply cmds_simulation_other_cons_inv in Htcmds; eauto.
    destruct Htcmds as [cs1' [Heq Htcmds]]; subst.

    exists 
      (Opsem.mkState 
        ((Opsem.mkEC 
           F1
           (block_intro l1 ps1
             (cs11 ++ insn_call rid noret0 ca ft fv lp :: cs1') 
             tmn)
           cs1' tmn lc1' als)::ECs1) Mem').
    split.

      assert (if fdef_dec (PI_f pinfo) F1
            then value_has_no_tmps pinfo fv else True) as Hntmp.
        destruct (fdef_dec (PI_f pinfo) F1); subst; auto; try congruence.
      inv H0.
      eapply lookupExFdecViaPtr__simulation with (TD:=(los,nts))(gl:=gl)
        (lc1:=lc1)(lc2:=lc) in H1; eauto.
      destruct H1 as [J3 J4].
      apply OpsemProps.sInsn__implies__sop_star.
      econstructor; eauto.
        erewrite params2GVs__simulation with (lc2:=lc); eauto.
          destruct (fdef_dec (PI_f pinfo) F1); subst; auto; try congruence.

      repeat (split; eauto 2 using cmds_at_block_tail_next); try solve [
        solve_if_rsim |
        apply reg_simulation__updateAddAL; auto |
        eapply cmds_simulation_other_stable; eauto |
        eapply ECs_simulation_tail_stable; eauto].
Qed.

Lemma phinodes_placement_is_bsim : forall maxb pinfo Cfg1 St1 Cfg2 St2 St2' tr
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo Cfg1 St1 Cfg2 St2)
  (Hop: Opsem.sInsn Cfg2 St2 St2' tr), 
  exists St1',
    Opsem.sop_star Cfg1 St1 St1' tr /\    
    State_simulation pinfo Cfg1 St1' Cfg2 St2'.
Proof.
  intros.
  (sInsn_cases (induction Hop) Case); 
    try apply noalias_State__noalias_EC in Hnoalias.

Case "sReturn".  
Focus.
  destruct_ctx_return.
  apply cmds_simulation_nil_inv in Htcmds. subst.
  apply cmds_simulation_non_ldst_cons_inv in Htcmds'; 
    try solve [
      destruct Heqb1' as [l3 [ps3 [cs3 Heqb1']]]; subst; eauto |
      simpl; auto
    ].
  destruct Htcmds' as [cs1'0 [EQ Htcmds']]; subst.
  assert (HwfF := Hwfs).
  eapply wf_system__wf_fdef with (f:=F1) in HwfF; eauto.
  assert (if fdef_dec (PI_f pinfo) F1
          then value_has_no_tmps pinfo Result else True) as Hnontmp.
    apply original_values_arent_tmps with 
      (instr:=insn_terminator (insn_return rid RetTy Result))(B:=B1)
      (ifs:=nil)(S:=S1)(m:=module_intro los nts Ps1); 
      simpl; try solve [auto | solve_tmnInFdefBlockB].
  eapply returnUpdateLocals_rsim in H1; eauto.
  destruct H1 as [lc1'' [H1 Hrsim'']].
  exists 
    (Opsem.mkState ((Opsem.mkEC F1' B1' cs1'0 tmn' lc1'' als')::ECs1) Mem').
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply OpsemProps.sInsn__implies__sop_star.
    constructor; auto.
  
    repeat (split; eauto 2 using cmds_at_block_tail_next).
      destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
      destruct Heqb2' as [l2 [ps2 [cs21 Heqb2']]]; subst.
      eapply cmds_simulation_stable; eauto.
      eapply ECs_simulation_tail_stable; eauto.
Unfocus.

Case "sReturnVoid".
Focus.
  destruct_ctx_return.
  apply cmds_simulation_nil_inv in Htcmds. subst.
  apply cmds_simulation_non_ldst_cons_inv in Htcmds'; 
    try solve [
      destruct Heqb1' as [l3 [ps3 [cs3 Heqb1']]]; subst; eauto |
      simpl; auto
    ].
  destruct Htcmds' as [cs1'0 [EQ Htcmds']]; subst.
  exists 
    (Opsem.mkState ((Opsem.mkEC F1' B1' cs1'0 tmn' lc1' als')::ECs1) Mem').
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply OpsemProps.sInsn__implies__sop_star.
    constructor; auto.
  
    repeat (split; eauto 2 using cmds_at_block_tail_next).
      destruct Heqb1' as [l1 [ps1 [cs11 Heqb1']]]; subst.
      destruct Heqb2' as [l2 [ps2 [cs21 Heqb2']]]; subst.
      eapply cmds_simulation_stable; eauto.
      eapply ECs_simulation_tail_stable; eauto.
Unfocus.

Case "sBranch". eapply phinodes_placement_is_correct__dsBranch; eauto.
Case "sBranch_uncond". 
  eapply phinodes_placement_is_correct__dsBranch_uncond; eauto. 
Case "sBop". abstract phinodes_placement_is_correct__common.
Case "sFBop". abstract phinodes_placement_is_correct__common.
Case "sExtractValue". abstract phinodes_placement_is_correct__common.
Case "sInsertValue". abstract phinodes_placement_is_correct__common.
Case "sMalloc". abstract phinodes_placement_is_correct__common.
Case "sFree". abstract phinodes_placement_is_correct__common.
Case "sAlloca". abstract phinodes_placement_is_correct__common.
Case "sLoad". eapply phinodes_placement_is_correct__dsLoad; eauto.
Case "sStore". eapply phinodes_placement_is_correct__dsStore; eauto.
Case "sGEP". abstract phinodes_placement_is_correct__common.
Case "sTrunc". abstract phinodes_placement_is_correct__common.
Case "sExt". abstract phinodes_placement_is_correct__common.
Case "sCast". abstract phinodes_placement_is_correct__common.
Case "sIcmp". abstract phinodes_placement_is_correct__common.
Case "sFcmp". abstract phinodes_placement_is_correct__common.
Case "sSelect". abstract phinodes_placement_is_correct__common.
Case "sCall". eapply phinodes_placement_is_correct__dsCall; eauto.
Case "sExCall". eapply phinodes_placement_is_correct__dsExCall; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
*)
