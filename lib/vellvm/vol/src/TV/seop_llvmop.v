Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import infrastructure_props.
Require Import opsem.
Require Import opsem_props.
Require Import dopsem.
Require Import trace.
Require Import symexe_def.
Require Import alist.

(****************************************************)
(* seop -> llvmop *)

Import Opsem.
Import OpsemProps.

Ltac replace_gv2gvs :=
match goal with
| [ t : typ |- context [(blk2GV ?TD ?mb)] ] => 
    replace (blk2GV TD mb) with ($ (blk2GV TD mb) # (typ_pointer t) $); eauto
| [ t : typ |- context [(updateAddAL _ ?lc ?id ?gv)] ] => 
    replace gv with ($ gv # t $); eauto
end.

Lemma seop_dbCmd__llvmop_dbInsn : forall TD lc als gl fs Mem c lc' als' Mem' tr 
    S Ps F B tmn cs,
  SimpleSE.dbCmd TD gl lc als Mem c lc' als' Mem' tr ->
  bInsn (mkbCfg S TD Ps gl fs F)
    (mkbEC B (c::cs) tmn lc als Mem) (mkbEC B cs tmn lc' als' Mem') tr.
Proof.
  intros TD lc als gl fs Mem0 c lc' als' Mem' tr S Ps F B tmn cs H.
  (se_dbCmd_cases (destruct H) Case); try replace_gv2gvs; 
    eauto using (@bSelect DGVs).
Qed.
  
Lemma seop_dbCmds__llvmop_dbop : forall TD lc als gl fs Mem cs cs' lc' als' Mem'
    tr S Ps F B tmn,
  SimpleSE.dbCmds TD gl lc als Mem cs lc' als' Mem' tr ->
  bops (mkbCfg S TD Ps gl fs F) 
    (mkbEC B (cs++cs') tmn lc als Mem) (mkbEC B cs' tmn lc' als' Mem') tr.
Proof.
  intros TD lc als gl fs Mem0 cs cs' lc' als' Mem' tr S Ps F B tmn H.
  generalize dependent S.
  generalize dependent Ps.
  generalize dependent F.
  generalize dependent B.
  generalize dependent tmn.
  generalize dependent cs'.
  (se_dbCmds_cases (induction H) Case);intros; auto.
    simpl_env.
    apply seop_dbCmd__llvmop_dbInsn with (S:=S)(Ps:=Ps)(F:=F)(B:=B)
      (tmn:=tmn)(cs:=cs++cs')(fs:=fs) in H; eauto.
Qed.

Lemma seop_dbTerminator__llvmop_dbInsn : forall TD lc als gl fs Mem lc' tr S Ps 
    F B tmn l' ps' cs' tmn',
  SimpleSE.dbTerminator TD Mem F gl B lc tmn (block_intro l' ps' cs' tmn') lc' tr
    ->
  bInsn (mkbCfg S TD Ps gl fs F) (mkbEC B nil tmn lc als Mem)
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc' als Mem) tr.
Proof.
  intros TD lc als gl fs Mem0 lc' tr S Ps F B tmn l' ps' cs' tmn' H.
  inversion H; subst; eauto.
Qed.

Definition seop_dbCall__llvmop_dbCall_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' 
  tr (db:SimpleSE.dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr) :=
  forall F B tmn cs als,
  bInsn (mkbCfg S TD Ps gl fs F) 
    (mkbEC B (call0::cs) tmn lc als Mem0) (mkbEC B cs tmn lc' als Mem') tr.
Definition seop_dbSubblock__llvmop_dbop_prop S TD Ps fs gl lc als Mem cs lc' als'
Mem' tr (db:SimpleSE.dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  forall F B tmn cs',
  bops (mkbCfg S TD Ps gl fs F)  
    (mkbEC B (cs++cs') tmn lc als Mem) (mkbEC B cs' tmn lc' als' Mem') tr.
Definition seop_dbSubblocks__llvmop_dbop_prop S TD Ps fs gl lc als Mem cs lc' 
  als' Mem' tr
  (db:SimpleSE.dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr) :=
  forall F B tmn cs',
  bops (mkbCfg S TD Ps gl fs F)   
    (mkbEC B (cs++cs') tmn lc als Mem) (mkbEC B cs' tmn lc' als' Mem') tr.
Definition seop_dbBlock__llvmop_dbop_prop S TD Ps fs gl F state state' tr
  (db:SimpleSE.dbBlock S TD Ps fs gl F state state' tr) :=
  forall l ps cs tmn lc als Mem l' ps' cs' tmn' lc' als' Mem',
  state = SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem 
    ->
  state' = SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' 
    als') Mem' ->
  bops (mkbCfg S TD Ps gl fs F) 
    (mkbEC (block_intro l ps cs tmn) cs tmn lc als Mem)
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc' als' Mem') tr.
Definition seop_dbBlocks__llvmop_dbop_prop S TD Ps fs gl F state state' tr
  (db:SimpleSE.dbBlocks S TD Ps fs gl F state state' tr) :=
  forall l ps cs tmn lc als Mem l' ps' cs' tmn' lc' als' Mem',
  state = SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem 
    ->
  state' = SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' 
    als') Mem' ->
  bops (mkbCfg S TD Ps gl fs F)  
    (mkbEC (block_intro l ps cs tmn) cs tmn lc als Mem)
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc' als' Mem') tr.
Definition seop_dbFdef__llvmop_dbFdef_prop fid rt lp S TD Ps lc gl fs Mem lc' 
  als' Mem' B' Rid oResult tr
  (db:SimpleSE.dbFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid 
    oResult tr) :=
  bFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr.

Lemma seop__llvmop :
  (forall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db, 
     seop_dbCall__llvmop_dbCall_prop S TD Ps fs gl lc Mem0 call0 lc' Mem' tr db) 
    /\
  (forall S TD Ps fs gl lc als Mem sb lc' als' Mem' tr db,
     seop_dbSubblock__llvmop_dbop_prop S TD Ps fs gl lc als Mem sb lc' als' Mem' 
       tr db) /\
  (forall S TD Ps fs gl lc als Mem sbs lc' als' Mem' tr db,
     seop_dbSubblocks__llvmop_dbop_prop S TD Ps fs gl lc als Mem sbs lc' als' 
       Mem' tr db) /\
  (forall S TD Ps fs gl F state1 state2 tr db,
     seop_dbBlock__llvmop_dbop_prop S TD Ps fs gl F state1 state2 tr db) /\
  (forall S TD Ps fs gl F state1 state2 tr db,
     seop_dbBlocks__llvmop_dbop_prop S TD Ps fs gl F state1 state2 tr db) /\
  (forall fid rt lp S1 TD Ps1 lc gl fs Mem lc' als' Mem' B' Rid oResult tr db,
     seop_dbFdef__llvmop_dbFdef_prop fid rt lp S1 TD Ps1 lc gl fs Mem lc' als' 
       Mem' B' Rid oResult tr db).
Proof.
(se_db_mutind_cases
  apply SimpleSE.db_mutind with
    (P  := seop_dbCall__llvmop_dbCall_prop)
    (P0 := seop_dbSubblock__llvmop_dbop_prop)
    (P1 := seop_dbSubblocks__llvmop_dbop_prop)
    (P2 := seop_dbBlock__llvmop_dbop_prop)
    (P3 := seop_dbBlocks__llvmop_dbop_prop)
    (P4 := seop_dbFdef__llvmop_dbFdef_prop) Case);
  unfold seop_dbCall__llvmop_dbCall_prop, 
         seop_dbFdef__llvmop_dbFdef_prop, seop_dbSubblock__llvmop_dbop_prop,
         seop_dbSubblocks__llvmop_dbop_prop, seop_dbBlock__llvmop_dbop_prop,
         seop_dbBlocks__llvmop_dbop_prop; intros; subst; eauto.
Case "dbSubblock_intro".
  apply seop_dbCmds__llvmop_dbop with (Ps:=Ps)(F:=F)(B:=B)(tmn:=tmn)
    (S:=S)(cs':=call0::cs')(fs:=fs) in d.
  eapply bops_trans; simpl_env ; eauto.
    apply bInsn__bops; auto. 

Case "dbSubblocks_cons".
  rewrite app_ass.
  apply bops_trans with (state2:=mkbEC B (cs'++cs'0) tmn lc2 als2 Mem2); eauto.

Case "dbBlock_intro".
  inversion H0; subst. clear H0.
  inversion H1; subst. clear H1.
  rewrite <- trace_app_commute.
  apply bops_trans with (state2:=mkbEC (block_intro l1 ps0 
    (cs++cs') tmn0) cs' tmn0 lc2 als2 Mem2); eauto.
    apply seop_dbCmds__llvmop_dbop with (fs:=fs)(Ps:=Ps)(F:=F)
      (B:=block_intro l1 ps0 (cs++cs') tmn0)(S:=S)(cs':=nil)
      (tmn:=tmn0) in d0.
    apply seop_dbTerminator__llvmop_dbInsn with (fs:=fs)(Ps:=Ps)(F:=F)
      (S:=S)(als:=als')(Mem:=Mem') in d1.
    simpl_env in d0.
    apply bops_trans with (state2:=mkbEC (block_intro l1 ps0 
      (cs++cs') tmn0) nil tmn0 lc3 als' Mem'); auto.
      apply bInsn__bops; auto. 

Case "dbBlocks_nil".
  inversion H0; subst. clear H0.
  auto.

Case "dbBlocks_cons".
  inversion d; subst.
  destruct B'.
  apply bops_trans with (state2:=mkbEC (block_intro l1 p c t) c t lc4 als3 Mem3); 
    eauto.

Case "dbFdef_func".
  eapply bFdef_func; eauto.
    rewrite <- trace_app_commute.
    apply seop_dbCmds__llvmop_dbop with (fs:=fs)(Ps:=Ps)(F:=fdef_intro 
      (fheader_intro fa rt fid la va) lb)(B:=block_intro l2 ps2 (cs21++cs22) 
        (insn_return rid rt Result))(S:=S)(cs':=nil)
      (tmn:=insn_return rid rt Result) in d1.
    simpl_env in d1. 
    apply bops_trans with (state2:=mkbEC 
        (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) 
        (cs21++cs22) (insn_return rid rt Result) lc1 als1 Mem1); 
      auto.
    apply bops_trans with (state2:=mkbEC
        (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) cs22 
        (insn_return rid rt Result) lc2 als2 Mem2); auto.

Case "dbFdef_proc".
  eapply bFdef_proc; eauto.
    rewrite <- trace_app_commute.
    apply seop_dbCmds__llvmop_dbop with (fs:=fs)(Ps:=Ps)
      (F:=fdef_intro (fheader_intro fa rt fid la va) lb)
      (B:=block_intro l2 ps2 (cs21++cs22) (insn_return_void rid))
        (S:=S)(cs':=nil)(tmn:=insn_return_void rid) in d1.
    simpl_env in d1. 
    apply bops_trans with (state2:=mkbEC 
        (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) (cs21++cs22) 
        (insn_return_void rid) lc1 als1 Mem1); auto.
    apply bops_trans with (state2:=mkbEC
        (block_intro l2 ps2 (cs21++cs22) 
        (insn_return_void rid)) cs22 (insn_return_void rid) lc2 als2 Mem2); auto.
Qed.

Lemma seop_dbCall__llvmop_dbCall : forall S TD Ps fs gl lc Mem0 call0 lc' Mem' 
    tr F B tmn cs als,
  SimpleSE.dbCall S TD Ps fs gl lc Mem0 call0 lc' Mem' tr ->
  bInsn (mkbCfg S TD Ps gl fs F)  
    (mkbEC B (call0::cs) tmn lc als Mem0) (mkbEC B cs tmn lc' als Mem') tr.
Proof.
  intros.
  destruct seop__llvmop as [J _]. 
  apply J; auto.
Qed.

Lemma seop_dbSubblock__llvmop_dbop : forall S TD Ps fs gl lc als Mem cs lc' als'
    Mem' tr F B tmn cs',
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  bops (mkbCfg S TD Ps gl fs F)   
    (mkbEC B (cs++cs') tmn lc als Mem) (mkbEC B cs' tmn lc' als' Mem') tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [J _]]. 
  apply J; auto.
Qed.

Lemma seop_dbSubblocks__llvmop_dbop : forall S TD Ps fs gl lc als Mem cs lc' als'
    Mem' tr F B tmn cs',
  SimpleSE.dbSubblocks S TD Ps fs gl lc als Mem cs lc' als' Mem' tr ->
  bops (mkbCfg S TD Ps gl fs F)    
    (mkbEC B (cs++cs') tmn lc als Mem) (mkbEC B cs' tmn lc' als' Mem') tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [J _]]]. 
  apply J; auto.
Qed.

Lemma seop_dbBlock__llvmop_dbop :  forall S TD Ps fs gl F tr l ps cs tmn lc 
    als Mem l' ps' cs' tmn' lc' als' Mem',
  SimpleSE.dbBlock S TD Ps fs gl F 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') 
    Mem') tr ->
  bops (mkbCfg S TD Ps gl fs F) 
    (mkbEC (block_intro l ps cs tmn) cs tmn lc als Mem)
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc' als' Mem') tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [J _]]]]. 
  unfold seop_dbBlock__llvmop_dbop_prop in J.
  eapply J; eauto.
Qed.

Lemma seop_dbBlocks__llvmop_dbop : forall S TD Ps fs gl F tr l ps cs tmn lc 
    als Mem l' ps' cs' tmn' lc' als' Mem',
  SimpleSE.dbBlocks S TD Ps fs gl F
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs' tmn') lc' als') 
      Mem') tr ->  
  bops (mkbCfg S TD Ps gl fs F)  
    (mkbEC (block_intro l ps cs tmn) cs tmn lc als Mem)
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc' als' Mem') tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [_ [J _]]]]]. 
  unfold seop_dbBlocks__llvmop_dbop_prop in J.
  eapply J; eauto.
Qed.

Lemma seop_dbFdef__llvmop_dbFdef : forall fid rt lp S TD Ps lc gl fs Mem lc' als'
    Mem' B' Rid oResult tr,
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr 
    ->
  bFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid 
    oResult tr.
Proof.
  intros.
  destruct seop__llvmop as [_ [_ [_ [_ [_ J]]]]]. 
  apply J; auto.
Qed.

(****************************************************)
(* llvmop -> seop *)

Lemma dbBlock__dbBlocks : forall S TD Ps fs gl F state state' tr,
  SimpleSE.dbBlock S TD Ps fs gl F state state' tr -> 
  SimpleSE.dbBlocks S TD Ps fs gl F state state' tr.
Proof.
  intros S TD Ps fs gl F state state' tr H.
  rewrite <- trace_app_nil__eq__trace.
  eapply SimpleSE.dbBlocks_cons; eauto.
Qed.

Lemma dbTerminator__dbBlock : forall TD F fs gl lc tmn l ps B' lc' tr als Ps S 
  Mem,
  SimpleSE.dbTerminator TD Mem F gl (block_intro l ps nil tmn) lc tmn B' lc' tr 
    ->
  SimpleSE.dbBlock S TD Ps fs gl F 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps nil tmn) lc als) Mem)
    (SimpleSE.mkState (SimpleSE.mkEC B' lc' als) Mem)
    tr.
Proof.
  intros TD F fs gl lc tmn l0 ps B' lc' tr als Ps S Mem0 H.
  rewrite <- nil_app_trace__eq__trace.
  rewrite <- nil_app_trace__eq__trace with (tr:=trace_nil).
  assert (@nil cmd=nil++nil) as EQ. auto.
  rewrite EQ.
  apply SimpleSE.dbBlock_intro with (lc2:=lc)(als2:=als)(Mem2:=Mem0)(lc3:=lc); 
    auto.
Qed.

Lemma dbCmd_dbSubblock__dbSubblock : forall S TD Ps lc als gl fs Mem0 c lc1 als1 
    Mem1 tr1 cs lc2 als2 Mem2 tr2,
  SimpleSE.dbCmd TD gl lc als Mem0 c lc1 als1 Mem1 tr1 ->
  SimpleSE.dbSubblock S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr2 ->
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem0 (c::cs) lc2 als2 Mem2 
    (trace_app tr1 tr2).
Proof.
 intros S TD Ps lc als gl fs Mem0 c lc1 als1 Mem1 tr1 cs lc2 als2 Mem2 tr2 H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  assert (c::cs0++call0::nil = (c::cs0)++call0::nil) as EQ. auto.
  rewrite EQ.
  eapply SimpleSE.dbSubblock_intro; eauto.
Qed.

Lemma dbCmd_dbSubblocks__dbCmd_or_dbSubblocks : forall S TD Ps lc als gl fs Mem0
    c lc1 als1 Mem1 tr1 cs lc2 als2 Mem2 tr2,
  SimpleSE.dbCmd TD gl lc als Mem0 c lc1 als1 Mem1 tr1 ->
  SimpleSE.dbSubblocks S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr2 ->
  (SimpleSE.dbCmd TD gl lc als Mem0 c lc2 als2 Mem2 tr1 /\ 
   cs = nil /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ Mem1 = Mem2 
  ) \/
  (SimpleSE.dbSubblocks S TD Ps fs gl lc als Mem0 (c::cs) lc2 als2 Mem2 
    (trace_app tr1 tr2)).
Proof.
 intros S TD Ps lc als gl fs Mem0 c lc1 als1 Mem1 tr1 cs lc2 als2 Mem2 tr2 H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      assert (c::cs0++cs'=(c::cs0)++cs') as EQ. auto.
      rewrite EQ.
      eapply SimpleSE.dbSubblocks_cons; eauto using dbCmd_dbSubblock__dbSubblock.
Qed.

Lemma dbTerminator_eqlabel : forall TD M F gl l1 ps1 cs1 tmn1 lc1 B lc2 tr cs2,
  SimpleSE.dbTerminator TD M F gl (block_intro l1 ps1 cs1 tmn1) lc1 tmn1 B lc2 
    tr ->
 SimpleSE.dbTerminator TD M F gl (block_intro l1 ps1 cs2 tmn1) lc1 tmn1 B lc2 tr.
Proof.
  intros.
  inversion H; subst.
    rewrite (@switchToNewBasicBlock_eq DGVs) with (ps2:=ps1)(cs2:=cs2)
      (tmn2:=insn_br bid Cond l0 l2) in H2; eauto.
    rewrite (@switchToNewBasicBlock_eq DGVs) with (ps2:=ps1)(cs2:=cs2)
      (tmn2:=insn_br_uncond bid l0) in H1; eauto.
Qed.

Lemma dbCmd_dbBlock__dbBlock : forall S TD Ps fs lc als gl Mem0 c lc1 als1 Mem1 
    tr1 lc2 als2 Mem2 tr2 l1 ps1 cs1 tmn1 B F,
  SimpleSE.dbCmd TD gl lc als Mem0 c lc1 als1 Mem1 tr1 ->
  SimpleSE.dbBlock S TD Ps fs gl F
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) 
       Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) Mem2)
    tr2 ->
  SimpleSE.dbBlock S TD Ps fs gl F 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (c::cs1) tmn1) lc als) 
       Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) Mem2)
    (trace_app tr1 tr2).
Proof.
  intros S TD Ps fs lc als gl Mem0 c lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
    l1 ps1 cs1 tmn1 B F H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  rewrite trace_app_commute.
  apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)(gl:=gl)
    (Mem0:=Mem0)(c:=c)(tr1:=tr1) in H19; auto.
  destruct H19 as [[J11 [EQ [EQ' [EQ1 [EQ2 EQ3]]]]] | J11]; subst.
    assert (c::nil++cs'=nil++c::cs') as EQ. auto.
    rewrite EQ. clear EQ.
    rewrite trace_app_nil__eq__trace.
    rewrite <- nil_app_trace__eq__trace.
    rewrite trace_app_commute.
    eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_eqlabel.

    assert (c::cs++cs'=(c::cs)++cs') as EQ. auto.
    rewrite EQ. clear EQ.
    eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_eqlabel.
Qed.

Lemma dbCmd_dbBlocks__dbCmd_or_dbBlocks : forall S TD Ps fs lc als gl Mem0 c lc1 
    als1 Mem1 tr1 lc2 als2 Mem2 tr2 l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F,
  SimpleSE.dbCmd TD gl lc als Mem0 c lc1 als1 Mem1 tr1 ->
  SimpleSE.dbBlocks S TD Ps fs gl F
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) 
      Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) 
      Mem2)
    tr2 ->
  (SimpleSE.dbCmd TD gl lc als Mem0 c lc2 als2 Mem2 tr1 /\ 
   cs1 = cs2 /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ Mem1 = Mem2 /\
   l1 = l2 /\ ps1 = ps2 /\ tmn1 = tmn2
  ) \/
  (SimpleSE.dbBlocks S TD Ps fs gl F
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (c::cs1) tmn1) lc als) 
      Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) 
      Mem2)
    (trace_app tr1 tr2)).
Proof.
  intros S TD Ps fs lc als gl Mem0 c lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
    l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      inversion H; subst.
      eapply SimpleSE.dbBlocks_cons; eauto using dbCmd_dbBlock__dbBlock.
Qed.

Lemma dbCall__dbSubblock : forall S TD Ps fs lc gl Mem c lc' Mem' tr als,
  SimpleSE.dbCall S TD Ps fs gl lc Mem c lc' Mem' tr ->
  SimpleSE.dbSubblock S TD Ps fs gl
    lc als Mem
    (c::nil)
    lc' als Mem'
    tr.
Proof.
  intros S TD Ps fs lc gl Mem0 c lc' Mem' tr als H.
  rewrite <- nil_app_trace__eq__trace.
  assert (c::nil=nil++c::nil) as EQ. auto.
  rewrite EQ.
  apply SimpleSE.dbSubblock_intro with (lc2:=lc)(Mem2:=Mem0); auto.
Qed.

Lemma dbCall_isCallInst : forall S TD Ps fs lc gl Mem c lc' Mem' tr,
  SimpleSE.dbCall S TD Ps fs gl lc Mem c lc' Mem' tr ->
  Instruction.isCallInst c = true.
Proof.
  intros S TD Ps lc fs gl Mem0 c lc' Mem' tr HdbCall.
  induction HdbCall; auto.
Qed.

Lemma dbSubblock_dbBlock__dbBlock : forall S TD Ps fs lc als gl Mem0 cs lc1 als1 
    Mem1 tr1 lc2 als2 Mem2 tr2 l1 ps1 cs1 tmn1 B F,
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem0 cs lc1 als1 Mem1 tr1 ->
  SimpleSE.dbBlock S TD Ps fs gl F 
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) 
      Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) Mem2)
    tr2 ->
  SimpleSE.dbBlock S TD Ps fs gl F
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (cs++cs1) tmn1) lc als) 
      Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC B lc2 als2) Mem2)
    (trace_app tr1 tr2).
Proof.
  intros S TD Ps fs lc als gl Mem0 cs lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
    l1 ps1 cs1 tmn1 B F H1 H2.
  inversion H2; subst.  
  rewrite trace_app_commute.
  rewrite trace_app_commute.
  rewrite <- app_ass.
  eapply SimpleSE.dbBlock_intro; eauto using dbTerminator_eqlabel.
Qed.

Lemma dbSubblock_dbBlocks__dbSubblock_or_dbBlocks : forall S TD Ps fs lc als gl
   Mem0 cs lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F,
  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem0 cs lc1 als1 Mem1 tr1 ->
  SimpleSE.dbBlocks S TD Ps fs gl F
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 cs1 tmn1) lc1 als1) 
      Mem1)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) 
      Mem2)
    tr2 ->
  (  SimpleSE.dbSubblock S TD Ps fs gl lc als Mem0 cs lc1 als1 Mem1 tr1 /\ 
   cs1 = cs2 /\ tr2 = trace_nil /\ 
   lc1 = lc2 /\ als1 = als2 /\ Mem1 = Mem2 /\
   l1 = l2 /\ ps1 = ps2 /\ tmn1 = tmn2
  ) \/
  (SimpleSE.dbBlocks S TD Ps fs gl F  
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l1 ps1 (cs++cs1) tmn1) lc als)
      Mem0)
    (SimpleSE.mkState (SimpleSE.mkEC (block_intro l2 ps2 cs2 tmn2) lc2 als2) Mem2)
    (trace_app tr1 tr2)).
Proof.
  intros S TD Ps fs lc als gl Mem0 cs lc1 als1 Mem1 tr1 lc2 als2 Mem2 tr2 
    l1 ps1 cs1 tmn1 l2 ps2 cs2 tmn2 F H1 H2.
  inversion H2; subst.
    left. repeat (split; auto).
    right. 
      rewrite trace_app_commute.
      inversion H; subst.
      eapply SimpleSE.dbBlocks_cons; eauto using dbSubblock_dbBlock__dbBlock.
Qed.


Definition llvmop_dbInsn__seop_prop cfg state1 state2 tr
  (db:bInsn cfg state1 state2 tr) :=
  forall S los nts Ps F l ps cs tmn lc als gl fs Mem cs0,
  cfg = mkbCfg S (los, nts) Ps gl fs F ->
  state1 = mkbEC (block_intro l ps cs0 tmn) cs tmn lc als Mem ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps)
    F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = mkbEC (block_intro l' ps' cs0' tmn') cs' tmn' lc' als' Mem' /\
  ((cs = nil /\ Mem = Mem' /\ als = als' /\ cs' = cs0' /\
              SimpleSE.dbTerminator (los, nts) Mem' F gl
                 (block_intro l ps cs tmn) lc
                 tmn 
                 (block_intro l' ps' cs' tmn') lc' 
                 tr ) \/ 
  (exists c, c::cs' = cs /\ SimpleSE.dbCmd (los, nts) gl lc als Mem c lc' als' 
    Mem' tr) \/
  (exists c, c::cs' = cs /\ SimpleSE.dbCall S (los, nts) Ps fs gl lc Mem c lc' 
    Mem' tr)).
Definition llvmop_dbop__seop_prop cfg state1 state2 tr
  (db:bops cfg state1 state2 tr) :=
  forall S los nts Ps F l ps cs tmn lc als gl fs Mem l' ps' cs' tmn' lc' als'
    Mem' cs0 cs0',
  cfg = mkbCfg S (los, nts) Ps gl fs F ->
  state1 = mkbEC (block_intro l ps cs0 tmn) cs tmn lc als Mem ->
  state2 = mkbEC (block_intro l' ps' cs0' tmn') cs' tmn' lc' als' Mem' ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps)
    F ->
  (exists cs1, exists cs2, 
  exists tr1, exists tr2,
  exists lc1, exists als1, exists Mem1,
    trace_app tr1 tr2 = tr /\  
    l = l' /\
    ps = ps' /\
    cs0 = cs0' /\
    tmn = tmn' /\
    cs = cs1++cs2++cs' /\
    SimpleSE.dbSubblocks S (los, nts) Ps fs gl
      lc als Mem
      cs1
      lc1 als1 Mem1
      tr1 /\
    SimpleSE.dbCmds (los, nts) gl
      lc1 als1 Mem1
      cs2
      lc' als' Mem'
      tr2) \/
  (exists cs1, exists cs2, 
  exists tr1, exists tr2, exists tr3,
  exists lc1, exists als1, exists Mem1,
  exists lc2, exists als2,  exists Mem2,
    cs1++cs2++cs'=cs0' /\
    (trace_app (trace_app tr1 tr2) tr3) = tr /\
    SimpleSE.dbBlocks S (los, nts) Ps fs gl F  
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs0' tmn') lc1 als1) Mem1)
      tr1 /\
    SimpleSE.dbSubblocks S (los, nts) Ps fs gl
      lc1 als1 Mem1
      cs1
      lc2 als2 Mem2
      tr2 /\
    SimpleSE.dbCmds (los, nts) gl
      lc2 als2 Mem2
      cs2
      lc' als' Mem'
      tr3).
Definition llvmop_dbFdef__seop_dbFdef_prop fid rt lp S TD Ps lc gl fs Mem lc'
    als' Mem' B' Rid oResult tr
  (db:bFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr) :=
  forall los nts,
  TD = (los, nts) ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  SimpleSE.dbFdef fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr.

Ltac dos_simpl := repeat dgvs_instantiate_inv.

Ltac app_inv :=
  match goal with
  | [ H: ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ ] => inv H
  | [ H: ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ ] => inv H
  | [ H: ?f _ _ = ?f _ _ |- _ ] => inv H
  end.

Lemma llvmop__seop : 
  (forall cfg state1 state2 tr db, @llvmop_dbInsn__seop_prop cfg state1 state2 tr db) /\
  (forall cfg state1 state2 tr db, @llvmop_dbop__seop_prop cfg state1 state2 tr  db) /\
  (forall fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db, 
    @llvmop_dbFdef__seop_dbFdef_prop fid rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db).
Proof.
(b_mutind_cases
  apply b_mutind with
    (P  := llvmop_dbInsn__seop_prop)
    (P0 := llvmop_dbop__seop_prop)
    (P1 := llvmop_dbFdef__seop_dbFdef_prop) Case);
  unfold llvmop_dbInsn__seop_prop, llvmop_dbop__seop_prop, 
    llvmop_dbFdef__seop_dbFdef_prop; intros; dos_simpl; subst; repeat app_inv.
Case "bBranch".
  exists l'. exists ps'. exists cs'. exists tmn'. exists lc'.
  exists als0. exists Mem1.
  exists cs'. split; auto.
  left. 
  split; auto.
  split; auto.
  split; auto.
  split; auto.
    apply SimpleSE.dbBranch with (c:=c); auto.
      erewrite switchToNewBasicBlock_eq; eauto.

Case "bBranch_uncond".
  exists l'. exists ps'. exists cs'. exists tmn'. exists lc'.
  exists als0. exists Mem1.
  exists cs'. split; auto.
  left.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
    apply SimpleSE.dbBranch_uncond; auto.
      erewrite switchToNewBasicBlock_eq; eauto.

Case "bBop".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_bop id0 bop0 sz0 v1 v2).
  split; eauto.

Case "bFBop".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_fbop id0 fbop0 fp v1 v2).
  split; eauto.

Case "bExtractValue".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv'). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_extractvalue id0 t v idxs).
  split; eauto.

Case "bInsertValue".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv''). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_insertvalue id0 t v t' v' idxs).
  split; eauto.

Case "bMalloc".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (blk2GV (los, nts) mb)). exists als0. 
  exists Mem'. exists cs1. split; auto.
  right. left.
  exists (insn_malloc id0 t v align0).
  split; eauto.

Case "bFree".
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_free fid t v).
  split; eauto.

Case "bAlloca".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 (blk2GV (los, nts) mb)). exists (mb::als0). 
  exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_alloca id0 t v align0).
  split; eauto.

Case "bLoad".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_load id0 t v align0).
  split; eauto.

Case "bStore".
  exists l0. exists ps. exists cs. exists tmn0.
  exists lc0. exists als0. exists Mem'.
  exists cs1. split; auto.
  right. left.
  exists (insn_store sid t v1 v2 align0).
  split; eauto.

Case "bGEP".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 mp'). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_gep id0 inbounds0 t v idxs).
  split; eauto.

Case "bTrunc".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_trunc id0 truncop0 t1 v1 t2).
  split; eauto.

Case "bExt".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_ext id0 extop0 t1 v1 t2).
  split; eauto.

Case "bCast".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv2). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_cast id0 castop0 t1 v1 t2).
  split; eauto.

Case "bIcmp".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_icmp id0 cond0 t v1 v2).
  split; eauto.

Case "bFcmp".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (updateAddAL _ lc0 id0 gv3). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_fcmp id0 fcond0 fp v1 v2).
  split; eauto.

Case "bSelect".
  exists l0. exists ps. exists cs. exists tmn0.
  exists (if isGVZero (los, nts) c then updateAddAL _ lc0 id0 gv2 else updateAddAL _ lc0 id0 gv1). exists als0. exists Mem1.
  exists cs1. split; auto.
  right. left.
  exists (insn_select id0 v0 t v1 v2).
  split; eauto.

Case "bCall".
  apply blockInSystemModuleFdef_inv in H3.
  destruct H3 as [J1 [J2 [J3 _]]].
  exists l0. exists ps. exists cs. exists tmn0. exists lc''.
  exists als0. exists Mem''.
  exists cs1. split; auto.
    right. right.
    exists (insn_call rid noret0 ca ft fv lp).
    split; eauto.

Case "bExCall".
  exists l0. exists ps. exists cs. exists tmn0. exists lc'.
  exists als0. exists Mem'.
  exists cs1. split; auto.
  right. right.
  exists (insn_call rid noret0 ca ft fv lp).
  split; eauto.

Case "bops_nil".
  left.
  exists nil. exists nil.
  exists trace_nil. exists trace_nil.
  exists lc'. exists als'. exists Mem'.
  repeat (split; auto).
  
Case "bops_cons".
  destruct (@H S los nts Ps F l0 ps cs tmn lc als gl fs Mem0 cs0)
    as [l1 [ps1 [cs1 [tmn1 [lc1 [als1 [Mem1 [cs2 [J1 J2]]]]]]]]]; subst; auto.
  clear H.
  assert (mkbEC (block_intro l1 ps1 cs2 tmn1) cs1 tmn1 lc1 als1 Mem1 =
    mkbEC (block_intro l1 ps1 cs2 tmn1) cs1 tmn1 lc1 als1 Mem1) as J'. auto.
  assert (d':=b).
  apply bInsn_preservation in d'; auto.
  eapply H0 with (l'0:=l')(ps'0:=ps')(cs'0:=cs')(tmn'0:=tmn')
    (lc'0:=lc')(als'0:=als')(Mem'0:=Mem')(cs0'0:=cs0') in J'; eauto.
  clear H0.
  destruct J2 as [[EQ [EQ' [EQ1 [EQ2 J2]]]] | [[c [EQ J2]] | [c [EQ J2]]]];subst.

  SCase "dbTerminator".
    destruct J' as [
      [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12
      ]]]]]]]]]]]]]] | 
      [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 
      [J22 J23]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      subst.
      right.
      exists cs3. exists cs4.
      exists t1. exists tr1. exists tr2.
      exists lc1. exists als1. exists Mem1.
      exists lc2. exists als2. exists Mem2.
      rewrite trace_app_commute.
      repeat (split; auto).
        apply dbBlock__dbBlocks; auto using dbTerminator__dbBlock.

    SSCase "multi block".
      right.
      exists cs3. exists cs4.
      exists (trace_app t1 tr1). exists tr2. exists tr3.
      exists lc2. exists als2. exists Mem2.
      exists lc3. exists als3. exists Mem3.
      rewrite trace_app_commute.
      rewrite trace_app_commute.
      repeat (split; auto).
        apply SimpleSE.dbBlocks_cons with (S2:=SimpleSE.mkState (SimpleSE.mkEC 
          (block_intro l1 ps1 cs2 tmn1) lc1 als1) Mem1); 
          auto using dbTerminator__dbBlock.
  SCase "dbCmd".
    apply bInsn__inv in b.
    destruct b as [EQ7 EQ8]; subst. inv EQ7.
    destruct J' as [
      [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12
      ]]]]]]]]]]]]]] | 
      [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 
      [J22 J23]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      left.
      apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)
        (gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=t1) in J11; auto.
      destruct J11 as [[J11 [EQ [EQ' [EQ1 [EQ2 EQ3]]]]] | J11]; subst.
        exists nil. exists (c::cs4).
        exists trace_nil. exists (trace_app t1 tr2).
        exists lc. exists als. exists Mem0.
        rewrite nil_app_trace__eq__trace.
        rewrite nil_app_trace__eq__trace.
        repeat (split; eauto). 

        exists (c::cs3). exists cs4.
        exists (trace_app t1 tr1). exists tr2.
        exists lc2. exists als2. exists Mem2.
        rewrite trace_app_commute. simpl_env in *.
        repeat (split; auto).
    
    SSCase "multi block".
      apply dbCmd_dbBlocks__dbCmd_or_dbBlocks with (lc:=lc)(als:=als)(gl:=gl)
        (Mem0:=Mem0)(c:=c)(tr1:=t1) in J21; auto.
      destruct J21 as [[J21 [EQ [EQ' [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]] | J21];
        subst.
        apply dbCmd_dbSubblocks__dbCmd_or_dbSubblocks with (lc:=lc)(als:=als)
          (gl:=gl)(Mem0:=Mem0)(c:=c)(tr1:=t1) in J22; auto.
        assert (cs2=cs3++cs4++cs') as EQcs.
          apply bops_preservation in b0; auto.
          assert (uniqFdef F) as UniqF.
            apply blockInSystemModuleFdef_inv in H5.
            destruct H5 as [_ [_ [_ H5]]].
            apply uniqSystem__uniqFdef in H5; auto.
          apply blockInSystemModuleFdef_uniq with (ps1:=ps')(cs1:=cs2)
            (tmn1:=tmn') in b0; auto.
          destruct b0 as [EQ1 [EQ2 EQ3]]; subst; auto.
        subst.
        destruct J22 as [[J22 [EQ [EQ' [EQ1 [EQ2 EQ3]]]]] | J22]; subst.
          left. 
          exists nil. exists (c::cs4).
          exists trace_nil. exists (trace_app t1 tr3).
          exists lc. exists als. exists Mem0.
          rewrite nil_app_trace__eq__trace.
          rewrite nil_app_trace__eq__trace.
          repeat (split; eauto).

          left.
          exists (c::cs3). exists cs4.
          exists (trace_app t1 tr2). exists tr3.
          exists lc3. exists als3. exists Mem3.
          rewrite nil_app_trace__eq__trace.
          rewrite trace_app_commute.
          repeat (split; eauto).
        
        right.
        exists cs3. exists cs4.
        exists (trace_app t1 tr1). exists tr2. exists tr3.
        exists lc2. exists als2. exists Mem2.
        exists lc3. exists als3. exists Mem3.
        rewrite trace_app_commute.
        rewrite trace_app_commute.
        repeat (split; eauto).

  SCase "dbCall".
    assert (J:=J2).
    apply dbCall_isCallInst in J.
    apply dbCall__dbSubblock with (als:=als1) in J2.
    apply bInsn_Call__inv in b; auto.
    destruct b as [EQ5 [EQ6 EQ7]]; subst. inv EQ5.
    destruct J' as [
       [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 
        J12]]]]]]]]]]]]]] | 
       [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 
        [J22 J23]]]]]]]]]]]]]]]
                   ]; subst.
    SSCase "one block".
      left.
      exists (c::cs3). exists cs4.
      exists (trace_app t1 tr1). exists tr2.
      exists lc2. exists als2. exists Mem2.
      rewrite trace_app_commute. simpl_env in *.
      repeat (split; eauto).

    SSCase "multi block".
      apply dbSubblock_dbBlocks__dbSubblock_or_dbBlocks with (lc:=lc)(als:=als1)
        (gl:=gl)(Mem0:=Mem0)(cs:=c::nil)(tr1:=t1) in J21; auto.
      destruct J21 as [[J21 [EQ [EQ' [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]] | J21];
        subst.
        left. 
        exists (c::cs3). exists cs4.
        exists (trace_app t1 tr2). exists tr3.
        exists lc3. exists als3. exists Mem3.
        rewrite nil_app_trace__eq__trace.
        assert (cs2=cs3++cs4++cs') as EQcs.        
          apply bops_preservation in b0; auto.
          assert (uniqFdef F) as UniqF.
            apply blockInSystemModuleFdef_inv in H5.
            destruct H5 as [_ [_ [_ H5]]].
            apply uniqSystem__uniqFdef in H5; auto.
          apply blockInSystemModuleFdef_uniq with (ps1:=ps')(cs1:=cs2)
            (tmn1:=tmn') in b0; auto.
          destruct b0 as [EQ1 [EQ2 EQ3]]; subst; auto.
        subst.
        rewrite trace_app_commute. simpl_env in *.
        repeat (split; eauto).
      
        right.
        exists cs3. exists cs4.
        exists (trace_app t1 tr1). exists tr2. exists tr3.
        exists lc2. exists als2. exists Mem2.
        exists lc3. exists als3. exists Mem3.
        rewrite trace_app_commute.
        rewrite trace_app_commute.
        repeat (split; eauto).     

Case "bFdef_func".
  assert (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc0 nil Mem0 =
          mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc0 nil Mem0) as J. auto.
  eapply H with (l'0:=l'')(ps'0:=ps'')(cs'0:=nil)
    (tmn'0:=insn_return rid rt Result)(lc'0:=lc')(als'0:=als')
    (Mem'0:=Mem')(cs0':=cs'') in J; 
    eauto using entryBlockInSystemBlockFdef''.
  clear H b.
  destruct J as [
   [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]]
    ]]]]]]]]]]] | 
   [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 [J22
    J23]]]]]]]]]]]]]]]
                ]; subst.
  SCase "one block".
    simpl_env in EQ6. subst.
    rewrite <- nil_app_trace__eq__trace with (tr:=tr1).
    eapply SimpleSE.dbFdef_func; eauto.
  
  SCase "multi block".
    simpl_env in *.
    eapply SimpleSE.dbFdef_func; eauto.

Case "bFdef_proc".
  assert (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc0 nil Mem0 =
          mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc0 nil Mem0) as J. auto.
  eapply H with (l'0:=l'')(ps'0:=ps'')(cs'0:=nil)(tmn'0:=insn_return_void rid)
    (lc'0:=lc')(als'0:=als')(Mem'0:=Mem')(cs0':=cs'') in J;
    eauto using entryBlockInSystemBlockFdef''.
  clear H b.
  destruct J as [
    [cs3 [cs4 [tr1 [tr2 [lc2 [als2 [Mem2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [J11 J12]]
     ]]]]]]]]]]]] | 
    [cs3 [cs4 [tr1 [tr2 [tr3 [lc2 [als2 [Mem2 [lc3 [als3 [Mem3 [EQ1 [EQ2 [J21 
     [J22 J23]]]]]]]]]]]]]]]
                ]; subst.
  SCase "one block".
    simpl_env in EQ6. subst.
    rewrite <- nil_app_trace__eq__trace with (tr:=tr1).
    eapply SimpleSE.dbFdef_proc; eauto.
  
  SCase "multi block".
    simpl_env in *.
    eapply SimpleSE.dbFdef_proc; eauto.
Qed.

Lemma llvmop_dbInsn__seop : forall state2 tr S los nts Ps F l ps cs tmn lc als 
    gl fs Mem cs0,
  bInsn (mkbCfg S (los, nts) Ps gl fs F) 
    (mkbEC (block_intro l ps cs0 tmn) cs tmn lc als Mem) state2 tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps) 
    F ->
  exists l', exists ps', exists cs', exists tmn', 
  exists lc', exists als', exists Mem', exists cs0',
  state2 = mkbEC (block_intro l' ps' cs0' tmn') cs' tmn' lc' als' Mem' /\
  ((cs = nil /\ Mem = Mem' /\ als = als' /\ cs' = cs0' /\
              SimpleSE.dbTerminator (los, nts) Mem' F gl
                 (block_intro l ps cs tmn) lc
                 tmn 
                 (block_intro l' ps' cs' tmn') lc' 
                 tr ) \/ 
  (exists c, c::cs' = cs /\ SimpleSE.dbCmd (los, nts) gl lc als Mem c lc' als' Mem' tr) \/
  (exists c, c::cs' = cs /\ SimpleSE.dbCall S (los, nts) Ps fs gl lc Mem c lc' Mem' tr)).
Proof.
  intros.
  destruct llvmop__seop as [J _]. 
  unfold llvmop_dbInsn__seop_prop in J.
  eapply J; eauto.
Qed.

Lemma llvmop_dbop__seop : forall tr S los nts Ps F l ps cs tmn lc als gl
    fs Mem l' ps' cs' tmn' lc' als' Mem' cs0 cs0',
  bops (mkbCfg S (los, nts) Ps gl fs F)  
    (mkbEC (block_intro l ps cs0 tmn) cs tmn lc als Mem)
    (mkbEC (block_intro l' ps' cs0' tmn') cs' tmn' lc' als' Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef (block_intro l ps cs0 tmn) S (module_intro los nts Ps)
    F ->
  (exists cs1, exists cs2, 
  exists tr1, exists tr2,
  exists lc1, exists als1, exists Mem1,
    trace_app tr1 tr2 = tr /\  
    l = l' /\
    ps = ps' /\
    cs0 = cs0' /\
    tmn = tmn' /\
    cs = cs1++cs2++cs' /\
    SimpleSE.dbSubblocks S (los, nts) Ps fs gl
      lc als Mem
      cs1
      lc1 als1 Mem1
      tr1 /\
    SimpleSE.dbCmds (los, nts) gl
      lc1 als1 Mem1
      cs2
      lc' als' Mem'
      tr2) \/
  (exists cs1, exists cs2, 
  exists tr1, exists tr2, exists tr3,
  exists lc1, exists als1, exists Mem1,
  exists lc2, exists als2, exists Mem2,
    cs1++cs2++cs'=cs0' /\
    (trace_app (trace_app tr1 tr2) tr3) = tr /\
    SimpleSE.dbBlocks S (los, nts) Ps fs gl F
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l ps cs tmn) lc als) Mem) 
      (SimpleSE.mkState (SimpleSE.mkEC (block_intro l' ps' cs0' tmn') lc1 als1) 
        Mem1)
      tr1 /\
    SimpleSE.dbSubblocks S (los, nts) Ps fs gl
      lc1 als1 Mem1
      cs1
      lc2 als2 Mem2
      tr2 /\
    SimpleSE.dbCmds (los, nts) gl
      lc2 als2 Mem2
      cs2
      lc' als' Mem'
      tr3).
Proof.
  intros.
  destruct llvmop__seop as [_ [J _]]. 
  unfold llvmop_dbop__seop_prop in J.
  eapply J; eauto.
Qed.

Lemma llvmop_dbFdef__seop_dbFdef : forall fid rt lp S los nts Ps lc gl fs Mem
    lc' als' Mem' B' Rid oResult tr,
  bFdef fid rt lp S (los, nts) Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  SimpleSE.dbFdef fid rt lp S (los, nts) Ps lc gl fs Mem lc' als' Mem' B' Rid 
    oResult tr.
Proof.
  intros.
  destruct llvmop__seop as [_ [_ J]]. 
  unfold llvmop_dbFdef__seop_dbFdef_prop in J.
  eapply J; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)


