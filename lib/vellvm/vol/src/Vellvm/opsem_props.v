Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "./GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import Ensembles.
Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Require Import analysis.
Require Import typings.
Require Import typings_props.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import AST.
Require Import Maps.
Require Import opsem.

Module OpsemProps. Section OpsemProps.

Context `{GVsSig : GenericValues}.

Export Opsem.

Notation GVs := GVsSig.(GVsT).
Notation "gv @ gvs" := 
  (GVsSig.(instantiate_gvs) gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (GVsSig.(gv2gvs) gv t) (at level 41).

Lemma func_callUpdateLocals_is_returnUpdateLocals : 
  forall TD rid noret0 tailc0 ft fid lp Result lc lc' gl,
  @returnUpdateLocals GVsSig TD (insn_call rid noret0 tailc0 ft fid lp) Result 
    lc lc' gl =
  callUpdateLocals TD ft noret0 rid (Some Result) lc' lc gl.
Proof.
  intros.
  unfold returnUpdateLocals. 
  unfold callUpdateLocals.
  destruct noret0; auto.
Qed.

Lemma proc_callUpdateLocals_is_id : forall TD ft rid noret0 lc lc' gl lc'',
  @callUpdateLocals GVsSig TD ft noret0 rid None lc' lc gl = Some lc'' -> 
  lc' = lc'' /\ noret0 = true.
Proof.
  intros.
  unfold callUpdateLocals in H. 
  destruct noret0; inversion H; auto.
Qed.

Lemma sInsn__implies__sop_star : forall cfg state state' tr,
  @sInsn GVsSig cfg state state' tr ->
  sop_star cfg state state' tr.
Proof.
  intros cfg state state' tr HdsInsn.
  rewrite <- trace_app_nil__eq__trace.
  eauto.
Qed.

Lemma sInsn__implies__sop_plus : forall cfg state state' tr,
  @sInsn GVsSig cfg state state' tr ->
  sop_plus cfg state state' tr.
Proof.
  intros cfg state state' tr HdsInsn.
  rewrite <- trace_app_nil__eq__trace.
  eauto.
Qed.

Lemma sop_plus__implies__sop_star : forall cfg state state' tr,
  @sop_plus GVsSig cfg state state' tr ->
  sop_star cfg state state' tr.
Proof.
  intros cfg state state' tr Hdsop_plus.
  inversion Hdsop_plus; subst; eauto.
Qed.

Hint Resolve sInsn__implies__sop_star sInsn__implies__sop_plus 
  sop_plus__implies__sop_star. 

Lemma sop_star_trans : forall cfg state1 state2 state3 tr12 tr23,
  @sop_star GVsSig cfg state1 state2 tr12 ->
  sop_star cfg state2 state3 tr23 ->
  sop_star cfg state1 state3 (trace_app tr12 tr23).
Proof.
  intros cfg state1 state2 state3 tr12 tr23 Hdsop12 Hdsop23.
  generalize dependent state3.
  generalize dependent tr23.
  induction Hdsop12; intros; auto.
    rewrite <- trace_app_commute. eauto.
Qed.

Lemma sop_diverging_trans : forall cfg state tr1 state' tr2,
  @sop_star GVsSig cfg state state' tr1 ->
  sop_diverges cfg state' tr2 ->
  sop_diverges cfg state (Trace_app tr1 tr2).
Proof. 
  intros cfg state tr1 state' tr2 state_dsop_state' state'_dsop_diverges.
  generalize dependent tr2.
  (sop_star_cases (induction state_dsop_state') Case); intros; auto.
  Case "sop_star_cons".
    rewrite <- Trace_app_commute. eauto.
Qed.

(***********************************************************)
(** big-step convergence -> small-step convergence *)

(** First, by mutual induction, we prove that bInsn, bops and  
    bFdef imply small-step semantics. *)

Definition bInsn__implies__sop_plus_prop cfg state state' tr 
  (db:@bInsn GVsSig cfg state state' tr) := 
  forall S TD Ps gl fs F B cs tmn lc als Mem B' cs' tmn' lc' als' Mem' ECs,
  cfg = (mkbCfg S TD Ps gl fs F) ->
  state = (mkbEC B cs tmn lc als Mem) ->
  state' = (mkbEC B' cs' tmn' lc' als' Mem') ->
  sop_plus (mkCfg S TD Ps gl fs) 
           (mkState ((mkEC F B cs tmn lc als)::ECs) Mem)
           (mkState ((mkEC F B' cs' tmn' lc' als')::ECs) Mem') tr.
Definition bops__implies__sop_star_prop cfg state state' tr 
  (db:@bops GVsSig cfg state state' tr) := 
  forall S TD Ps gl fs F B cs tmn lc als Mem B' cs' tmn' lc' als' Mem' ECs,
  cfg = (mkbCfg S TD Ps gl fs F) ->
  state = (mkbEC B cs tmn lc als Mem) ->
  state' = (mkbEC B' cs' tmn' lc' als' Mem') ->
  sop_star (mkCfg S TD Ps gl fs) 
           (mkState ((mkEC F B cs tmn lc als)::ECs) Mem)
           (mkState ((mkEC F B' cs' tmn' lc' als')::ECs) Mem') tr.
Definition bFdef__implies__sop_star_prop fv rt lp S TD Ps lc gl fs Mem lc'
als' Mem' B'' rid oResult tr 
(db:@bFdef GVsSig fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B'' rid oResult tr)
  := 
  match oResult with
  | Some Result => forall ECs fptrs,
    getOperandValue TD fv lc gl = Some fptrs -> 
    exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
    exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
    fptr @ fptrs /\
    lookupFdefViaPtr Ps fs fptr = 
      Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
    getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
      Some (block_intro l' ps' cs' tmn') /\
    params2GVs TD lp lc gl = Some gvs /\
    initLocals TD la gvs = Some lc0 /\
    sop_star (mkCfg S TD Ps gl fs)
      (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                              (block_intro l' ps' cs' tmn') cs' tmn' 
                              lc0 nil)::ECs) Mem)
      (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                               B'' nil (insn_return rid rt Result) lc'
                               als')::ECs) Mem')
      tr
  | None => forall ECs fptrs,
    getOperandValue TD fv lc gl = Some fptrs -> 
    exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
    exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
    fptr @ fptrs /\
    lookupFdefViaPtr Ps fs fptr = 
      Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
    getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
      Some (block_intro l' ps' cs' tmn') /\
    params2GVs TD lp lc gl = Some gvs /\
    initLocals TD la gvs = Some lc0 /\
    sop_star (mkCfg S TD Ps gl fs)
      (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                              (block_intro l' ps' cs' tmn') cs' tmn' 
                              lc0 nil)::ECs) Mem)
      (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                               B'' nil (insn_return_void rid) lc'
                               als')::ECs) Mem')
      tr
  end
  .

Ltac app_inv :=
  match goal with
  | [ H: ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ ] => inv H
  | [ H: ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ ] => inv H
  | [ H: ?f _ _ = ?f _ _ |- _ ] => inv H
  end.

Lemma b__implies__s:
  (forall cfg state state' t db, 
     @bInsn__implies__sop_plus_prop cfg state state' t db) /\
  (forall cfg state state' t db, 
     @bops__implies__sop_star_prop cfg state state' t db) /\
  (forall fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B'' rid oret tr db, 
     @bFdef__implies__sop_star_prop fv rt lp S TD Ps lc gl fs Mem lc' als' 
       Mem' B'' rid oret tr db).
Proof.
(b_mutind_cases
  apply b_mutind with
    (P  := bInsn__implies__sop_plus_prop)
    (P0 := bops__implies__sop_star_prop)
    (P1 := bFdef__implies__sop_star_prop)
    Case);
  unfold bInsn__implies__sop_plus_prop, 
         bops__implies__sop_star_prop, 
         bFdef__implies__sop_star_prop; 
  intros; subst; simpl; repeat app_inv; eauto.
  Case "bCall".
    inversion b; subst.
    SCase "bFdef_func".
    assert (Hlookup:=H0).
    apply H with (ECs:=(mkEC F0 B0 ((insn_call rid noret0 ca ft fv lp)::cs') 
                         tmn0 lc0 als0)::ECs) in H0; auto. clear H.
    destruct H0 as [fptr' [fa0 [fid0 [la0 [va0 [lb0 [l0 [ps0 [cs0 [tmn0' [gvs0 
      [lc0' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]]]]]].
    rewrite <- nil_app_trace__eq__trace.
    apply sop_plus_cons with 
     (state2:=mkState ((mkEC (fdef_intro (fheader_intro fa0 rt fid0 la0 va0) lb0)
                             (block_intro l0 ps0 cs0 tmn0') cs0 tmn0' lc0' nil)::
                        (mkEC F0 B0 ((insn_call rid noret0 ca ft fv lp)::cs') 
                         tmn0 lc0 als0)::ECs) Mem1); eauto.
    rewrite <- trace_app_nil__eq__trace.
    apply sop_star_trans with 
     (state2:=mkState ((mkEC (fdef_intro (fheader_intro fa0 rt fid0 la0 va0) lb0)
                               (block_intro l'' ps'' cs'' 
                                (insn_return Rid rt Result)) nil 
                                (insn_return Rid rt Result) lc'
                                als')::
                        (mkEC F0 B0 ((insn_call rid noret0 ca ft fv lp)::cs') 
                         tmn0 lc0 als0)::ECs) Mem'); auto.
      apply sInsn__implies__sop_star.
        apply sReturn; auto.
          erewrite func_callUpdateLocals_is_returnUpdateLocals; eauto.

    SCase "bFdef_proc".
    assert (Hlookup:=H0).
    apply H with (ECs:=(mkEC F0 B0 ((insn_call rid noret0 ca ft fv lp)::cs') 
                         tmn0 lc0 als0)::ECs) in H0; auto. clear H.
    destruct H0 as [fptr' [fa0 [fid0 [la0 [va0 [lb0 [l0 [ps0 [cs0 [tmn0' [gvs0 
      [lc0'' [J1 [J2 [J3 [J4 [J5 J6]]]]]]]]]]]]]]]]].
    rewrite <- nil_app_trace__eq__trace.
    apply sop_plus_cons with 
     (state2:=mkState ((mkEC (fdef_intro (fheader_intro fa0 rt fid0 la0 va0) lb0)
                            (block_intro l0 ps0 cs0 tmn0') cs0 tmn0' lc0'' nil)::
                        (mkEC F0 B0 ((insn_call rid noret0 ca ft fv lp)::cs') 
                         tmn0 lc0 als0)::ECs) Mem1); eauto.
    rewrite <- trace_app_nil__eq__trace.
    apply proc_callUpdateLocals_is_id in e0.
    destruct e0; subst.
    apply sop_star_trans with 
     (state2:=mkState ((mkEC (fdef_intro (fheader_intro fa0 rt fid0 la0 va0) lb0)
                               (block_intro l'' ps'' cs'' (insn_return_void Rid))
                                nil (insn_return_void Rid) lc' als')::
                        (mkEC F0 B0 ((insn_call rid true ca ft fv lp)::cs') 
                         tmn0 lc'0 als0)::ECs) Mem'); auto.

  Case "bops_cons".
    destruct S2 as [b3 cs3 tmn3 lc3 als3].
    apply sop_star_trans with 
      (state2:=mkState ((mkEC F b3 cs3 tmn3 lc3 als3)::ECs) bMem0); auto.
        
  Case "bFdef_func".
    rewrite H0 in e. inv e. exists fptr. exists fa. exists fid. exists la.
    exists va. exists lb. exists l'. exists ps'. exists cs'. exists tmn'. 
    exists gvs. exists lc0. repeat (split; auto).

  Case "bFdef_proc".
   rewrite H0 in e. inv e. exists fptr. exists fa. exists fid. exists la.
    exists va. exists lb. exists l'. exists ps'. exists cs'. exists tmn'. 
    exists gvs. exists lc0. repeat (split; auto).
Qed.  
    
Lemma bInsn__implies__sop_plus : forall tr S TD Ps gl fs F B cs tmn lc als Mem B'
    cs' tmn' lc' als' Mem' ECs,
  @bInsn GVsSig (mkbCfg S TD Ps gl fs F) (mkbEC B cs tmn lc als Mem) 
    (mkbEC B' cs' tmn' lc' als' Mem') tr ->
  sop_plus (mkCfg S TD Ps gl fs) 
           (mkState ((mkEC F B cs tmn lc als)::ECs) Mem)
           (mkState ((mkEC F B' cs' tmn' lc' als')::ECs) Mem') tr.
Proof.
  destruct b__implies__s as [J _]. intros. 
  unfold bInsn__implies__sop_plus_prop in J. eapply J; eauto.
Qed.

Lemma bInsn__implies__sop_star : forall tr S TD Ps gl fs F B cs tmn lc als Mem B'
    cs' tmn' lc' als' Mem' ECs,
  @bInsn GVsSig (mkbCfg S TD Ps gl fs F) (mkbEC B cs tmn lc als Mem) 
    (mkbEC B' cs' tmn' lc' als' Mem') tr ->
  sop_star (mkCfg S TD Ps gl fs) 
           (mkState ((mkEC F B cs tmn lc als)::ECs) Mem)
           (mkState ((mkEC F B' cs' tmn' lc' als')::ECs) Mem') tr.
Proof. 
  intros. eapply bInsn__implies__sop_plus in H; eauto.
Qed.

Lemma bops__implies__sop_star : forall tr S TD Ps gl fs F B cs tmn lc als Mem B' 
    cs' tmn' lc' als' Mem' ECs,
  @bops GVsSig (mkbCfg S TD Ps gl fs F) (mkbEC B cs tmn lc als Mem) 
    (mkbEC B' cs' tmn' lc' als' Mem') tr ->
  sop_star (mkCfg S TD Ps gl fs) 
           (mkState ((mkEC F B cs tmn lc als)::ECs) Mem)
           (mkState ((mkEC F B' cs' tmn' lc' als')::ECs) Mem') tr.
Proof.
  destruct b__implies__s as [_ [J _]]. intros.
  unfold bops__implies__sop_star_prop in J. eapply J; eauto.
Qed.

Lemma bFdef_func__implies__sop_star : forall fv rt lp S TD Ps ECs lc gl fs
    Mem lc' als' Mem' B'' rid Result tr fptrs, 
  @bFdef GVsSig fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B'' rid
    (Some Result) tr ->
  getOperandValue TD fv lc gl = Some fptrs -> 
  exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
  exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
  fptr @ fptrs /\
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') /\
  params2GVs TD lp lc gl = Some gvs /\
  initLocals TD la gvs = Some lc0 /\
  sop_star (mkCfg S TD Ps gl fs)
    (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             (block_intro l' ps' cs' tmn') cs' tmn' lc0
                             nil)::ECs) Mem)
    (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             B'' nil (insn_return rid rt Result) lc'
                             als')::ECs) Mem')
    tr.
Proof.
  intros fv rt lp S TD Ps ECs lc gl fs Mem0 lc' als' Mem' B'' rid Result tr 
    fptrs H H1.
  destruct b__implies__s as [_ [_ J]]. 
  assert (K:=@J fv rt lp S TD Ps lc gl fs Mem0 lc' als' Mem' B'' rid 
    (Some Result) tr H ECs fptrs H1); auto.
Qed.

Lemma bFdef_proc__implies__sop_star : forall fv rt lp S TD Ps ECs lc gl fs
    Mem lc' als' Mem' B'' rid tr fptrs,
  @bFdef GVsSig fv rt lp S TD Ps lc gl fs  Mem lc' als' Mem' B'' rid None tr ->
  getOperandValue TD fv lc gl = Some fptrs -> 
  exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
  exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
  fptr @ fptrs /\
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') /\
  params2GVs TD lp lc gl = Some gvs /\
  initLocals TD la gvs = Some lc0 /\
  sop_star (mkCfg S TD Ps gl fs) 
    (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                            (block_intro l' ps' cs' tmn') cs' tmn' lc0
                            nil)::ECs) Mem)
    (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                             B'' nil (insn_return_void rid) lc'
                             als')::ECs) Mem')
    tr.
Proof.
  intros fv rt lp S TD Ps ECs lc gl fs Mem0 lc' als' Mem' B'' rid tr fptrs H H1.
  destruct b__implies__s as [_ [_ J]]. 
  assert (K:=@J fv rt lp S TD Ps lc gl fs Mem0 lc' als' Mem' B'' rid None tr 
    H ECs fptrs H1); auto.
Qed.

(** Then we prove that the whole program holds the same property. *)

Lemma b_genInitState_inv : forall S main Args initmem S0 TD Ps gl fs F B cs tmn 
  lc als M, 
 @b_genInitState GVsSig S main Args initmem = 
   Some (mkbCfg S0 TD Ps gl fs F, mkbEC B cs tmn lc als M) ->
 s_genInitState S main Args initmem =
   Some (mkCfg S0 TD Ps gl fs, mkState ((mkEC F B cs tmn lc als)::nil) M).
Proof.
  intros.
  unfold b_genInitState in H.
  remember (s_genInitState S main Args initmem) as R.
  destruct R as [[]|]; tinv H. destruct c; tinv H. destruct s; tinv H. 
  destruct ECS0; tinv H. destruct e; tinv H. destruct ECS0; inv H; auto.
Qed.

Lemma b_converges__implies__s_converges : forall sys main VarArgs B cs tmn lc 
    als M,
  @b_converges GVsSig sys main VarArgs (mkbEC B cs tmn lc als M) ->
  exists F,
  s_converges sys main VarArgs (mkState ((mkEC F B cs tmn lc als)::nil) M).
Proof.
  intros sys main VarArgs B cs tmn lc als M Hdb_converges.
  inversion Hdb_converges; subst. destruct cfg. destruct IS.
  apply b_genInitState_inv in H.
  exists bCurFunction0.
  eapply s_converges_intro; eauto.
  apply bops__implies__sop_star; eauto.
Qed.

Lemma b_goeswrong__implies__s_goeswrong : forall sys main VarArgs B cs tmn lc 
    als M,
  @b_goeswrong GVsSig sys main VarArgs (mkbEC B cs tmn lc als M) ->
  exists F,
  s_goeswrong sys main VarArgs (mkState ((mkEC F B cs tmn lc als)::nil) M).
Proof.
  intros sys main VarArgs B cs tmn lc als M Hdb_goeswrong.
  inversion Hdb_goeswrong; subst. destruct cfg. destruct IS.
  apply b_genInitState_inv in H.
  exists bCurFunction0.
  eapply s_goeswrong_intro; eauto.
  apply bops__implies__sop_star; eauto.
Qed.

(***********************************************************)
(** big-step divergence -> small-step divergence *)

(** First,we prove that bInsn, bops and bFdef imply small-step semantics,
    by nested coinduction. *)

Lemma bFdefInf_bopInf__implies__sop_diverges : 
   forall (fv : value) (rt : typ) (lp : params) (S : system)
     (TD : TargetData) (Ps : products) (ECs : list ExecutionContext)
     (lc : GVsMap) (gl fs : GVMap) (Mem0 : mem) (tr : Trace) 
     (fid : id) (fa : fnattrs) (lc1 : GVsMap) (l' : l) 
     (ps' : phinodes) (cs' : cmds) (tmn' : terminator) 
     (la : args) (va : varg) (lb : blocks) (gvs : list GVs) 
     (fptrs0 : GVs) (fptr : GenericValue),
   fptr @ fptrs0 ->
   lookupFdefViaPtr Ps fs fptr =
   ret fdef_intro (fheader_intro fa rt fid la va) lb ->
   getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) =
   ret block_intro l' ps' cs' tmn' ->
   params2GVs TD lp lc gl = ret gvs ->
   initLocals TD la gvs = ret lc1 ->
   bopInf (mkbCfg S TD Ps gl fs (fdef_intro (fheader_intro fa rt fid la va) lb))
     {|
     bCurBB := block_intro l' ps' cs' tmn';
     bCurCmds := cs';
     bTerminator := tmn';
     bLocals := lc1;
     bAllocas := nil;
     bMem := Mem0 |} tr ->
   getOperandValue TD fv lc gl = ret fptrs0 ->
   sop_diverges (mkCfg S TD Ps gl fs)
     {|
     ECS := {|
            CurFunction := fdef_intro (fheader_intro fa rt fid la va) lb;
            CurBB := block_intro l' ps' cs' tmn';
            CurCmds := cs';
            Terminator := tmn';
            Locals := lc1;
            Allocas := nil |} :: ECs;
     Mem := Mem0 |} tr.
Proof.
  cofix CIH_bFdefInf.

  assert (forall S tr TD Ps gl fs F B cs tmn lc als Mem ECs,
    @bInsnInf GVsSig (mkbCfg S TD Ps gl fs F) (mkbEC B cs tmn lc als Mem) tr ->
    sop_diverges (mkCfg S TD Ps gl fs) 
                 (mkState ((mkEC F B cs tmn lc als)::ECs) Mem) tr)
    as bInsnInf__implies__sop_diverges.
    cofix CIH_bInsnInf.
    intros S tr TD Ps gl fs F B cs tmn lc als Mem ECs HbInsnInf.
    
    inversion HbInsnInf; subst.
    rewrite <- nil_app_Trace__eq__Trace.
    assert (HbFdefInf:=H12).
    inversion H12; subst.
    apply sop_diverges_intro with 
      (state2:=mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va)lb)
                               (block_intro l' ps' cs' tmn') cs' tmn' lc1
                               nil)::
                        (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs0) 
                         tmn lc als)::ECs) Mem); 
      try solve [clear CIH_bFdefInf CIH_bInsnInf; eauto].
      inv HbFdefInf.
      eapply CIH_bFdefInf with (fid:=fid)(l':=l')(ps':=ps')(cs':=cs')(tmn':=tmn')
        (fa:=fa)(la:=la)(va:=va)(lb:=lb)(gvs:=gvs)(lc1:=lc1)(fptr:=fptr)(fv:=fv)
        (lp:=lp)(lc:=lc)(fptrs0:=fptrs) in H5; eauto.

  assert (forall S tr TD Ps gl fs F B cs tmn lc als Mem ECs,
    @bopInf GVsSig (mkbCfg S TD Ps gl fs F) (mkbEC B cs tmn lc als Mem) tr ->
    sop_diverges (mkCfg S TD Ps gl fs) 
                 (mkState ((mkEC F B cs tmn lc als)::ECs) Mem) tr) 
    as bopInf__implies__sop_diverges.
    cofix CIH_bopInf.
    intros S tr TD Ps gl fs F B cs tmn lc als Mem ECs HbopInf.
    inversion HbopInf; subst.
    Case "bopInf_insn".
      eapply bInsnInf__implies__sop_diverges in H; eauto.
    Case "bopInf_cons".
      destruct state2.
      apply bInsn__implies__sop_plus with (ECs:=ECs) in H.
      inversion H; subst.
      SCase "dsop_plus_cons".
        apply CIH_bopInf with (ECs:=ECs) in H0. clear CIH_bopInf.
        eapply sop_diverges_intro; eauto.

  intros fv rt lp S TD Ps ECs lc gl fs Mem0 tr fid fa lc1 l' ps' cs' tmn' la va 
    lb gvs fptrs0 fptr Hin Hlookup HgetEntryBlock Hp2gvs Hinit HbFdefInf Hget.
  inversion HbFdefInf; subst; eauto.
Qed.

Lemma bFdefInf__implies__sop_diverges : forall fv rt lp S TD Ps ECs lc gl fs Mem
    tr fptrs,
  bFdefInf fv rt lp S TD Ps lc gl fs Mem tr ->
  getOperandValue TD fv lc gl = Some fptrs -> 
  exists fptr, exists fa, exists fid, exists la, exists va, exists lb, 
  exists l', exists ps', exists cs', exists tmn', exists gvs, exists lc0, 
  fptr @ fptrs /\
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) /\
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') /\
  params2GVs TD lp lc gl = Some gvs /\
  initLocals TD la gvs = Some lc0 /\
  sop_diverges (mkCfg S TD Ps gl fs)
    (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
              (block_intro l' ps' cs' tmn') cs' tmn' lc0 nil)::ECs) Mem)
    tr.
Proof.
  intros fv rt lp S TD Ps ECs lc gl fs Mem0 tr fptrs HdbFdefInf Hget.
  inv HdbFdefInf; subst.
  exists fptr. exists fa. exists fid. exists la. exists va. exists lb. exists l'.
  exists ps'. exists cs'. exists tmn'. exists gvs. exists lc1.
  rewrite Hget in H. inv H.
  repeat (split; auto).
    eapply bFdefInf_bopInf__implies__sop_diverges; eauto.
Qed.

Lemma bInsnInf__implies__sop_diverges : forall S tr TD Ps gl fs F B cs tmn lc als
  Mem ECs,
  @bInsnInf GVsSig (mkbCfg S TD Ps gl fs F) (mkbEC B cs tmn lc als Mem) tr ->
  sop_diverges (mkCfg S TD Ps gl fs) 
    (mkState ((mkEC F B cs tmn lc als)::ECs) Mem) tr.
Proof.
  cofix CIH_bInsnInf.
  intros S tr TD Ps gl fs F B cs tmn lc als Mem ECs HbInsnInf.
  
  inversion HbInsnInf; subst.
  rewrite <- nil_app_Trace__eq__Trace.
  assert (HbFdefInf:=H12).
  inversion H12; subst.
  apply sop_diverges_intro with 
    (state2:=mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va)lb)
                             (block_intro l' ps' cs' tmn') cs' tmn' lc1
                             nil)::
                      (mkEC F B ((insn_call rid noret0 ca ft fv lp)::cs0) 
                       tmn lc als)::ECs) Mem); 
    try solve [clear CIH_bInsnInf; eauto].
    eapply bFdefInf_bopInf__implies__sop_diverges with (l':=l')(ps':=ps')
      (cs':=cs')(tmn':=tmn')(la:=la)(va:=va)(lb:=lb)(fa:=fa)(gvs:=gvs)(lc1:=lc1) 
      in H5; eauto.
Qed.

Lemma bopInf__implies__sop_diverges : forall S tr TD Ps gl fs F B cs tmn lc als
  Mem ECs,
  @bopInf GVsSig (mkbCfg S TD Ps gl fs F) (mkbEC B cs tmn lc als Mem) tr ->
  sop_diverges (mkCfg S TD Ps gl fs) 
    (mkState ((mkEC F B cs tmn lc als)::ECs) Mem) tr.
Proof.
  cofix CIH_bopInf.
  intros S tr TD Ps gl fs F B cs tmn lc als Mem ECs HbopInf.
  inversion HbopInf; subst.
  Case "bopInf_insn".
    eapply bInsnInf__implies__sop_diverges in H; eauto.
  Case "bopInf_cons".
    destruct state2.
    apply bInsn__implies__sop_plus with (ECs:=ECs) in H.
    inversion H; subst.
    SCase "dsop_plus_cons".
      apply CIH_bopInf with (ECs:=ECs) in H0. clear CIH_bopInf.
      eapply sop_diverges_intro; eauto.
Qed.

(** Then we prove that the whole program holds the same property. *)

Lemma b_diverges__implies__s_diverges : forall sys main VarArgs tr, 
  @b_diverges GVsSig sys main VarArgs tr ->
  s_diverges sys main VarArgs tr.
Proof.
  intros sys main VarArgs tr Hdb_diverges.
  inversion Hdb_diverges; subst.
  destruct cfg. destruct IS.
  apply b_genInitState_inv in H.
  eapply s_diverges_intro; eauto.
  apply bopInf__implies__sop_diverges; eauto.
Qed.

Lemma BOP_inversion : forall TD lc gl b s v1 v2 gv2,
  BOP TD lc gl b s v1 v2 = Some gv2 ->
  exists gvs1, exists gvs2,
    getOperandValue TD v1 lc gl = Some gvs1 /\
    getOperandValue TD v2 lc gl = Some gvs2 /\
    GVsSig.(lift_op2) (mbop TD b s) gvs1 gvs2 (typ_int s) = Some gv2.
Proof.
  intros TD lc gl b s v1 v2 gv2 HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HBOP]. 
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HBOP.
  eauto.
Qed.

Lemma FBOP_inversion : forall TD lc gl b fp v1 v2 gv,
  FBOP TD lc gl b fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    GVsSig.(lift_op2) (mfbop TD b fp) gv1 gv2 (typ_floatpoint fp) = Some gv.
Proof.
  intros TD lc gl b fp v1 v2 gv HFBOP.
  unfold FBOP in HFBOP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFBOP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HFBOP.
  eauto.
Qed.

Lemma CAST_inversion : forall TD lc gl op t1 v1 t2 gv,
  CAST TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    GVsSig.(lift_op1) (mcast TD op t1 t2) gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HCAST.
  unfold CAST in HCAST.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HCAST.
  eauto.
Qed.

Lemma TRUNC_inversion : forall TD lc gl op t1 v1 t2 gv,
  TRUNC TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    GVsSig.(lift_op1) (mtrunc TD op t1 t2) gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HTRUNC.
  unfold TRUNC in HTRUNC.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HTRUNC.
  eauto.
Qed.

Lemma EXT_inversion : forall TD lc gl op t1 v1 t2 gv,
  EXT TD lc gl op t1 v1 t2 = Some gv ->
  exists gv1,
    getOperandValue TD v1 lc gl = Some gv1 /\
    GVsSig.(lift_op1) (mext TD op t1 t2) gv1 t2 = Some gv.
Proof.
  intros TD lc gl op t1 v1 t2 gv HEXT.
  unfold EXT in HEXT.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; inv HEXT.
  eauto.
Qed.

Lemma ICMP_inversion : forall TD lc gl cond t v1 v2 gv,
  ICMP TD lc gl cond t v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    GVsSig.(lift_op2) (micmp TD cond t) gv1 gv2 (typ_int 1%nat) = Some gv.
Proof.
  intros TD lc gl cond0 t v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HICMP.
  eauto.
Qed.

Lemma FCMP_inversion : forall TD lc gl cond fp v1 v2 gv,
  FCMP TD lc gl cond fp v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue TD v1 lc gl = Some gv1 /\
    getOperandValue TD v2 lc gl = Some gv2 /\
    GVsSig.(lift_op2) (mfcmp TD cond fp) gv1 gv2 (typ_int 1%nat) = Some gv.
Proof.
  intros TD lc gl cond0 fp v1 v2 gv HFCMP.
  unfold FCMP in HFCMP.
  remember (getOperandValue TD v1 lc gl) as ogv1.
  destruct ogv1; try solve [inversion HFCMP].
  remember (getOperandValue TD v2 lc gl) as ogv2.
  destruct ogv2; inv HFCMP.
  eauto.
Qed.

(*
Lemma GEP_inversion : forall (TD:TargetData) (t:typ) (ma:GenericValue) 
  (vidxs:list GenericValue) ib mptr0,
  GEP TD t ma vidxs ib = Some mptr0 ->
  exists idxs, exists ptr, exists ptr0, 
    GVs2Nats TD vidxs = Some idxs /\ 
    GV2ptr TD (getPointerSize TD) ma = Some ptr /\
    mgep TD t ptr idxs = Some ptr0 /\
    ptr2GV TD ptr0 = mptr0.
Proof.
  intros.
  unfold GEP in H.
  remember (GVs2Nats TD vidxs) as oidxs.
  remember (GV2ptr TD (getPointerSize TD) ma) as R.
  destruct R.
    destruct oidxs.
      remember (mgep TD t v l0) as og.
      destruct og; inversion H; subst.
        exists l0. exists v. exists v0. auto.
        exists l0. exists v. exists v0. auto.

Qed.
*)

Lemma const2GV_eqAL : forall c gl1 gl2 TD, 
  eqAL _ gl1 gl2 -> 
  @const2GV GVsSig TD gl1 c = const2GV TD gl2 c.
Proof.
  intros. unfold const2GV.
  destruct const2GV_eqAL_aux.
  erewrite H0; eauto.
Qed.

Lemma getOperandValue_eqAL : forall lc1 gl lc2 v TD,
  eqAL _ lc1 lc2 ->
  @getOperandValue GVsSig TD v lc1 gl = getOperandValue TD v lc2 gl.
Proof.
  intros lc1 gl lc2 v TD HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
Qed.

Lemma BOP_eqAL : forall lc1 gl lc2 bop0 sz0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  @BOP GVsSig TD lc1 gl bop0 sz0 v1 v2 = BOP TD lc2 gl bop0 sz0 v1 v2.
Proof.
  intros lc1 gl lc2 bop0 sz0 v1 v2 TD HeqEnv.
  unfold BOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FBOP_eqAL : forall lc1 gl lc2 fbop0 fp0 v1 v2 TD,
  eqAL _ lc1 lc2 ->
  @FBOP GVsSig TD lc1 gl fbop0 fp0 v1 v2 = FBOP TD lc2 gl fbop0 fp0 v1 v2.
Proof.
  intros lc1 gl lc2 fbop0 fp0 v1 v2 TD HeqEnv.
  unfold FBOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma CAST_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  @CAST GVsSig TD lc1 gl op t1 v1 t2 = CAST TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold CAST in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma TRUNC_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  @TRUNC GVsSig TD lc1 gl op t1 v1 t2 = TRUNC TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold TRUNC in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma EXT_eqAL : forall lc1 gl lc2 op t1 v1 t2 TD,
  eqAL _ lc1 lc2 ->
  @EXT GVsSig TD lc1 gl op t1 v1 t2 = EXT TD lc2 gl op t1 v1 t2.
Proof.
  intros lc1 gl lc2 op t1 v1 t2 TD HeqAL.
  unfold EXT in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
Qed.

Lemma ICMP_eqAL : forall lc1 gl lc2 cond t v1 v2 TD,
  eqAL _ lc1 lc2 ->
  @ICMP GVsSig TD lc1 gl cond t v1 v2 = ICMP TD lc2 gl cond t v1 v2.
Proof.
  intros lc1 gl lc2 cond0 t v1 v2 TD HeqAL.
  unfold ICMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma FCMP_eqAL : forall lc1 gl lc2 cond fp v1 v2 TD,
  eqAL _ lc1 lc2 ->
  @FCMP GVsSig TD lc1 gl cond fp v1 v2 = FCMP TD lc2 gl cond fp v1 v2.
Proof.
  intros lc1 gl lc2 cond0 fp v1 v2 TD HeqAL.
  unfold FCMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma values2GVs_eqAL : forall l0 lc1 gl lc2 TD,
  eqAL _ lc1 lc2 ->
  @values2GVs GVsSig TD l0 lc1 gl = values2GVs TD l0 lc2 gl.
Proof.
  induction l0; intros lc1 gl lc2 TD HeqAL; simpl; auto.
    rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v); auto.
    erewrite IHl0; eauto.
Qed.
(*
Lemma lookupFdefViaGV_inversion : forall TD Ps gl lc fs fv f,
  lookupFdefViaGV TD Ps gl lc fs fv = Some f ->
  exists fptr, exists fn,
    getOperandValue TD fv lc gl = Some fptr /\
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupFdefViaGV in H.
  destruct (getOperandValue TD fv lc gl); tinv H.
  simpl in H. exists g.
  destruct (lookupFdefViaGVFromFunTable fs g); tinv H.
  simpl in H. exists i0. eauto.
Qed.  
*)

Lemma eqAL_callUpdateLocals : forall TD noret0 rid oResult lc1 lc2 gl lc1' 
  lc2' ft,
  eqAL _ lc1 lc1' ->
  eqAL _ lc2 lc2' ->
  match (@callUpdateLocals GVsSig  TD ft noret0 rid oResult lc1 lc2 gl,
         callUpdateLocals TD ft noret0 rid oResult lc1' lc2' gl) with
  | (Some lc, Some lc') => eqAL _ lc lc'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros TD noret0 rid oResult lc1 lc2 gl lc1' lc2' ft H1 H2.
    unfold callUpdateLocals.
    destruct noret0; auto.
      destruct oResult; simpl; auto.
        destruct v; simpl.
          rewrite H2.
          destruct (lookupAL _ lc2' i0); auto using eqAL_updateAddAL.

          destruct (@const2GV GVsSig TD gl c); auto using eqAL_updateAddAL.
      destruct oResult; simpl; auto.
        destruct v; simpl.
          rewrite H2.
          destruct (lookupAL _ lc2' i0); auto.
          destruct ft; auto.
          destruct (GVsSig.(lift_op1) (fit_gv TD ft) g ft); 
            auto using eqAL_updateAddAL.

          destruct (@const2GV GVsSig TD gl c); auto using eqAL_updateAddAL.
          destruct ft; auto.
          destruct (GVsSig.(lift_op1) (fit_gv TD ft) g ft); 
            auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_getIncomingValuesForBlockFromPHINodes : forall TD ps B gl lc lc',
  eqAL _ lc lc' ->
  @getIncomingValuesForBlockFromPHINodes GVsSig TD ps B gl lc = 
  getIncomingValuesForBlockFromPHINodes TD ps B gl lc'.
Proof.
  induction ps; intros; simpl; auto.
    destruct a; auto.
    destruct (getValueViaBlockFromValuels l0 B); auto.
    destruct v; simpl; erewrite IHps; eauto.
      rewrite H. auto.
Qed.
  
Lemma eqAL_updateValuesForNewBlock : forall vs lc lc',
  eqAL _ lc lc' ->
  eqAL _ (@updateValuesForNewBlock GVsSig vs lc)(updateValuesForNewBlock vs lc').
Proof.
  induction vs; intros; simpl; auto.
    destruct a; auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_switchToNewBasicBlock : forall TD B1 B2 gl lc lc',
  eqAL _ lc lc' ->
  match (@switchToNewBasicBlock GVsSig TD B1 B2 gl lc,
         switchToNewBasicBlock TD B1 B2 gl lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite eqAL_getIncomingValuesForBlockFromPHINodes; eauto.
  destruct 
    (getIncomingValuesForBlockFromPHINodes TD (getPHINodesFromBlock B1) B2 gl 
    lc'); auto using eqAL_updateValuesForNewBlock.
Qed.

Lemma eqAL_switchToNewBasicBlock' : forall TD B1 B2 gl lc lc' lc1,
  eqAL _ lc lc' ->
  @switchToNewBasicBlock GVsSig TD B1 B2 gl lc = Some lc1 ->
  exists lc1', switchToNewBasicBlock TD B1 B2 gl lc' = Some lc1' /\
               eqAL _ lc1 lc1'.
Proof.
  intros.
  assert (J:=@eqAL_switchToNewBasicBlock TD B1 B2 gl lc lc' H).
  rewrite H0 in J.
  destruct (switchToNewBasicBlock TD B1 B2 gl lc'); try solve [inversion J].
  exists g. auto.
Qed.

Lemma eqAL_params2GVs : forall lp TD lc gl lc',
  eqAL _ lc lc' ->
  @params2GVs GVsSig TD lp lc gl = params2GVs TD lp lc' gl.
Proof.
  induction lp; intros; simpl; auto.
    destruct a. 
    destruct v; simpl.
      rewrite H. erewrite IHlp; eauto.
      erewrite IHlp; eauto.
Qed.

Lemma eqAL_exCallUpdateLocals : forall TD noret0 rid oResult lc lc' ft,
  eqAL _ lc lc' ->
  match (@exCallUpdateLocals GVsSig TD ft noret0 rid oResult lc,
         exCallUpdateLocals TD ft noret0 rid oResult lc') with
  | (Some lc1, Some lc1') => eqAL _ lc1 lc1'
  | (None, None) => True
  | _ => False
  end.
Proof.
  intros TD noret0 rid oResult lc lc' ft H1.
    unfold exCallUpdateLocals.
    destruct noret0; auto.
    destruct oResult; auto.
    destruct ft; auto.
    destruct (fit_gv TD ft g); auto using eqAL_updateAddAL.
Qed.

Lemma eqAL_callUpdateLocals' : forall TD ft noret0 rid oResult lc1 lc2 gl lc1' 
    lc2' lc,
  eqAL _ lc1 lc1' ->
  eqAL _ lc2 lc2' ->
  @callUpdateLocals GVsSig TD ft noret0 rid oResult lc1 lc2 gl = Some lc ->
  exists lc', 
    callUpdateLocals TD ft noret0 rid oResult lc1' lc2' gl = Some lc' /\
    eqAL _ lc lc'.
Proof.
  intros TD ft noret0 rid oResult lc1 lc2 gl lc1' lc2' lc H H0 H1.
  assert (J:=@eqAL_callUpdateLocals TD noret0 rid oResult lc1 lc2 gl lc1' lc2'
    ft H H0).
  rewrite H1 in J.
  destruct (callUpdateLocals TD ft noret0 rid oResult lc1' lc2' gl);
    try solve [inversion J].
  exists g. auto.
Qed.

Lemma eqAL_exCallUpdateLocals' : forall TD ft noret0 rid oResult lc lc' lc0,
  eqAL _ lc lc' ->
  @exCallUpdateLocals GVsSig TD ft noret0 rid oResult lc = Some lc0 ->
  exists lc0', exCallUpdateLocals TD ft noret0 rid oResult lc' = Some lc0' /\
               eqAL _ lc0 lc0'.
Proof.
  intros TD ft noret0 rid oResult lc lc' lc0 H H0.
  assert (J:=@eqAL_exCallUpdateLocals TD noret0 rid oResult lc lc' ft H).
  rewrite H0 in J.
  destruct (exCallUpdateLocals TD ft noret0 rid oResult lc'); 
    try solve [inversion J].
  exists g. auto.
Qed.

Lemma exCallUpdateLocals_uniq : forall TD ft noret0 rid oresult lc lc',
  uniq lc ->
  @exCallUpdateLocals GVsSig TD ft noret0 rid oresult lc = Some lc' ->
  uniq lc'.
Proof.
  intros.
  unfold exCallUpdateLocals in H0.
  destruct noret0; auto.
    inversion H0; subst; auto.

    destruct oresult; try solve [inversion H0].
    destruct ft; try solve [inversion H0].
    destruct (fit_gv TD ft g); inversion H0; subst.
      apply updateAddAL_uniq; auto.
Qed.

Lemma callUpdateLocals_uniq : forall TD ft noret0 rid oresult lc lc' gl lc'',
  uniq lc ->
  @callUpdateLocals GVsSig TD ft noret0 rid oresult lc lc' gl = Some lc'' ->
  uniq lc''.
Proof.
  intros.
  unfold callUpdateLocals in H0.
  destruct noret0; auto.
    destruct oresult; try solve [inversion H0; subst; auto].
    destruct (getOperandValue TD v lc' gl); inversion H0; subst; auto.

    destruct oresult; try solve [inversion H0; subst; auto].
    destruct (getOperandValue TD v lc' gl); tinv H0.
    destruct ft; tinv H0.
    destruct (lift_op1 _ (fit_gv TD ft) g ft); inv H0.
      apply updateAddAL_uniq; auto.
Qed.

Lemma updateValuesForNewBlock_uniq : forall l0 lc,
  uniq lc ->
  uniq (@updateValuesForNewBlock GVsSig l0 lc).
Proof.
  induction l0; intros lc Uniqc; simpl; auto.
    destruct a; apply updateAddAL_uniq; auto.
Qed.

Lemma updateValuesForNewBlock_spec4 : forall rs lc id1 gv,
  lookupAL _ rs id1 = Some gv ->
  lookupAL _ (@updateValuesForNewBlock GVsSig rs lc) id1 = Some gv.
Proof.  
  induction rs; intros; simpl in *.   
    inversion H.

    destruct a.
    destruct (id1==a); subst.
      inversion H; subst. apply lookupAL_updateAddAL_eq; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.

Lemma switchToNewBasicBlock_uniq : forall TD B1 B2 gl lc lc',
  uniq lc ->
  @switchToNewBasicBlock GVsSig TD B1 B2 gl lc = Some lc' ->
  uniq lc'.
Proof.
  intros TD B1 B2 gl lc lc' Uniqc H.
  unfold switchToNewBasicBlock in H.
  destruct (getIncomingValuesForBlockFromPHINodes TD (getPHINodesFromBlock B1)
    B2 gl lc); inversion H; subst.
  apply updateValuesForNewBlock_uniq; auto.
Qed.      

Lemma initializeFrameValues_init : forall TD la l0 lc,
  @_initializeFrameValues GVsSig TD la l0 nil = Some lc ->
  uniq lc.
Proof.
  induction la; intros; simpl in *; auto.
    inv H. auto.

    destruct a as [[t ?] id0].
    destruct l0.
      remember (@_initializeFrameValues GVsSig TD la nil nil) as R.
      destruct R; tinv H.
      destruct (gundef TD t); inv H; eauto using updateAddAL_uniq.

      remember (@_initializeFrameValues GVsSig TD la l0 nil) as R.
      destruct R; tinv H.
      destruct (GVsSig.(lift_op1) (fit_gv TD t) g t); inv H; 
        eauto using updateAddAL_uniq.
Qed.

Lemma initLocals_uniq : forall TD la ps lc,
  @initLocals GVsSig TD la ps = Some lc -> uniq lc.
Proof.
  intros la ps.
  unfold initLocals.
  apply initializeFrameValues_init; auto.
Qed.

Lemma initLocals_spec : forall TD la gvs id1 lc,
  In id1 (getArgsIDs la) ->
  @initLocals GVsSig TD la gvs = Some lc ->
  exists gv, lookupAL _ lc id1 = Some gv.
Proof.
  unfold initLocals.
  induction la; intros; simpl in *.
    inversion H.

    destruct a as [[t c] id0].  
    simpl in H.
    destruct H as [H | H]; subst; simpl.
      destruct gvs. 
        remember (@_initializeFrameValues GVsSig TD la nil nil) as R1.
        destruct R1; tinv H0.
        remember (gundef TD t) as R2.
        destruct R2; inv H0.
        eauto using lookupAL_updateAddAL_eq.

        remember (@_initializeFrameValues GVsSig TD la gvs nil) as R1.
        destruct R1; tinv H0.
        destruct (GVsSig.(lift_op1) (fit_gv TD t) g t); inv H0.
        eauto using lookupAL_updateAddAL_eq.

      destruct (eq_atom_dec id0 id1); subst.
        destruct gvs.
          remember (@_initializeFrameValues GVsSig TD la nil nil) as R1.
          destruct R1; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          eauto using lookupAL_updateAddAL_eq.

          remember (@_initializeFrameValues GVsSig TD la gvs nil) as R1.
          destruct R1; tinv H0.
          destruct (GVsSig.(lift_op1) (fit_gv TD t) g t); inv H0.
          eauto using lookupAL_updateAddAL_eq.

        destruct gvs.
          remember (@_initializeFrameValues GVsSig TD la nil nil) as R1.
          destruct R1; tinv H0.
          remember (gundef TD t) as R2.
          destruct R2; inv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          rewrite <- lookupAL_updateAddAL_neq; eauto.

          remember (@_initializeFrameValues GVsSig TD la gvs nil) as R1.
          destruct R1; tinv H0.
          destruct (GVsSig.(lift_op1) (fit_gv TD t) g t); inv H0.
          symmetry in HeqR1.
          eapply IHla in HeqR1; eauto.
          destruct HeqR1 as [gv HeqR1]. 
          rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_eq : 
  forall ps TD l1 ps1 cs1 tmn1 ps2 cs2 tmn2,
  @getIncomingValuesForBlockFromPHINodes GVsSig TD ps 
    (block_intro l1 ps1 cs1 tmn1) =
  getIncomingValuesForBlockFromPHINodes TD ps (block_intro l1 ps2 cs2 tmn2).
Proof.
  induction ps; intros; auto.
    simpl.
    erewrite IHps; eauto.
Qed.

Lemma switchToNewBasicBlock_eq : 
  forall TD B l1 ps1 cs1 tmn1 ps2 cs2 tmn2 gl lc,
  @switchToNewBasicBlock GVsSig TD B (block_intro l1 ps1 cs1 tmn1) gl lc =
  switchToNewBasicBlock TD B (block_intro l1 ps2 cs2 tmn2) gl lc.
Proof.
  intros.
  unfold switchToNewBasicBlock.
  erewrite getIncomingValuesForBlockFromPHINodes_eq; eauto.
Qed.

Lemma updateValuesForNewBlock_spec6 : forall lc rs id1 gvs
  (Hlk : lookupAL _ (@updateValuesForNewBlock GVsSig rs lc) id1 = ret gvs)
  (Hin : id1 `in` (dom rs)),
  lookupAL _ rs id1 = Some gvs.
Proof.
  induction rs; simpl; intros.
    fsetdec.

    destruct a.
    assert (id1 = i0 \/ id1 `in` dom rs) as J. fsetdec.   
    destruct J as [J | J]; subst.
      rewrite lookupAL_updateAddAL_eq in Hlk; auto. inv Hlk.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0); auto.
        contradict n; auto.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 i0); 
        subst; eauto.
        rewrite lookupAL_updateAddAL_eq in Hlk; auto. 
        rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto. 
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec6 : forall TD b gl lc ps' rs id1
  (HeqR1 : ret rs = @getIncomingValuesForBlockFromPHINodes GVsSig TD ps' b gl lc)
  (Hin : In id1 (getPhiNodesIDs ps')),
  id1 `in` dom rs.
Proof.
  induction ps'; simpl; intros.
    inv Hin.

    destruct a. destruct b. simpl in *.
    inv_mbind. inv HeqR1.
    destruct Hin as [Hin | Hin]; subst; simpl; auto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec7 : forall TD b gl lc ps' rs id1
  (HeqR1 : ret rs = @getIncomingValuesForBlockFromPHINodes GVsSig TD ps' b gl lc)
  (Hin : id1 `in` dom rs),
  In id1 (getPhiNodesIDs ps').
Proof.
  induction ps'; simpl; intros.
    inv HeqR1. fsetdec.

    destruct a. destruct b. simpl in *.
    inv_mbind. inv HeqR1. simpl in *.
    assert (id1 = i0 \/ id1 `in` dom l2) as J. fsetdec.
    destruct J as [J | J]; subst; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec8 : forall TD b gl lc ps' rs id1
  (HeqR1 : ret rs = @getIncomingValuesForBlockFromPHINodes GVsSig TD ps' b gl lc)
  (Hnotin : ~ In id1 (getPhiNodesIDs ps')),
  id1 `notin` dom rs.
Proof.
  intros.
  intro J. apply Hnotin. 
  eapply getIncomingValuesForBlockFromPHINodes_spec7 in HeqR1; eauto.
Qed.

Lemma updateValuesForNewBlock_spec7 : forall lc rs id1 gvs
  (Hlk : lookupAL _ (@updateValuesForNewBlock GVsSig rs lc) id1 = ret gvs)
  (Hnotin : id1 `notin` (dom rs)),
  lookupAL _ lc id1 = ret gvs.
Proof.
  induction rs; simpl; intros; auto.
    destruct a.

    destruct_notin.
    rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto. 
Qed.

Lemma updateValuesForNewBlock_spec6' : forall lc rs id1 
  (Hin : id1 `in` (dom rs)),
  lookupAL _ (@updateValuesForNewBlock GVsSig rs lc) id1 = lookupAL _ rs id1.
Proof.
  induction rs; simpl; intros.
    fsetdec.

    destruct a.
    assert (id1 = a \/ id1 `in` dom rs) as J. fsetdec.   
    destruct J as [J | J]; subst.
      rewrite lookupAL_updateAddAL_eq.
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) a a); auto.
        contradict n; auto.

      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
        subst; eauto.
        rewrite lookupAL_updateAddAL_eq; auto. 
        rewrite <- lookupAL_updateAddAL_neq; eauto. 
Qed.

Lemma updateValuesForNewBlock_spec7' : forall lc rs id1 
  (Hin : id1 `notin` (dom rs)),
  lookupAL _ (@updateValuesForNewBlock GVsSig rs lc) id1 = lookupAL _ lc id1.
Proof.
  induction rs; simpl; intros; auto.
    destruct a. destruct_notin.
    rewrite <- lookupAL_updateAddAL_neq; eauto. 
Qed.

Lemma updateValuesForNewBlock_sim : forall id0 lc lc'
  (Heq : forall id' : id,
        id' <> id0 ->
        lookupAL _ lc id' = lookupAL GVs lc' id')
  g0 g
  (EQ : forall id' : id,
       id' <> id0 ->
       lookupAL _ g0 id' = lookupAL _ g id'),
  forall id', id' <> id0 ->
   lookupAL _ (updateValuesForNewBlock g0 lc) id' =
   lookupAL _ (updateValuesForNewBlock g lc') id'.
Proof.
  intros.
  destruct (AtomSetProperties.In_dec id' (dom g0)).
    rewrite updateValuesForNewBlock_spec6'; auto.
    destruct (AtomSetProperties.In_dec id' (dom g)).
      rewrite updateValuesForNewBlock_spec6'; auto.
      
      apply notin_lookupAL_None in n.
      erewrite <- EQ in n; eauto.
      apply indom_lookupAL_Some in i0.
      destruct i0 as [gv0 i0].
      rewrite i0 in n. congruence.

    rewrite updateValuesForNewBlock_spec7'; auto.
    destruct (AtomSetProperties.In_dec id' (dom g)).
      apply notin_lookupAL_None in n.
      erewrite EQ in n; eauto.
      apply indom_lookupAL_Some in i0.
      destruct i0 as [gv0 i0].
      rewrite i0 in n. congruence.

      rewrite updateValuesForNewBlock_spec7'; auto.
Qed.

Lemma bops_trans : forall cfg state1 state2 state3 tr1 tr2,
  @bops GVsSig cfg state1 state2 tr1 ->
  bops cfg state2 state3 tr2 ->
  bops cfg state1 state3 (trace_app tr1 tr2).
Proof.
  intros cfg state1 state2 state3 tr1 tr2 H.
  generalize dependent state3.
  generalize dependent tr2.
  induction H; intros; auto.
    rewrite <- trace_app_commute. eauto.
Qed.

Lemma bInsn__bops : forall cfg state1 state2 tr,
  @bInsn GVsSig cfg state1 state2 tr ->
  bops cfg state1 state2 tr.
Proof.
  intros.
  rewrite <- trace_app_nil__eq__trace.
  eauto.
Qed.

Lemma bInsn__inv : forall cfg B1 c cs tmn3 lc1 als1 Mem1 B2 tmn4 lc2 als2 
  Mem2 tr,
  @bInsn GVsSig cfg (mkbEC B1 (c::cs) tmn3 lc1 als1 Mem1) 
    (mkbEC B2 cs tmn4 lc2 als2 Mem2) tr ->
  B1 = B2 /\ tmn3 = tmn4.
Proof.
  intros.
  inversion H; subst; repeat (split; auto).
Qed.

Lemma bInsn_Call__inv : forall cfg B1 c cs tmn3 lc1 als1 Mem1 B2 tmn4 lc2 als2 
  Mem2 tr,
  @bInsn GVsSig cfg
    (mkbEC B1 (c::cs) tmn3 lc1 als1 Mem1) (mkbEC B2 cs tmn4 lc2 als2 Mem2) tr ->
  Instruction.isCallInst c = true ->
  B1 = B2 /\ tmn3 = tmn4 /\ als1 = als2.
Proof.
  intros.
  inversion H; subst; try solve [inversion H0 | repeat (split; auto)].
Qed.

(* preservation of uniqueness and inclusion *)

Definition bInsn_preservation_prop cfg state1 state2 tr
  (db:@bInsn GVsSig cfg state1 state2 tr) :=
  forall S los nts Ps gl fs F B cs tmn lc als Mem cs' tmn' B' lc' als' Mem',
  cfg = (mkbCfg S (los, nts) Ps gl fs F) ->
  state1 = (mkbEC B cs tmn lc als Mem) ->
  uniqSystem S ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F ->
  state2 = (mkbEC B' cs' tmn' lc' als' Mem') ->
  blockInSystemModuleFdef B' S (module_intro los nts Ps) F.
Definition bops_preservation_prop cfg state1 state2 tr
  (db:@bops GVsSig cfg state1 state2 tr) :=
  forall S los nts Ps gl fs F B cs tmn lc als Mem B' cs' tmn' lc' als' Mem',
  cfg = (mkbCfg S (los, nts) Ps gl fs F) ->
  state1 = (mkbEC B cs tmn lc als Mem) ->
  state2 = (mkbEC B' cs' tmn' lc' als' Mem') ->
  uniqSystem S ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F ->
  blockInSystemModuleFdef B' S (module_intro los nts Ps) F.
Definition bFdef_preservation_prop fv rt lp S TD Ps lc gl fs Mem lc' als' 
 Mem' B' Rid oResult tr
 (db:@bFdef GVsSig fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr)
  :=
  forall los nts,
  TD = (los, nts) ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  exists fptrs, exists fptr, exists F, 
    getOperandValue TD fv lc gl = Some fptrs /\
    fptr @ fptrs /\ 
    lookupFdefViaPtr Ps fs fptr = Some F /\
    uniqFdef F /\
    blockInSystemModuleFdef B' S (module_intro los nts Ps) F.

Lemma b_preservation : 
  (forall cfg state1 state2 tr db, 
     @bInsn_preservation_prop cfg state1 state2 tr db) /\
  (forall cfg state1 state2 tr db, 
     @bops_preservation_prop cfg state1 state2 tr  db) /\
  (forall fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr db, 
    @bFdef_preservation_prop fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid 
      oResult tr db).
Proof.
(b_mutind_cases
  apply b_mutind with
    (P  := bInsn_preservation_prop)
    (P0 := bops_preservation_prop)
    (P1 := bFdef_preservation_prop) Case);
  unfold bInsn_preservation_prop, 
         bops_preservation_prop, 
         bFdef_preservation_prop; intros; subst; repeat app_inv; auto.
Case "bBranch".
  apply andb_true_iff in H2.
  destruct H2.
  eapply andb_true_iff.
  split; auto.
    assert (uniqFdef F0) as UniqF0.
      eapply uniqSystem__uniqFdef with (S:=S0); eauto.
    symmetry in e0.
    destruct (isGVZero (los, nts) c);
      apply lookupBlockViaLabelFromFdef_inv in e0;
      destruct e0; auto.

Case "bBranch_uncond".
  apply andb_true_iff in H2.
  destruct H2.
  eapply andb_true_iff.
  split; auto.
    assert (uniqFdef F0) as UniqF0.
      eapply uniqSystem__uniqFdef with (S:=S0); eauto.
    symmetry in e.
    apply lookupBlockViaLabelFromFdef_inv in e; auto.
    destruct e; auto.
  
Case "bops_cons".
  destruct S2 as [b2 cs2 tmn2 lc2 als2 M2].
  eapply H with (cs0:=cs)(lc0:=lc)(als0:=als)(gl0:=gl)(fs0:=fs)(Mem:=Mem0)
    (B':=b2)(lc':=lc2)(cs':=cs2)(tmn':=tmn2)(als':=als2)(Mem':=M2) in H5; eauto.

Case "bFdef_func".
  exists fptrs. exists fptr.
  exists (fdef_intro (fheader_intro fa rt fid la va) lb).
  split; auto.
  split; auto.
  split; auto.
  split.
    eapply lookupFdefViaPtr_uniq; eauto.
    eapply H with (lc'0:=lc')(cs'0:=nil)(als'0:=als')(Mem'0:=Mem'); 
      eauto using entryBlockInSystemBlockFdef''.   

Case "bFdef_proc".
  exists fptrs. exists fptr.
  exists (fdef_intro (fheader_intro fa rt fid la va) lb).
  split; auto.
  split; auto.
  split; auto.
  split.
    eapply lookupFdefViaPtr_uniq; eauto.
    eapply H; eauto using entryBlockInSystemBlockFdef''.
Qed.

Lemma bInsn_preservation : forall tr S los nts Ps F cs tmn lc als 
  gl fs Mem cs' tmn' lc' als' Mem' B B',
  @bInsn GVsSig (mkbCfg S (los, nts) Ps gl fs F)
    (mkbEC B cs tmn lc als Mem) 
    (mkbEC B' cs' tmn' lc' als' Mem') tr ->
  uniqSystem S ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F ->
  blockInSystemModuleFdef B' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct b_preservation as [J _].
  unfold bInsn_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma bops_preservation : forall tr S los nts Ps F B cs tmn lc als gl
    fs Mem B' cs' tmn' lc' als' Mem',
  @bops GVsSig (mkbCfg S (los, nts) Ps gl fs F)
    (mkbEC B cs tmn lc als Mem) (mkbEC B' cs' tmn' lc' als' Mem')
    tr ->
  uniqSystem S ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F ->
  blockInSystemModuleFdef B' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct b_preservation as [_ [J _]].
  unfold bops_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma bFdef_preservation : forall fv rt lp S los nts Ps lc gl fs Mem lc' 
    als' Mem' B' Rid oResult tr,
  @bFdef GVsSig fv rt lp S (los, nts) Ps lc gl fs Mem lc' als' Mem' B' Rid 
    oResult tr ->
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  exists fptrs, exists fptr, exists F, 
    getOperandValue (los, nts) fv lc gl = Some fptrs /\
    fptr @ fptrs /\ 
    lookupFdefViaPtr Ps fs fptr = Some F /\
    uniqFdef F /\
    blockInSystemModuleFdef B' S (module_intro los nts Ps) F.
Proof.
  intros.
  destruct b_preservation as [_ [_ J]].
  unfold bFdef_preservation_prop in J.
  eapply J; eauto.
Qed.

Lemma In_initializeFrameValues__In_getArgsIDs: forall
  (TD : TargetData) (la : args) (gvs : list (GVsT GVsSig)) (id1 : atom) 
  (lc : Opsem.GVsMap) (gv : GVsT GVsSig) acc,
  Opsem._initializeFrameValues TD la gvs acc = ret lc ->
  lookupAL (GVsT GVsSig) lc id1 = ret gv -> 
  In id1 (getArgsIDs la) \/ id1 `in` dom acc.
Proof.
  induction la as [|[]]; simpl; intros.
    inv H.
    right. apply lookupAL_Some_indom in H0; auto.

    destruct p.
    destruct gvs.
      inv_mbind'. inv H.
      destruct (id_dec i0 id1); subst; auto.
      rewrite <- lookupAL_updateAddAL_neq in H0; auto.
      eapply IHla in H0; eauto.
      destruct H0 as [H0 | H0]; auto.

      inv_mbind'. inv H.
      destruct (id_dec i0 id1); subst; auto.
      rewrite <- lookupAL_updateAddAL_neq in H0; auto.
      eapply IHla in H0; eauto.
      destruct H0 as [H0 | H0]; auto.
Qed.

Lemma In_initLocals__In_getArgsIDs : forall TD la gvs id1 lc gv,
  @Opsem.initLocals GVsSig TD la gvs = Some lc ->
  lookupAL _ lc id1 = Some gv ->
  In id1 (getArgsIDs la).
Proof.
  unfold Opsem.initLocals.
  intros.
  eapply In_initializeFrameValues__In_getArgsIDs in H; eauto.
  destruct H as [H | H]; auto.
    fsetdec.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec9: forall TD gl lc b id0 gvs0
  ps' l0,
  ret l0 = @Opsem.getIncomingValuesForBlockFromPHINodes GVsSig TD ps' b gl lc ->
  id0 `in` dom l0 ->
  lookupAL _ l0 id0 = ret gvs0 ->
  exists id1, exists t1, exists vls1, exists v, exists n,
    In (insn_phi id1 t1 vls1) ps' /\
    nth_list_value_l n vls1 = Some (v, getBlockLabel b) /\
    Opsem.getOperandValue TD v lc gl= Some gvs0.
Proof.
  induction ps' as [|[]]; simpl; intros.
    inv H. fsetdec.
    
    inv_mbind. inv H. simpl in *. 
    destruct (id0 == i0); subst.
      destruct b. simpl in *.
      symmetry in HeqR.
      apply getValueViaLabelFromValuels__nth_list_value_l in HeqR; auto.
      destruct HeqR as [n HeqR].
      destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i0 i0); 
        try congruence.
      inv H1.
      exists i0. exists t. exists l0. exists v. exists n.
      split; auto. 

      apply IHps' in H1; auto; try fsetdec.
      destruct H1 as [id1 [t1 [vls1 [v' [n' [J1 [J2 J3]]]]]]].
      exists id1. exists t1. exists vls1. exists v'. exists n'.
      split; auto.
Qed.

Lemma updateValuesForNewBlock_spec5: forall lc1' lc2' i0
  (Hlk: lookupAL _ lc1' i0 = lookupAL _ lc2' i0) lc2
  (Hlk: merror = lookupAL _ lc2 i0),
  lookupAL _ lc1' i0 =
    lookupAL _ (@Opsem.updateValuesForNewBlock GVsSig lc2 lc2') i0.
Proof.
  induction lc2 as [|[]]; simpl; intros; auto.
    destruct (i0 == a); try congruence.
    rewrite <- lookupAL_updateAddAL_neq; auto.
Qed.


End OpsemProps. End OpsemProps.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
