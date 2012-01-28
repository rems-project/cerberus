Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import Values.
Require Import vellvm.
Require Import genericvalues.
Require Import trace.
Require Import Memory.
Require Import alist.
Require Import Integers.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import opsem.
Require Import dopsem.
Require Import sb_def.
Require Import sb_ds_trans.
Require Import sb_msim.
Require Import sb_ds_gv_inject.
Require Import sb_ds_sim.
Require Import sb_ds_trans_lib.

Import SB_ds_pass.
Export SBspec.

Ltac destruct_ctx_br :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           SBspec.ECS := {|
                          SBspec.CurFunction := ?F;
                          SBspec.CurBB := _;
                          SBspec.CurCmds := nil;
                          SBspec.Terminator := _;
                          SBspec.Locals := _;
                          SBspec.Rmap := _;
                          SBspec.Allocas := _ |} :: _;
           SBspec.Mem := _;
           SBspec.Mmap := _ |} ?Cfg ?St |- _] =>
  destruct Cfg as [S2 TD2 Ps2 gl2 fs2];
  destruct St as [ECs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim [Hwfg 
    [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [Hclib [HBinF [HFinPs [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst
end.

Ltac destruct_ctx_return :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           SBspec.ECS := {|
                          SBspec.CurFunction := ?F;
                          SBspec.CurBB := _;
                          SBspec.CurCmds := nil;
                          SBspec.Terminator := _;
                          SBspec.Locals := _;
                          SBspec.Rmap := _;
                          SBspec.Allocas := _ |}
                          :: {|
                             SBspec.CurFunction := ?F';
                             SBspec.CurBB := _;
                             SBspec.CurCmds := ?c' :: _;
                             SBspec.Terminator := _;
                             SBspec.Locals := _;
                             SBspec.Rmap := _;
                             SBspec.Allocas := _ |} :: _;
           SBspec.Mem := _;
           SBspec.Mmap := _ |} ?Cfg ?St |- _] =>
  destruct Cfg as [S2 TD2 Ps2 gl2 fs2];
  destruct St as [ECs2 M2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim [Hwfg 
    [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct ECs2 as [|[F2' B2' cs2' tmn2' lc2' als2'] ECs2];
    try solve [inversion HsimECs];
  destruct HsimECs as [HsimEC' HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [Hclib [HBinF [HFinPs [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst;
  destruct F' as [fh1' bs1'];
  destruct F2' as [fh2' bs2'];
  destruct c'; try solve [inversion HsimEC'];
  destruct HsimEC' as [Hclib' [HBinF' [HFinPs' [Htfdef' [Heq0' [Hasim' [Hnth' 
    [Heqb1' [Heqb2' [ex_ids' [rm2' [ex_ids3' [ex_ids4' [cs22' [cs23' [cs24' 
    [Hgenmeta' [Hrsim' [Hinc' [Hcall' [Htcmds' [Httmn' Heq2']]]]]]]]]]]]
    ]]]]]]]]]]; 
    subst
end.

Ltac destruct_ctx_other :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           SBspec.ECS := {|
                          SBspec.CurFunction := ?F;
                          SBspec.CurBB := _;
                          SBspec.CurCmds := ?c::_;
                          SBspec.Terminator := _;
                          SBspec.Locals := _;
                          SBspec.Rmap := _;
                          SBspec.Allocas := _ |} :: _;
           SBspec.Mem := _;
           SBspec.Mmap := _ |} ?Cfg ?St |- _] =>
  destruct St as [ECs2 M2];
  destruct Cfg as [S2 TD2 Ps2 gl2 fs2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim
    [Hwfg [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [Hclib [HBinF [HFinPS [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst
end.

Definition updateAddALs (X:Type) (lc:AssocList X) (kvs:list (atom*X)) : 
  AssocList X :=
fold_left  (fun lc0 kv => let '(k, v) := kv in updateAddAL _ lc0 k v) kvs lc.

Lemma simpl_cons_updateAddALs : forall X lc v k vks,
  updateAddALs X lc ((v,k)::vks) = updateAddALs _ (updateAddAL _ lc v k) vks.
Proof. auto. Qed.

Ltac next_insn :=
  let nonupdate_insn F2 B2 cs2 tmn2 lc2 als2 ECs2 M2 M2' :=
    match goal with
    | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
         ((Opsem.mkEC _ _ (insn_store _ _ _ _ _ :: _) _ _ _)::_) _
       ) _ _ ] =>
    apply Opsem.sop_star_cons with (state2:=
      Opsem.mkState 
        ((Opsem.mkEC F2 B2 cs2 tmn2 lc2 als2):: 
          ECs2) M2'); eauto 

    | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
         ((Opsem.mkEC _ _ (insn_call _ true _ _ _ _ :: _) _ _ _)::_) _
       ) _ _ ] =>
    apply Opsem.sop_star_cons with (state2:=
      Opsem.mkState 
        ((Opsem.mkEC F2 B2 cs2 tmn2 lc2 als2):: 
          ECs2) M2); eauto 
    end in

  let update_insn F2 B2 cs2 tmn2 lc2 k v als2 ECs2 M2 als2' M2' :=
    match goal with
    | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
         ((Opsem.mkEC _ _ (insn_malloc _ _ _ _ :: _) _ _ _)::_) _
       ) _ _ ] =>
    apply Opsem.sop_star_cons with (state2:=
      Opsem.mkState 
        ((Opsem.mkEC F2 B2 cs2 tmn2 (updateAddAL _ lc2 k v) als2):: 
          ECs2) M2'); eauto 

    | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
         ((Opsem.mkEC _ _ (insn_alloca _ _ _ _ :: _) _ _ _)::_) _
       ) _ _ ] =>
    apply Opsem.sop_star_cons with (state2:=
      Opsem.mkState 
        ((Opsem.mkEC F2 B2 cs2 tmn2 (updateAddAL _ lc2 k v) als2'):: 
          ECs2) M2'); eauto 

    | |- _ =>
    apply Opsem.sop_star_cons with (state2:=
      Opsem.mkState 
        ((Opsem.mkEC F2 B2 cs2 tmn2 (updateAddAL _ lc2 k v) als2):: 
          ECs2) M2); eauto 
    end in

  rewrite <- (@trace_app_nil__eq__trace trace_nil);
  match goal with
  | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
           ((Opsem.mkEC ?F2 ?B2 (_ :: ?cs2) ?tmn2 ?lc2 ?als2)::?ECs2) ?M2) 
       (Opsem.mkState ((Opsem.mkEC _ _ _ _ _ _)::_) ?M2') _ ] => 
       nonupdate_insn F2 B2 cs2 tmn2 lc2 als2 ECs2 M2 M2'
  | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
           ((Opsem.mkEC ?F2 ?B2 (_ :: ?cs2) ?tmn2 ?lc2 ?als2)::?ECs2) ?M2) 
       (Opsem.mkState 
           ((Opsem.mkEC _ _ _ _ (updateAddALs _ ?lc2 ((?k,?v)::_)) ?als2')::_) 
       ?M2') _ ] => update_insn F2 B2 cs2 tmn2 lc2 k v als2 ECs2 M2 als2' M2'
  | |- context [updateAddALs ?Typ _ _] => 
    try rewrite (simpl_cons_updateAddALs Typ);
    match goal with
    | |- context [ Opsem.sop_star _ 
       (Opsem.mkState 
           ((Opsem.mkEC ?F2 ?B2 (_ :: ?cs2) ?tmn2 ?lc2 ?als2)::?ECs2) ?M2) 
       (Opsem.mkState 
           ((Opsem.mkEC _ _ _ _ (updateAddALs _ ?lc2 ((?k,?v)::_)) ?als2')::_) 
       ?M2') _ ] => update_insn F2 B2 cs2 tmn2 lc2 k v als2 ECs2 M2 als2' M2'
    end
  end.

Ltac inv_mbind :=
  repeat match goal with
         | H : match ?e with
               | Some _ => _
               | None => None
               end = Some _ |- _ => remember e as R; destruct R as [[]|]; inv H
         end.

Ltac tac0 := match goal with
  | |- exists _, _ => idtac
  | |- _ => solve [eauto]
  end.

Ltac simulation_ops :=
  let gv3' := fresh "gv3'" in
  let Hop := fresh "Hop" in
  let Hinj := fresh "Hinj" in
  match goal with
  | H : BOP _ _ _ _ _ _ _ = Some _ |- _ =>
    eapply simulation__BOP in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : FBOP _ _ _ _ _ _ _ = Some _ |- _ =>
    eapply simulation__FBOP in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : EXT _ _ _ _ _ _ _ = Some _ |- _ =>
    eapply simulation__EXT in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : TRUNC _ _ _ _ _ _ _ = Some _ |- _ =>
    eapply simulation__TRUNC in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : ICMP _ _ _ _ _ _ _ = Some _ |- _ =>
    eapply simulation__ICMP in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : FCMP _ _ _ _ _ _ _ = Some _ |- _ =>
    eapply simulation__FCMP in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : CAST _ _ _ _ _ _ _ = Some _ |- _ =>
    eapply simulation__CAST in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : getOperandValue _ _ _ _ = Some _ |- _ =>
    (* It is important to place getOperandValue before extract/insert/select, 
       because their proofs need the simulation of getOperandValue. *)
    eapply simulation__getOperandValue in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : extractGenericValue _ _ _ _ = Some _ |- _ =>
    eapply simulation__extractGenericValue in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  | H : insertGenericValue _ _ _ _ _ _ = Some _ |- _ =>
    eapply simulation__insertGenericValue in H; tac0;
    destruct H as [gv3' [Hop Hinj]]
  end.             

Ltac inv_trans_cmds :=
  match goal with
  | Htcmds : trans_cmds _ _ _ = Some _ |- _ => 
    apply trans_cmds_inv in Htcmds;
    destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst;
    try match goal with
    | H1 : isPointerTypB ?t = false,
      Htcmd : trans_cmd _ _ _ = munit _ |- _ => 
      (* for Bitcase_nptr, Select_nptr *)
      simpl in Htcmd; rewrite H1 in Htcmd; inv Htcmd
    | H0 : ?castop0 <> castop_bitcast /\ ?castop0 <> castop_inttoptr,
      Htcmd : trans_cmd ?ex_ids3 _ ?c = munit (?ex_ids5, ?cs1') |- _ =>
      (* Othercast *)
      assert (ex_ids5 = ex_ids3 /\ cs1' = [c]) as EQ; try solve 
        [destruct H0 as [J1 J2];
         simpl in Htcmd;
         destruct castop0; inv Htcmd; 
          try solve [contradict J1; auto | contradict J2; auto | auto]]; 
      destruct EQ; subst
    | Htcmd : trans_cmd _ _ _ = munit _ |- _ => (* Other instructions *) 
      inv Htcmd    
    end
  end.

Ltac SBpass_is_correct__dsOp :=
match goal with
| [Hsim : sbState_simulates_State _ _
           {|
           OpsemAux.CurSystem := _;
           OpsemAux.CurTargetData := ?TD;
           OpsemAux.CurProducts := _;
           OpsemAux.Globals := _;
           OpsemAux.FunTable := _ |}
           {|
           SBspec.ECS := {|
                          SBspec.CurFunction := ?F;
                          SBspec.CurBB := _;
                          SBspec.CurCmds := ?c::_;
                          SBspec.Terminator := _;
                          SBspec.Locals := _;
                          SBspec.Rmap := _;
                          SBspec.Allocas := _ |} :: _;
           SBspec.Mem := _;
           SBspec.Mmap := _ |} ?Cfg ?St |- _] =>

  (* destruct hyps *)
  destruct St as [ECs2 M2];
  destruct Cfg as [S2 TD2 Ps2 gl2 fs2];
  destruct TD as [los nts];
  destruct Hsim as [Hwfs [HMinS [Htsym [Heq1 [Htps [HsimECs [Htprds [Hfsim
    [Hwfg [Hwfmi HsimM]]]]]]]]]];
    subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2];
    try solve [inversion HsimECs];
  simpl in HsimECs;
  destruct HsimECs as [HsimEC HsimECs];
  destruct F as [fh1 bs1];
  destruct F2 as [fh2 bs2];
  destruct HsimEC as [Hclib [HBinF [HFinPS [Htfdef [Heq0 [Hasim [Hnth [Heqb1 
    [Heqb2 [ex_ids [rm2 [ex_ids3 [ex_ids4 [cs22 [cs23 [Hgenmeta [Hrsim [Hinc 
    [Htcmds [Httmn Heq2]]]]]]]]]]]]]]]]]]]]; subst;

  (* inv trans_cmds *) 
  inv_trans_cmds; simpl in Heqb2;

  (* applying simulation of different operations *)
  repeat simulation_ops;

  (* instantiate goals *)
  let solve_goal mi id0 ex_ids3 cs2' gv3' :=
    exists (Opsem.mkState
            ((Opsem.mkEC (fdef_intro fh2 bs2) B2
              (cs2' ++ cs23) tmn2 (updateAddAL _ lc2 id0 gv3') als2)::
              ECs2) M2);
    exists mi;
    repeat (split; try solve [auto using inject_incr_refl | 
                              eapply cmds_at_block_tail_next; eauto]);
    try solve [
      simpl_env; simpl;
      rewrite <- (@trace_app_nil__eq__trace trace_nil);
      eapply Opsem.sop_star_cons; eauto; eauto |
    
      exists ex_ids; exists rm2;
      exists ex_ids3; exists ex_ids4; exists cs2'; exists cs23;
      repeat (split; eauto using reg_simulation__updateAddAL_lc, 
                                 getCmdID_in_getFdefLocs)
    ] in
  try solve [match goal with
  | [mi : MoreMem.meminj,
     id0 : id,
     _ : trans_cmds _ _ _ = Some (_, ?cs2'),
     _ : incl _ ?ex_ids3 |- _ ] =>
     match goal with
     | H : _ _ _ _ _ _ _ _ = munit ?gv3' |- _ => 
       solve_goal mi id0 ex_ids3 cs2' gv3'
     | H : LLVMgv.extractGenericValue _ _ _ _ = munit ?gv3' |- _  => 
       solve_goal mi id0 ex_ids3 cs2' gv3'
     | H : LLVMgv.insertGenericValue _ _ _ _ _ _ = munit ?gv3' |- _  => 
       solve_goal mi id0 ex_ids3 cs2' gv3'
    end
  end]
end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
