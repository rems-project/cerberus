Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import List.
Require Import Arith.
Require Import Metatheory.
Require Import alist.
Require Import CoqListFacts.
Require Import Coqlib.

(***************************************************************)
(* Syntax easy to be proved with symbolic execution. *)

Module SimpleSE.

Export Opsem.

Definition DGVMap := @GVsMap DGVs.
Hint Unfold DGVMap.

(***************************************************************)
(* deterministic big-step for this new syntax with subblocks. *)

Record ExecutionContext : Type := mkEC {
CurBB       : block;
Locals      : DGVMap;                (* LLVM values used in this invocation *)
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Record State : Type := mkState {
Frame          : ExecutionContext;
Mem            : mem
}.

Definition isCall (i:cmd) : bool :=
match i with
| insn_call _ _ _ _ _ _ => true
| _ => false
end.

Inductive dbCmd : TargetData -> GVMap ->
                  DGVMap -> list mblock -> mem -> 
                  cmd -> 
                  DGVMap -> list mblock -> mem -> 
                  trace -> Prop :=
| dbBop: forall TD lc gl id bop sz v1 v2 gv3 Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_bop id bop sz v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil 
| dbFBop: forall TD lc gl id fbop fp v1 v2 gv3 Mem als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_fbop id fbop fp v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil 
| dbExtractValue : forall TD lc gl id t v gv gv' Mem als idxs,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  dbCmd TD gl
    lc als Mem
    (insn_extractvalue id t v idxs)
    (updateAddAL _ lc id gv') als Mem
    trace_nil 
| dbInsertValue : forall TD lc gl id t v t' v' gv gv' gv'' idxs Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  dbCmd TD gl
    lc als Mem
    (insn_insertvalue id t v t' v' idxs)
    (updateAddAL _ lc id gv'') als Mem
    trace_nil 
| dbMalloc : forall TD lc gl id t v gn align Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  @getOperandValue DGVs TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  dbCmd TD gl
    lc als Mem
    (insn_malloc id t v align)
    (updateAddAL _ lc id (blk2GV TD mb)) als Mem'
    trace_nil
| dbFree : forall TD lc gl fid t v Mem als Mem' mptr,
  @getOperandValue DGVs TD v lc gl = Some mptr ->
  free TD Mem mptr = Some Mem'->
  dbCmd TD gl
    lc als Mem
    (insn_free fid t v)
    lc als Mem'
    trace_nil
| dbAlloca : forall TD lc gl id t v gn align Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  @getOperandValue DGVs TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  dbCmd TD gl
    lc als Mem
    (insn_alloca id t v align)
    (updateAddAL _ lc id (blk2GV TD mb)) (mb::als) Mem'
    trace_nil
| dbLoad : forall TD lc gl id t v align Mem als mp gv,
  @getOperandValue DGVs TD v lc gl = Some mp ->
  mload TD Mem mp t align = Some gv ->
  dbCmd TD gl
    lc als Mem
    (insn_load id t v align)
    (updateAddAL _ lc id gv) als Mem
    trace_nil
| dbStore : forall TD lc gl sid t v1 v2 align Mem als mp2 gv1 Mem',
  @getOperandValue DGVs TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  dbCmd TD gl 
    lc als Mem
    (insn_store sid t v1 v2 align)
    lc als Mem'
    trace_nil
| dbGEP : forall TD lc gl id inbounds t v idxs vidxs mp mp' Mem als,
  @getOperandValue DGVs TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  GEP TD t mp vidxs inbounds = Some mp' ->
  dbCmd TD gl
    lc als Mem
    (insn_gep id inbounds t v idxs)
    (updateAddAL _ lc id mp') als Mem
    trace_nil 
| dbTrunc : forall TD lc gl id truncop t1 v1 t2 gv2 Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_trunc id truncop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil
| dbExt : forall TD lc gl id extop t1 v1 t2 gv2 Mem als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_ext id extop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil
| dbCast : forall TD lc gl id castop t1 v1 t2 gv2 Mem als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_cast id castop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil
| dbIcmp : forall TD lc gl id cond t v1 v2 gv3 Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_icmp id cond t v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil
| dbFcmp : forall TD lc gl id fcond fp v1 v2 gv3 Mem als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_fcmp id fcond fp v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil
| dbSelect : forall TD lc gl id v0 t v1 v2 cond Mem als gv1 gv2,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_select id v0 t v1 v2)
    (if isGVZero TD cond then updateAddAL _ lc id gv2 
     else updateAddAL _ lc id gv1) als Mem
    trace_nil
.

Inductive dbTerminator : 
  TargetData -> mem -> fdef -> GVMap -> 
  block -> (@GVsMap DGVs) -> 
  terminator -> 
  block -> (@GVsMap DGVs) -> 
  trace -> Prop :=
| dbBranch : forall TD Mem F B lc gl bid Cond l1 l2 c
                              l' ps' sbs' tmn' lc',   
  @getOperandValue DGVs TD Cond lc gl = Some c ->
  Some (block_intro l' ps' sbs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  Some lc' = switchToNewBasicBlock TD
    (block_intro l' ps' sbs' tmn') B gl lc ->
  dbTerminator TD Mem F gl
    B lc
    (insn_br bid Cond l1 l2)
    (block_intro l' ps' sbs' tmn') lc' 
    trace_nil 
| dbBranch_uncond : forall TD Mem F B lc gl l bid
                              l' ps' sbs' tmn' lc',   
  Some (block_intro l' ps' sbs' tmn') = lookupBlockViaLabelFromFdef F l ->
  Some lc' = switchToNewBasicBlock TD
    (block_intro l' ps' sbs' tmn') B gl lc ->
  dbTerminator TD Mem F gl
    B lc
    (insn_br_uncond bid l) 
    (block_intro l' ps' sbs' tmn') lc'
    trace_nil 
.

Inductive dbCmds : TargetData -> GVMap -> 
                   DGVMap -> list mblock -> mem -> 
                   cmds -> 
                   DGVMap -> list mblock -> mem -> 
                   trace -> Prop :=
| dbCmds_nil : forall TD lc als gl Mem, 
    dbCmds TD gl lc als Mem nil lc als Mem trace_nil
| dbCmds_cons : forall TD c cs gl lc1 als1 Mem1 t1 t2 lc2 als2 Mem2
                       lc3 als3 Mem3,
    dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 t1 ->
    dbCmds TD gl lc2 als2 Mem2 cs lc3 als3 Mem3 t2 ->
    dbCmds TD gl lc1 als1 Mem1 (c::cs) lc3 als3 Mem3 (trace_app t1 t2).

Inductive dbCall : system -> TargetData -> list product -> GVMap -> 
                   GVMap -> DGVMap -> mem -> 
                   cmd -> 
                   DGVMap -> mem -> 
                   trace -> Prop :=
| dbCall_internal : forall S TD Ps lc gl fs rid noret tailc rt fv lp
                       Rid oResult tr lc' Mem Mem' als' Mem'' B' lc'' ft,
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  free_allocas TD Mem' als' = Some Mem'' ->
  isCall (insn_call rid noret tailc ft fv lp) = true ->
  callUpdateLocals TD ft noret rid oResult lc lc' gl = Some lc'' ->
  dbCall S TD Ps fs gl lc Mem (insn_call rid noret tailc ft fv lp) lc'' Mem'' tr

| dbCall_external : forall S TD Ps lc gl fs rid noret ca fv fid fptr
                          lp rt la va Mem oresult Mem' lc' ft fa gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  @getOperandValue DGVs TD fv lc gl = Some fptr -> 
  lookupExFdecViaPtr Ps fs fptr = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvs ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  isCall (insn_call rid noret ca ft fv lp) = true ->
  exCallUpdateLocals TD ft noret rid oresult lc = Some lc' ->
  dbCall S TD Ps fs gl lc Mem (insn_call rid noret ca ft fv lp) lc' Mem' 
    trace_nil

with dbSubblock : system -> TargetData -> list product -> GVMap -> GVMap -> 
                  DGVMap -> list mblock -> mem -> 
                  cmds -> 
                  DGVMap -> list mblock -> mem -> 
                  trace -> Prop :=
| dbSubblock_intro : forall S TD Ps lc1 als1 gl fs Mem1 cs call0 lc2 als2 Mem2 
                     tr1 lc3 Mem3 tr2,
  dbCmds TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr1 ->
  dbCall S TD Ps fs gl lc2 Mem2 call0 lc3 Mem3 tr2 ->
  dbSubblock S TD Ps fs gl
             lc1 als1 Mem1
             (cs++call0::nil) 
             lc3 als2 Mem3
             (trace_app tr1 tr2)
with dbSubblocks : system -> TargetData -> list product -> GVMap -> GVMap -> 
                   DGVMap -> list mblock -> mem -> 
                   cmds -> 
                   DGVMap -> list mblock -> mem -> 
                   trace -> Prop :=
| dbSubblocks_nil : forall S TD Ps lc als gl fs Mem, 
    dbSubblocks S TD Ps fs gl lc als Mem nil lc als Mem trace_nil
| dbSubblocks_cons : forall S TD Ps lc1 als1 gl fs Mem1 lc2 als2 Mem2 lc3 als3 
                     Mem3 cs cs' t1 t2,
    dbSubblock S TD Ps fs gl lc1 als1 Mem1 cs lc2 als2 Mem2 t1 ->
    dbSubblocks S TD Ps fs gl lc2 als2 Mem2 cs' lc3 als3 Mem3 t2 ->
    dbSubblocks S TD Ps fs gl lc1 als1 Mem1 (cs++cs') lc3 als3 Mem3 
      (trace_app t1 t2)
with dbBlock : system -> TargetData -> list product -> GVMap -> GVMap -> fdef ->
               State -> State -> trace -> Prop :=
| dbBlock_intro : forall S TD Ps F tr1 tr2 l ps cs cs' tmn gl fs lc1 als1 Mem1
                         lc2 als2 Mem2 lc3 als3 Mem3 lc4 B' tr3,
  dbSubblocks S TD Ps fs gl
    lc1 als1 Mem1
    cs
    lc2 als2 Mem2
    tr1 ->
  dbCmds TD gl lc2 als2 Mem2 cs' lc3 als3 Mem3 tr2 ->
  dbTerminator TD Mem3 F gl
    (block_intro l ps (cs++cs') tmn) lc3
    tmn
    B' lc4
    tr3 ->
  dbBlock S TD Ps fs gl F
    (mkState (mkEC (block_intro l ps (cs++cs') tmn) lc1 als1) Mem1)
    (mkState (mkEC B' lc4 als3) Mem3)
    (trace_app (trace_app tr1 tr2) tr3)
with dbBlocks : system -> TargetData -> list product -> GVMap -> GVMap -> fdef ->
                State -> State -> trace -> Prop :=
| dbBlocks_nil : forall S TD Ps gl fs F state, 
    dbBlocks S TD Ps fs gl F state state trace_nil
| dbBlocks_cons : forall S TD Ps gl fs F S1 S2 S3 t1 t2,
    dbBlock S TD Ps fs gl F S1 S2 t1 ->
    dbBlocks S TD Ps fs gl F S2 S3 t2 ->
    dbBlocks S TD Ps fs gl F S1 S3 (trace_app t1 t2)
with dbFdef : value -> typ -> params -> system -> TargetData -> list product -> 
              DGVMap -> GVMap -> GVMap -> mem -> DGVMap -> list mblock -> mem -> 
              block -> id -> option value -> trace -> Prop :=
| dbFdef_func : forall S TD Ps gl fs fv fid lp lc rid fptr
                    l1 ps1 cs1 tmn1 fa rt la va lb Result lc1 tr1 Mem Mem1 als1
                    l2 ps2 cs21 cs22 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3 gvs lc0,
  @getOperandValue DGVs TD fv lc gl = Some fptr -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l1 ps1 cs1 tmn1) ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) lc0 nil) Mem)
    (mkState (mkEC (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result))
      lc1 als1) Mem1)
    tr1 ->
  dbSubblocks S TD Ps fs gl
    lc1 als1 Mem1
    cs21
    lc2 als2 Mem2
    tr2 ->
  dbCmds TD gl
    lc2 als2 Mem2
    cs22
    lc3 als3 Mem3
    tr3 ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc3 als3 Mem3 
    (block_intro l2 ps2 (cs21++cs22) (insn_return rid rt Result)) rid 
    (Some Result) (trace_app (trace_app tr1 tr2) tr3)
| dbFdef_proc : forall S TD Ps gl fs fv fid lp lc rid fptr
                    l1 ps1 cs1 tmn1 fa rt la va lb lc1 tr1 Mem Mem1 als1
                    l2 ps2 cs21 cs22 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3 gvs lc0,
  @getOperandValue DGVs TD fv lc gl = Some fptr -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l1 ps1 cs1 tmn1) ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    (mkState (mkEC (block_intro l1 ps1 cs1 tmn1) lc0 nil) Mem)
    (mkState (mkEC (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) lc1 
      als1) Mem1)
    tr1 ->
  dbSubblocks S TD Ps fs gl
    lc1 als1 Mem1
    cs21
    lc2 als2 Mem2
    tr2 ->
  dbCmds TD gl
    lc2 als2 Mem2
    cs22
    lc3 als3 Mem3
    tr3 ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc3 als3 Mem3 
    (block_intro l2 ps2 (cs21++cs22) (insn_return_void rid)) rid None 
    (trace_app (trace_app tr1 tr2) tr3)
.

Scheme dbCall_ind2 := Induction for dbCall Sort Prop
  with dbSubblock_ind2 := Induction for dbSubblock Sort Prop
  with dbSubblocks_ind2 := Induction for dbSubblocks Sort Prop
  with dbBlock_ind2 := Induction for dbBlock Sort Prop
  with dbBlocks_ind2 := Induction for dbBlocks Sort Prop
  with dbFdef_ind2 := Induction for dbFdef Sort Prop.

Combined Scheme db_mutind from dbCall_ind2, dbSubblock_ind2, dbSubblocks_ind2,
                               dbBlock_ind2, dbBlocks_ind2, dbFdef_ind2.

Hint Constructors dbCmd dbCmds dbTerminator dbCall 
                  dbSubblock dbSubblocks dbBlock dbBlocks dbFdef.

(***************************************************************)
(** LLVM.syntax -> Symexe.syntax *)

Record nbranch := mkNB
{ nbranching_cmd:cmd;
  notcall:isCall nbranching_cmd = false
}.

Record subblock := mkSB
{
  NBs : list nbranch;
  call_cmd : cmd;
  call_cmd_isCall : isCall call_cmd = true
}.

Lemma isCall_dec : forall c, 
  {isCall c = false} + {isCall c = true}.
Proof.
  destruct c; simpl; auto.
Qed.

Fixpoint cmds2sbs (cs:cmds) : (list subblock*list nbranch) :=
match cs with
| nil => (nil,nil)
| c::cs' =>
  match (isCall_dec c) with
  | left isnotcall => 
    match (cmds2sbs cs') with
    | (nil, nbs0) => (nil, mkNB c isnotcall::nbs0) 
    | (mkSB nbs call0 iscall0::sbs', nbs0) => 
      (mkSB (mkNB c isnotcall::nbs) call0 iscall0::sbs', nbs0) 
    end
  | right iscall => 
    match (cmds2sbs cs') with
    | (sbs, nbs0) => (mkSB nil c iscall::sbs, nbs0) 
    end
  end
end.

Fixpoint nbranchs2cmds (nbs:list nbranch) : list cmd :=
match nbs with
| nil => nil
| (mkNB c nc)::nbs' =>c::nbranchs2cmds nbs'
end.

Definition cmd2nbranch (c:cmd) : option nbranch :=
match (isCall_dec c) with 
| left H => Some (mkNB c H)
| right _ => None
end.

Lemma dbCmd_isNotCallInst : forall TD lc als gl Mem1 c lc' als' Mem2 tr,
  dbCmd TD gl lc als Mem1 c lc' als' Mem2 tr ->
  isCall c = false.
Proof.
  intros TD lc als gl Mem1 c lc' als' Mem2 tr HdbCmd.
  induction HdbCmd; auto.
Qed.

Definition dbCmd2nbranch : forall TD lc als gl Mem1 c lc' als' Mem2 tr, 
  dbCmd TD gl lc als Mem1 c lc' als' Mem2 tr ->
  exists nb, cmd2nbranch c = Some nb.
Proof.
  intros.
  apply dbCmd_isNotCallInst in H.
  unfold cmd2nbranch.
  destruct (isCall_dec).
    exists (mkNB c e). auto.
    rewrite H in e. inversion e.
Qed.

(* This may not work sometimes. This function creates a proof
   that a cmd is not a call, which can only be proved to eual to
   the same proof in the context by proof-irrevelance axiom. *)
Fixpoint cmds2nbranchs (cs:list cmd) : option (list nbranch) :=
match cs with
| nil => Some nil
| c::cs' =>
  match (cmd2nbranch c, cmds2nbranchs cs') with
  | (Some nb, Some nbs') => Some (nb::nbs')
  | _ => None
  end
end.

Definition dbCmds2nbranchs : forall cs TD lc als gl Mem1 lc' als' Mem2 tr, 
  dbCmds TD gl lc als Mem1 cs lc' als' Mem2 tr ->
  exists nbs, cmds2nbranchs cs = Some nbs.
Proof.
  induction cs; intros.
    exists nil. simpl. auto.

    inversion H; subst.
    apply dbCmd2nbranch in H7.
    apply IHcs in H12.
    destruct H7 as [nb J1].
    destruct H12 as [nbs J2].
    exists (nb::nbs).
    simpl. 
    rewrite J1.
    rewrite J2.
    auto.
Qed.

Inductive wf_nbranchs : list nbranch -> Prop :=
| wf_nbranchs_intro : forall cs nbs, 
  cmds2sbs cs = (nil, nbs) ->
  NoDup (getCmdsLocs cs) ->
  wf_nbranchs nbs.

Inductive wf_subblock : subblock -> Prop :=
| wf_subblock_intro : forall nbs call0 iscall0, 
  wf_nbranchs nbs ->
  wf_subblock (mkSB nbs call0 iscall0).

Inductive wf_subblocks : list subblock -> Prop :=
| wf_subblocks_nil : wf_subblocks nil
| wf_subblocks_cons : forall sb sbs,
  wf_subblock sb ->
  wf_subblocks sbs ->
  wf_subblocks (sb::sbs).

Inductive wf_block : block -> Prop :=
| wf_block_intro : forall l ps cs sbs nbs tmn, 
  cmds2sbs cs = (sbs,nbs) ->
  wf_subblocks sbs ->
  wf_nbranchs nbs ->
  wf_block (block_intro l ps cs tmn).

Hint Constructors wf_subblocks.

(***************************************************************)
(** symbolic terms and memories. *)

Inductive sterm : Set := 
| sterm_val : value -> sterm
| sterm_bop : bop -> sz -> sterm -> sterm -> sterm
| sterm_fbop : fbop -> floating_point -> sterm -> sterm -> sterm
| sterm_extractvalue : typ -> sterm -> list_const -> sterm
| sterm_insertvalue : typ -> sterm -> typ -> sterm -> list_const -> sterm
| sterm_malloc : smem -> typ -> sterm -> align -> sterm
| sterm_alloca : smem -> typ -> sterm -> align -> sterm
| sterm_load : smem -> typ -> sterm -> align -> sterm
| sterm_gep : inbounds -> typ -> sterm -> list_sterm -> sterm
| sterm_trunc : truncop -> typ -> sterm -> typ -> sterm
| sterm_ext : extop -> typ -> sterm -> typ -> sterm
| sterm_cast : castop -> typ -> sterm -> typ -> sterm
| sterm_icmp : cond -> typ -> sterm -> sterm -> sterm
| sterm_fcmp : fcond -> floating_point -> sterm -> sterm -> sterm
| sterm_phi : typ -> list_sterm_l -> sterm
| sterm_select : sterm -> typ -> sterm -> sterm -> sterm
with list_sterm : Set :=
| Nil_list_sterm : list_sterm
| Cons_list_sterm : sz -> sterm -> list_sterm -> list_sterm
with list_sterm_l : Set :=
| Nil_list_sterm_l : list_sterm_l
| Cons_list_sterm_l : sterm -> l -> list_sterm_l -> list_sterm_l
with smem : Set :=
| smem_init : smem
| smem_malloc : smem -> typ -> sterm -> align -> smem
| smem_free : smem -> typ -> sterm -> smem
| smem_alloca : smem -> typ -> sterm -> align -> smem
| smem_load : smem -> typ -> sterm -> align -> smem
| smem_store : smem -> typ -> sterm -> sterm -> align -> smem
with sframe : Set :=
| sframe_init : sframe
| sframe_alloca : smem -> sframe -> typ -> sterm -> align -> sframe
.

Scheme sterm_rec2 := Induction for sterm Sort Set
  with list_sterm_rec2 := Induction for list_sterm Sort Set
  with list_sterm_l_rec2 := Induction for list_sterm_l Sort Set
  with smem_rec2 := Induction for smem Sort Set
  with sframe_rec2 := Induction for sframe Sort Set.

Definition se_mutrec P1 P2 P3 P4 P5:=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 =>
   (pair
      (pair 
           (pair 
                 (pair (@sterm_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)
                       (@list_sterm_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28))
                 (@list_sterm_l_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28))
            (@smem_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28))
      (@sframe_rec2 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)).

Fixpoint map_list_sterm (A:Set) (f:sz->sterm->A) (l0:list_sterm) {struct l0} 
  : list A :=
  match l0 with
  | Nil_list_sterm => nil
  | Cons_list_sterm s h tl_ => cons (f s h) (map_list_sterm A f tl_)
  end.
Implicit Arguments map_list_sterm.

Fixpoint make_list_sterm (l0:list (sz * sterm)) : list_sterm :=
  match l0 with
  | nil  => Nil_list_sterm
  | cons (s, h) tl_ => Cons_list_sterm s h (make_list_sterm tl_)
  end.

Fixpoint unmake_list_sterm (l0:list_sterm) :  list (sz * sterm) :=
  match l0 with
  | Nil_list_sterm => nil
  | Cons_list_sterm s h tl_ =>  cons (s, h) (unmake_list_sterm tl_)
  end.

Fixpoint nth_list_sterm (n:nat) (l0:list_sterm) {struct n} : option (sz * sterm) :=
  match n,l0 with
  | O, Cons_list_sterm s h tl_ => Some (s, h)
  | O, other => None
  | S m, Nil_list_sterm => None
  | S m, Cons_list_sterm _ _ tl_ => nth_list_sterm m tl_
  end.
Implicit Arguments nth_list_sterm.

Fixpoint app_list_sterm (l0 m:list_sterm) {struct l0} : list_sterm :=
  match l0 with
  | Nil_list_sterm => m
  | Cons_list_sterm s h tl_ => Cons_list_sterm s h (app_list_sterm tl_ m)
  end.

Fixpoint map_list_sterm_l (A:Set) (f:sterm->l->A) (l0:list_sterm_l) {struct l0} 
  : list A :=
  match l0 with
  | Nil_list_sterm_l => nil
  | Cons_list_sterm_l h0 h1 tl_ => cons (f h0 h1) (map_list_sterm_l A f tl_)
  end.
Implicit Arguments map_list_sterm_l.

Fixpoint make_list_sterm_l (l0:list (sterm*l)) : list_sterm_l :=
  match l0 with
  | nil  => Nil_list_sterm_l
  | cons (h0,h1) tl_ => Cons_list_sterm_l h0 h1 (make_list_sterm_l tl_)
  end.

Fixpoint unmake_list_sterm_l (l0:list_sterm_l) :  list (sterm*l) :=
  match l0 with
  | Nil_list_sterm_l => nil
  | Cons_list_sterm_l h0 h1 tl_ =>  cons (h0,h1) (unmake_list_sterm_l tl_)
  end.

Fixpoint nth_list_sterm_l (n:nat) (l0:list_sterm_l) {struct n} : option (sterm*l)
  :=
  match n,l0 with
  | O, Cons_list_sterm_l h0 h1 tl_ => Some (h0,h1)
  | O, other => None
  | S m, Nil_list_sterm_l => None
  | S m, Cons_list_sterm_l h0 h1 tl_ => nth_list_sterm_l m tl_
  end.
Implicit Arguments nth_list_sterm_l.

Fixpoint app_list_sterm_l (l0 m:list_sterm_l) {struct l0} : list_sterm_l :=
  match l0 with
  | Nil_list_sterm_l => m
  | Cons_list_sterm_l h0 h1 tl_ => 
      Cons_list_sterm_l h0 h1 (app_list_sterm_l tl_ m)
  end.

Inductive sterminator : Set :=
| stmn_return : id -> typ -> sterm -> sterminator
| stmn_return_void : id -> sterminator
| stmn_br : id -> sterm -> l -> l -> sterminator
| stmn_br_uncond : id -> l -> sterminator
| stmn_unreachable : id -> sterminator
.

Definition smap := list (atom*sterm).

Record sstate : Set := mkSstate 
{
  STerms : smap;
  SMem : smem;
  SFrame : sframe;
  SEffects : list sterm
}.

Definition sstate_init := mkSstate nil smem_init sframe_init nil.

Fixpoint lookupSmap (sm:smap) (i0:id) : sterm :=
match sm with
| nil => (sterm_val (value_id i0))
| (id0, s0)::sm' => 
  if i0 == id0 then s0 else lookupSmap sm' i0
end.

Definition value2Sterm (sm:smap) (v:value) : sterm :=
match v with
| value_const _ => sterm_val v
| value_id i0 => lookupSmap sm i0
end.

Fixpoint list_param__list_typ_subst_sterm (list_param1:params) (sm:smap) 
  : list (typ*attributes*sterm) :=
match list_param1 with
| nil => nil
| ((t, attr), v)::list_param1' => 
    ((t, attr), (value2Sterm sm v))::
      (list_param__list_typ_subst_sterm list_param1' sm)
end.

Definition se_call : forall i id0 noret0 tailc0 ft fv lp,
  i=insn_call id0 noret0 tailc0 ft fv lp ->
  isCall i = false ->
  sstate.
Proof.
  intros; subst. simpl in H0.
  destruct fv; inversion H0.
Defined.

Definition se_cmd (st : sstate) (c:nbranch) : sstate :=
match c with 
| mkNB i notcall =>
  (match i as r return (i = r -> _) with 
  | insn_bop id0 op0 sz0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_bop op0 sz0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_fbop id0 op0 fp0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_fbop op0 fp0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
 | insn_extractvalue id0 t1 v1 cs3 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_extractvalue t1 
                     (value2Sterm st.(STerms) v1)
                     cs3))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_insertvalue id0 t1 v1 t2 v2 cs3 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_insertvalue 
                     t1 
                     (value2Sterm st.(STerms) v1)
                     t2 
                     (value2Sterm st.(STerms) v2)
                     cs3))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_malloc id0 t1 v1 al1 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_malloc st.(SMem) t1 (value2Sterm st.(STerms) v1) al1))
                 (smem_malloc st.(SMem) t1 (value2Sterm st.(STerms) v1) al1)
                 st.(SFrame)
                 st.(SEffects))
  | insn_free id0 t0 v0 => fun _ =>  
       (mkSstate st.(STerms)
                 (smem_free st.(SMem) t0 
                   (value2Sterm st.(STerms) v0))
                 st.(SFrame)
                 st.(SEffects))
  | insn_alloca id0 t1 v1 al1 => fun _ =>   
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_alloca st.(SMem) t1 (value2Sterm st.(STerms) v1) al1))
                 (smem_alloca st.(SMem) t1 (value2Sterm st.(STerms) v1) al1)
                 (sframe_alloca st.(SMem) st.(SFrame) t1 
                 (value2Sterm st.(STerms) v1) al1)
                 st.(SEffects))
  | insn_load id0 t2 v2 align => fun _ =>   
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_load st.(SMem) t2 
                     (value2Sterm st.(STerms) v2) align))
                 (smem_load st.(SMem) t2 
                   (value2Sterm st.(STerms) v2) align)
                 st.(SFrame)
                 st.(SEffects))
  | insn_store id0 t0 v1 v2 align => fun _ =>  
       (mkSstate st.(STerms)
                 (smem_store st.(SMem) t0 
                   (value2Sterm st.(STerms) v1)
                   (value2Sterm st.(STerms) v2)
                   align)
                 st.(SFrame)
                 st.(SEffects))
  | insn_gep id0 inbounds0 t1 v1 lv2 => fun _ =>  
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_gep inbounds0 t1 
                     (value2Sterm st.(STerms) v1)
                     (make_list_sterm (map_list_sz_value 
                       (fun sz' v' => (sz', value2Sterm st.(STerms) v')) lv2))))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_trunc id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_trunc op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_ext id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_ext op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_cast id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_cast op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_icmp id0 c0 t0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_icmp c0 t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_fcmp id0 c0 fp0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_fcmp c0 fp0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_select id0 v0 t0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_select 
                     (value2Sterm st.(STerms) v0)
                     t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_call id0 noret0 tailc0 ft fv lp =>
    fun (EQ:i=insn_call id0 noret0 tailc0 ft fv lp ) =>
    se_call i id0 noret0 tailc0 ft fv lp EQ notcall
  end) (@refl_equal _ i)
end.

Fixpoint _se_phinodes (st st0: sstate) (ps:list phinode) : sstate :=
match ps with
| nil => st
| insn_phi id0 t0 idls0::ps' =>  
    _se_phinodes 
     (mkSstate (updateAL _ st.(STerms) id0 
                 (sterm_phi 
                   t0 
                   (make_list_sterm_l
                     (map_list_value_l
                       (fun v5 l5 =>
                        ((value2Sterm st.(STerms) v5), l5)
                       )
                       idls0
                     )
                   )
                 )
               )
               st.(SMem)
               st.(SFrame)
               st.(SEffects))
     st0
     ps'
end.

Fixpoint se_phinodes (st: sstate) (ps:list phinode) := _se_phinodes st st ps.

Fixpoint se_cmds (st : sstate) (cs:list nbranch) : sstate :=
match cs with
| nil => st
| c::cs' => se_cmds (se_cmd st c) cs'
end.

Definition se_terminator (st : sstate) (i:terminator) : sterminator :=
match i with 
| insn_return id0 t0 v0 => stmn_return id0 t0 (value2Sterm st.(STerms) v0)
| insn_return_void id0 => stmn_return_void id0 
| insn_br id0 v0 l1 l2 => stmn_br id0 (value2Sterm st.(STerms) v0) l1 l2
| insn_br_uncond id0 l0 => stmn_br_uncond id0 l0
| insn_unreachable id0 => stmn_unreachable id0 
end.

(***************************************************************)
(* Denotational semantics of symbolic exe *)

Inductive sterm_denotes_genericvalue : 
   TargetData ->            (* CurTatgetData *)
   DGVMap ->                (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   sterm ->                 (* symbolic term *)
   GenericValue ->          (* value that denotes sterm *)
   Prop :=
| sterm_val_denotes : forall TD lc gl Mem v gv,
  getOperandValue TD v lc gl = Some gv ->  
  sterm_denotes_genericvalue TD lc gl Mem (sterm_val v) gv
| sterm_bop_denotes : forall TD lc gl Mem op0 sz0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  mbop TD op0 sz0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_bop op0 sz0 st1 st2) gv3
| sterm_fbop_denotes : forall TD lc gl Mem op0 fp0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  mfbop TD op0 fp0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_fbop op0 fp0 st1 st2) gv3
| sterm_extractvalue_denotes : forall TD lc gl Mem t1 st1 idxs0 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  @extractGenericValue DGVs TD t1 gv1 idxs0 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_extractvalue t1 st1 idxs0) gv2
| sterm_insertvalue_denotes: forall TD lc gl Mem t1 st1 t2 st2 idxs0 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  @insertGenericValue DGVs TD t1 gv1 idxs0 t2 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_insertvalue t1 st1 t2 st2 idxs0) gv3
| sterm_malloc_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st0 gv0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  malloc TD Mem1 tsz0 gv0 align0 = Some (Mem2, mb) ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_malloc sm0 t0 st0 align0) (blk2GV TD mb)
| sterm_alloca_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st0 gv0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  malloc TD Mem1 tsz0 gv0 align0 = Some (Mem2, mb) ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_alloca sm0 t0 st0 align0) (blk2GV TD mb)
| sterm_load_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 align0 st0 gv0 gv1,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  mload TD Mem1 gv0 t0 align0 = Some gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 (sterm_load sm0 t0 st0 align0) gv1
| sterm_gep_denotes : forall TD lc gl Mem ib0 t0 st0 sts0 gv0 gvs0 gv1,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  sterms_denote_genericvalues TD lc gl Mem sts0 gvs0 ->
  @GEP DGVs TD t0 gv0 gvs0 ib0 = Some gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_gep ib0 t0 st0 sts0) gv1
| sterm_trunc_denotes : forall TD lc gl Mem op0 t1 st1 t2 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  mtrunc TD op0 t1 t2 gv1 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_trunc op0 t1 st1 t2) gv2
| sterm_ext_denotes : forall TD lc gl Mem op0 t1 st1 t2 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  mext TD op0 t1 t2 gv1 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_ext op0 t1 st1 t2) gv2
| sterm_cast_denotes : forall TD lc gl Mem op0 t1 st1 t2 gv1 gv2,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  mcast TD op0 t1 t2 gv1 = Some gv2 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_cast op0 t1 st1 t2) gv2
| sterm_icmp_denotes : forall TD lc gl Mem cond0 t0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  micmp TD cond0 t0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_icmp cond0 t0 st1 st2) gv3
| sterm_fcmp_denotes : forall TD lc gl Mem cond0 fp0 st1 st2 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  mfcmp TD cond0 fp0 gv1 gv2 = Some gv3 ->
  sterm_denotes_genericvalue TD lc gl Mem (sterm_fcmp cond0 fp0 st1 st2) gv3
| sterm_select_denotes : forall TD lc gl Mem st0 t0 st1 st2 gv0 gv1 gv2 gv3,
  sterm_denotes_genericvalue TD lc gl Mem st0 gv0 ->
  sterm_denotes_genericvalue TD lc gl Mem st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem st2 gv2 ->
  (if isGVZero TD gv0 then gv2 else gv1) = gv3 -> 
  sterm_denotes_genericvalue TD lc gl Mem (sterm_select st0 t0 st1 st2) gv3
with sterms_denote_genericvalues : 
   TargetData ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   list_sterm ->            (* symbolic terms *)
   list GenericValue ->     (* values that denote sterms *)
   Prop :=
| sterms_nil_denote : forall TD lc gl Mem,
  sterms_denote_genericvalues TD lc gl Mem Nil_list_sterm nil
| sterms_cons_denote : forall TD lc gl Mem sts sz0 st gvs gv,
  sterms_denote_genericvalues TD lc gl Mem sts gvs ->
  sterm_denotes_genericvalue TD lc gl Mem st gv ->
  sterms_denote_genericvalues TD lc gl Mem (Cons_list_sterm sz0 st sts)(gv::gvs)
with smem_denotes_mem : 
   TargetData ->               (* CurTatgetData *)
   GVMap ->                 (* local registers *)
   GVMap ->                 (* global variables *)
   mem ->                   (* Memory *)
   smem ->                  (* symbolic mem *)
   mem ->                   (* value that denotes smem *)
   Prop :=
| smem_init_denotes : forall TD lc gl Mem,
  smem_denotes_mem TD lc gl Mem smem_init Mem
| smem_malloc_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st0 gv0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  malloc TD Mem1 tsz0 gv0 align0 = Some (Mem2, mb) ->
  smem_denotes_mem TD lc gl Mem0 (smem_malloc sm0 t0 st0 align0) Mem2
| smem_free_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st0 gv0 Mem2,
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  free TD Mem1 gv0 = Some Mem2->
  smem_denotes_mem TD lc gl Mem0 (smem_free sm0 t0 st0) Mem2
| smem_alloca_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st0 gv0 align0 tsz0 Mem2 mb,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  malloc TD Mem1 tsz0 gv0 align0 = Some (Mem2, mb) ->
  smem_denotes_mem TD lc gl Mem0 (smem_alloca sm0 t0 st0 align0) Mem2
| smem_load_denotes : forall TD lc gl Mem0 sm0 t0 st0 align0 Mem1,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  smem_denotes_mem TD lc gl Mem0 (smem_load sm0 t0 st0 align0) Mem1
| smem_store_denotes : forall TD lc gl Mem0 Mem1 sm0 t0 st1 st2 align0 gv1 gv2  Mem2,
  sterm_denotes_genericvalue TD lc gl Mem0 st1 gv1 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st2 gv2 ->
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  mstore TD Mem1 gv2 t0 gv1 align0 = Some Mem2 ->
  smem_denotes_mem TD lc gl Mem0 (smem_store sm0 t0 st1 st2 align0) Mem2
.

Inductive sframe_denotes_frame : 
   TargetData ->            (* CurTatgetData *)
   DGVMap ->                (* local registers *)
   GVMap ->                 (* global variables *)
   list mblock ->           (* Track memory allocated by alloca *)
   mem ->                   (* mem *)
   sframe ->                (* symbolic frame *)
   list mblock ->           (* allocas that denotes sframe *)
   Prop :=
| sframe_init_denotes : forall TD lc gl Mem als,
  sframe_denotes_frame TD lc gl als Mem sframe_init als
| sframe_alloca_denotes : forall TD lc gl Mem0 Mem1 als0 als1 t0 st0 gv0 align0 tsz0 Mem2 mb sm0 sf0,
  smem_denotes_mem TD lc gl Mem0 sm0 Mem1 ->
  sframe_denotes_frame TD lc gl als0 Mem0 sf0 als1 ->
  getTypeAllocSize TD t0 = Some tsz0 ->
  sterm_denotes_genericvalue TD lc gl Mem0 st0 gv0 ->
  malloc TD Mem1 tsz0 gv0 align0 = Some (Mem2, mb) ->
  sframe_denotes_frame TD lc gl als0 Mem0 (sframe_alloca sm0 sf0 t0 st0 align0) (mb::als1)
.

Inductive seffects_denote_trace : 
   list sterm ->            (* symbolic effects *)
   trace ->                 (* trace that denotes seffects *)
   Prop :=
| seffects_nil_denote : 
  seffects_denote_trace nil trace_nil
.

Hint Constructors sterm_denotes_genericvalue sterms_denote_genericvalues 
                  smem_denotes_mem sframe_denotes_frame seffects_denote_trace.

Scheme sterm_denotes_genericvalue_ind2 := Induction for sterm_denotes_genericvalue Sort Prop
  with sterms_denote_genericvalues_ind2 := Induction for sterms_denote_genericvalues Sort Prop
  with smem_denotes_mem_ind2 := Induction for smem_denotes_mem Sort Prop.

Combined Scheme sd_mutind from sterm_denotes_genericvalue_ind2, 
                               sterms_denote_genericvalues_ind2, 
                               smem_denotes_mem_ind2.

Definition smap_denotes_gvmap TD lc gl Mem smap' lc' :=
(forall id',  
  id' `in` dom smap' `union` dom lc ->
  exists gv',
    sterm_denotes_genericvalue TD lc gl Mem (lookupSmap smap' id') gv' /\
    lookupAL _ lc' id' = Some gv') /\
(forall id' gv',  
  lookupAL _ lc' id' = Some gv' ->
  sterm_denotes_genericvalue TD lc gl Mem (lookupSmap smap' id') gv'
).

Definition sstate_denotes_state TD lc gl als Mem sstate' lc' als' mem' tr :=
smap_denotes_gvmap TD lc gl Mem sstate'.(STerms) lc' /\
smem_denotes_mem TD lc gl Mem sstate'.(SMem) mem' /\
sframe_denotes_frame TD lc gl als Mem sstate'.(SFrame) als' /\
seffects_denote_trace sstate'.(SEffects) tr.

(* Definions below have not been used yet. *)

Fixpoint subst_tt (id0:id) (s0:sterm) (s:sterm) : sterm :=
match s with
| sterm_val (value_id id1) => if id0 == id1 then s0 else s
| sterm_val (value_const c) => sterm_val (value_const c)
| sterm_bop op sz s1 s2 => 
    sterm_bop op sz (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_fbop op fp s1 s2 => 
    sterm_fbop op fp (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_extractvalue t1 s1 cs => 
    sterm_extractvalue t1 (subst_tt id0 s0 s1) cs
| sterm_insertvalue t1 s1 t2 s2 cs => 
    sterm_insertvalue t1 (subst_tt id0 s0 s1) t2 (subst_tt id0 s0 s2) cs
| sterm_malloc m1 t1 s1 align => 
    sterm_malloc (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align
| sterm_alloca m1 t1 s1 align => 
    sterm_alloca (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align
| sterm_load m1 t1 s1 align => 
    sterm_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align
| sterm_gep inbounds t1 s1 ls2 =>
    sterm_gep inbounds t1 (subst_tt id0 s0 s1) (subst_tlt id0 s0 ls2)
| sterm_trunc truncop t1 s1 t2 => 
    sterm_trunc truncop t1 (subst_tt id0 s0 s1) t2
| sterm_ext extop t1 s1 t2 => 
    sterm_ext extop t1 (subst_tt id0 s0 s1) t2
| sterm_cast castop t1 s1 t2 => 
    sterm_cast castop t1 (subst_tt id0 s0 s1) t2
| sterm_icmp cond t1 s1 s2 => 
    sterm_icmp cond t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_fcmp cond fp1 s1 s2 => 
    sterm_fcmp cond fp1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_phi t1 lsl1 => 
    sterm_phi t1 (subst_tltl id0 s0 lsl1)
| sterm_select s1 t1 s2 s3 => 
    sterm_select (subst_tt id0 s0 s1) t1 (subst_tt id0 s0 s2) (subst_tt id0 s0 s3)
end
with subst_tlt (id0:id) (s0:sterm) (ls:list_sterm) : list_sterm :=
match ls with
| Nil_list_sterm => Nil_list_sterm
| Cons_list_sterm sz0 s ls' => 
    Cons_list_sterm sz0 (subst_tt id0 s0 s) (subst_tlt id0 s0 ls')
end
with subst_tltl (id0:id) (s0:sterm) (ls:list_sterm_l) : list_sterm_l :=
match ls with
| Nil_list_sterm_l => Nil_list_sterm_l
| Cons_list_sterm_l s l0 ls' =>
     Cons_list_sterm_l (subst_tt id0 s0 s) l0 (subst_tltl id0 s0 ls')
end
with subst_tm (id0:id) (s0:sterm) (m:smem) : smem :=
match m with 
| smem_init => smem_init
| smem_malloc m1 t1 sz align => smem_malloc (subst_tm id0 s0 m1) t1 sz align
| smem_free m1 t1 s1 => smem_free (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_alloca m1 t1 sz align => smem_alloca (subst_tm id0 s0 m1) t1 sz align
| smem_load m1 t1 s1 align => smem_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align 
| smem_store m1 t1 s1 s2 align => 
    smem_store (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2) align
end
.

Fixpoint subst_mt (sm:smap) (s:sterm) : sterm :=
match sm with
| nil => s
| (id0, s0)::sm' => subst_mt sm' (subst_tt id0 s0 s)
end.

Fixpoint subst_mm (sm:smap) (m:smem) : smem :=
match sm with
| nil => m
| (id0, s0)::sm' => subst_mm sm' (subst_tm id0 s0 m)
end.

End SimpleSE.

Tactic Notation "se_db_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCall_internal" | c "dbCall_external" | 
    c "dbSubblock_intro" | c "dbSubblocks_nil" | c "dbSubblocks_cons" | 
    c "dbBlock_intro" | c "dbBlocks_nil" | c "dbBlocks_cons" | 
    c "dbFdef_func" | c "dbFdef_proc" ].

Tactic Notation "se_dbCmd_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBop" | c "dbFBop" | c "dbExtractValue" | c "dbInsertValue" |
    c "dbMalloc" | c "dbFree" |
    c "dbAlloca" | c "dbLoad" | c "dbStore" | c "dbGEP" |
    c "dbTrunc" | c "dbExt" | c "dbCast" | 
    c "dbIcmp" | c "dbFcmp" | c "dbSelect" ].

Tactic Notation "se_dbTerminator_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbBranch" | c "dbBranch_uncond" ].

Tactic Notation "se_dbCmds_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCmds_nil" | c "dbCmds_cons" ].

Tactic Notation "sd_mutind_cases" tactic(first) tactic(c) :=
  first;
[ c "sterm_val_denotes"
| c "sterm_bop_denotes"
| c "sterm_fbop_denotes"
| c "sterm_extractvalue_denotes"
| c "sterm_insertvalue_denotes"
| c "sterm_malloc_denotes"
| c "sterm_alloca_denotes"
| c "sterm_load_denotes"
| c "sterm_gep_denotes"
| c "sterm_trunc_denotes"
| c "sterm_ext_denotes"
| c "sterm_cast_denotes"
| c "sterm_icmp_denotes" 
| c "sterm_fcmp_denotes" 
| c "sterm_select_denotes"
| c "sterms_nil_denote"
| c "sterms_cons_denote"
| c "smem_init_denotes"
| c "smem_malloc_denotes"
| c "smem_free_denotes"
| c "smem_alloca_denotes"
| c "smem_load_denotes"
| c "smem_store_denotes" ].

Tactic Notation "se_mut_cases" tactic(first) tactic(c) :=
  first;
  [ c "sterm_val" | 
    c "sterm_bop" |
    c "sterm_fbop" |
    c "sterm_extractvalue" |
    c "sterm_insertvalue" |
    c "sterm_malloc" |
    c "sterm_alloca" |
    c "sterm_load" |
    c "sterm_gep" |
    c "sterm_trunc" |
    c "sterm_ext" |
    c "sterm_cast" |
    c "sterm_icmp" |
    c "sterm_fcmp" |
    c "sterm_phi" |
    c "sterm_select" |
    c "list_sterm_nil" |
    c "list_sterm_cons" |
    c "list_sterm_l_nil" |
    c "list_sterm_l_cons" |
    c "smem_init" |
    c "smem_malloc" |
    c "smem_free" |
    c "smem_alloca" |
    c "smem_load" |
    c "smem_store" |
    c "sframe_init" |
    c "sframe_alloca" ].

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
