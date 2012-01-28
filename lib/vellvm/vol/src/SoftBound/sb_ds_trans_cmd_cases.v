Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
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
Require Import sb_ds_trans_tactics.

Import SB_ds_pass.
Export SBspec.

Lemma SBpass_is_correct__dsBop : forall (mi : MoreMem.meminj)(mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) (id0 : id) (bop0 : bop) (sz0 : sz) (v1 : value) (v2 : value)
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           OpsemAux.CurSystem := S;
           OpsemAux.CurTargetData := TD;
           OpsemAux.CurProducts := Ps;
           OpsemAux.Globals := gl;
           OpsemAux.FunTable := fs |}
           {|
           SBspec.ECS := {|
                          SBspec.CurFunction := F;
                          SBspec.CurBB := B;
                          SBspec.CurCmds := insn_bop id0 bop0 sz0 v1 v2
                                             :: cs;
                          SBspec.Terminator := tmn;
                          SBspec.Locals := lc;
                          SBspec.Rmap := rm;
                          SBspec.Allocas := als |} :: EC;
           SBspec.Mem := Mem;
           SBspec.Mmap := MM |} Cfg St)
  (gv3 : GenericValue)
  (H : BOP TD lc gl bop0 sz0 v1 v2 = ret gv3),
  exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
           OpsemAux.CurSystem := S;
           OpsemAux.CurTargetData := TD;
           OpsemAux.CurProducts := Ps;
           OpsemAux.Globals := gl;
           OpsemAux.FunTable := fs |}
         {|
         SBspec.ECS := {|
                        SBspec.CurFunction := F;
                        SBspec.CurBB := B;
                        SBspec.CurCmds := cs;
                        SBspec.Terminator := tmn;
                        SBspec.Locals := updateAddAL _ lc id0 gv3;
                        SBspec.Rmap := rm;
                        SBspec.Allocas := als |} :: EC;
         SBspec.Mem := Mem;
         SBspec.Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsFBop : forall (mi : MoreMem.meminj) (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) (id0 : id) fbop0 fp (v1 : value) (v2 : value)
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |}
           {|
           SBspec.ECS := {|
                          SBspec.CurFunction := F;
                          SBspec.CurBB := B;
                          SBspec.CurCmds := insn_fbop id0 fbop0 fp v1 v2
                                             :: cs;
                          SBspec.Terminator := tmn;
                          SBspec.Locals := lc;
                          SBspec.Rmap := rm;
                          SBspec.Allocas := als |} :: EC;
           SBspec.Mem := Mem;
           SBspec.Mmap := MM |} Cfg St)
  (gv3 : GenericValue)
  (H : FBOP TD lc gl fbop0 fp v1 v2 = ret gv3),
  exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |}
         {|
         SBspec.ECS := {|
                        SBspec.CurFunction := F;
                        SBspec.CurBB := B;
                        SBspec.CurCmds := cs;
                        SBspec.Terminator := tmn;
                        SBspec.Locals := updateAddAL _ lc id0 gv3;
                        SBspec.Rmap := rm;
                        SBspec.Allocas := als |} :: EC;
         SBspec.Mem := Mem;
         SBspec.Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsTrunc : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id) (truncop0 : truncop)
  (t1 : typ) (v1 : value) (t2 : typ) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           SBspec.ECS := {|
                  SBspec.CurFunction := F;
                  SBspec.CurBB := B;
                  SBspec.CurCmds := insn_trunc id0 truncop0 t1 v1 t2 :: cs;
                  SBspec.Terminator := tmn;
                  SBspec.Locals := lc;
                  SBspec.Rmap := rm;
                  SBspec.Allocas := als |} :: EC;
           SBspec.Mem := Mem0;
           SBspec.Mmap := MM |} Cfg St)
  (gv2 : GenericValue)
  (H : TRUNC TD lc gl truncop0 t1 v1 t2 = ret gv2),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
         SBspec.ECS := {|
                SBspec.CurFunction := F;
                SBspec.CurBB := B;
                SBspec.CurCmds := cs;
                SBspec.Terminator := tmn;
                SBspec.Locals := updateAddAL _ lc id0 gv2;
                SBspec.Rmap := rm;
                SBspec.Allocas := als |} :: EC;
         SBspec.Mem := Mem0;
         SBspec.Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsExt : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id) extop0
  (t1 : typ) (v1 : value) (t2 : typ) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {| 
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_ext id0 extop0 t1 v1 t2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv2 : GenericValue)
  (H : EXT TD lc gl extop0 t1 v1 t2 = ret gv2),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb  {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc id0 gv2;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsBitcase_nptr : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id)
  (t1 : typ) (v1 : value) (t2 : typ) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_cast id0 castop_bitcast t1 v1 t2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv2 : GenericValue)
  (H : CAST TD lc gl castop_bitcast t1 v1 t2 = ret gv2)
  (H0 : isPointerTypB t1 = false),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc id0 gv2;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsOthercast : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id)
  (t1 : typ) (v1 : value) (t2 : typ) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock)
  (castop0 : castop) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_cast id0 castop0 t1 v1 t2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv2 : GenericValue)
  (H : CAST TD lc gl castop0 t1 v1 t2 = ret gv2)
  (H0 : castop0 <> castop_bitcast /\ castop0 <> castop_inttoptr),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc id0 gv2;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsIcmp : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id) cond0 
  (t : typ) (v1 : value) v2 (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_icmp id0 cond0 t v1 v2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv2 : GenericValue)
  (H : ICMP TD lc gl cond0 t v1 v2 = ret gv2),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc id0 gv2;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsFcmp : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id) fcond0 
  fp (v1 : value) v2 (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_fcmp id0 fcond0 fp v1 v2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv2 : GenericValue)
  (H : FCMP TD lc gl fcond0 fp v1 v2 = ret gv2),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc id0 gv2;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsExtractValue : forall (mi : MoreMem.meminj) 
  (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) (id0 : id) t (v : value) idxs
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           SBspec.ECS := {|
                          SBspec.CurFunction := F;
                          SBspec.CurBB := B;
                          SBspec.CurCmds := insn_extractvalue id0 t v idxs
                                             :: cs;
                          SBspec.Terminator := tmn;
                          SBspec.Locals := lc;
                          SBspec.Rmap := rm;
                          SBspec.Allocas := als |} :: EC;
           SBspec.Mem := Mem;
           SBspec.Mmap := MM |} Cfg St)
  gv gv'
  (H : getOperandValue TD v lc gl = ret gv)
  (H0 : extractGenericValue TD t gv idxs = ret gv'),
  exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         SBspec.ECS := {|
                        SBspec.CurFunction := F;
                        SBspec.CurBB := B;
                        SBspec.CurCmds := cs;
                        SBspec.Terminator := tmn;
                        SBspec.Locals := updateAddAL _ lc id0 gv';
                        SBspec.Rmap := rm;
                        SBspec.Allocas := als |} :: EC;
         SBspec.Mem := Mem;
         SBspec.Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsInsertValue : forall (mi : MoreMem.meminj) 
  (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) (id0 : id) t (v : value) t' v' idxs
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           SBspec.ECS := {|
                          SBspec.CurFunction := F;
                          SBspec.CurBB := B;
                          SBspec.CurCmds := insn_insertvalue id0 t v t' v' idxs
                                             :: cs;
                          SBspec.Terminator := tmn;
                          SBspec.Locals := lc;
                          SBspec.Rmap := rm;
                          SBspec.Allocas := als |} :: EC;
           SBspec.Mem := Mem;
           SBspec.Mmap := MM |} Cfg St)
  gv gv' gv''
  (H : getOperandValue TD v lc gl = ret gv)
  (H0 : getOperandValue TD v' lc gl = ret gv')
  (H1 : insertGenericValue TD t gv idxs t' gv' = ret gv''),
  exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         SBspec.ECS := {|
                        SBspec.CurFunction := F;
                        SBspec.CurBB := B;
                        SBspec.CurCmds := cs;
                        SBspec.Terminator := tmn;
                        SBspec.Locals := updateAddAL _ lc id0 gv'';
                        SBspec.Rmap := rm;
                        SBspec.Allocas := als |} :: EC;
         SBspec.Mem := Mem;
         SBspec.Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.
Qed.

Lemma SBpass_is_correct__dsGEP : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : atom) (inbounds0 : bool)
  (t : typ) (vp : value) (idxs : list_sz_value) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |}
           {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_gep id0 inbounds0 t vp idxs :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (vidxs : list GenericValue) gvp (gvp' : GenericValue)
  (lc' : DGVMap) (rm' : rmetadata) (md : metadata)
  (H : SBspecAux.get_reg_metadata TD gl rm vp = ret md)
  (H0 : getOperandValue TD vp lc gl = ret gvp)
  (H1 : values2GVs TD idxs lc gl = ret vidxs)
  (H2 : GEP TD t gvp vidxs inbounds0 = ret gvp')
  (H3 : prop_reg_metadata lc rm id0 gvp' md = (lc', rm')),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb{|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |}
         {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  apply trans_cmds_inv in Htcmds.
  destruct Htcmds as [ex_ids5 [cs1' [cs2' [Htcmd [Htcmds Heq]]]]]; subst.
  simpl in Htcmd. 
  apply prop_metadata_inv in Htcmd.
  destruct Htcmd as [bv [ev [bid0 [eid0 [Hgetrm [Hlk [Heq1 Heq2]]]]]]]; subst.
  invert_prop_reg_metadata.
  destruct md.
  assert (J:=Hrsim).
  destruct J as [Hrsim1 Hrsim2].
  apply Hrsim2 in H; auto.
  destruct H as [bv2 [ev2 [bgv2 [egv2 [Hgetr [Hget1 [Hget2 [Hinj1 Hinj2]]]]]]]].
  rewrite Hgetrm in Hgetr. inv Hgetr.
  eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H0; eauto.
  destruct H0 as [gv' [H0 Hinj]].
  
  eapply simulation__values2GVs with (mi:=mi)(Mem2:=M2) in H1; eauto.
  destruct H1 as [gvs' [H1 Hinj']].
  eapply simulation__GEP in H2; eauto.
  destruct H2 as [gvp2 [H2 Hinj'']].
  exists (Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
              (updateAddALs _ lc2 ((id0,gvp2)::(bid0,bgv2)::(eid0,egv2)::nil))
             als2):: 
            ECs2) M2).
  exists mi.

  assert (Hfr1 := Hgetrm).
  eapply get_reg_metadata_fresh3 in Hfr1; eauto. destruct Hfr1 as [Hneq1 Hneq2].
  assert (Hfr2 := Hgetrm).
  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eapply getCmdID_in_getFdefLocs; eauto.
  eapply get_reg_metadata_fresh'' with (id0:=id0) in Hfr2; eauto.
  destruct Hfr2 as [Hneq3 Hneq4].

  split.
  SCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.

    next_insn.
      eapply Opsem.sCast; eauto.
        unfold Opsem.CAST, mcast, mbitcast, p8. simpl.
        rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite Hget1. auto.

    next_insn.
      eapply Opsem.sCast; eauto.
        unfold Opsem.CAST, mcast, mbitcast, p8. simpl.
        rewrite <- getOperandValue_eq_fresh_id; auto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
        rewrite Hget2. auto.

    repeat (split; eauto 2 using cmds_at_block_tail_next, 
                                 cmds_at_block_tails_next).
  exists ex_ids. exists rm2.
  exists ex_ids3. exists ex_ids4. exists cs2'. exists cs23.
  split; auto.
  split.
  SCase "rsim".
    Transparent updateAddALs. simpl.
    eapply reg_simulation__updateAddAL_prop; eauto.
  split; auto.
Qed.

Lemma SBpass_is_correct__dsBitcase_ptr : forall 
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id)
  (t1 : typ) (v1 : value) (t2 : typ) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_cast id0 castop_bitcast t1 v1 t2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv2 : GenericValue)
  (H : CAST TD lc gl castop_bitcast t1 v1 t2 = ret gv2)
  (H0 : isPointerTypB t1 = true) md  lc' rm'
  (H1 : SBspecAux.get_reg_metadata TD gl rm v1 = ret md)
  (H2 : prop_reg_metadata lc rm id0 gv2 md = (lc', rm')),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  simpl in Htcmds.
  rewrite H0 in Htcmds.
  remember (prop_metadata ex_ids3 rm2 (insn_cast id0 castop_bitcast t1 v1 t2) 
    v1 id0) as R.
  destruct R as [[ex_ids2 cs2]|]; try solve [inv Htcmds].
  remember (trans_cmds ex_ids2 rm2 cs) as R1.
  destruct R1 as [[ex_ids3' cs3]|]; inv Htcmds.

  symmetry in HeqR.
  apply prop_metadata_inv in HeqR.
  destruct HeqR as [bv [ev [bid0 [eid0 [Hgetrm [Hlk [Heq1 Heq2]]]]]]]; subst.
  invert_prop_reg_metadata.
  destruct md.
  assert (J:=Hrsim).
  destruct J as [Hrsim1 Hrsim2].
  apply Hrsim2 in H1; auto.
  destruct H1 as [bv2 [ev2 [bgv2 [egv2 [Hgetr [Hget1 [Hget2 [Hinj1 Hinj2]]]]]]]].
  rewrite Hgetrm in Hgetr. inv Hgetr.
  eapply simulation__CAST in H; eauto.
  destruct H as [gv3' [Hcast Hinj]].
  exists (Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs3 ++ cs23) tmn2 
              (updateAddALs _ lc2 ((id0,gv3')::(bid0,bgv2)::(eid0,egv2)::nil)) 
            als2)::ECs2) M2).
  exists mi.

  assert (Hfr1 := Hgetrm).
  eapply get_reg_metadata_fresh3 in Hfr1; eauto. destruct Hfr1 as [Hneq1 Hneq2].
  assert (Hfr2 := Hgetrm).
  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eapply getCmdID_in_getFdefLocs; eauto.
  eapply get_reg_metadata_fresh'' with (id0:=id0) in Hfr2; eauto.
  destruct Hfr2 as [Hneq3 Hneq4].

  split.
  SCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.

    next_insn.
      eapply Opsem.sCast; eauto.
        unfold Opsem.CAST, mcast, mbitcast, p8. simpl.
        rewrite <- getOperandValue_eq_fresh_id; auto.
        rewrite Hget1. auto.

    next_insn.
      eapply Opsem.sCast; eauto.
        unfold Opsem.CAST, mcast, mbitcast, p8. simpl.
        rewrite <- getOperandValue_eq_fresh_id; auto.
        rewrite <- getOperandValue_eq_fresh_id; auto.
        rewrite Hget2. auto. 

    repeat (split; eauto 2 using cmds_at_block_tail_next, 
                                 cmds_at_block_tails_next).
  exists ex_ids. exists rm2.
  exists ex_ids3. exists ex_ids4. exists cs3. exists cs23.
  split; auto.
  split.
  SCase "rsim".
    Transparent updateAddALs. simpl.
    eapply reg_simulation__updateAddAL_prop; eauto.
  split; auto.
Qed.

Lemma SBpass_is_correct__dsInttoptr : forall
  (mi : MoreMem.meminj) (mgb : Values.block) (St : Opsem.State) (S : system)
  (TD : TargetData) (Ps : list product) (F : fdef) (B : block) (lc : DGVMap)
  (rm : rmetadata) (gl : GVMap) (fs : GVMap) (id0 : id)
  (t1 : typ) (v1 : value) (t2 : typ) (EC : list ExecutionContext)
  (cs : list cmd) (tmn : terminator) (Mem0 : mem) (MM : mmetadata)
  (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_cast id0 castop_inttoptr t1 v1 t2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (gv2 : GenericValue) (lc' : DGVMap) (rm' : rmetadata)
  (H : CAST TD lc gl castop_inttoptr t1 v1 t2 = ret gv2)
  (H0 : prop_reg_metadata lc rm id0 gv2 null_md = (lc', rm')),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  simpl in Htcmds.
  remember (lookupAL (id * id) rm2 id0) as R.
  destruct R as [[bid0 eid0]|]; try solve [inv Htcmds].
  remember (trans_cmds ex_ids3 rm2 cs) as R1.
  destruct R1 as [[ex_ids3' cs3]|]; inv Htcmds.

  invert_prop_reg_metadata.
  eapply simulation__CAST in H; eauto.
  destruct H as [gv3' [Hcast Hinj]].
  exists (Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs3 ++ cs23) tmn2 
               (updateAddALs _ lc2 ((id0,gv3')::(bid0,null)::(eid0,null)::nil)) 
               als2)::ECs2) M2).
  exists mi.
  split.
  SCase "opsem".
    Opaque updateAddALs. simpl.
    next_insn.
    next_insn.
    next_insn.

    repeat (split; eauto 2 using cmds_at_block_tail_next).
    destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
    exists l2. exists ps2. exists (cs21 ++
                  (insn_cast id0 castop_inttoptr t1 v1 t2
          :: insn_cast bid0 castop_bitcast p8 vnullp8 p8
             :: insn_cast eid0 castop_bitcast p8 vnullp8 p8 :: nil)).
    simpl_env. auto.

  exists ex_ids. exists rm2.
  exists ex_ids3. exists ex_ids4. exists cs3. exists cs23.
  split; auto.
  split.
  SCase "rsim".
    Transparent updateAddALs. simpl.
    eapply reg_simulation__updateAddAL_prop; eauto using gv_inject_null_refl.
      eapply getCmdID_in_getFdefLocs; eauto.
  split; auto.
Qed.

Lemma SBpass_is_correct__dsSelect_nptr : forall (mi : MoreMem.meminj) 
  (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) (id0 : id) t (v0 : value) v1 v2
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem0 : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_select id0 v0 t v1 v2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (c gv1 gv2 : GenericValue)
  (H : getOperandValue TD v0 lc gl = ret c)
  (H0 : getOperandValue TD v1 lc gl = ret gv1)
  (H1 : getOperandValue TD v2 lc gl = ret gv2)
  (H2 : isPointerTypB t = false),
  exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := if isGVZero TD c
                          then updateAddAL _ lc id0 gv2
                          else updateAddAL _ lc id0 gv1;
                Rmap := rm;
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros. SBpass_is_correct__dsOp.

  exists (Opsem.mkState
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2' ++ cs23) tmn2 
            (if isGVZero (los, nts) gv3'1
             then updateAddAL _ lc2 id0 gv3'
             else updateAddAL _ lc2 id0 gv3'0)
            als2):: 
            ECs2) M2).
  exists mi.
  repeat (split; try solve [auto using inject_incr_refl | 
                            eapply cmds_at_block_tail_next; eauto]).
      simpl_env; simpl;
      rewrite <- (@trace_app_nil__eq__trace trace_nil);
      eapply Opsem.sop_star_cons; eauto; eauto.
    
      exists ex_ids; exists rm2;
      exists ex_ids5; exists ex_ids4; exists cs2'; exists cs23;
      split; auto.
      split.
        assert (isGVZero (los, nts) c = isGVZero (los, nts) gv3'1) as Heqc.
          eapply simulation__isGVZero; eauto.
        rewrite Heqc.
        destruct (isGVZero (los,nts) gv3'1);
          apply reg_simulation__updateAddAL_lc with (ex_ids3:=ex_ids); eauto
            using getCmdID_in_getFdefLocs.
      repeat (split; auto).
Qed.

Lemma SBpass_is_correct__dsSelect_ptr : forall (mi : MoreMem.meminj) 
  (mgb : Values.block)
  (St : Opsem.State) (S : system) (TD : TargetData) (Ps : list product)
  (F : fdef) (B : block) (lc : DGVMap) (rm : SBspecAux.rmetadata) (gl : GVMap)
  (fs : GVMap) (id0 : id) t (v0 : value) v1 v2
  (EC : list SBspec.ExecutionContext) (cs : list cmd) (tmn : terminator)
  (Mem0 : mem) (MM : SBspecAux.mmetadata) (als : list mblock) Cfg
  (Hsim : sbState_simulates_State mi mgb {|
           CurSystem := S;
           CurTargetData := TD;
           CurProducts := Ps;
           Globals := gl;
           FunTable := fs |} {|
           ECS := {|
                  CurFunction := F;
                  CurBB := B;
                  CurCmds := insn_select id0 v0 t v1 v2 :: cs;
                  Terminator := tmn;
                  Locals := lc;
                  Rmap := rm;
                  Allocas := als |} :: EC;
           Mem := Mem0;
           Mmap := MM |} Cfg St)
  (c gv1 gv2 : GenericValue) md1 md2 lc' rm'
  (H : getOperandValue TD v0 lc gl = ret c)
  (H0 : getOperandValue TD v1 lc gl = ret gv1)
  (H1 : getOperandValue TD v2 lc gl = ret gv2)
  (H2 : isPointerTypB t = true)
  (H3 : SBspecAux.get_reg_metadata TD gl rm v1 = ret md1)
  (H4 : SBspecAux.get_reg_metadata TD gl rm v2 = ret md2)
  (H5 : (if isGVZero TD c
        then prop_reg_metadata lc rm id0 gv2 md2
        else prop_reg_metadata lc rm id0 gv1 md1) = 
       (lc', rm')),
   exists St' : Opsem.State,
     exists mi' : MoreMem.meminj,
       Opsem.sop_star Cfg St St' trace_nil /\
       sbState_simulates_State mi' mgb {|
         CurSystem := S;
         CurTargetData := TD;
         CurProducts := Ps;
         Globals := gl;
         FunTable := fs |} {|
         ECS := {|
                CurFunction := F;
                CurBB := B;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Rmap := rm';
                Allocas := als |} :: EC;
         Mem := Mem0;
         Mmap := MM |} Cfg St' /\ inject_incr mi mi'.
Proof.
  intros.
  destruct_ctx_other.
  simpl in Htcmds.
  rewrite H2 in Htcmds.
  assert (Hc := H).
  eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in Hc; eauto.
  destruct Hc as [c' [Hc Hinjc]].
  eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H0; eauto.
  destruct H0 as [gv1' [H0 Hinj1]].
  eapply simulation__getOperandValue with (mi:=mi)(Mem2:=M2) in H1; eauto.
  destruct H1 as [gv2' [H1 Hinj2]].

  assert (isGVZero (los, nts) c = isGVZero (los, nts) c') as Heqc.
    eapply simulation__isGVZero; eauto.
  erewrite Heqc in H5.

  remember (SB_ds_pass.get_reg_metadata rm2 v1) as R1.
  destruct R1 as [[bv1 ev1]|]; tinv Htcmds.
  remember (SB_ds_pass.get_reg_metadata rm2 v2) as R2.
  destruct R2 as [[bv2 ev2]|]; tinv Htcmds.
  remember (lookupAL (id * id) rm2 id0) as R3.
  destruct R3 as [[bid0 eid0]|]; tinv Htcmds.
  remember (mk_tmp ex_ids3) as R9.
  destruct R9 as [ctmp ex_ids3'].
  remember (trans_cmds ex_ids3' rm2 cs) as R4.
  destruct R4 as [[ex_ids2 cs2]|]; inv Htcmds.

  assert (Hrsim':=Hrsim).
  destruct Hrsim as [Hrsim1 Hrsim2].
  destruct md1 as [bgv1 egv1]. destruct md2 as [bgv2 egv2].
  eapply Hrsim2 in H3; eauto.
  destruct H3 as [bv1' [ev1' [bgv1' [egv1' [J1 [J2 [J3 [J4 J5]]]]]]]].
  eapply Hrsim2 in H4; eauto.
  destruct H4 as [bv2' [ev2' [bgv2' [egv2' [J1' [J2' [J3' [J4' J5']]]]]]]].
  rewrite <- HeqR1 in J1. inv J1.
  rewrite <- HeqR2 in J1'. inv J1'.

  assert (id_fresh_in_value v0 ctmp /\ id_fresh_in_value v1 ctmp /\ 
          id_fresh_in_value v2 ctmp) as Hfresh_ctmp.
    assert (Hwfc := HBinF).
    destruct Heqb1 as [l1 [ps1 [cs11 Heqb1]]]; subst.
    eapply wf_system__wf_cmd with (c:=insn_select id0 v0 t v1 v2) in Hwfc; eauto.
      inv Hwfc. 
      split. eapply wf_value_id__in_getFdefLocs in H14; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
      split. eapply wf_value_id__in_getFdefLocs in H16; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.
             eapply wf_value_id__in_getFdefLocs in H17; auto.
          eapply get_reg_metadata_fresh' with (rm2:=rm2); eauto; try fsetdec.

      apply in_or_app. right. simpl. auto. 
  destruct Hfresh_ctmp as [Hfresh_ctmp0 [Hfresh_ctmp1 Hfresh_ctmp2]].

  assert (Hspec := Hgenmeta).
  apply gen_metadata_fdef_spec in Hspec; auto.
  destruct Hspec as [Hinc1 [Hdisj1 [Hinc3 Hdisj2]]].

  exists (Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (cs2 ++ cs23) tmn2 
            (if isGVZero (los, nts) c'
             then updateAddAL _
              (if isGVZero (los, nts) c' then
                 updateAddAL _ 
                   (if isGVZero (los, nts) c'
                    then updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv2'
                    else updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv1') 
                   bid0 bgv2'
              else
                 updateAddAL _ 
                   (if isGVZero (los, nts) c'
                    then updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv2'
                    else updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv1') 
                   bid0 bgv1') eid0 egv2'
             else updateAddAL _
              (if isGVZero (los, nts) c' then
                 updateAddAL _ 
                   (if isGVZero (los, nts) c'
                    then updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv2'
                    else updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv1') 
                   bid0 bgv2'
              else
                 updateAddAL _ 
                   (if isGVZero (los, nts) c'
                    then updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv2'
                    else updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv1') 
                   bid0 bgv1') eid0 egv1')
            als2):: 
            ECs2) M2).

  symmetry in HeqR1, HeqR2.
  assert (Hfr1 := HeqR1).
  eapply get_reg_metadata_fresh3 in Hfr1; eauto. destruct Hfr1 as [Hneq1 Hneq2].
  assert (Hfr1' := HeqR2). 
  eapply get_reg_metadata_fresh3 in Hfr1'; eauto. 
  destruct Hfr1' as [Hneq1' Hneq2'].

  assert (In id0 (getFdefLocs (fdef_intro fh1 bs1))) as Hin. 
    eauto using getCmdID_in_getFdefLocs.
  assert (Hfr2 := HeqR1).
  eapply get_reg_metadata_fresh'' with (id0:=id0) in Hfr2; eauto.
  destruct Hfr2 as [Hneq3 Hneq4].
  assert (Hfr2' := HeqR2).
  eapply get_reg_metadata_fresh'' with (id0:=id0) in Hfr2'; eauto.
  destruct Hfr2' as [Hneq3' Hneq4'].

  assert (ctmp <> id0) as Hctmp_neq_id0.
    apply tmp_is_fresh2 with (i0:=id0)(d:=getFdefLocs (fdef_intro fh1 bs1)) 
      (ex_ids1:=ex_ids) in HeqR9; auto.
  assert (bid0 <> ctmp /\ eid0 <> ctmp) as Hctmp'.
    eapply tmp_is_fresh3 with (bid:=bid0)(eid:=eid0)(ex_ids1:=ex_ids) in HeqR9; 
      eauto.
  destruct Hctmp' as [Hctmpb Hctmpe].

  assert (id_fresh_in_value bv1' ctmp /\ id_fresh_in_value ev1' ctmp) as Hfr3.
    eapply get_reg_metadata__fresh; eauto.
  destruct Hfr3 as [Hfr3a Hfr3b]. 
  assert (id_fresh_in_value bv2' ctmp /\ id_fresh_in_value ev2' ctmp) as Hfr4.
    eapply get_reg_metadata__fresh; eauto.
  destruct Hfr4 as [Hfr4a Hfr4b].
 
  exists mi.
  split.
    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply Opsem.sop_star_cons with (state2 := 
        Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (insn_select id0 v0 t v1 v2 ::
             insn_select bid0 (value_id ctmp) p8 bv1' bv2' :: 
             insn_select eid0 (value_id ctmp) p8 ev1' ev2' ::
             cs2 ++ cs23) tmn2 
             (updateAddAL _ lc2 ctmp c')
            als2):: 
            ECs2) M2); auto.
      eapply Opsem.sCast; eauto.
        unfold Opsem.CAST. 
        replace (@getOperandValue DGVs) with LLVMgv.getOperandValue; auto.
        rewrite Hc. simpl. unfold mbitcast, i1. auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply Opsem.sop_star_cons with (state2 := 
        Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (insn_select bid0 (value_id ctmp) p8 bv1' bv2' :: 
             insn_select eid0 (value_id ctmp) p8 ev1' ev2' ::
             cs2 ++ cs23) tmn2 
            (if isGVZero (los, nts) c'
             then updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv2'
             else updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv1')
            als2):: 
            ECs2) M2); auto.
      eapply Opsem.sSelect; eauto;
        rewrite <- getOperandValue_eq_fresh_id; auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    apply Opsem.sop_star_cons with (state2 := 
        Opsem.mkState 
          ((Opsem.mkEC (fdef_intro fh2 bs2) B2
            (insn_select eid0 (value_id ctmp) p8 ev1' ev2' ::
             cs2 ++ cs23) tmn2 
            (if isGVZero (los, nts) c' then
               updateAddAL _ 
                 (if isGVZero (los, nts) c'
                  then updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv2'
                  else updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv1') 
                 bid0 bgv2'
            else
               updateAddAL _ 
                 (if isGVZero (los, nts) c'
                  then updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv2'
                  else updateAddAL _ (updateAddAL _ lc2 ctmp c') id0 gv1') 
                bid0 bgv1')
            als2):: 
            ECs2) M2); auto.
      eapply Opsem.sSelect; eauto.
        destruct (isGVZero (los, nts) c');
          rewrite <- getOperandValue_eq_fresh_id; simpl;
            try solve [auto | rewrite lookupAL_updateAddAL_eq; auto].
        destruct (isGVZero (los, nts) c');
          rewrite <- getOperandValue_eq_fresh_id; auto;
          rewrite <- getOperandValue_eq_fresh_id; auto.
        destruct (isGVZero (los, nts) c');
          rewrite <- getOperandValue_eq_fresh_id; auto;
          rewrite <- getOperandValue_eq_fresh_id; auto.

    rewrite <- (@trace_app_nil__eq__trace trace_nil).
    eapply Opsem.sop_star_cons; eauto.
      eapply Opsem.sSelect; eauto.
        destruct (isGVZero (los, nts) c');
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
            simpl. rewrite lookupAL_updateAddAL_eq; auto.
            simpl. clear - Hctmpb. auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
            simpl. rewrite lookupAL_updateAddAL_eq; auto.
            simpl. clear - Hctmpb. auto.
        destruct (isGVZero (los, nts) c');
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
        destruct (isGVZero (los, nts) c');
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.
          rewrite <- getOperandValue_eq_fresh_id; auto.

    split; auto using inject_incr_refl.
    repeat (split; auto).
      eapply cmds_at_block_tail_next; eauto.
      
      destruct Heqb2 as [l2 [ps2 [cs21 Heqb2]]]; subst.
      exists l2. exists ps2. exists (cs21 ++
                  (insn_cast ctmp castop_bitcast i1 v0 i1
                :: insn_select id0 v0 t v1 v2
                :: insn_select bid0 (value_id ctmp) p8 bv1' bv2'
                   :: insn_select eid0 (value_id ctmp) p8 ev1' ev2' :: nil)).
      simpl_env. auto.

      exists ex_ids. exists rm2.
      exists ex_ids3'. exists ex_ids4. exists cs2. exists cs23.
      split; auto.
      split.
        destruct (isGVZero (los,nts) c'); inv H5.
          eapply reg_simulation__updateAddAL_prop; eauto.
            eapply reg_simulation__updateAddAL_tmp; eauto.
          eapply reg_simulation__updateAddAL_prop; eauto.
            eapply reg_simulation__updateAddAL_tmp; eauto.
      repeat (split; auto).
        clear - Hinc HeqR9.
        eapply mk_tmp_inc; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-impredicative-set") ***
*** End: ***
 *)



