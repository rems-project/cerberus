open Alist
open Dopsem
open Genericvalues
open Infrastructure
open Monad
open Syntax
open Targetdata
open Trace

(** val interInsn :
    Opsem.OpsemAux.coq_Config -> Opsem.Opsem.coq_State ->
    (Opsem.Opsem.coq_State*trace) option **)

let interInsn cfg state =
  let { Opsem.OpsemAux.coq_CurSystem = sys;
    Opsem.OpsemAux.coq_CurTargetData = tD; Opsem.OpsemAux.coq_CurProducts =
    ps; Opsem.OpsemAux.coq_Globals = gl; Opsem.OpsemAux.coq_FunTable = fs } =
    cfg
  in
  let { Opsem.Opsem.coq_ECS = eCS; Opsem.Opsem.coq_Mem = mem0 } = state in
  (match eCS with
     | [] -> None
     | e::eC ->
         let { Opsem.Opsem.coq_CurFunction = f; Opsem.Opsem.coq_CurBB = b;
           Opsem.Opsem.coq_CurCmds = cs; Opsem.Opsem.coq_Terminator = tmn;
           Opsem.Opsem.coq_Locals = lc; Opsem.Opsem.coq_Allocas = als } = e
         in
         (match cs with
            | [] ->
                (match tmn with
                   | LLVMsyntax.Coq_insn_return (rid, retTy, result) ->
                       (match eC with
                          | [] -> None
                          | e0::eC'' ->
                              let { Opsem.Opsem.coq_CurFunction = f';
                                Opsem.Opsem.coq_CurBB = b';
                                Opsem.Opsem.coq_CurCmds = curCmds;
                                Opsem.Opsem.coq_Terminator = tmn';
                                Opsem.Opsem.coq_Locals = lc';
                                Opsem.Opsem.coq_Allocas = als' } = e0
                              in
                              (match curCmds with
                                 | [] -> None
                                 | c'::cs' ->
                                     if LLVMinfra.Instruction.isCallInst c'
                                     then mbind (fun mem' ->
                                            mbind (fun lc'' -> Some
                                              ({ Opsem.Opsem.coq_ECS =
                                              ({ Opsem.Opsem.coq_CurFunction =
                                              f'; Opsem.Opsem.coq_CurBB = b';
                                              Opsem.Opsem.coq_CurCmds = cs';
                                              Opsem.Opsem.coq_Terminator =
                                              tmn'; Opsem.Opsem.coq_Locals =
                                              lc''; Opsem.Opsem.coq_Allocas =
                                              als' }::eC'');
                                              Opsem.Opsem.coq_Mem =
                                              mem' },Coq_trace_nil))
                                              (Opsem.Opsem.returnUpdateLocals
                                                coq_DGVs tD c' result lc lc'
                                                gl))
                                            (LLVMgv.free_allocas tD mem0 als)
                                     else None))
                   | LLVMsyntax.Coq_insn_return_void rid ->
                       (match eC with
                          | [] -> None
                          | e0::eC'' ->
                              let { Opsem.Opsem.coq_CurFunction = f';
                                Opsem.Opsem.coq_CurBB = b';
                                Opsem.Opsem.coq_CurCmds = curCmds;
                                Opsem.Opsem.coq_Terminator = tmn';
                                Opsem.Opsem.coq_Locals = lc';
                                Opsem.Opsem.coq_Allocas = als' } = e0
                              in
                              (match curCmds with
                                 | [] -> None
                                 | c'::cs' ->
                                     if LLVMinfra.Instruction.isCallInst c'
                                     then (match LLVMinfra.getCallerReturnID
                                                  c' with
                                             | Some i -> None
                                             | None ->
                                                 mbind (fun mem' -> Some
                                                  ({ Opsem.Opsem.coq_ECS =
                                                  ({ Opsem.Opsem.coq_CurFunction =
                                                  f'; Opsem.Opsem.coq_CurBB =
                                                  b';
                                                  Opsem.Opsem.coq_CurCmds =
                                                  cs';
                                                  Opsem.Opsem.coq_Terminator =
                                                  tmn';
                                                  Opsem.Opsem.coq_Locals =
                                                  lc';
                                                  Opsem.Opsem.coq_Allocas =
                                                  als' }::eC'');
                                                  Opsem.Opsem.coq_Mem =
                                                  mem' },Coq_trace_nil))
                                                  (LLVMgv.free_allocas tD
                                                  mem0 als))
                                     else None))
                   | LLVMsyntax.Coq_insn_br (bid, cond, l1, l2) ->
                       mbind (fun cond0 ->
                         match if LLVMgv.isGVZero tD (Obj.magic cond0)
                               then LLVMinfra.lookupBlockViaLabelFromFdef f
                                      l2
                               else LLVMinfra.lookupBlockViaLabelFromFdef f
                                      l1 with
                           | Some b0 ->
                               let LLVMsyntax.Coq_block_intro
                                 (l', ps', cs', tmn') = b0
                               in
                               mbind (fun lc' -> Some
                                 ({ Opsem.Opsem.coq_ECS =
                                 ({ Opsem.Opsem.coq_CurFunction = f;
                                 Opsem.Opsem.coq_CurBB =
                                 (LLVMsyntax.Coq_block_intro (l', ps', cs',
                                 tmn')); Opsem.Opsem.coq_CurCmds = cs';
                                 Opsem.Opsem.coq_Terminator = tmn';
                                 Opsem.Opsem.coq_Locals = lc';
                                 Opsem.Opsem.coq_Allocas = als }::eC);
                                 Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                                 (Opsem.Opsem.switchToNewBasicBlock coq_DGVs
                                   tD (LLVMsyntax.Coq_block_intro (l', ps',
                                   cs', tmn')) b gl lc)
                           | None -> None)
                         (Opsem.Opsem.getOperandValue coq_DGVs tD cond lc gl)
                   | LLVMsyntax.Coq_insn_br_uncond (
                       bid, l0) ->
                       (match LLVMinfra.lookupBlockViaLabelFromFdef f l0 with
                          | Some b0 ->
                              let LLVMsyntax.Coq_block_intro
                                (l', ps', cs', tmn') = b0
                              in
                              mbind (fun lc' -> Some ({ Opsem.Opsem.coq_ECS =
                                ({ Opsem.Opsem.coq_CurFunction = f;
                                Opsem.Opsem.coq_CurBB =
                                (LLVMsyntax.Coq_block_intro (l', ps', cs',
                                tmn')); Opsem.Opsem.coq_CurCmds = cs';
                                Opsem.Opsem.coq_Terminator = tmn';
                                Opsem.Opsem.coq_Locals = lc';
                                Opsem.Opsem.coq_Allocas = als }::eC);
                                Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                                (Opsem.Opsem.switchToNewBasicBlock coq_DGVs
                                  tD (LLVMsyntax.Coq_block_intro (l', ps',
                                  cs', tmn')) b gl lc)
                          | None -> None)
                   | LLVMsyntax.Coq_insn_unreachable i -> None)
            | c::cs0 ->
                (match c with
                   | LLVMsyntax.Coq_insn_bop (id0, bop0, sz0, v1, v2) ->
                       mbind (fun gv3 -> Some ({ Opsem.Opsem.coq_ECS =
                         ({ Opsem.Opsem.coq_CurFunction = f;
                         Opsem.Opsem.coq_CurBB = b; Opsem.Opsem.coq_CurCmds =
                         cs0; Opsem.Opsem.coq_Terminator = tmn;
                         Opsem.Opsem.coq_Locals = (updateAddAL lc id0 gv3);
                         Opsem.Opsem.coq_Allocas = als }::eC);
                         Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                         (Opsem.Opsem.coq_BOP coq_DGVs tD lc gl bop0 sz0 v1
                           v2)
                   | LLVMsyntax.Coq_insn_fbop (id0, fbop0, fp0, v1, v2) ->
                       mbind (fun gv3 -> Some ({ Opsem.Opsem.coq_ECS =
                         ({ Opsem.Opsem.coq_CurFunction = f;
                         Opsem.Opsem.coq_CurBB = b; Opsem.Opsem.coq_CurCmds =
                         cs0; Opsem.Opsem.coq_Terminator = tmn;
                         Opsem.Opsem.coq_Locals = (updateAddAL lc id0 gv3);
                         Opsem.Opsem.coq_Allocas = als }::eC);
                         Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                         (Opsem.Opsem.coq_FBOP coq_DGVs tD lc gl fbop0 fp0 v1
                           v2)
                   | LLVMsyntax.Coq_insn_extractvalue (
                       id0, t, v, idxs) ->
                       mbind (fun gv ->
                         mbind (fun gv' -> Some ({ Opsem.Opsem.coq_ECS =
                           ({ Opsem.Opsem.coq_CurFunction = f;
                           Opsem.Opsem.coq_CurBB = b;
                           Opsem.Opsem.coq_CurCmds = cs0;
                           Opsem.Opsem.coq_Terminator = tmn;
                           Opsem.Opsem.coq_Locals = 
                           (updateAddAL lc id0 gv');
                           Opsem.Opsem.coq_Allocas = als }::eC);
                           Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                           (Opsem.Opsem.extractGenericValue coq_DGVs tD t gv
                             idxs))
                         (Opsem.Opsem.getOperandValue coq_DGVs tD v lc gl)
                   | LLVMsyntax.Coq_insn_insertvalue
                       (id0, t, v, t', v', idxs) ->
                       mbind (fun gv ->
                         mbind (fun gv' ->
                           mbind (fun gv'' -> Some ({ Opsem.Opsem.coq_ECS =
                             ({ Opsem.Opsem.coq_CurFunction = f;
                             Opsem.Opsem.coq_CurBB = b;
                             Opsem.Opsem.coq_CurCmds = cs0;
                             Opsem.Opsem.coq_Terminator = tmn;
                             Opsem.Opsem.coq_Locals =
                             (updateAddAL lc id0 gv'');
                             Opsem.Opsem.coq_Allocas = als }::eC);
                             Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                             (Opsem.Opsem.insertGenericValue coq_DGVs tD t gv
                               idxs t' gv'))
                           (Opsem.Opsem.getOperandValue coq_DGVs tD v' lc gl))
                         (Opsem.Opsem.getOperandValue coq_DGVs tD v lc gl)
                   | LLVMsyntax.Coq_insn_malloc (id0, t, v0, align0) ->
                       mbind (fun tsz ->
                         mbind (fun gn ->
                           match LLVMgv.malloc tD mem0 tsz 
                                   (Obj.magic gn) align0 with
                             | Some p ->
                                 let mem',mb = p in
                                 Some ({ Opsem.Opsem.coq_ECS =
                                 ({ Opsem.Opsem.coq_CurFunction = f;
                                 Opsem.Opsem.coq_CurBB = b;
                                 Opsem.Opsem.coq_CurCmds = cs0;
                                 Opsem.Opsem.coq_Terminator = tmn;
                                 Opsem.Opsem.coq_Locals =
                                 (updateAddAL lc id0
                                   (coq_DGVs.Opsem.gv2gvs
                                     (LLVMgv.blk2GV tD mb)
                                     (LLVMsyntax.Coq_typ_pointer t)));
                                 Opsem.Opsem.coq_Allocas = als }::eC);
                                 Opsem.Opsem.coq_Mem = mem' },Coq_trace_nil)
                             | None -> None)
                           (Opsem.Opsem.getOperandValue coq_DGVs tD v0 lc gl))
                         (LLVMtd.getTypeAllocSize tD t)
                   | LLVMsyntax.Coq_insn_free (fid, t, v) ->
                       mbind (fun mptr ->
                         mbind (fun mem' -> Some ({ Opsem.Opsem.coq_ECS =
                           ({ Opsem.Opsem.coq_CurFunction = f;
                           Opsem.Opsem.coq_CurBB = b;
                           Opsem.Opsem.coq_CurCmds = cs0;
                           Opsem.Opsem.coq_Terminator = tmn;
                           Opsem.Opsem.coq_Locals = lc;
                           Opsem.Opsem.coq_Allocas = als }::eC);
                           Opsem.Opsem.coq_Mem = mem' },Coq_trace_nil))
                           (LLVMgv.free tD mem0 (Obj.magic mptr)))
                         (Opsem.Opsem.getOperandValue coq_DGVs tD v lc gl)
                   | LLVMsyntax.Coq_insn_alloca (id0, t, v0, align0) ->
                       mbind (fun tsz ->
                         mbind (fun gn ->
                           match LLVMgv.malloc tD mem0 tsz 
                                   (Obj.magic gn) align0 with
                             | Some p ->
                                 let mem',mb = p in
                                 Some ({ Opsem.Opsem.coq_ECS =
                                 ({ Opsem.Opsem.coq_CurFunction = f;
                                 Opsem.Opsem.coq_CurBB = b;
                                 Opsem.Opsem.coq_CurCmds = cs0;
                                 Opsem.Opsem.coq_Terminator = tmn;
                                 Opsem.Opsem.coq_Locals =
                                 (updateAddAL lc id0
                                   (coq_DGVs.Opsem.gv2gvs
                                     (LLVMgv.blk2GV tD mb)
                                     (LLVMsyntax.Coq_typ_pointer t)));
                                 Opsem.Opsem.coq_Allocas = (mb::als) }::eC);
                                 Opsem.Opsem.coq_Mem = mem' },Coq_trace_nil)
                             | None -> None)
                           (Opsem.Opsem.getOperandValue coq_DGVs tD v0 lc gl))
                         (LLVMtd.getTypeAllocSize tD t)
                   | LLVMsyntax.Coq_insn_load (id0, t, v, align0) ->
                       mbind (fun mp ->
                         mbind (fun gv -> Some ({ Opsem.Opsem.coq_ECS =
                           ({ Opsem.Opsem.coq_CurFunction = f;
                           Opsem.Opsem.coq_CurBB = b;
                           Opsem.Opsem.coq_CurCmds = cs0;
                           Opsem.Opsem.coq_Terminator = tmn;
                           Opsem.Opsem.coq_Locals =
                           (updateAddAL lc id0 (coq_DGVs.Opsem.gv2gvs gv t));
                           Opsem.Opsem.coq_Allocas = als }::eC);
                           Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                           (LLVMgv.mload tD mem0 (Obj.magic mp) t align0))
                         (Opsem.Opsem.getOperandValue coq_DGVs tD v lc gl)
                   | LLVMsyntax.Coq_insn_store (sid, t, v1, v2, align0) ->
                       mbind (fun gv1 ->
                         mbind (fun mp2 ->
                           mbind (fun mem' -> Some ({ Opsem.Opsem.coq_ECS =
                             ({ Opsem.Opsem.coq_CurFunction = f;
                             Opsem.Opsem.coq_CurBB = b;
                             Opsem.Opsem.coq_CurCmds = cs0;
                             Opsem.Opsem.coq_Terminator = tmn;
                             Opsem.Opsem.coq_Locals = lc;
                             Opsem.Opsem.coq_Allocas = als }::eC);
                             Opsem.Opsem.coq_Mem = mem' },Coq_trace_nil))
                             (LLVMgv.mstore tD mem0 
                               (Obj.magic mp2) t (Obj.magic gv1) align0))
                           (Opsem.Opsem.getOperandValue coq_DGVs tD v2 lc gl))
                         (Opsem.Opsem.getOperandValue coq_DGVs tD v1 lc gl)
                   | LLVMsyntax.Coq_insn_gep (id0, inbounds0, t, v, idxs) ->
                       mbind (fun mp ->
                         mbind (fun vidxs ->
                           mbind (fun mp' -> Some ({ Opsem.Opsem.coq_ECS =
                             ({ Opsem.Opsem.coq_CurFunction = f;
                             Opsem.Opsem.coq_CurBB = b;
                             Opsem.Opsem.coq_CurCmds = cs0;
                             Opsem.Opsem.coq_Terminator = tmn;
                             Opsem.Opsem.coq_Locals =
                             (updateAddAL lc id0 mp');
                             Opsem.Opsem.coq_Allocas = als }::eC);
                             Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                             (Opsem.Opsem.coq_GEP coq_DGVs tD t mp
                               (Obj.magic vidxs) inbounds0))
                           (Opsem.Opsem.values2GVs coq_DGVs tD idxs lc gl))
                         (Opsem.Opsem.getOperandValue coq_DGVs tD v lc gl)
                   | LLVMsyntax.Coq_insn_trunc (id0, truncop0, t1, v1, t2) ->
                       mbind (fun gv2 -> Some ({ Opsem.Opsem.coq_ECS =
                         ({ Opsem.Opsem.coq_CurFunction = f;
                         Opsem.Opsem.coq_CurBB = b; Opsem.Opsem.coq_CurCmds =
                         cs0; Opsem.Opsem.coq_Terminator = tmn;
                         Opsem.Opsem.coq_Locals = (updateAddAL lc id0 gv2);
                         Opsem.Opsem.coq_Allocas = als }::eC);
                         Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                         (Opsem.Opsem.coq_TRUNC coq_DGVs tD lc gl truncop0 t1
                           v1 t2)
                   | LLVMsyntax.Coq_insn_ext (id0, extop0, t1, v1, t2) ->
                       mbind (fun gv2 -> Some ({ Opsem.Opsem.coq_ECS =
                         ({ Opsem.Opsem.coq_CurFunction = f;
                         Opsem.Opsem.coq_CurBB = b; Opsem.Opsem.coq_CurCmds =
                         cs0; Opsem.Opsem.coq_Terminator = tmn;
                         Opsem.Opsem.coq_Locals = (updateAddAL lc id0 gv2);
                         Opsem.Opsem.coq_Allocas = als }::eC);
                         Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                         (Opsem.Opsem.coq_EXT coq_DGVs tD lc gl extop0 t1 v1
                           t2)
                   | LLVMsyntax.Coq_insn_cast (id0, castop0, t1, v1, t2) ->
                       mbind (fun gv2 -> Some ({ Opsem.Opsem.coq_ECS =
                         ({ Opsem.Opsem.coq_CurFunction = f;
                         Opsem.Opsem.coq_CurBB = b; Opsem.Opsem.coq_CurCmds =
                         cs0; Opsem.Opsem.coq_Terminator = tmn;
                         Opsem.Opsem.coq_Locals = (updateAddAL lc id0 gv2);
                         Opsem.Opsem.coq_Allocas = als }::eC);
                         Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                         (Opsem.Opsem.coq_CAST coq_DGVs tD lc gl castop0 t1
                           v1 t2)
                   | LLVMsyntax.Coq_insn_icmp (id0, cond0, t, v1, v2) ->
                       mbind (fun gv3 -> Some ({ Opsem.Opsem.coq_ECS =
                         ({ Opsem.Opsem.coq_CurFunction = f;
                         Opsem.Opsem.coq_CurBB = b; Opsem.Opsem.coq_CurCmds =
                         cs0; Opsem.Opsem.coq_Terminator = tmn;
                         Opsem.Opsem.coq_Locals = (updateAddAL lc id0 gv3);
                         Opsem.Opsem.coq_Allocas = als }::eC);
                         Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                         (Opsem.Opsem.coq_ICMP coq_DGVs tD lc gl cond0 t v1
                           v2)
                   | LLVMsyntax.Coq_insn_fcmp (id0, fcond0, fp, v1, v2) ->
                       mbind (fun gv3 -> Some ({ Opsem.Opsem.coq_ECS =
                         ({ Opsem.Opsem.coq_CurFunction = f;
                         Opsem.Opsem.coq_CurBB = b; Opsem.Opsem.coq_CurCmds =
                         cs0; Opsem.Opsem.coq_Terminator = tmn;
                         Opsem.Opsem.coq_Locals = (updateAddAL lc id0 gv3);
                         Opsem.Opsem.coq_Allocas = als }::eC);
                         Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                         (Opsem.Opsem.coq_FCMP coq_DGVs tD lc gl fcond0 fp v1
                           v2)
                   | LLVMsyntax.Coq_insn_select (id0, v0, t, v1, v2) ->
                       mbind (fun cond0 ->
                         mbind (fun gv1 ->
                           mbind (fun gv2 -> Some ({ Opsem.Opsem.coq_ECS =
                             ({ Opsem.Opsem.coq_CurFunction = f;
                             Opsem.Opsem.coq_CurBB = b;
                             Opsem.Opsem.coq_CurCmds = cs0;
                             Opsem.Opsem.coq_Terminator = tmn;
                             Opsem.Opsem.coq_Locals =
                             (if LLVMgv.isGVZero tD (Obj.magic cond0)
                              then updateAddAL lc id0 gv2
                              else updateAddAL lc id0 gv1);
                             Opsem.Opsem.coq_Allocas = als }::eC);
                             Opsem.Opsem.coq_Mem = mem0 },Coq_trace_nil))
                             (Opsem.Opsem.getOperandValue coq_DGVs tD v2 lc
                               gl))
                           (Opsem.Opsem.getOperandValue coq_DGVs tD v1 lc gl))
                         (Opsem.Opsem.getOperandValue coq_DGVs tD v0 lc gl)
                   | LLVMsyntax.Coq_insn_call
                       (rid, noret0, tailc0, ft, fv, lp) ->
                       mbind (fun fptr ->
                         mbind (fun fid ->
                           match LLVMinfra.lookupFdefViaIDFromProducts ps fid with
                             | Some f0 ->
                                 let LLVMsyntax.Coq_fdef_intro (f1, lb) = f0
                                 in
                                 let LLVMsyntax.Coq_fheader_intro
                                   (fa, rt, fid', la, va) = f1
                                 in
                                 if LLVMinfra.id_dec fid fid'
                                 then (match LLVMinfra.getEntryBlock
                                               (LLVMsyntax.Coq_fdef_intro
                                               ((LLVMsyntax.Coq_fheader_intro
                                               (fa, rt, fid, la, va)), lb)) with
                                         | Some b0 ->
                                             let LLVMsyntax.Coq_block_intro
                                               (l', ps', cs', tmn') = b0
                                             in
                                             mbind (fun gvs ->
                                               mbind (fun lc0 -> Some
                                                 ({ Opsem.Opsem.coq_ECS =
                                                 ({ Opsem.Opsem.coq_CurFunction =
                                                 (LLVMsyntax.Coq_fdef_intro
                                                 ((LLVMsyntax.Coq_fheader_intro
                                                 (fa, rt, fid, la, va)),
                                                 lb));
                                                 Opsem.Opsem.coq_CurBB =
                                                 (LLVMsyntax.Coq_block_intro
                                                 (l', ps', cs', tmn'));
                                                 Opsem.Opsem.coq_CurCmds =
                                                 cs';
                                                 Opsem.Opsem.coq_Terminator =
                                                 tmn';
                                                 Opsem.Opsem.coq_Locals =
                                                 lc0;
                                                 Opsem.Opsem.coq_Allocas =
                                                 [] }::({ Opsem.Opsem.coq_CurFunction =
                                                 f; Opsem.Opsem.coq_CurBB =
                                                 b; Opsem.Opsem.coq_CurCmds =
                                                 ((LLVMsyntax.Coq_insn_call
                                                 (rid, noret0, tailc0, ft,
                                                 fv, lp))::cs0);
                                                 Opsem.Opsem.coq_Terminator =
                                                 tmn;
                                                 Opsem.Opsem.coq_Locals = lc;
                                                 Opsem.Opsem.coq_Allocas =
                                                 als }::eC));
                                                 Opsem.Opsem.coq_Mem =
                                                 mem0 },Coq_trace_nil))
                                                 (Opsem.Opsem.initLocals
                                                  coq_DGVs tD la gvs))
                                               (Opsem.Opsem.params2GVs
                                                 coq_DGVs tD lp lc gl)
                                         | None -> None)
                                 else None
                             | None ->
                                 (match LLVMinfra.lookupFdecViaIDFromProducts
                                          ps fid with
                                    | Some f0 ->
                                        let LLVMsyntax.Coq_fheader_intro
                                          (fa, rt', fid', la, va) = f0
                                        in
                                        if LLVMinfra.id_dec fid fid'
                                        then mbind (fun gvs ->
                                               match 
                                               Opsem.OpsemAux.callExternalFunction
                                                 mem0 fid 
                                                 (Obj.magic gvs) with
                                                 | 
                                               Some p ->
                                                 let oresult,mem1 = p in
                                                 mbind (fun lc' -> Some
                                                  ({ Opsem.Opsem.coq_ECS =
                                                  ({ Opsem.Opsem.coq_CurFunction =
                                                  f; Opsem.Opsem.coq_CurBB =
                                                  b;
                                                  Opsem.Opsem.coq_CurCmds =
                                                  cs0;
                                                  Opsem.Opsem.coq_Terminator =
                                                  tmn;
                                                  Opsem.Opsem.coq_Locals =
                                                  lc';
                                                  Opsem.Opsem.coq_Allocas =
                                                  als }::eC);
                                                  Opsem.Opsem.coq_Mem =
                                                  mem1 },Coq_trace_nil))
                                                  (Opsem.Opsem.exCallUpdateLocals
                                                  coq_DGVs tD ft noret0 rid
                                                  oresult lc)
                                                 | 
                                               None -> None)
                                               (Opsem.Opsem.params2GVs
                                                 coq_DGVs tD lp lc gl)
                                        else None
                                    | None -> None))
                           (Opsem.OpsemAux.lookupFdefViaGVFromFunTable fs
                             (Obj.magic fptr)))
                         (Opsem.Opsem.getOperandValue coq_DGVs tD fv lc gl))))

