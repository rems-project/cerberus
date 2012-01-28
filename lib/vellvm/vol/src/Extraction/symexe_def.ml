open CoqEqDec
open Datatypes
open MetatheoryAtom
open Alist
open Genericvalues
open Syntax
open Trace

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module SimpleSE = 
 struct 
  type coq_DGVMap = Opsem.Opsem.coq_GVsMap
  
  type coq_ExecutionContext = { coq_CurBB : LLVMsyntax.block;
                                coq_Locals : coq_DGVMap;
                                coq_Allocas : LLVMgv.mblock list }
  
  (** val coq_ExecutionContext_rect :
      (LLVMsyntax.block -> coq_DGVMap -> LLVMgv.mblock list -> 'a1) ->
      coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rect f e =
    let { coq_CurBB = x; coq_Locals = x0; coq_Allocas = x1 } = e in f x x0 x1
  
  (** val coq_ExecutionContext_rec :
      (LLVMsyntax.block -> coq_DGVMap -> LLVMgv.mblock list -> 'a1) ->
      coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rec f e =
    let { coq_CurBB = x; coq_Locals = x0; coq_Allocas = x1 } = e in f x x0 x1
  
  (** val coq_CurBB : coq_ExecutionContext -> LLVMsyntax.block **)
  
  let coq_CurBB x = x.coq_CurBB
  
  (** val coq_Locals : coq_ExecutionContext -> coq_DGVMap **)
  
  let coq_Locals x = x.coq_Locals
  
  (** val coq_Allocas : coq_ExecutionContext -> LLVMgv.mblock list **)
  
  let coq_Allocas x = x.coq_Allocas
  
  type coq_State = { coq_Frame : coq_ExecutionContext; coq_Mem : LLVMgv.mem }
  
  (** val coq_State_rect :
      (coq_ExecutionContext -> LLVMgv.mem -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rect f s =
    let { coq_Frame = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_State_rec :
      (coq_ExecutionContext -> LLVMgv.mem -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rec f s =
    let { coq_Frame = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_Frame : coq_State -> coq_ExecutionContext **)
  
  let coq_Frame x = x.coq_Frame
  
  (** val coq_Mem : coq_State -> LLVMgv.mem **)
  
  let coq_Mem x = x.coq_Mem
  
  (** val isCall : LLVMsyntax.cmd -> bool **)
  
  let isCall = function
    | LLVMsyntax.Coq_insn_call (i0, n, c, t, v, p) -> true
    | _ -> false
  
  type nbranch =
    LLVMsyntax.cmd
    (* singleton inductive, whose constructor was mkNB *)
  
  (** val nbranch_rect : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1 **)
  
  let nbranch_rect f n =
    f n __
  
  (** val nbranch_rec : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1 **)
  
  let nbranch_rec f n =
    f n __
  
  (** val nbranching_cmd : nbranch -> LLVMsyntax.cmd **)
  
  let nbranching_cmd n =
    n
  
  type subblock = { coq_NBs : nbranch list; call_cmd : LLVMsyntax.cmd }
  
  (** val subblock_rect :
      (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1 **)
  
  let subblock_rect f s =
    let { coq_NBs = x; call_cmd = x0 } = s in f x x0 __
  
  (** val subblock_rec :
      (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1 **)
  
  let subblock_rec f s =
    let { coq_NBs = x; call_cmd = x0 } = s in f x x0 __
  
  (** val coq_NBs : subblock -> nbranch list **)
  
  let coq_NBs x = x.coq_NBs
  
  (** val call_cmd : subblock -> LLVMsyntax.cmd **)
  
  let call_cmd x = x.call_cmd
  
  (** val isCall_dec : LLVMsyntax.cmd -> bool **)
  
  let isCall_dec = function
    | LLVMsyntax.Coq_insn_call (i0, n, c0, t, v, p) -> false
    | _ -> true
  
  (** val cmds2sbs : LLVMsyntax.cmds -> subblock list*nbranch list **)
  
  let rec cmds2sbs = function
    | [] -> [],[]
    | c::cs' ->
        if isCall_dec c
        then let l0,nbs0 = cmds2sbs cs' in
             (match l0 with
                | [] -> [],(c::nbs0)
                | s::sbs' ->
                    let { coq_NBs = nbs; call_cmd = call0 } = s in
                    ({ coq_NBs = (c::nbs); call_cmd = call0 }::sbs'),nbs0)
        else let sbs,nbs0 = cmds2sbs cs' in
             ({ coq_NBs = []; call_cmd = c }::sbs),nbs0
  
  (** val nbranchs2cmds : nbranch list -> LLVMsyntax.cmd list **)
  
  let rec nbranchs2cmds = function
    | [] -> []
    | n::nbs' -> n::(nbranchs2cmds nbs')
  
  (** val cmd2nbranch : LLVMsyntax.cmd -> nbranch option **)
  
  let cmd2nbranch c =
    if isCall_dec c then Some c else None
  
  (** val cmds2nbranchs : LLVMsyntax.cmd list -> nbranch list option **)
  
  let rec cmds2nbranchs = function
    | [] -> Some []
    | c::cs' ->
        let o = cmd2nbranch c in
        let o0 = cmds2nbranchs cs' in
        (match o with
           | Some nb ->
               (match o0 with
                  | Some nbs' -> Some (nb::nbs')
                  | None -> None)
           | None -> None)
  
  type sterm =
    | Coq_sterm_val of LLVMsyntax.value
    | Coq_sterm_bop of LLVMsyntax.bop * LLVMsyntax.sz * sterm * sterm
    | Coq_sterm_fbop of LLVMsyntax.fbop * LLVMsyntax.floating_point * 
       sterm * sterm
    | Coq_sterm_extractvalue of LLVMsyntax.typ * sterm
       * LLVMsyntax.list_const
    | Coq_sterm_insertvalue of LLVMsyntax.typ * sterm * 
       LLVMsyntax.typ * sterm * LLVMsyntax.list_const
    | Coq_sterm_malloc of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_sterm_alloca of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_sterm_load of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_sterm_gep of LLVMsyntax.inbounds * LLVMsyntax.typ * 
       sterm * list_sterm
    | Coq_sterm_trunc of LLVMsyntax.truncop * LLVMsyntax.typ * 
       sterm * LLVMsyntax.typ
    | Coq_sterm_ext of LLVMsyntax.extop * LLVMsyntax.typ * 
       sterm * LLVMsyntax.typ
    | Coq_sterm_cast of LLVMsyntax.castop * LLVMsyntax.typ * 
       sterm * LLVMsyntax.typ
    | Coq_sterm_icmp of LLVMsyntax.cond * LLVMsyntax.typ * sterm * sterm
    | Coq_sterm_fcmp of LLVMsyntax.fcond * LLVMsyntax.floating_point * 
       sterm * sterm
    | Coq_sterm_phi of LLVMsyntax.typ * list_sterm_l
    | Coq_sterm_select of sterm * LLVMsyntax.typ * sterm * sterm
  and list_sterm =
    | Nil_list_sterm
    | Cons_list_sterm of LLVMsyntax.sz * sterm * list_sterm
  and list_sterm_l =
    | Nil_list_sterm_l
    | Cons_list_sterm_l of sterm * LLVMsyntax.l * list_sterm_l
  and smem =
    | Coq_smem_init
    | Coq_smem_malloc of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_smem_free of smem * LLVMsyntax.typ * sterm
    | Coq_smem_alloca of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_smem_load of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_smem_store of smem * LLVMsyntax.typ * sterm * 
       sterm * LLVMsyntax.align
  and sframe =
    | Coq_sframe_init
    | Coq_sframe_alloca of smem * sframe * LLVMsyntax.typ * 
       sterm * LLVMsyntax.align
  
  (** val sterm_rect :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a1) ->
      (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ
      -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fcond ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> list_sterm_l -> 'a1) -> (sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> sterm -> 'a1 **)
  
  let rec sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
    | Coq_sterm_val v -> f v
    | Coq_sterm_bop (b, s0, s1, s2) ->
        f0 b s0 s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          s2
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s2)
    | Coq_sterm_fbop (f15, f16, s0, s1) ->
        f1 f15 f16 s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
    | Coq_sterm_extractvalue (t, s0, l0) ->
        f2 t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          l0
    | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
        f3 t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t0 s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          l0
    | Coq_sterm_malloc (s0, t, s1, a) ->
        f4 s0 t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          a
    | Coq_sterm_alloca (s0, t, s1, a) ->
        f5 s0 t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          a
    | Coq_sterm_load (s0, t, s1, a) ->
        f6 s0 t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          a
    | Coq_sterm_gep (i, t, s0, l0) ->
        f7 i t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          l0
    | Coq_sterm_trunc (t, t0, s0, t1) ->
        f8 t t0 s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t1
    | Coq_sterm_ext (e, t, s0, t0) ->
        f9 e t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t0
    | Coq_sterm_cast (c, t, s0, t0) ->
        f10 c t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t0
    | Coq_sterm_icmp (c, t, s0, s1) ->
        f11 c t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
    | Coq_sterm_fcmp (f15, f16, s0, s1) ->
        f12 f15 f16 s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
    | Coq_sterm_phi (t, l0) -> f13 t l0
    | Coq_sterm_select (s0, t, s1, s2) ->
        f14 s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          s2
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s2)
  
  (** val sterm_rec :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm -> 'a1) ->
      (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ
      -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fcond ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> list_sterm_l -> 'a1) -> (sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> sterm -> 'a1 **)
  
  let rec sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
    | Coq_sterm_val v -> f v
    | Coq_sterm_bop (b, s0, s1, s2) ->
        f0 b s0 s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          s2
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s2)
    | Coq_sterm_fbop (f15, f16, s0, s1) ->
        f1 f15 f16 s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
    | Coq_sterm_extractvalue (t, s0, l0) ->
        f2 t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          l0
    | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
        f3 t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t0 s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          l0
    | Coq_sterm_malloc (s0, t, s1, a) ->
        f4 s0 t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          a
    | Coq_sterm_alloca (s0, t, s1, a) ->
        f5 s0 t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          a
    | Coq_sterm_load (s0, t, s1, a) ->
        f6 s0 t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          a
    | Coq_sterm_gep (i, t, s0, l0) ->
        f7 i t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          l0
    | Coq_sterm_trunc (t, t0, s0, t1) ->
        f8 t t0 s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t1
    | Coq_sterm_ext (e, t, s0, t0) ->
        f9 e t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t0
    | Coq_sterm_cast (c, t, s0, t0) ->
        f10 c t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t0
    | Coq_sterm_icmp (c, t, s0, s1) ->
        f11 c t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
    | Coq_sterm_fcmp (f15, f16, s0, s1) ->
        f12 f15 f16 s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
    | Coq_sterm_phi (t, l0) -> f13 t l0
    | Coq_sterm_select (s0, t, s1, s2) ->
        f14 s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s0)
          t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s1)
          s2
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 s2)
  
  (** val list_sterm_rect :
      'a1 -> (LLVMsyntax.sz -> sterm -> list_sterm -> 'a1 -> 'a1) ->
      list_sterm -> 'a1 **)
  
  let rec list_sterm_rect f f0 = function
    | Nil_list_sterm -> f
    | Cons_list_sterm (s, s0, l1) -> f0 s s0 l1 (list_sterm_rect f f0 l1)
  
  (** val list_sterm_rec :
      'a1 -> (LLVMsyntax.sz -> sterm -> list_sterm -> 'a1 -> 'a1) ->
      list_sterm -> 'a1 **)
  
  let rec list_sterm_rec f f0 = function
    | Nil_list_sterm -> f
    | Cons_list_sterm (s, s0, l1) -> f0 s s0 l1 (list_sterm_rec f f0 l1)
  
  (** val list_sterm_l_rect :
      'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
      list_sterm_l -> 'a1 **)
  
  let rec list_sterm_l_rect f f0 = function
    | Nil_list_sterm_l -> f
    | Cons_list_sterm_l (s, l1, l2) -> f0 s l1 l2 (list_sterm_l_rect f f0 l2)
  
  (** val list_sterm_l_rec :
      'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
      list_sterm_l -> 'a1 **)
  
  let rec list_sterm_l_rec f f0 = function
    | Nil_list_sterm_l -> f
    | Cons_list_sterm_l (s, l1, l2) -> f0 s l1 l2 (list_sterm_l_rec f f0 l2)
  
  (** val smem_rect :
      'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> sterm -> LLVMsyntax.align -> 'a1) -> smem
      -> 'a1 **)
  
  let rec smem_rect f f0 f1 f2 f3 f4 = function
    | Coq_smem_init -> f
    | Coq_smem_malloc (s0, t, s1, a) ->
        f0 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_free (s0, t, s1) -> f1 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1
    | Coq_smem_alloca (s0, t, s1, a) ->
        f2 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_load (s0, t, s1, a) ->
        f3 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_store (s0, t, s1, s2, a) ->
        f4 s0 (smem_rect f f0 f1 f2 f3 f4 s0) t s1 s2 a
  
  (** val smem_rec :
      'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> sterm -> LLVMsyntax.align -> 'a1) -> smem
      -> 'a1 **)
  
  let rec smem_rec f f0 f1 f2 f3 f4 = function
    | Coq_smem_init -> f
    | Coq_smem_malloc (s0, t, s1, a) ->
        f0 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_free (s0, t, s1) -> f1 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1
    | Coq_smem_alloca (s0, t, s1, a) ->
        f2 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_load (s0, t, s1, a) ->
        f3 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1 a
    | Coq_smem_store (s0, t, s1, s2, a) ->
        f4 s0 (smem_rec f f0 f1 f2 f3 f4 s0) t s1 s2 a
  
  (** val sframe_rect :
      'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> sterm ->
      LLVMsyntax.align -> 'a1) -> sframe -> 'a1 **)
  
  let rec sframe_rect f f0 = function
    | Coq_sframe_init -> f
    | Coq_sframe_alloca (s0, s1, t, s2, a) ->
        f0 s0 s1 (sframe_rect f f0 s1) t s2 a
  
  (** val sframe_rec :
      'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> sterm ->
      LLVMsyntax.align -> 'a1) -> sframe -> 'a1 **)
  
  let rec sframe_rec f f0 = function
    | Coq_sframe_init -> f
    | Coq_sframe_alloca (s0, s1, t, s2, a) ->
        f0 s0 s1 (sframe_rec f f0 s1) t s2 a
  
  (** val sframe_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
      'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2
      -> 'a2) -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3
      -> 'a3) -> 'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a5) -> sframe -> 'a5 **)
  
  let sframe_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =
    let rec f27 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f27 s1) s2 (f27 s2)
      | Coq_sterm_fbop (f32, f33, s0, s1) ->
          f1 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f27 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f27 s0) t0 s1 (f27 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f27 s0) l0 (f28 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f27 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f27 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f27 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_fcmp (f32, f33, s0, s1) ->
          f12 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f29 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f27 s0) t s1 (f27 s1) s2 (f27 s2)
    and f28 = function
      | Nil_list_sterm -> f15
      | Cons_list_sterm (s, s0, l1) -> f16 s s0 (f27 s0) l1 (f28 l1)
    and f29 = function
      | Nil_list_sterm_l -> f17
      | Cons_list_sterm_l (s, l1, l2) -> f18 s (f27 s) l1 l2 (f29 l2)
    and f30 = function
      | Coq_smem_init -> f19
      | Coq_smem_malloc (s0, t, s1, a) -> f20 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_free (s0, t, s1) -> f21 s0 (f30 s0) t s1 (f27 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f22 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f23 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f24 s0 (f30 s0) t s1 (f27 s1) s2 (f27 s2) a
    and f31 = function
      | Coq_sframe_init -> f25
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f26 s0 (f30 s0) s1 (f31 s1) t s2 (f27 s2) a
    in f31
  
  (** val smem_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
      'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2
      -> 'a2) -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3
      -> 'a3) -> 'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a5) -> smem -> 'a4 **)
  
  let smem_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =
    let rec f27 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f27 s1) s2 (f27 s2)
      | Coq_sterm_fbop (f32, f33, s0, s1) ->
          f1 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f27 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f27 s0) t0 s1 (f27 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f27 s0) l0 (f28 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f27 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f27 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f27 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_fcmp (f32, f33, s0, s1) ->
          f12 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f29 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f27 s0) t s1 (f27 s1) s2 (f27 s2)
    and f28 = function
      | Nil_list_sterm -> f15
      | Cons_list_sterm (s, s0, l1) -> f16 s s0 (f27 s0) l1 (f28 l1)
    and f29 = function
      | Nil_list_sterm_l -> f17
      | Cons_list_sterm_l (s, l1, l2) -> f18 s (f27 s) l1 l2 (f29 l2)
    and f30 = function
      | Coq_smem_init -> f19
      | Coq_smem_malloc (s0, t, s1, a) -> f20 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_free (s0, t, s1) -> f21 s0 (f30 s0) t s1 (f27 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f22 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f23 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f24 s0 (f30 s0) t s1 (f27 s1) s2 (f27 s2) a
    and f31 = function
      | Coq_sframe_init -> f25
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f26 s0 (f30 s0) s1 (f31 s1) t s2 (f27 s2) a
    in f30
  
  (** val list_sterm_l_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
      'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2
      -> 'a2) -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3
      -> 'a3) -> 'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a5) -> list_sterm_l -> 'a3 **)
  
  let list_sterm_l_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =
    let rec f27 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f27 s1) s2 (f27 s2)
      | Coq_sterm_fbop (f32, f33, s0, s1) ->
          f1 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f27 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f27 s0) t0 s1 (f27 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f27 s0) l0 (f28 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f27 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f27 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f27 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_fcmp (f32, f33, s0, s1) ->
          f12 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f29 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f27 s0) t s1 (f27 s1) s2 (f27 s2)
    and f28 = function
      | Nil_list_sterm -> f15
      | Cons_list_sterm (s, s0, l1) -> f16 s s0 (f27 s0) l1 (f28 l1)
    and f29 = function
      | Nil_list_sterm_l -> f17
      | Cons_list_sterm_l (s, l1, l2) -> f18 s (f27 s) l1 l2 (f29 l2)
    and f30 = function
      | Coq_smem_init -> f19
      | Coq_smem_malloc (s0, t, s1, a) -> f20 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_free (s0, t, s1) -> f21 s0 (f30 s0) t s1 (f27 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f22 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f23 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f24 s0 (f30 s0) t s1 (f27 s1) s2 (f27 s2) a
    and f31 = function
      | Coq_sframe_init -> f25
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f26 s0 (f30 s0) s1 (f31 s1) t s2 (f27 s2) a
    in f29
  
  (** val list_sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
      'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2
      -> 'a2) -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3
      -> 'a3) -> 'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a5) -> list_sterm -> 'a2 **)
  
  let list_sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =
    let rec f27 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f27 s1) s2 (f27 s2)
      | Coq_sterm_fbop (f32, f33, s0, s1) ->
          f1 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f27 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f27 s0) t0 s1 (f27 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f27 s0) l0 (f28 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f27 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f27 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f27 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_fcmp (f32, f33, s0, s1) ->
          f12 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f29 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f27 s0) t s1 (f27 s1) s2 (f27 s2)
    and f28 = function
      | Nil_list_sterm -> f15
      | Cons_list_sterm (s, s0, l1) -> f16 s s0 (f27 s0) l1 (f28 l1)
    and f29 = function
      | Nil_list_sterm_l -> f17
      | Cons_list_sterm_l (s, l1, l2) -> f18 s (f27 s) l1 l2 (f29 l2)
    and f30 = function
      | Coq_smem_init -> f19
      | Coq_smem_malloc (s0, t, s1, a) -> f20 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_free (s0, t, s1) -> f21 s0 (f30 s0) t s1 (f27 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f22 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f23 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f24 s0 (f30 s0) t s1 (f27 s1) s2 (f27 s2) a
    and f31 = function
      | Coq_sframe_init -> f25
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f26 s0 (f30 s0) s1 (f31 s1) t s2 (f27 s2) a
    in f28
  
  (** val sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
      'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2
      -> 'a2) -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3
      -> 'a3) -> 'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a5) -> sterm -> 'a1 **)
  
  let sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 =
    let rec f27 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f27 s1) s2 (f27 s2)
      | Coq_sterm_fbop (f32, f33, s0, s1) ->
          f1 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f27 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f27 s0) t0 s1 (f27 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f27 s0) l0 (f28 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f27 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f27 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f27 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_fcmp (f32, f33, s0, s1) ->
          f12 f32 f33 s0 (f27 s0) s1 (f27 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f29 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f27 s0) t s1 (f27 s1) s2 (f27 s2)
    and f28 = function
      | Nil_list_sterm -> f15
      | Cons_list_sterm (s, s0, l1) -> f16 s s0 (f27 s0) l1 (f28 l1)
    and f29 = function
      | Nil_list_sterm_l -> f17
      | Cons_list_sterm_l (s, l1, l2) -> f18 s (f27 s) l1 l2 (f29 l2)
    and f30 = function
      | Coq_smem_init -> f19
      | Coq_smem_malloc (s0, t, s1, a) -> f20 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_free (s0, t, s1) -> f21 s0 (f30 s0) t s1 (f27 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f22 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f23 s0 (f30 s0) t s1 (f27 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f24 s0 (f30 s0) t s1 (f27 s1) s2 (f27 s2) a
    and f31 = function
      | Coq_sframe_init -> f25
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f26 s0 (f30 s0) s1 (f31 s1) t s2 (f27 s2) a
    in f27
  
  (** val se_mutrec :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
      'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2
      -> 'a2) -> 'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3
      -> 'a3) -> 'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 ->
      (smem -> 'a4 -> sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.align -> 'a5) -> ((((sterm -> 'a1)*(list_sterm ->
      'a2))*(list_sterm_l -> 'a3))*(smem -> 'a4))*(sframe -> 'a5) **)
  
  let se_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 =
    ((((sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
         h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28),
      (list_sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)),
      (list_sterm_l_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)),
      (smem_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)),
      (sframe_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)
  
  (** val map_list_sterm :
      (LLVMsyntax.sz -> sterm -> 'a1) -> list_sterm -> 'a1 list **)
  
  let rec map_list_sterm f = function
    | Nil_list_sterm -> []
    | Cons_list_sterm (s, h, tl_) -> (f s h)::(map_list_sterm f tl_)
  
  (** val make_list_sterm : (LLVMsyntax.sz*sterm) list -> list_sterm **)
  
  let rec make_list_sterm = function
    | [] -> Nil_list_sterm
    | p::tl_ -> let s,h = p in Cons_list_sterm (s, h, (make_list_sterm tl_))
  
  (** val unmake_list_sterm : list_sterm -> (LLVMsyntax.sz*sterm) list **)
  
  let rec unmake_list_sterm = function
    | Nil_list_sterm -> []
    | Cons_list_sterm (s, h, tl_) -> (s,h)::(unmake_list_sterm tl_)
  
  (** val nth_list_sterm :
      nat -> list_sterm -> (LLVMsyntax.sz*sterm) option **)
  
  let rec nth_list_sterm n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sterm -> None
             | Cons_list_sterm (s, h, tl_) -> Some (s,h))
      | S m ->
          (match l0 with
             | Nil_list_sterm -> None
             | Cons_list_sterm (s, s0, tl_) -> nth_list_sterm m tl_)
  
  (** val app_list_sterm : list_sterm -> list_sterm -> list_sterm **)
  
  let rec app_list_sterm l0 m =
    match l0 with
      | Nil_list_sterm -> m
      | Cons_list_sterm (s, h, tl_) -> Cons_list_sterm (s, h,
          (app_list_sterm tl_ m))
  
  (** val map_list_sterm_l :
      (sterm -> LLVMsyntax.l -> 'a1) -> list_sterm_l -> 'a1 list **)
  
  let rec map_list_sterm_l f = function
    | Nil_list_sterm_l -> []
    | Cons_list_sterm_l (h0, h1, tl_) -> (f h0 h1)::(map_list_sterm_l f tl_)
  
  (** val make_list_sterm_l : (sterm*LLVMsyntax.l) list -> list_sterm_l **)
  
  let rec make_list_sterm_l = function
    | [] -> Nil_list_sterm_l
    | p::tl_ ->
        let h0,h1 = p in Cons_list_sterm_l (h0, h1, (make_list_sterm_l tl_))
  
  (** val unmake_list_sterm_l : list_sterm_l -> (sterm*LLVMsyntax.l) list **)
  
  let rec unmake_list_sterm_l = function
    | Nil_list_sterm_l -> []
    | Cons_list_sterm_l (h0, h1, tl_) -> (h0,h1)::(unmake_list_sterm_l tl_)
  
  (** val nth_list_sterm_l :
      nat -> list_sterm_l -> (sterm*LLVMsyntax.l) option **)
  
  let rec nth_list_sterm_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sterm_l -> None
             | Cons_list_sterm_l (h0, h1, tl_) -> Some (h0,h1))
      | S m ->
          (match l0 with
             | Nil_list_sterm_l -> None
             | Cons_list_sterm_l (h0, h1, tl_) -> nth_list_sterm_l m tl_)
  
  (** val app_list_sterm_l : list_sterm_l -> list_sterm_l -> list_sterm_l **)
  
  let rec app_list_sterm_l l0 m =
    match l0 with
      | Nil_list_sterm_l -> m
      | Cons_list_sterm_l (h0, h1, tl_) -> Cons_list_sterm_l (h0, h1,
          (app_list_sterm_l tl_ m))
  
  type sterminator =
    | Coq_stmn_return of LLVMsyntax.id * LLVMsyntax.typ * sterm
    | Coq_stmn_return_void of LLVMsyntax.id
    | Coq_stmn_br of LLVMsyntax.id * sterm * LLVMsyntax.l * LLVMsyntax.l
    | Coq_stmn_br_uncond of LLVMsyntax.id * LLVMsyntax.l
    | Coq_stmn_unreachable of LLVMsyntax.id
  
  (** val sterminator_rect :
      (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
      'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
      -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
      sterminator -> 'a1 **)
  
  let sterminator_rect f f0 f1 f2 f3 = function
    | Coq_stmn_return (x, x0, x1) -> f x x0 x1
    | Coq_stmn_return_void x -> f0 x
    | Coq_stmn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_stmn_br_uncond (x, x0) -> f2 x x0
    | Coq_stmn_unreachable x -> f3 x
  
  (** val sterminator_rec :
      (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
      'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
      -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
      sterminator -> 'a1 **)
  
  let sterminator_rec f f0 f1 f2 f3 = function
    | Coq_stmn_return (x, x0, x1) -> f x x0 x1
    | Coq_stmn_return_void x -> f0 x
    | Coq_stmn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_stmn_br_uncond (x, x0) -> f2 x x0
    | Coq_stmn_unreachable x -> f3 x
  
  type smap = (AtomImpl.atom*sterm) list
  
  type sstate = { coq_STerms : smap; coq_SMem : smem; coq_SFrame : 
                  sframe; coq_SEffects : sterm list }
  
  (** val sstate_rect :
      (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1 **)
  
  let sstate_rect f s =
    let { coq_STerms = x; coq_SMem = x0; coq_SFrame = x1; coq_SEffects =
      x2 } = s
    in
    f x x0 x1 x2
  
  (** val sstate_rec :
      (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1 **)
  
  let sstate_rec f s =
    let { coq_STerms = x; coq_SMem = x0; coq_SFrame = x1; coq_SEffects =
      x2 } = s
    in
    f x x0 x1 x2
  
  (** val coq_STerms : sstate -> smap **)
  
  let coq_STerms x = x.coq_STerms
  
  (** val coq_SMem : sstate -> smem **)
  
  let coq_SMem x = x.coq_SMem
  
  (** val coq_SFrame : sstate -> sframe **)
  
  let coq_SFrame x = x.coq_SFrame
  
  (** val coq_SEffects : sstate -> sterm list **)
  
  let coq_SEffects x = x.coq_SEffects
  
  (** val sstate_init : sstate **)
  
  let sstate_init =
    { coq_STerms = []; coq_SMem = Coq_smem_init; coq_SFrame =
      Coq_sframe_init; coq_SEffects = [] }
  
  (** val lookupSmap : smap -> LLVMsyntax.id -> sterm **)
  
  let rec lookupSmap sm i0 =
    match sm with
      | [] -> Coq_sterm_val (LLVMsyntax.Coq_value_id i0)
      | p::sm' ->
          let id0,s0 = p in
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) i0 id0
          then s0
          else lookupSmap sm' i0
  
  (** val value2Sterm : smap -> LLVMsyntax.value -> sterm **)
  
  let value2Sterm sm v = match v with
    | LLVMsyntax.Coq_value_id i0 -> lookupSmap sm i0
    | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v
  
  (** val list_param__list_typ_subst_sterm :
      LLVMsyntax.params -> smap ->
      ((LLVMsyntax.typ*LLVMsyntax.attributes)*sterm) list **)
  
  let rec list_param__list_typ_subst_sterm list_param1 sm =
    match list_param1 with
      | [] -> []
      | p::list_param1' ->
          let p0,v = p in
          (p0,(value2Sterm sm v))::(list_param__list_typ_subst_sterm
                                     list_param1' sm)
  
  (** val se_call :
      LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.noret ->
      LLVMsyntax.clattrs -> LLVMsyntax.typ -> LLVMsyntax.value ->
      LLVMsyntax.params -> sstate **)
  
  let se_call i0 id0 noret0 tailc0 ft fv lp =
    assert false (* absurd case *)
  
  (** val se_cmd : sstate -> nbranch -> sstate **)
  
  let se_cmd st c = match c with
    | LLVMsyntax.Coq_insn_bop (id0, op0, sz0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_bop (op0, sz0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_fbop (id0, op0, fp0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_fbop (op0, fp0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_extractvalue (id0, t1, v1, cs3) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_extractvalue (t1,
          (value2Sterm st.coq_STerms v1), cs3))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_insertvalue (id0, t1, v1, t2, v2, cs3) ->
        { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_insertvalue (t1,
          (value2Sterm st.coq_STerms v1), t2, (value2Sterm st.coq_STerms v2),
          cs3))); coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame;
        coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_malloc (id0, t1, v1, al1) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_malloc (st.coq_SMem, t1,
          (value2Sterm st.coq_STerms v1), al1))); coq_SMem = (Coq_smem_malloc
        (st.coq_SMem, t1, (value2Sterm st.coq_STerms v1), al1)); coq_SFrame =
        st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_free (id0, t0, v0) -> { coq_STerms = st.coq_STerms;
        coq_SMem = (Coq_smem_free (st.coq_SMem, t0,
        (value2Sterm st.coq_STerms v0))); coq_SFrame = st.coq_SFrame;
        coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_alloca (id0, t1, v1, al1) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_alloca (st.coq_SMem, t1,
          (value2Sterm st.coq_STerms v1), al1))); coq_SMem = (Coq_smem_alloca
        (st.coq_SMem, t1, (value2Sterm st.coq_STerms v1), al1)); coq_SFrame =
        (Coq_sframe_alloca (st.coq_SMem, st.coq_SFrame, t1,
        (value2Sterm st.coq_STerms v1), al1)); coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_load (id0, t2, v2, align0) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_load (st.coq_SMem, t2,
          (value2Sterm st.coq_STerms v2), align0))); coq_SMem =
        (Coq_smem_load (st.coq_SMem, t2, (value2Sterm st.coq_STerms v2),
        align0)); coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_store (id0, t0, v1, v2, align0) -> { coq_STerms =
        st.coq_STerms; coq_SMem = (Coq_smem_store (st.coq_SMem, t0,
        (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2),
        align0)); coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_gep (id0, inbounds0, t1, v1, lv2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_gep (inbounds0, t1,
          (value2Sterm st.coq_STerms v1),
          (make_list_sterm
            (LLVMsyntax.map_list_sz_value (fun sz' v' ->
              sz',(value2Sterm st.coq_STerms v')) lv2))))); coq_SMem =
        st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_trunc (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_trunc (op0, t1,
          (value2Sterm st.coq_STerms v1), t2))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_ext (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_ext (op0, t1,
          (value2Sterm st.coq_STerms v1), t2))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_cast (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_cast (op0, t1,
          (value2Sterm st.coq_STerms v1), t2))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_icmp (id0, c0, t0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_icmp (c0, t0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_fcmp (id0, c0, fp0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_fcmp (c0, fp0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_select (id0, v0, t0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_select
          ((value2Sterm st.coq_STerms v0), t0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_call (id0, noret0, tailc0, ft, fv, lp) ->
        se_call c id0 noret0 tailc0 ft fv lp
  
  (** val _se_phinodes :
      sstate -> sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec _se_phinodes st st0 = function
    | [] -> st
    | p::ps' ->
        let LLVMsyntax.Coq_insn_phi (id0, t0, idls0) = p in
        _se_phinodes { coq_STerms =
          (updateAL st.coq_STerms id0 (Coq_sterm_phi (t0,
            (make_list_sterm_l
              (LLVMsyntax.map_list_value_l (fun v5 l5 ->
                (value2Sterm st.coq_STerms v5),l5) idls0))))); coq_SMem =
          st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
          st.coq_SEffects } st0 ps'
  
  (** val se_phinodes : sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec se_phinodes st ps =
    _se_phinodes st st ps
  
  (** val se_cmds : sstate -> nbranch list -> sstate **)
  
  let rec se_cmds st = function
    | [] -> st
    | c::cs' -> se_cmds (se_cmd st c) cs'
  
  (** val se_terminator : sstate -> LLVMsyntax.terminator -> sterminator **)
  
  let se_terminator st = function
    | LLVMsyntax.Coq_insn_return (id0, t0, v0) -> Coq_stmn_return (id0, t0,
        (value2Sterm st.coq_STerms v0))
    | LLVMsyntax.Coq_insn_return_void id0 -> Coq_stmn_return_void id0
    | LLVMsyntax.Coq_insn_br (id0, v0, l1, l2) -> Coq_stmn_br (id0,
        (value2Sterm st.coq_STerms v0), l1, l2)
    | LLVMsyntax.Coq_insn_br_uncond (id0, l0) -> Coq_stmn_br_uncond (id0, l0)
    | LLVMsyntax.Coq_insn_unreachable id0 -> Coq_stmn_unreachable id0
  
  (** val seffects_denote_trace_rect : 'a1 -> sterm list -> trace -> 'a1 **)
  
  let seffects_denote_trace_rect f l0 t =
    f
  
  (** val seffects_denote_trace_rec : 'a1 -> sterm list -> trace -> 'a1 **)
  
  let seffects_denote_trace_rec f l0 t =
    f
  
  (** val subst_tt : LLVMsyntax.id -> sterm -> sterm -> sterm **)
  
  let rec subst_tt id0 s0 s = match s with
    | Coq_sterm_val v ->
        (match v with
           | LLVMsyntax.Coq_value_id id1 ->
               if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id1
               then s0
               else s
           | LLVMsyntax.Coq_value_const c -> Coq_sterm_val
               (LLVMsyntax.Coq_value_const c))
    | Coq_sterm_bop (op, sz0, s1, s2) -> Coq_sterm_bop (op, sz0,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_fbop (op, fp, s1, s2) -> Coq_sterm_fbop (op, fp,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_extractvalue (t1, s1, cs) -> Coq_sterm_extractvalue (t1,
        (subst_tt id0 s0 s1), cs)
    | Coq_sterm_insertvalue (t1, s1, t2, s2, cs) -> Coq_sterm_insertvalue
        (t1, (subst_tt id0 s0 s1), t2, (subst_tt id0 s0 s2), cs)
    | Coq_sterm_malloc (m1, t1, s1, align0) -> Coq_sterm_malloc
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_sterm_alloca (m1, t1, s1, align0) -> Coq_sterm_alloca
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_sterm_load (m1, t1, s1, align0) -> Coq_sterm_load
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_sterm_gep (inbounds0, t1, s1, ls2) -> Coq_sterm_gep (inbounds0, t1,
        (subst_tt id0 s0 s1), (subst_tlt id0 s0 ls2))
    | Coq_sterm_trunc (truncop0, t1, s1, t2) -> Coq_sterm_trunc (truncop0,
        t1, (subst_tt id0 s0 s1), t2)
    | Coq_sterm_ext (extop0, t1, s1, t2) -> Coq_sterm_ext (extop0, t1,
        (subst_tt id0 s0 s1), t2)
    | Coq_sterm_cast (castop0, t1, s1, t2) -> Coq_sterm_cast (castop0, t1,
        (subst_tt id0 s0 s1), t2)
    | Coq_sterm_icmp (cond0, t1, s1, s2) -> Coq_sterm_icmp (cond0, t1,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_fcmp (cond0, fp1, s1, s2) -> Coq_sterm_fcmp (cond0, fp1,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_phi (t1, lsl1) -> Coq_sterm_phi (t1,
        (subst_tltl id0 s0 lsl1))
    | Coq_sterm_select (s1, t1, s2, s3) -> Coq_sterm_select
        ((subst_tt id0 s0 s1), t1, (subst_tt id0 s0 s2),
        (subst_tt id0 s0 s3))
  
  (** val subst_tlt : LLVMsyntax.id -> sterm -> list_sterm -> list_sterm **)
  
  and subst_tlt id0 s0 = function
    | Nil_list_sterm -> Nil_list_sterm
    | Cons_list_sterm (sz0, s, ls') -> Cons_list_sterm (sz0,
        (subst_tt id0 s0 s), (subst_tlt id0 s0 ls'))
  
  (** val subst_tltl :
      LLVMsyntax.id -> sterm -> list_sterm_l -> list_sterm_l **)
  
  and subst_tltl id0 s0 = function
    | Nil_list_sterm_l -> Nil_list_sterm_l
    | Cons_list_sterm_l (s, l0, ls') -> Cons_list_sterm_l
        ((subst_tt id0 s0 s), l0, (subst_tltl id0 s0 ls'))
  
  (** val subst_tm : LLVMsyntax.id -> sterm -> smem -> smem **)
  
  and subst_tm id0 s0 = function
    | Coq_smem_init -> Coq_smem_init
    | Coq_smem_malloc (m1, t1, sz0, align0) -> Coq_smem_malloc
        ((subst_tm id0 s0 m1), t1, sz0, align0)
    | Coq_smem_free (m1, t1, s1) -> Coq_smem_free (
        (subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1))
    | Coq_smem_alloca (m1, t1, sz0, align0) -> Coq_smem_alloca
        ((subst_tm id0 s0 m1), t1, sz0, align0)
    | Coq_smem_load (m1, t1, s1, align0) -> Coq_smem_load
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_smem_store (m1, t1, s1, s2, align0) -> Coq_smem_store
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1),
        (subst_tt id0 s0 s2), align0)
  
  (** val subst_mt : smap -> sterm -> sterm **)
  
  let rec subst_mt sm s =
    match sm with
      | [] -> s
      | p::sm' -> let id0,s0 = p in subst_mt sm' (subst_tt id0 s0 s)
  
  (** val subst_mm : smap -> smem -> smem **)
  
  let rec subst_mm sm m =
    match sm with
      | [] -> m
      | p::sm' -> let id0,s0 = p in subst_mm sm' (subst_tm id0 s0 m)
 end

