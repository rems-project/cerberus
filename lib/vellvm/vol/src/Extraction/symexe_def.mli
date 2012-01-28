open CoqEqDec
open Datatypes
open MetatheoryAtom
open Alist
open Genericvalues
open Syntax
open Trace

type __ = Obj.t

module SimpleSE : 
 sig 
  type coq_DGVMap = Opsem.Opsem.coq_GVsMap
  
  type coq_ExecutionContext = { coq_CurBB : LLVMsyntax.block;
                                coq_Locals : coq_DGVMap;
                                coq_Allocas : LLVMgv.mblock list }
  
  val coq_ExecutionContext_rect :
    (LLVMsyntax.block -> coq_DGVMap -> LLVMgv.mblock list -> 'a1) ->
    coq_ExecutionContext -> 'a1
  
  val coq_ExecutionContext_rec :
    (LLVMsyntax.block -> coq_DGVMap -> LLVMgv.mblock list -> 'a1) ->
    coq_ExecutionContext -> 'a1
  
  val coq_CurBB : coq_ExecutionContext -> LLVMsyntax.block
  
  val coq_Locals : coq_ExecutionContext -> coq_DGVMap
  
  val coq_Allocas : coq_ExecutionContext -> LLVMgv.mblock list
  
  type coq_State = { coq_Frame : coq_ExecutionContext; coq_Mem : LLVMgv.mem }
  
  val coq_State_rect :
    (coq_ExecutionContext -> LLVMgv.mem -> 'a1) -> coq_State -> 'a1
  
  val coq_State_rec :
    (coq_ExecutionContext -> LLVMgv.mem -> 'a1) -> coq_State -> 'a1
  
  val coq_Frame : coq_State -> coq_ExecutionContext
  
  val coq_Mem : coq_State -> LLVMgv.mem
  
  val isCall : LLVMsyntax.cmd -> bool
  
  type nbranch =
    LLVMsyntax.cmd
    (* singleton inductive, whose constructor was mkNB *)
  
  val nbranch_rect : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1
  
  val nbranch_rec : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1
  
  val nbranching_cmd : nbranch -> LLVMsyntax.cmd
  
  type subblock = { coq_NBs : nbranch list; call_cmd : LLVMsyntax.cmd }
  
  val subblock_rect :
    (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1
  
  val subblock_rec :
    (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1
  
  val coq_NBs : subblock -> nbranch list
  
  val call_cmd : subblock -> LLVMsyntax.cmd
  
  val isCall_dec : LLVMsyntax.cmd -> bool
  
  val cmds2sbs : LLVMsyntax.cmds -> subblock list*nbranch list
  
  val nbranchs2cmds : nbranch list -> LLVMsyntax.cmd list
  
  val cmd2nbranch : LLVMsyntax.cmd -> nbranch option
  
  val cmds2nbranchs : LLVMsyntax.cmd list -> nbranch list option
  
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
  
  val sterm_rect :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm -> 'a1
    -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    sterm -> 'a1 -> list_sterm -> 'a1) -> (LLVMsyntax.truncop ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fcond ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> list_sterm_l -> 'a1) -> (sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> sterm -> 'a1
  
  val sterm_rec :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm -> 'a1
    -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    sterm -> 'a1 -> list_sterm -> 'a1) -> (LLVMsyntax.truncop ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ ->
    'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fcond ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> list_sterm_l -> 'a1) -> (sterm -> 'a1 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> sterm -> 'a1
  
  val list_sterm_rect :
    'a1 -> (LLVMsyntax.sz -> sterm -> list_sterm -> 'a1 -> 'a1) -> list_sterm
    -> 'a1
  
  val list_sterm_rec :
    'a1 -> (LLVMsyntax.sz -> sterm -> list_sterm -> 'a1 -> 'a1) -> list_sterm
    -> 'a1
  
  val list_sterm_l_rect :
    'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
    list_sterm_l -> 'a1
  
  val list_sterm_l_rec :
    'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
    list_sterm_l -> 'a1
  
  val smem_rect :
    'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1) -> (smem -> 'a1
    -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1 ->
    LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1 ->
    LLVMsyntax.typ -> sterm -> sterm -> LLVMsyntax.align -> 'a1) -> smem ->
    'a1
  
  val smem_rec :
    'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align ->
    'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1) -> (smem -> 'a1
    -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1 ->
    LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1 ->
    LLVMsyntax.typ -> sterm -> sterm -> LLVMsyntax.align -> 'a1) -> smem ->
    'a1
  
  val sframe_rect :
    'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> sterm ->
    LLVMsyntax.align -> 'a1) -> sframe -> 'a1
  
  val sframe_rec :
    'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> sterm ->
    LLVMsyntax.align -> 'a1) -> sframe -> 'a1
  
  val sframe_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm ->
    'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond ->
    LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm
    -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) ->
    (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1)
    -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
    'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align
    -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 ->
    sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a5) -> sframe -> 'a5
  
  val smem_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm ->
    'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond ->
    LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm
    -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) ->
    (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1)
    -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
    'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align
    -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 ->
    sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a5) -> smem -> 'a4
  
  val list_sterm_l_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm ->
    'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond ->
    LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm
    -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) ->
    (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1)
    -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
    'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align
    -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 ->
    sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a5) -> list_sterm_l -> 'a3
  
  val list_sterm_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm ->
    'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond ->
    LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm
    -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) ->
    (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1)
    -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
    'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align
    -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 ->
    sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a5) -> list_sterm -> 'a2
  
  val sterm_rec2 :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm ->
    'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond ->
    LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm
    -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) ->
    (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1)
    -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
    'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align
    -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 ->
    sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a5) -> sterm -> 'a1
  
  val se_mutrec :
    (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm ->
    'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
    (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.list_const -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm
    -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a4 ->
    LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sterm ->
    'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm ->
    'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ ->
    sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond ->
    LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
    (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm
    -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a3 -> 'a1) ->
    (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1)
    -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sterm -> 'a2 -> 'a2) ->
    'a3 -> (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a3 -> 'a3) ->
    'a4 -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align
    -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a4) ->
    (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm -> 'a1 ->
    LLVMsyntax.align -> 'a4) -> (smem -> 'a4 -> LLVMsyntax.typ -> sterm ->
    'a1 -> sterm -> 'a1 -> LLVMsyntax.align -> 'a4) -> 'a5 -> (smem -> 'a4 ->
    sframe -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
    'a5) -> ((((sterm -> 'a1)*(list_sterm -> 'a2))*(list_sterm_l ->
    'a3))*(smem -> 'a4))*(sframe -> 'a5)
  
  val map_list_sterm :
    (LLVMsyntax.sz -> sterm -> 'a1) -> list_sterm -> 'a1 list
  
  val make_list_sterm : (LLVMsyntax.sz*sterm) list -> list_sterm
  
  val unmake_list_sterm : list_sterm -> (LLVMsyntax.sz*sterm) list
  
  val nth_list_sterm : nat -> list_sterm -> (LLVMsyntax.sz*sterm) option
  
  val app_list_sterm : list_sterm -> list_sterm -> list_sterm
  
  val map_list_sterm_l :
    (sterm -> LLVMsyntax.l -> 'a1) -> list_sterm_l -> 'a1 list
  
  val make_list_sterm_l : (sterm*LLVMsyntax.l) list -> list_sterm_l
  
  val unmake_list_sterm_l : list_sterm_l -> (sterm*LLVMsyntax.l) list
  
  val nth_list_sterm_l : nat -> list_sterm_l -> (sterm*LLVMsyntax.l) option
  
  val app_list_sterm_l : list_sterm_l -> list_sterm_l -> list_sterm_l
  
  type sterminator =
    | Coq_stmn_return of LLVMsyntax.id * LLVMsyntax.typ * sterm
    | Coq_stmn_return_void of LLVMsyntax.id
    | Coq_stmn_br of LLVMsyntax.id * sterm * LLVMsyntax.l * LLVMsyntax.l
    | Coq_stmn_br_uncond of LLVMsyntax.id * LLVMsyntax.l
    | Coq_stmn_unreachable of LLVMsyntax.id
  
  val sterminator_rect :
    (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
    'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
    -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
    sterminator -> 'a1
  
  val sterminator_rec :
    (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
    'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
    -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
    sterminator -> 'a1
  
  type smap = (AtomImpl.atom*sterm) list
  
  type sstate = { coq_STerms : smap; coq_SMem : smem; coq_SFrame : 
                  sframe; coq_SEffects : sterm list }
  
  val sstate_rect :
    (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1
  
  val sstate_rec :
    (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1
  
  val coq_STerms : sstate -> smap
  
  val coq_SMem : sstate -> smem
  
  val coq_SFrame : sstate -> sframe
  
  val coq_SEffects : sstate -> sterm list
  
  val sstate_init : sstate
  
  val lookupSmap : smap -> LLVMsyntax.id -> sterm
  
  val value2Sterm : smap -> LLVMsyntax.value -> sterm
  
  val list_param__list_typ_subst_sterm :
    LLVMsyntax.params -> smap ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*sterm) list
  
  val se_call :
    LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs
    -> LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> sstate
  
  val se_cmd : sstate -> nbranch -> sstate
  
  val _se_phinodes : sstate -> sstate -> LLVMsyntax.phinode list -> sstate
  
  val se_phinodes : sstate -> LLVMsyntax.phinode list -> sstate
  
  val se_cmds : sstate -> nbranch list -> sstate
  
  val se_terminator : sstate -> LLVMsyntax.terminator -> sterminator
  
  val seffects_denote_trace_rect : 'a1 -> sterm list -> trace -> 'a1
  
  val seffects_denote_trace_rec : 'a1 -> sterm list -> trace -> 'a1
  
  val subst_tt : LLVMsyntax.id -> sterm -> sterm -> sterm
  
  val subst_tlt : LLVMsyntax.id -> sterm -> list_sterm -> list_sterm
  
  val subst_tltl : LLVMsyntax.id -> sterm -> list_sterm_l -> list_sterm_l
  
  val subst_tm : LLVMsyntax.id -> sterm -> smem -> smem
  
  val subst_mt : smap -> sterm -> sterm
  
  val subst_mm : smap -> smem -> smem
 end

