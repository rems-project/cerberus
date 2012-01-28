open Alist
open Genericvalues
open Infrastructure
open Monad
open Syntax
open Targetdata

type __ = Obj.t

type coq_GenericValues = { cgv2gvs : (LLVMgv.coq_GenericValue ->
                                     LLVMsyntax.typ -> __);
                           gv2gvs : (LLVMgv.coq_GenericValue ->
                                    LLVMsyntax.typ -> __);
                           lift_op1 : ((LLVMgv.coq_GenericValue ->
                                      LLVMgv.coq_GenericValue option) -> __
                                      -> LLVMsyntax.typ -> __ option);
                           lift_op2 : ((LLVMgv.coq_GenericValue ->
                                      LLVMgv.coq_GenericValue ->
                                      LLVMgv.coq_GenericValue option) -> __
                                      -> __ -> LLVMsyntax.typ -> __ option) }

val coq_GenericValues_rect :
  (__ -> __ -> __ -> (LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> __) ->
  (LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> __) ->
  ((LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> __ ->
  LLVMsyntax.typ -> __ option) -> ((LLVMgv.coq_GenericValue ->
  LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> __ -> __ ->
  LLVMsyntax.typ -> __ option) -> __ -> __ -> __ -> __ -> __ -> __ -> __ ->
  __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> coq_GenericValues -> 'a1

val coq_GenericValues_rec :
  (__ -> __ -> __ -> (LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> __) ->
  (LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> __) ->
  ((LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> __ ->
  LLVMsyntax.typ -> __ option) -> ((LLVMgv.coq_GenericValue ->
  LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> __ -> __ ->
  LLVMsyntax.typ -> __ option) -> __ -> __ -> __ -> __ -> __ -> __ -> __ ->
  __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> coq_GenericValues -> 'a1

type coq_GVsT = __

val cgv2gvs :
  coq_GenericValues -> LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> coq_GVsT

val gv2gvs :
  coq_GenericValues -> LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> coq_GVsT

val lift_op1 :
  coq_GenericValues -> (LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue
  option) -> coq_GVsT -> LLVMsyntax.typ -> coq_GVsT option

val lift_op2 :
  coq_GenericValues -> (LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue ->
  LLVMgv.coq_GenericValue option) -> coq_GVsT -> coq_GVsT -> LLVMsyntax.typ
  -> coq_GVsT option

module OpsemAux : 
 sig 
  val lookupFdefViaGVFromFunTable :
    LLVMgv.coq_GVMap -> LLVMgv.coq_GenericValue -> LLVMsyntax.id option
  
  val lookupFdefViaPtr :
    LLVMsyntax.products -> LLVMgv.coq_GVMap -> LLVMgv.coq_GenericValue ->
    LLVMsyntax.fdef option
  
  val lookupExFdecViaPtr :
    LLVMsyntax.products -> LLVMgv.coq_GVMap -> LLVMgv.coq_GenericValue ->
    LLVMsyntax.fdec option
  
  val callExternalFunction :
    LLVMgv.mem -> LLVMsyntax.id -> LLVMgv.coq_GenericValue list ->
    (LLVMgv.coq_GenericValue option*LLVMgv.mem) option
  
  val initGlobal :
    LLVMtd.coq_TargetData -> LLVMgv.coq_GVMap -> LLVMgv.mem -> LLVMsyntax.id
    -> LLVMsyntax.typ -> LLVMsyntax.const -> LLVMsyntax.align ->
    (LLVMgv.coq_GenericValue*LLVMgv.mem) option
  
  val initTargetData :
    LLVMsyntax.layouts -> LLVMsyntax.namedts -> LLVMgv.mem ->
    LLVMtd.coq_TargetData
  
  val getExternalGlobal :
    LLVMgv.mem -> LLVMsyntax.id -> LLVMgv.coq_GenericValue option
  
  val initFunTable :
    LLVMgv.mem -> LLVMsyntax.id -> LLVMgv.coq_GenericValue option
  
  val genGlobalAndInitMem :
    LLVMtd.coq_TargetData -> LLVMsyntax.product list -> LLVMgv.coq_GVMap ->
    LLVMgv.coq_GVMap -> LLVMgv.mem ->
    ((LLVMgv.coq_GVMap*LLVMgv.coq_GVMap)*LLVMgv.mem) option
  
  type coq_Config = { coq_CurSystem : LLVMsyntax.system;
                      coq_CurTargetData : LLVMtd.coq_TargetData;
                      coq_CurProducts : LLVMsyntax.product list;
                      coq_Globals : LLVMgv.coq_GVMap;
                      coq_FunTable : LLVMgv.coq_GVMap }
  
  val coq_Config_rect :
    (LLVMsyntax.system -> LLVMtd.coq_TargetData -> LLVMsyntax.product list ->
    LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> 'a1) -> coq_Config -> 'a1
  
  val coq_Config_rec :
    (LLVMsyntax.system -> LLVMtd.coq_TargetData -> LLVMsyntax.product list ->
    LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> 'a1) -> coq_Config -> 'a1
  
  val coq_CurSystem : coq_Config -> LLVMsyntax.system
  
  val coq_CurTargetData : coq_Config -> LLVMtd.coq_TargetData
  
  val coq_CurProducts : coq_Config -> LLVMsyntax.product list
  
  val coq_Globals : coq_Config -> LLVMgv.coq_GVMap
  
  val coq_FunTable : coq_Config -> LLVMgv.coq_GVMap
  
  type bConfig = { bCurSystem : LLVMsyntax.system;
                   bCurTargetData : LLVMtd.coq_TargetData;
                   bCurProducts : LLVMsyntax.product list;
                   bGlobals : LLVMgv.coq_GVMap; bFunTable : 
                   LLVMgv.coq_GVMap; bCurFunction : 
                   LLVMsyntax.fdef }
  
  val bConfig_rect :
    (LLVMsyntax.system -> LLVMtd.coq_TargetData -> LLVMsyntax.product list ->
    LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> LLVMsyntax.fdef -> 'a1) ->
    bConfig -> 'a1
  
  val bConfig_rec :
    (LLVMsyntax.system -> LLVMtd.coq_TargetData -> LLVMsyntax.product list ->
    LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> LLVMsyntax.fdef -> 'a1) ->
    bConfig -> 'a1
  
  val bCurSystem : bConfig -> LLVMsyntax.system
  
  val bCurTargetData : bConfig -> LLVMtd.coq_TargetData
  
  val bCurProducts : bConfig -> LLVMsyntax.product list
  
  val bGlobals : bConfig -> LLVMgv.coq_GVMap
  
  val bFunTable : bConfig -> LLVMgv.coq_GVMap
  
  val bCurFunction : bConfig -> LLVMsyntax.fdef
 end

module Opsem : 
 sig 
  type coq_GVsMap = (LLVMsyntax.id*coq_GVsT) list
  
  val const2GV :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMgv.coq_GVMap ->
    LLVMsyntax.const -> coq_GVsT option
  
  val getOperandValue :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.value ->
    coq_GVsMap -> LLVMgv.coq_GVMap -> coq_GVsT option
  
  type coq_ExecutionContext = { coq_CurFunction : LLVMsyntax.fdef;
                                coq_CurBB : LLVMsyntax.block;
                                coq_CurCmds : LLVMsyntax.cmds;
                                coq_Terminator : LLVMsyntax.terminator;
                                coq_Locals : coq_GVsMap;
                                coq_Allocas : LLVMgv.mblock list }
  
  val coq_ExecutionContext_rect :
    coq_GenericValues -> (LLVMsyntax.fdef -> LLVMsyntax.block ->
    LLVMsyntax.cmds -> LLVMsyntax.terminator -> coq_GVsMap -> LLVMgv.mblock
    list -> 'a1) -> coq_ExecutionContext -> 'a1
  
  val coq_ExecutionContext_rec :
    coq_GenericValues -> (LLVMsyntax.fdef -> LLVMsyntax.block ->
    LLVMsyntax.cmds -> LLVMsyntax.terminator -> coq_GVsMap -> LLVMgv.mblock
    list -> 'a1) -> coq_ExecutionContext -> 'a1
  
  val coq_CurFunction :
    coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.fdef
  
  val coq_CurBB :
    coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.block
  
  val coq_CurCmds :
    coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.cmds
  
  val coq_Terminator :
    coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.terminator
  
  val coq_Locals : coq_GenericValues -> coq_ExecutionContext -> coq_GVsMap
  
  val coq_Allocas :
    coq_GenericValues -> coq_ExecutionContext -> LLVMgv.mblock list
  
  type coq_ECStack = coq_ExecutionContext list
  
  type coq_State = { coq_ECS : coq_ECStack; coq_Mem : LLVMgv.mem }
  
  val coq_State_rect :
    coq_GenericValues -> (coq_ECStack -> LLVMgv.mem -> 'a1) -> coq_State ->
    'a1
  
  val coq_State_rec :
    coq_GenericValues -> (coq_ECStack -> LLVMgv.mem -> 'a1) -> coq_State ->
    'a1
  
  val coq_ECS : coq_GenericValues -> coq_State -> coq_ECStack
  
  val coq_Mem : coq_GenericValues -> coq_State -> LLVMgv.mem
  
  val getIncomingValuesForBlockFromPHINodes :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.phinode list ->
    LLVMsyntax.block -> LLVMgv.coq_GVMap -> coq_GVsMap ->
    (LLVMsyntax.id*coq_GVsT) list option
  
  val updateValuesForNewBlock :
    coq_GenericValues -> (LLVMsyntax.id*coq_GVsT) list -> coq_GVsMap ->
    coq_GVsMap
  
  val switchToNewBasicBlock :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.block ->
    LLVMsyntax.block -> LLVMgv.coq_GVMap -> coq_GVsMap -> coq_GVsMap option
  
  val params2GVs :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.params ->
    coq_GVsMap -> LLVMgv.coq_GVMap -> coq_GVsT list option
  
  val exCallUpdateLocals :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ -> bool ->
    LLVMsyntax.id -> LLVMgv.coq_GenericValue option -> coq_GVsMap ->
    coq_GVsMap option
  
  val values2GVs :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.list_sz_value ->
    coq_GVsMap -> LLVMgv.coq_GVMap -> coq_GVsT list option
  
  val _initializeFrameValues :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.args -> coq_GVsT
    list -> coq_GVsMap -> coq_GVsMap option
  
  val initLocals :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.args -> coq_GVsT
    list -> coq_GVsMap option
  
  val coq_BOP :
    coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
    LLVMgv.coq_GVMap -> LLVMsyntax.bop -> LLVMsyntax.sz -> LLVMsyntax.value
    -> LLVMsyntax.value -> coq_GVsT option
  
  val coq_FBOP :
    coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
    LLVMgv.coq_GVMap -> LLVMsyntax.fbop -> LLVMsyntax.floating_point ->
    LLVMsyntax.value -> LLVMsyntax.value -> coq_GVsT option
  
  val coq_ICMP :
    coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
    LLVMgv.coq_GVMap -> LLVMsyntax.cond -> LLVMsyntax.typ -> LLVMsyntax.value
    -> LLVMsyntax.value -> coq_GVsT option
  
  val coq_FCMP :
    coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
    LLVMgv.coq_GVMap -> LLVMsyntax.fcond -> LLVMsyntax.floating_point ->
    LLVMsyntax.value -> LLVMsyntax.value -> coq_GVsT option
  
  val coq_CAST :
    coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
    LLVMgv.coq_GVMap -> LLVMsyntax.castop -> LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.typ -> coq_GVsT option
  
  val coq_TRUNC :
    coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
    LLVMgv.coq_GVMap -> LLVMsyntax.truncop -> LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.typ -> coq_GVsT option
  
  val coq_EXT :
    coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
    LLVMgv.coq_GVMap -> LLVMsyntax.extop -> LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.typ -> coq_GVsT option
  
  val coq_GEP :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GVsT
    -> LLVMgv.coq_GenericValue list -> bool -> coq_GVsT option
  
  val extractGenericValue :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GVsT
    -> LLVMsyntax.list_const -> coq_GVsT option
  
  val insertGenericValue :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GVsT
    -> LLVMsyntax.list_const -> LLVMsyntax.typ -> coq_GVsT -> coq_GVsT option
  
  val returnUpdateLocals :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.cmd ->
    LLVMsyntax.value -> coq_GVsMap -> coq_GVsMap -> LLVMgv.coq_GVMap ->
    coq_GVsMap option
  
  val s_genInitState :
    coq_GenericValues -> LLVMsyntax.system -> LLVMsyntax.id -> coq_GVsT list
    -> LLVMgv.mem -> (OpsemAux.coq_Config*coq_State) option
  
  val s_isFinialState : coq_GenericValues -> coq_State -> bool
  
  val callUpdateLocals :
    coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ -> bool ->
    LLVMsyntax.id -> LLVMsyntax.value option -> coq_GVsMap -> coq_GVsMap ->
    LLVMgv.coq_GVMap -> coq_GVsMap option
  
  type bExecutionContext = { bCurBB : LLVMsyntax.block;
                             bCurCmds : LLVMsyntax.cmds;
                             bTerminator : LLVMsyntax.terminator;
                             bLocals : coq_GVsMap;
                             bAllocas : LLVMgv.mblock list; bMem : 
                             LLVMgv.mem }
  
  val bExecutionContext_rect :
    coq_GenericValues -> (LLVMsyntax.block -> LLVMsyntax.cmds ->
    LLVMsyntax.terminator -> coq_GVsMap -> LLVMgv.mblock list -> LLVMgv.mem
    -> 'a1) -> bExecutionContext -> 'a1
  
  val bExecutionContext_rec :
    coq_GenericValues -> (LLVMsyntax.block -> LLVMsyntax.cmds ->
    LLVMsyntax.terminator -> coq_GVsMap -> LLVMgv.mblock list -> LLVMgv.mem
    -> 'a1) -> bExecutionContext -> 'a1
  
  val bCurBB : coq_GenericValues -> bExecutionContext -> LLVMsyntax.block
  
  val bCurCmds : coq_GenericValues -> bExecutionContext -> LLVMsyntax.cmds
  
  val bTerminator :
    coq_GenericValues -> bExecutionContext -> LLVMsyntax.terminator
  
  val bLocals : coq_GenericValues -> bExecutionContext -> coq_GVsMap
  
  val bAllocas : coq_GenericValues -> bExecutionContext -> LLVMgv.mblock list
  
  val bMem : coq_GenericValues -> bExecutionContext -> LLVMgv.mem
  
  val b_genInitState :
    coq_GenericValues -> LLVMsyntax.system -> LLVMsyntax.id -> coq_GVsT list
    -> LLVMgv.mem -> (OpsemAux.bConfig*bExecutionContext) option
  
  val b_isFinialState : coq_GenericValues -> bExecutionContext -> bool
 end

