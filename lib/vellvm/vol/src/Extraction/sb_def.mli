open BinInt
open BinPos
open Coqlib
open Datatypes
open Integers
open List0
open Memory
open MetatheoryAtom
open Values
open Alist
open Genericvalues
open Infrastructure
open Syntax
open Targetdata

module SBspecAux : 
 sig 
  type metadata = { md_blk : block; md_bofs : Int.int; md_eofs : Int.int }
  
  val metadata_rect : (block -> Int.int -> Int.int -> 'a1) -> metadata -> 'a1
  
  val metadata_rec : (block -> Int.int -> Int.int -> 'a1) -> metadata -> 'a1
  
  val md_blk : metadata -> block
  
  val md_bofs : metadata -> Int.int
  
  val md_eofs : metadata -> Int.int
  
  type rmetadata = (LLVMsyntax.id*metadata) list
  
  val bound2MD : LLVMgv.mblock -> LLVMsyntax.sz -> coq_Z -> metadata
  
  val i8 : LLVMsyntax.typ
  
  val p8 : LLVMsyntax.typ
  
  val get_const_metadata :
    LLVMsyntax.const -> (LLVMsyntax.const*LLVMsyntax.const) option
  
  val null_md : metadata
  
  val get_reg_metadata :
    LLVMtd.coq_TargetData -> LLVMgv.coq_GVMap -> rmetadata ->
    LLVMsyntax.value -> metadata option
  
  val assert_mptr :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> LLVMgv.coq_GenericValue ->
    metadata -> bool
  
  type mmetadata = block -> Int.int -> metadata option
  
  val get_mem_metadata :
    LLVMtd.coq_TargetData -> (block -> Int.int -> metadata option) ->
    LLVMgv.coq_GenericValue -> metadata
  
  val set_mem_metadata :
    LLVMtd.coq_TargetData -> mmetadata -> LLVMgv.coq_GenericValue -> metadata
    -> mmetadata
 end

module SBspec : 
 sig 
  val prop_reg_metadata :
    Opsem.coq_GenericValues -> Opsem.coq_GVsT coq_AssocList ->
    SBspecAux.metadata coq_AssocList -> AtomImpl.atom -> Opsem.coq_GVsT ->
    SBspecAux.metadata -> Opsem.Opsem.coq_GVsMap*SBspecAux.rmetadata
  
  type coq_GVsMap = (LLVMsyntax.id*Opsem.coq_GVsT) list
  
  type coq_ExecutionContext = { coq_CurFunction : LLVMsyntax.fdef;
                                coq_CurBB : LLVMsyntax.block;
                                coq_CurCmds : LLVMsyntax.cmds;
                                coq_Terminator : LLVMsyntax.terminator;
                                coq_Locals : coq_GVsMap;
                                coq_Rmap : SBspecAux.rmetadata;
                                coq_Allocas : LLVMgv.mblock list }
  
  val coq_ExecutionContext_rect :
    Opsem.coq_GenericValues -> (LLVMsyntax.fdef -> LLVMsyntax.block ->
    LLVMsyntax.cmds -> LLVMsyntax.terminator -> coq_GVsMap ->
    SBspecAux.rmetadata -> LLVMgv.mblock list -> 'a1) -> coq_ExecutionContext
    -> 'a1
  
  val coq_ExecutionContext_rec :
    Opsem.coq_GenericValues -> (LLVMsyntax.fdef -> LLVMsyntax.block ->
    LLVMsyntax.cmds -> LLVMsyntax.terminator -> coq_GVsMap ->
    SBspecAux.rmetadata -> LLVMgv.mblock list -> 'a1) -> coq_ExecutionContext
    -> 'a1
  
  val coq_CurFunction :
    Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.fdef
  
  val coq_CurBB :
    Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.block
  
  val coq_CurCmds :
    Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.cmds
  
  val coq_Terminator :
    Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.terminator
  
  val coq_Locals :
    Opsem.coq_GenericValues -> coq_ExecutionContext -> coq_GVsMap
  
  val coq_Rmap :
    Opsem.coq_GenericValues -> coq_ExecutionContext -> SBspecAux.rmetadata
  
  val coq_Allocas :
    Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMgv.mblock list
  
  type coq_ECStack = coq_ExecutionContext list
  
  type coq_State = { coq_ECS : coq_ECStack; coq_Mem : 
                     LLVMgv.mem; coq_Mmap : SBspecAux.mmetadata }
  
  val coq_State_rect :
    Opsem.coq_GenericValues -> (coq_ECStack -> LLVMgv.mem ->
    SBspecAux.mmetadata -> 'a1) -> coq_State -> 'a1
  
  val coq_State_rec :
    Opsem.coq_GenericValues -> (coq_ECStack -> LLVMgv.mem ->
    SBspecAux.mmetadata -> 'a1) -> coq_State -> 'a1
  
  val coq_ECS : Opsem.coq_GenericValues -> coq_State -> coq_ECStack
  
  val coq_Mem : Opsem.coq_GenericValues -> coq_State -> LLVMgv.mem
  
  val coq_Mmap : Opsem.coq_GenericValues -> coq_State -> SBspecAux.mmetadata
  
  val getIncomingValuesForBlockFromPHINodes :
    Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.phinode
    list -> LLVMsyntax.block -> LLVMgv.coq_GVMap -> coq_GVsMap ->
    SBspecAux.rmetadata -> ((LLVMsyntax.id*Opsem.coq_GVsT)*SBspecAux.metadata
    option) list option
  
  val updateValuesForNewBlock :
    Opsem.coq_GenericValues ->
    ((LLVMsyntax.id*Opsem.coq_GVsT)*SBspecAux.metadata option) list ->
    coq_GVsMap -> SBspecAux.rmetadata -> coq_GVsMap*SBspecAux.rmetadata
  
  val switchToNewBasicBlock :
    Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.block ->
    LLVMsyntax.block -> LLVMgv.coq_GVMap -> coq_GVsMap -> SBspecAux.rmetadata
    -> (coq_GVsMap*SBspecAux.rmetadata) option
  
  val returnResult :
    Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ ->
    LLVMsyntax.value -> coq_GVsMap -> SBspecAux.rmetadata -> LLVMgv.coq_GVMap
    -> (Opsem.coq_GVsT*SBspecAux.metadata) option
  
  val returnUpdateLocals :
    Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.cmd ->
    LLVMsyntax.typ -> LLVMsyntax.value -> coq_GVsMap -> coq_GVsMap ->
    SBspecAux.rmetadata -> SBspecAux.rmetadata -> LLVMgv.coq_GVMap ->
    (coq_GVsMap*SBspecAux.rmetadata) option
  
  val exCallUpdateLocals :
    Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ ->
    bool -> LLVMsyntax.id -> LLVMgv.coq_GenericValue option -> coq_GVsMap ->
    SBspecAux.rmetadata -> (coq_GVsMap*SBspecAux.rmetadata) option
  
  val params2GVs :
    Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.params ->
    coq_GVsMap -> LLVMgv.coq_GVMap -> SBspecAux.rmetadata ->
    (Opsem.coq_GVsT*SBspecAux.metadata option) list option
  
  val _initializeFrameValues :
    Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.args ->
    (Opsem.coq_GVsT*SBspecAux.metadata option) list -> coq_GVsMap ->
    SBspecAux.rmetadata -> (coq_GVsMap*SBspecAux.rmetadata) option
  
  val initLocals :
    Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.args ->
    (Opsem.coq_GVsT*SBspecAux.metadata option) list ->
    (coq_GVsMap*SBspecAux.rmetadata) option
  
  val s_isFinialState : Opsem.coq_GenericValues -> coq_State -> bool
  
  val sbEC__EC :
    Opsem.coq_GenericValues -> coq_ExecutionContext ->
    Opsem.Opsem.coq_ExecutionContext
  
  val sbECs__ECs :
    Opsem.coq_GenericValues -> coq_ECStack -> Opsem.Opsem.coq_ECStack
  
  val sbState__State :
    Opsem.coq_GenericValues -> coq_State -> Opsem.Opsem.coq_State
 end

