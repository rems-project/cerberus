open AST
open BinInt
open Coqlib
open Datatypes
open Integers
open Memdata
open Memory
open Peano
open Values
open Alist
open Syntax
open Targetdata

module LLVMgv : 
 sig 
  type moffset = Int.int
  
  type mem = Llvmcaml.GenericValue.mem
  
  type coq_GenericValue = Llvmcaml.GenericValue.t
  
  type coq_GVMap = (LLVMsyntax.id*coq_GenericValue) list
  
  type mblock = Llvmcaml.GenericValue.t
  
  type mptr = Llvmcaml.GenericValue.t
  
  val null : coq_GenericValue
  
  val eq_gv : coq_GenericValue -> coq_GenericValue -> bool
  
  val uninits : nat -> coq_GenericValue
  
  val gundef :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue option
  
  val coq_GV2val :
    LLVMtd.coq_TargetData -> coq_GenericValue -> coq_val option
  
  val coq_GV2int :
    LLVMtd.coq_TargetData -> LLVMsyntax.sz -> coq_GenericValue -> coq_Z
    option
  
  val coq_GV2ptr :
    LLVMtd.coq_TargetData -> LLVMsyntax.sz -> coq_GenericValue -> coq_val
    option
  
  val val2GV :
    LLVMtd.coq_TargetData -> coq_val -> memory_chunk -> coq_GenericValue
  
  val ptr2GV : LLVMtd.coq_TargetData -> coq_val -> coq_GenericValue
  
  val blk2GV : LLVMtd.coq_TargetData -> mblock -> coq_GenericValue
  
  val isGVZero : LLVMtd.coq_TargetData -> coq_GenericValue -> bool
  
  val mgep :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_val -> coq_Z list ->
    coq_val option
  
  val sizeGenericValue : coq_GenericValue -> nat
  
  val splitGenericValue :
    coq_GenericValue -> coq_Z -> (coq_GenericValue*coq_GenericValue) option
  
  val mget :
    LLVMtd.coq_TargetData -> coq_GenericValue -> coq_Z -> LLVMsyntax.typ ->
    coq_GenericValue option
  
  val mset :
    LLVMtd.coq_TargetData -> coq_GenericValue -> coq_Z -> LLVMsyntax.typ ->
    coq_GenericValue -> coq_GenericValue option
  
  val coq_GVs2Nats :
    LLVMtd.coq_TargetData -> coq_GenericValue list -> coq_Z list option
  
  val extractGenericValue :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue ->
    LLVMsyntax.list_const -> coq_GenericValue option
  
  val insertGenericValue :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue ->
    LLVMsyntax.list_const -> LLVMsyntax.typ -> coq_GenericValue ->
    coq_GenericValue option
  
  val mtrunc :
    LLVMtd.coq_TargetData -> LLVMsyntax.truncop -> LLVMsyntax.typ ->
    LLVMsyntax.typ -> coq_GenericValue -> coq_GenericValue option
  
  val mbop :
    LLVMtd.coq_TargetData -> LLVMsyntax.bop -> LLVMsyntax.sz ->
    coq_GenericValue -> coq_GenericValue -> coq_GenericValue option
  
  val mfbop :
    LLVMtd.coq_TargetData -> LLVMsyntax.fbop -> LLVMsyntax.floating_point ->
    coq_GenericValue -> coq_GenericValue -> coq_GenericValue option
  
  val mptrtoint :
    LLVMtd.coq_TargetData -> mem -> coq_GenericValue -> nat ->
    coq_GenericValue option
  
  val mbitcast :
    LLVMsyntax.typ -> coq_GenericValue -> LLVMsyntax.typ -> coq_GenericValue
    option
  
  val minttoptr :
    LLVMtd.coq_TargetData -> mem -> coq_GenericValue -> coq_GenericValue
    option
  
  val mcast :
    LLVMtd.coq_TargetData -> LLVMsyntax.castop -> LLVMsyntax.typ ->
    LLVMsyntax.typ -> coq_GenericValue -> coq_GenericValue option
  
  val mext :
    LLVMtd.coq_TargetData -> LLVMsyntax.extop -> LLVMsyntax.typ ->
    LLVMsyntax.typ -> coq_GenericValue -> coq_GenericValue option
  
  val micmp_int :
    LLVMtd.coq_TargetData -> LLVMsyntax.cond -> coq_GenericValue ->
    coq_GenericValue -> coq_GenericValue option
  
  val micmp_ptr :
    LLVMtd.coq_TargetData -> mem -> LLVMsyntax.cond -> coq_GenericValue ->
    coq_GenericValue -> coq_GenericValue option
  
  val micmp :
    LLVMtd.coq_TargetData -> LLVMsyntax.cond -> LLVMsyntax.typ ->
    coq_GenericValue -> coq_GenericValue -> coq_GenericValue option
  
  val mfcmp :
    LLVMtd.coq_TargetData -> LLVMsyntax.fcond -> LLVMsyntax.floating_point ->
    coq_GenericValue -> coq_GenericValue -> coq_GenericValue option
  
  val repeatGV : coq_GenericValue -> nat -> coq_GenericValue
  
  val zeroconst2GV :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue option
  
  val zeroconsts2GV :
    LLVMtd.coq_TargetData -> LLVMsyntax.list_typ -> coq_GenericValue option
  
  val _const2GV :
    LLVMtd.coq_TargetData -> coq_GVMap -> LLVMsyntax.const ->
    (coq_GenericValue*LLVMsyntax.typ) option
  
  val _list_const_arr2GV :
    LLVMtd.coq_TargetData -> coq_GVMap -> LLVMsyntax.typ ->
    LLVMsyntax.list_const -> coq_GenericValue option
  
  val _list_const_struct2GV :
    LLVMtd.coq_TargetData -> coq_GVMap -> LLVMsyntax.list_const ->
    (coq_GenericValue*LLVMsyntax.list_typ) option
  
  val cundef_gv : coq_GenericValue -> LLVMsyntax.typ -> coq_GenericValue
  
  val cgv2gv : coq_GenericValue -> LLVMsyntax.typ -> coq_GenericValue
  
  val const2GV :
    LLVMtd.coq_TargetData -> coq_GVMap -> LLVMsyntax.const ->
    coq_GenericValue option
  
  val getOperandValue :
    LLVMtd.coq_TargetData -> LLVMsyntax.value -> coq_GVMap -> coq_GVMap ->
    coq_GenericValue option
  
  val getOperandInt :
    LLVMtd.coq_TargetData -> LLVMsyntax.sz -> LLVMsyntax.value -> coq_GVMap
    -> coq_GVMap -> coq_Z option
  
  val getOperandPtr :
    LLVMtd.coq_TargetData -> LLVMsyntax.value -> coq_GVMap -> coq_GVMap ->
    coq_val option
  
  val getOperandPtrInBits :
    LLVMtd.coq_TargetData -> LLVMsyntax.sz -> LLVMsyntax.value -> coq_GVMap
    -> coq_GVMap -> coq_val option
  
  val params2GVs :
    LLVMtd.coq_TargetData -> LLVMsyntax.params -> coq_GVMap -> coq_GVMap ->
    coq_GenericValue list option
  
  val values2GVs :
    LLVMtd.coq_TargetData -> LLVMsyntax.list_sz_value -> coq_GVMap ->
    coq_GVMap -> coq_GenericValue list option
  
  val intValues2Nats :
    LLVMtd.coq_TargetData -> LLVMsyntax.list_sz_value -> coq_GVMap ->
    coq_GVMap -> coq_Z list option
  
  val fit_gv :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue ->
    coq_GenericValue option
  
  val _initializeFrameValues :
    LLVMtd.coq_TargetData -> LLVMsyntax.args -> coq_GenericValue list ->
    coq_GVMap -> coq_GVMap option
  
  val initLocals :
    LLVMtd.coq_TargetData -> LLVMsyntax.args -> coq_GenericValue list ->
    coq_GVMap option
  
  val coq_BOP :
    LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.bop ->
    LLVMsyntax.sz -> LLVMsyntax.value -> LLVMsyntax.value -> coq_GenericValue
    option
  
  val coq_FBOP :
    LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.fbop ->
    LLVMsyntax.floating_point -> LLVMsyntax.value -> LLVMsyntax.value ->
    coq_GenericValue option
  
  val coq_TRUNC :
    LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.truncop ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ -> coq_GenericValue
    option
  
  val coq_CAST :
    LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.castop ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ -> coq_GenericValue
    option
  
  val coq_EXT :
    LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.extop ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ -> coq_GenericValue
    option
  
  val coq_ICMP :
    LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.cond ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.value ->
    coq_GenericValue option
  
  val coq_FCMP :
    LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.fcond ->
    LLVMsyntax.floating_point -> LLVMsyntax.value -> LLVMsyntax.value ->
    coq_GenericValue option
  
  val coq_GEP :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue ->
    coq_GenericValue list -> bool -> coq_GenericValue option
  
  val malloc :
    LLVMtd.coq_TargetData -> mem -> LLVMsyntax.sz -> coq_GenericValue ->
    LLVMsyntax.align -> (mem*mblock) option
  
  val malloc_one :
    LLVMtd.coq_TargetData -> mem -> LLVMsyntax.sz -> LLVMsyntax.align ->
    (mem*mblock) option
  
  val free : LLVMtd.coq_TargetData -> mem -> mptr -> mem option
  
  val free_allocas :
    LLVMtd.coq_TargetData -> mem -> mblock list -> mem option
  
  val uninitMCs : nat -> memory_chunk list
  
  val repeatMC : memory_chunk list -> nat -> memory_chunk list
  
  val sizeMC : memory_chunk list -> nat
  
  val flatten_typ :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> memory_chunk list option
  
  val flatten_typs :
    LLVMtd.coq_TargetData -> LLVMsyntax.list_typ -> memory_chunk list option
  
  val mload_aux :
    Mem.mem -> memory_chunk list -> block -> coq_Z -> coq_GenericValue option
  
  val mload :
    LLVMtd.coq_TargetData -> mem -> mptr -> LLVMsyntax.typ ->
    LLVMsyntax.align -> coq_GenericValue option
  
  val mstore_aux : mem -> coq_GenericValue -> block -> coq_Z -> mem option
  
  val mstore :
    LLVMtd.coq_TargetData -> mem -> mptr -> LLVMsyntax.typ ->
    coq_GenericValue -> LLVMsyntax.align -> mem option
  
  val gep :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue list -> bool
    -> coq_GenericValue -> coq_GenericValue option
  
  val mget' :
    LLVMtd.coq_TargetData -> coq_Z -> LLVMsyntax.typ -> coq_GenericValue ->
    coq_GenericValue option
  
  val mset' :
    LLVMtd.coq_TargetData -> coq_Z -> LLVMsyntax.typ -> LLVMsyntax.typ ->
    coq_GenericValue -> coq_GenericValue -> coq_GenericValue option
 end

