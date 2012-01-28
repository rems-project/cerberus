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

module LLVMgv = 
 struct 
  type moffset = Int.int
  
  type mem = Llvmcaml.GenericValue.mem
  
  type coq_GenericValue = Llvmcaml.GenericValue.t
  
  type coq_GVMap = (LLVMsyntax.id*coq_GenericValue) list
  
  type mblock = Llvmcaml.GenericValue.t
  
  type mptr = Llvmcaml.GenericValue.t
  
  (** val null : coq_GenericValue **)
  
  let null = Llvmcaml.GenericValue.null
  
  (** val eq_gv : coq_GenericValue -> coq_GenericValue -> bool **)
  
  let rec eq_gv = Llvmcaml.GenericValue.eq_gv
  
  (** val uninits : nat -> coq_GenericValue **)
  
  let uninits = Llvmcaml.GenericValue.uninits
  
  (** val gundef :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue option **)
  
  let gundef = Llvmcaml.GenericValue.gundef
  
  (** val coq_GV2val :
      LLVMtd.coq_TargetData -> coq_GenericValue -> coq_val option **)
  
  let coq_GV2val = Llvmcaml.GenericValue.gv2val
  
  (** val coq_GV2int :
      LLVMtd.coq_TargetData -> LLVMsyntax.sz -> coq_GenericValue -> coq_Z
      option **)
  
  let coq_GV2int = Llvmcaml.GenericValue.gv2int
  
  (** val coq_GV2ptr :
      LLVMtd.coq_TargetData -> LLVMsyntax.sz -> coq_GenericValue -> coq_val
      option **)
  
  let coq_GV2ptr = Llvmcaml.GenericValue.gv2ptr
  
  (** val val2GV :
      LLVMtd.coq_TargetData -> coq_val -> memory_chunk -> coq_GenericValue **)
  
  let val2GV = Llvmcaml.GenericValue.val2gv
  
  (** val ptr2GV : LLVMtd.coq_TargetData -> coq_val -> coq_GenericValue **)
  
  let ptr2GV = Llvmcaml.GenericValue.ptr2gv
  
  (** val blk2GV : LLVMtd.coq_TargetData -> mblock -> coq_GenericValue **)
  
  let blk2GV = Llvmcaml.GenericValue.blk2gv
  
  (** val isGVZero : LLVMtd.coq_TargetData -> coq_GenericValue -> bool **)
  
  let isGVZero = Llvmcaml.GenericValue.isZero
  
  (** val mgep :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_val -> coq_Z list ->
      coq_val option **)
  
  let mgep = Llvmcaml.GenericValue.mgep
  
  (** val sizeGenericValue : coq_GenericValue -> nat **)
  
  let rec sizeGenericValue = Llvmcaml.GenericValue.sizeGenericValue
  
  (** val splitGenericValue :
      coq_GenericValue -> coq_Z -> (coq_GenericValue*coq_GenericValue) option **)
  
  let rec splitGenericValue = Llvmcaml.GenericValue.splitGenericValue
  
  (** val mget :
      LLVMtd.coq_TargetData -> coq_GenericValue -> coq_Z -> LLVMsyntax.typ ->
      coq_GenericValue option **)
  
  let mget = Llvmcaml.GenericValue.mget
  
  (** val mset :
      LLVMtd.coq_TargetData -> coq_GenericValue -> coq_Z -> LLVMsyntax.typ ->
      coq_GenericValue -> coq_GenericValue option **)
  
  let mset = Llvmcaml.GenericValue.mset
  
  (** val coq_GVs2Nats :
      LLVMtd.coq_TargetData -> coq_GenericValue list -> coq_Z list option **)
  
  let rec coq_GVs2Nats tD = function
    | [] -> Some []
    | gv::lgv' ->
        (match coq_GV2int tD LLVMsyntax.Size.coq_ThirtyTwo gv with
           | Some z ->
               (match coq_GVs2Nats tD lgv' with
                  | Some ns -> Some (z::ns)
                  | None -> None)
           | None -> None)
  
  (** val extractGenericValue :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue ->
      LLVMsyntax.list_const -> coq_GenericValue option **)
  
  let extractGenericValue = Llvmcaml.GenericValue.extractGenericValue
  
  (** val insertGenericValue :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue ->
      LLVMsyntax.list_const -> LLVMsyntax.typ -> coq_GenericValue ->
      coq_GenericValue option **)
  
  let insertGenericValue = Llvmcaml.GenericValue.insertGenericValue
  
  (** val mtrunc :
      LLVMtd.coq_TargetData -> LLVMsyntax.truncop -> LLVMsyntax.typ ->
      LLVMsyntax.typ -> coq_GenericValue -> coq_GenericValue option **)
  
  let mtrunc = Llvmcaml.GenericValue.mtrunc
  
  (** val mbop :
      LLVMtd.coq_TargetData -> LLVMsyntax.bop -> LLVMsyntax.sz ->
      coq_GenericValue -> coq_GenericValue -> coq_GenericValue option **)
  
  let mbop = Llvmcaml.GenericValue.mbop
  
  (** val mfbop :
      LLVMtd.coq_TargetData -> LLVMsyntax.fbop -> LLVMsyntax.floating_point
      -> coq_GenericValue -> coq_GenericValue -> coq_GenericValue option **)
  
  let mfbop = Llvmcaml.GenericValue.mfbop
  
  (** val mptrtoint :
      LLVMtd.coq_TargetData -> mem -> coq_GenericValue -> nat ->
      coq_GenericValue option **)
  
  let mptrtoint = Llvmcaml.GenericValue.mptrtoint
  
  (** val mbitcast :
      LLVMsyntax.typ -> coq_GenericValue -> LLVMsyntax.typ ->
      coq_GenericValue option **)
  
  let mbitcast t1 gv1 t2 =
    match t1 with
      | LLVMsyntax.Coq_typ_int sz1 ->
          (match t2 with
             | LLVMsyntax.Coq_typ_int sz2 -> Some gv1
             | _ -> None)
      | LLVMsyntax.Coq_typ_pointer t ->
          (match t2 with
             | LLVMsyntax.Coq_typ_pointer t0 -> Some gv1
             | _ -> None)
      | _ -> None
  
  (** val minttoptr :
      LLVMtd.coq_TargetData -> mem -> coq_GenericValue -> coq_GenericValue
      option **)
  
  let minttoptr = Llvmcaml.GenericValue.minttoptr
  
  (** val mcast :
      LLVMtd.coq_TargetData -> LLVMsyntax.castop -> LLVMsyntax.typ ->
      LLVMsyntax.typ -> coq_GenericValue -> coq_GenericValue option **)
  
  let mcast = Llvmcaml.GenericValue.mcast
  
  (** val mext :
      LLVMtd.coq_TargetData -> LLVMsyntax.extop -> LLVMsyntax.typ ->
      LLVMsyntax.typ -> coq_GenericValue -> coq_GenericValue option **)
  
  let mext = Llvmcaml.GenericValue.mext
  
  (** val micmp_int :
      LLVMtd.coq_TargetData -> LLVMsyntax.cond -> coq_GenericValue ->
      coq_GenericValue -> coq_GenericValue option **)
  
  let micmp_int = Llvmcaml.GenericValue.micmp_int
  
  (** val micmp_ptr :
      LLVMtd.coq_TargetData -> mem -> LLVMsyntax.cond -> coq_GenericValue ->
      coq_GenericValue -> coq_GenericValue option **)
  
  let micmp_ptr = Llvmcaml.GenericValue.micmp_ptr
  
  (** val micmp :
      LLVMtd.coq_TargetData -> LLVMsyntax.cond -> LLVMsyntax.typ ->
      coq_GenericValue -> coq_GenericValue -> coq_GenericValue option **)
  
  let micmp = Llvmcaml.GenericValue.micmp
  
  (** val mfcmp :
      LLVMtd.coq_TargetData -> LLVMsyntax.fcond -> LLVMsyntax.floating_point
      -> coq_GenericValue -> coq_GenericValue -> coq_GenericValue option **)
  
  let mfcmp = Llvmcaml.GenericValue.mfcmp
  
  (** val repeatGV : coq_GenericValue -> nat -> coq_GenericValue **)
  
  let rec repeatGV = Llvmcaml.GenericValue.repeatGV
  
  (** val zeroconst2GV :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue option **)
  
  let rec zeroconst2GV = Llvmcaml.GenericValue._zeroconst2GV
  
  (** val zeroconsts2GV :
      LLVMtd.coq_TargetData -> LLVMsyntax.list_typ -> coq_GenericValue option **)
  
  and zeroconsts2GV = Llvmcaml.GenericValue._list_typ_zerostruct2GV
  
  (** val _const2GV :
      LLVMtd.coq_TargetData -> coq_GVMap -> LLVMsyntax.const ->
      (coq_GenericValue*LLVMsyntax.typ) option **)
  
  let rec _const2GV = Llvmcaml.GenericValue._const2GV
  
  (** val _list_const_arr2GV :
      LLVMtd.coq_TargetData -> coq_GVMap -> LLVMsyntax.typ ->
      LLVMsyntax.list_const -> coq_GenericValue option **)
  
  and _list_const_arr2GV = Llvmcaml.GenericValue._list_const_arr2GV
  
  (** val _list_const_struct2GV :
      LLVMtd.coq_TargetData -> coq_GVMap -> LLVMsyntax.list_const ->
      (coq_GenericValue*LLVMsyntax.list_typ) option **)
  
  and _list_const_struct2GV = Llvmcaml.GenericValue._list_const_struct2GV
  
  (** val cundef_gv :
      coq_GenericValue -> LLVMsyntax.typ -> coq_GenericValue **)
  
  let cundef_gv = Llvmcaml.GenericValue.cundef_gv
  
  (** val cgv2gv : coq_GenericValue -> LLVMsyntax.typ -> coq_GenericValue **)
  
  let cgv2gv = Llvmcaml.GenericValue.cgv2gv
  
  (** val const2GV :
      LLVMtd.coq_TargetData -> coq_GVMap -> LLVMsyntax.const ->
      coq_GenericValue option **)
  
  let const2GV = Llvmcaml.GenericValue.const2GV
  
  (** val getOperandValue :
      LLVMtd.coq_TargetData -> LLVMsyntax.value -> coq_GVMap -> coq_GVMap ->
      coq_GenericValue option **)
  
  let getOperandValue = Llvmcaml.GenericValue.getOperandValue
  
  (** val getOperandInt :
      LLVMtd.coq_TargetData -> LLVMsyntax.sz -> LLVMsyntax.value -> coq_GVMap
      -> coq_GVMap -> coq_Z option **)
  
  let getOperandInt tD bsz v locals globals =
    match getOperandValue tD v locals globals with
      | Some gi -> coq_GV2int tD bsz gi
      | None -> None
  
  (** val getOperandPtr :
      LLVMtd.coq_TargetData -> LLVMsyntax.value -> coq_GVMap -> coq_GVMap ->
      coq_val option **)
  
  let getOperandPtr tD v locals globals =
    match getOperandValue tD v locals globals with
      | Some gi -> coq_GV2ptr tD (LLVMtd.getPointerSize tD) gi
      | None -> None
  
  (** val getOperandPtrInBits :
      LLVMtd.coq_TargetData -> LLVMsyntax.sz -> LLVMsyntax.value -> coq_GVMap
      -> coq_GVMap -> coq_val option **)
  
  let getOperandPtrInBits tD s v locals globals =
    match getOperandValue tD v locals globals with
      | Some gi -> coq_GV2ptr tD s gi
      | None -> None
  
  (** val params2GVs :
      LLVMtd.coq_TargetData -> LLVMsyntax.params -> coq_GVMap -> coq_GVMap ->
      coq_GenericValue list option **)
  
  let rec params2GVs tD lp locals globals =
    match lp with
      | [] -> Some []
      | p::lp' ->
          let p0,v = p in
          let o = getOperandValue tD v locals globals in
          let o0 = params2GVs tD lp' locals globals in
          (match o with
             | Some gv ->
                 (match o0 with
                    | Some gvs -> Some (gv::gvs)
                    | None -> None)
             | None -> None)
  
  (** val values2GVs :
      LLVMtd.coq_TargetData -> LLVMsyntax.list_sz_value -> coq_GVMap ->
      coq_GVMap -> coq_GenericValue list option **)
  
  let rec values2GVs tD lv locals globals =
    match lv with
      | LLVMsyntax.Nil_list_sz_value -> Some []
      | LLVMsyntax.Cons_list_sz_value (s, v, lv') ->
          (match getOperandValue tD v locals globals with
             | Some gV ->
                 (match values2GVs tD lv' locals globals with
                    | Some gVs -> Some (gV::gVs)
                    | None -> None)
             | None -> None)
  
  (** val intValues2Nats :
      LLVMtd.coq_TargetData -> LLVMsyntax.list_sz_value -> coq_GVMap ->
      coq_GVMap -> coq_Z list option **)
  
  let rec intValues2Nats tD lv locals globals =
    match lv with
      | LLVMsyntax.Nil_list_sz_value -> Some []
      | LLVMsyntax.Cons_list_sz_value (s, v, lv') ->
          (match getOperandValue tD v locals globals with
             | Some gV ->
                 (match coq_GV2int tD LLVMsyntax.Size.coq_ThirtyTwo gV with
                    | Some z ->
                        (match intValues2Nats tD lv' locals globals with
                           | Some ns -> Some (z::ns)
                           | None -> None)
                    | None -> None)
             | None -> None)
  
  (** val fit_gv :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue ->
      coq_GenericValue option **)
  
  let fit_gv = Llvmcaml.GenericValue.fit_gv
  
  (** val _initializeFrameValues :
      LLVMtd.coq_TargetData -> LLVMsyntax.args -> coq_GenericValue list ->
      coq_GVMap -> coq_GVMap option **)
  
  let rec _initializeFrameValues tD la lg locals =
    match la with
      | [] -> Some locals
      | p::la' ->
          let p0,id0 = p in
          let t,a = p0 in
          (match lg with
             | [] ->
                 (match _initializeFrameValues tD la' [] locals with
                    | Some lc' ->
                        (match gundef tD t with
                           | Some gv -> Some
                               (updateAddAL lc' id0 (cgv2gv gv t))
                           | None -> None)
                    | None -> None)
             | g::lg' ->
                 (match _initializeFrameValues tD la' lg' locals with
                    | Some lc' ->
                        (match fit_gv tD t g with
                           | Some gv -> Some
                               (updateAddAL lc' id0 (cgv2gv gv t))
                           | None -> None)
                    | None -> None))
  
  (** val initLocals :
      LLVMtd.coq_TargetData -> LLVMsyntax.args -> coq_GenericValue list ->
      coq_GVMap option **)
  
  let initLocals tD la lg =
    _initializeFrameValues tD la lg []
  
  (** val coq_BOP :
      LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.bop ->
      LLVMsyntax.sz -> LLVMsyntax.value -> LLVMsyntax.value ->
      coq_GenericValue option **)
  
  let coq_BOP tD lc gl op bsz v1 v2 =
    let o = getOperandValue tD v1 lc gl in
    let o0 = getOperandValue tD v2 lc gl in
    (match o with
       | Some gv1 ->
           (match o0 with
              | Some gv2 -> mbop tD op bsz gv1 gv2
              | None -> None)
       | None -> None)
  
  (** val coq_FBOP :
      LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> LLVMsyntax.value -> LLVMsyntax.value ->
      coq_GenericValue option **)
  
  let coq_FBOP tD lc gl op fp v1 v2 =
    let o = getOperandValue tD v1 lc gl in
    let o0 = getOperandValue tD v2 lc gl in
    (match o with
       | Some gv1 ->
           (match o0 with
              | Some gv2 -> mfbop tD op fp gv1 gv2
              | None -> None)
       | None -> None)
  
  (** val coq_TRUNC :
      LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.truncop
      -> LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ ->
      coq_GenericValue option **)
  
  let coq_TRUNC tD lc gl op t1 v1 t2 =
    match getOperandValue tD v1 lc gl with
      | Some gv1 -> mtrunc tD op t1 t2 gv1
      | None -> None
  
  (** val coq_CAST :
      LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.castop ->
      LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ ->
      coq_GenericValue option **)
  
  let coq_CAST tD lc gl op t1 v1 t2 =
    match getOperandValue tD v1 lc gl with
      | Some gv1 -> mcast tD op t1 t2 gv1
      | None -> None
  
  (** val coq_EXT :
      LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.extop ->
      LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ ->
      coq_GenericValue option **)
  
  let coq_EXT tD lc gl op t1 v1 t2 =
    match getOperandValue tD v1 lc gl with
      | Some gv1 -> mext tD op t1 t2 gv1
      | None -> None
  
  (** val coq_ICMP :
      LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.cond ->
      LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.value ->
      coq_GenericValue option **)
  
  let coq_ICMP tD lc gl c t v1 v2 =
    let o = getOperandValue tD v1 lc gl in
    let o0 = getOperandValue tD v2 lc gl in
    (match o with
       | Some gv1 ->
           (match o0 with
              | Some gv2 -> micmp tD c t gv1 gv2
              | None -> None)
       | None -> None)
  
  (** val coq_FCMP :
      LLVMtd.coq_TargetData -> coq_GVMap -> coq_GVMap -> LLVMsyntax.fcond ->
      LLVMsyntax.floating_point -> LLVMsyntax.value -> LLVMsyntax.value ->
      coq_GenericValue option **)
  
  let coq_FCMP tD lc gl c fp v1 v2 =
    let o = getOperandValue tD v1 lc gl in
    let o0 = getOperandValue tD v2 lc gl in
    (match o with
       | Some gv1 ->
           (match o0 with
              | Some gv2 -> mfcmp tD c fp gv1 gv2
              | None -> None)
       | None -> None)
  
  (** val coq_GEP :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue ->
      coq_GenericValue list -> bool -> coq_GenericValue option **)
  
  let coq_GEP = Llvmcaml.GenericValue.gep
  
  (** val malloc :
      LLVMtd.coq_TargetData -> mem -> LLVMsyntax.sz -> coq_GenericValue ->
      LLVMsyntax.align -> (mem*mblock) option **)
  
  let malloc = Llvmcaml.GenericValue.malloc
  
  (** val malloc_one :
      LLVMtd.coq_TargetData -> mem -> LLVMsyntax.sz -> LLVMsyntax.align ->
      (mem*mblock) option **)
  
  let malloc_one = Llvmcaml.GenericValue.malloc_one
  
  (** val free : LLVMtd.coq_TargetData -> mem -> mptr -> mem option **)
  
  let free = Llvmcaml.GenericValue.free
  
  (** val free_allocas :
      LLVMtd.coq_TargetData -> mem -> mblock list -> mem option **)
  
  let rec free_allocas tD mem0 = function
    | [] -> Some mem0
    | alloca::allocas' ->
        (match free tD mem0 (blk2GV tD alloca) with
           | Some mem' -> free_allocas tD mem' allocas'
           | None -> None)
  
  (** val uninitMCs : nat -> memory_chunk list **)
  
  let uninitMCs n =
    list_repeat n (Mint (S (S (S (S (S (S (S O))))))))
  
  (** val repeatMC : memory_chunk list -> nat -> memory_chunk list **)
  
  let rec repeatMC mcs = function
    | O -> []
    | S n' -> app mcs (repeatMC mcs n')
  
  (** val sizeMC : memory_chunk list -> nat **)
  
  let rec sizeMC = function
    | [] -> O
    | c::mc' -> plus (size_chunk_nat c) (sizeMC mc')
  
  (** val flatten_typ :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> memory_chunk list option **)
  
  let rec flatten_typ = Llvmcaml.GenericValue.flatten_typ
  
  (** val flatten_typs :
      LLVMtd.coq_TargetData -> LLVMsyntax.list_typ -> memory_chunk list
      option **)
  
  and flatten_typs = Llvmcaml.GenericValue.flatten_typs
  
  (** val mload_aux :
      Mem.mem -> memory_chunk list -> block -> coq_Z -> coq_GenericValue
      option **)
  
  let rec mload_aux = Llvmcaml.GenericValue.mload_aux
  
  (** val mload :
      LLVMtd.coq_TargetData -> mem -> mptr -> LLVMsyntax.typ ->
      LLVMsyntax.align -> coq_GenericValue option **)
  
  let mload = Llvmcaml.GenericValue.mload
  
  (** val mstore_aux :
      mem -> coq_GenericValue -> block -> coq_Z -> mem option **)
  
  let rec mstore_aux = Llvmcaml.GenericValue.mstore_aux
  
  (** val mstore :
      LLVMtd.coq_TargetData -> mem -> mptr -> LLVMsyntax.typ ->
      coq_GenericValue -> LLVMsyntax.align -> mem option **)
  
  let mstore = Llvmcaml.GenericValue.mstore
  
  (** val gep :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_GenericValue list ->
      bool -> coq_GenericValue -> coq_GenericValue option **)
  
  let gep tD ty vidxs inbounds ma =
    coq_GEP tD ty ma vidxs inbounds
  
  (** val mget' :
      LLVMtd.coq_TargetData -> coq_Z -> LLVMsyntax.typ -> coq_GenericValue ->
      coq_GenericValue option **)
  
  let mget' tD o t' gv =
    match mget tD gv o t' with
      | Some gv' -> Some gv'
      | None -> gundef tD t'
  
  (** val mset' :
      LLVMtd.coq_TargetData -> coq_Z -> LLVMsyntax.typ -> LLVMsyntax.typ ->
      coq_GenericValue -> coq_GenericValue -> coq_GenericValue option **)
  
  let mset' tD o t t0 gv gv0 =
    match mset tD gv o t0 gv0 with
      | Some gv' -> Some gv'
      | None -> gundef tD t
 end

