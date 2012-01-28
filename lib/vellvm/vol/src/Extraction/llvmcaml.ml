open Llvm_executionengine
open Syntax
open LLVMsyntax
open Printf
open Llvm
open Llvm_aux

let coqtype_2_llvmtype (ctx:llcontext) (m:llmodule) (t:LLVMsyntax.typ) 
  : Llvm.lltype = Coq2llvm.translate_typ ctx m t
let coqbop_2_llvmopcode (op:LLVMsyntax.bop) : Llvm.InstrOpcode.t = 
  Coq2llvm.translate_bop op
let coqfbop_2_llvmopcode (op:LLVMsyntax.fbop) : Llvm.InstrOpcode.t = 
  Coq2llvm.translate_fbop op
let coqtd_2_llvmtd (td:layouts) = Coq2llvm.translate_layouts td
let coqcond_2_llvmicmp (c:cond) : Llvm.Icmp.t = Coq2llvm.translate_icond c
let coqcond_2_llvmfcmp (c:fcond) : Llvm.Fcmp.t = Coq2llvm.translate_fcond c
let getRealName = Coq_pretty_printer.getRealName

module TargetData = struct

  type t = ExecutionEngine.t * Llvm.llmodule

  let getTypeAllocSize (td:t) typ = 
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    let ltd = ExecutionEngine.target_data ee in
    Some (Int64.to_int (Llvm_target.get_type_alloc_size ltd (coqtype_2_llvmtype 
      ctx mm typ)))
    
  let getTypeAllocSizeInBits x y = failwith "undef"
  let _getStructElementOffset x y z = failwith "undef"
  let getStructElementOffset x y z = failwith "undef"
  let getStructElementOffsetInBits x y z = failwith "undef"
  let _getStructElementContainingOffset x y z = failwith "undef"
  let getStructElementContainingOffset x y z = failwith "undef"
  let _getIntAlignmentInfo x = failwith "undef"
  let getIntAlignmentInfo x = failwith "undef"
  let _getPointerAlignmentInfo x = failwith "undef"
  let getPointerAlignmentInfo x = failwith "undef"
  let _getStructAlignmentInfo x = failwith "undef"
  let getStructAlignmentInfo x = failwith "undef"
  let _getPointerSize x = failwith "undef"
  let getPointerSize0 x = failwith "undef"
  let getPointerSize x = failwith "undef"
  let getPointerSizeInBits x = failwith "undef"
  let _getTypeSizeInBits_and_Alignment x = failwith "undef"
  let _getListTypeSizeInBits_and_Alignment x = failwith "undef"
  let getTypeSizeInBits_and_Alignment_for_namedts x = failwith "undef"
  let _getTypeSizeInBits_and_Alignment_for_namedts x = failwith "undef"
  let getTypeSizeInBits_and_Alignment x = failwith "undef"
  let getListTypeSizeInBits_and_Alignment x = failwith "undef"
  let getAlignment x = failwith "undef"
  let getABITypeAlignment x = failwith "undef"
  let getPrefTypeAlignment x = failwith "undef"
  let getTypeSizeInBits x = failwith "undef"
  let getTypeStoreSize x = failwith "undef"
  let getTypeStoreSizeInBits x = failwith "undef"
  let getStructSizeInBytes x = failwith "undef"
  let getStructSizeInBits x = failwith "undef"
  let getStructAlignment x = failwith "undef"
  let getFloatAlignmentInfo x = failwith "undef"          
  let mgetoffset_aux x y z w = failwith "mgetoffset_aux undef"
  let mgetoffset x y z = failwith "mgetoffset undef"
    
end  

module GenericValue = struct

  type t = GenericValue.t
  type mem = ExecutionEngine.t * Llvm.llmodule

  (* useless at runtime *)
  let null = GenericValue.of_null_pointer ()
  let sizeGenericValue x = failwith "sizeGenericValue undef"
  let splitGenericValue x y = failwith "splitGenericValue undef"
  let uninits x = failwith "uninits undef"
  let gundef td t = Some null
  let fit_gv td t x = Some x
  let gv2val x y = failwith "gv2val undef"
  let gv2int x y z = failwith "gv2int undef"
  let gv2ptr x y z = failwith "gv2ptr undef"
  let val2gv x y z = failwith "val2gv undef"
  let ptr2gv x y = failwith "val2gv undef"
  let _zeroconst2GV x y = failwith "_zeroconst2GV undef"
  let _list_typ_zerostruct2GV x y = failwith "_list_typ_zerostruct2GV undef"
  let repeatGV x y = failwith "repeatGV undef"
  let _list_const_arr2GV x y z = failwith "_list_const_arr2GV undef" 
  let _list_const_struct2GV x y z = failwith "_list_const_struct2GV undef" 
  let cundef_gv x y = x
  let cgv2gv x y = x
  let eq_gv x y = failwith "eq_gv undef"
  let mgep x y z w = failwith "mgep undef"
  let mget x y z w = failwith "mget undef"
  let mset x y z w u = failwith "mset undef"
  let mptrtoint x = failwith "mptrtotint undef"
  let minttoptr x = failwith "minttoptr undef"
  let micmp_ptr x = failwith "micmp_ptr undef"
  let micmp_int x = failwith "micmp_int undef"

  (* used at runtime *)
  let blk2gv (td:TargetData.t) (v:t) = v

  let isZero (td:TargetData.t) (v:t) = GenericValue.as_int v == 0
  
  let rec list_llvalue2list_int (vs:Llvm.llvalue list) : (int list) option =
  match vs with
  | [] -> Some []
  | v::vs' ->    
    if Llvm.is_constantint v
    then
      let i = Int64.to_int (Llvm.APInt.get_sext_value 
        (Llvm.APInt.const_int_get_value v)) in
      match list_llvalue2list_int vs' with
      | None -> None
      | Some is -> Some (i::is)
    else None 

  let rec const2llvalue (td:TargetData.t) gl (c:const) : Llvm.llvalue option = 
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    match c with
    | Coq_const_zeroinitializer _ -> Some (Coq2llvm.translate_constant ctx mm c)
    | Coq_const_int (sz, i) -> Some (Coq2llvm.translate_constant ctx mm c)
    | Coq_const_floatpoint (_, _) -> Some (Coq2llvm.translate_constant ctx mm c)
    | Coq_const_undef t -> Some (Coq2llvm.translate_constant ctx mm c) 
    | Coq_const_null t -> Some (Coq2llvm.translate_constant ctx mm c) 
    | Coq_const_arr (t, cs) -> Some (Coq2llvm.translate_constant ctx mm c)  
    | Coq_const_struct cs -> Some (Coq2llvm.translate_constant ctx mm c)
    | Coq_const_gid (_,id) -> 
      begin
        match Llvm.lookup_global (getRealName id) mm with
        | None -> Llvm.lookup_function (getRealName id) mm
        | Some gv -> Some gv
      end  
    | Coq_const_truncop (op, c, t) -> 
      (match (const2llvalue td gl c) with
      | Some v -> 
        Some (match op with
        | Coq_truncop_int -> Llvm.const_trunc v (Coq2llvm.translate_typ ctx mm t)
        | Coq_truncop_fp -> Llvm.const_fptrunc v (Coq2llvm.translate_typ ctx mm t))
      | None -> None)
    | Coq_const_extop (op, c, t) ->   
      (match (const2llvalue td gl c) with
      | Some v -> 
        Some (match op with
        | Coq_extop_z -> Llvm.const_zext v (Coq2llvm.translate_typ ctx mm t)
        | Coq_extop_s -> Llvm.const_sext v (Coq2llvm.translate_typ ctx mm t)
        | Coq_extop_fp -> Llvm.const_fpext v (Coq2llvm.translate_typ ctx mm t))
      | None -> None)
    | Coq_const_castop (op, c, t) -> 
      (match (const2llvalue td gl c) with
      | Some v -> 
        Some (match op with
        | LLVMsyntax.Coq_castop_fptoui -> 
            Llvm.const_fptoui v (Coq2llvm.translate_typ ctx mm t)      
        | LLVMsyntax.Coq_castop_fptosi ->
            Llvm.const_fptosi v (Coq2llvm.translate_typ ctx mm t)    
        | LLVMsyntax.Coq_castop_uitofp -> 
            Llvm.const_uitofp v (Coq2llvm.translate_typ ctx mm t) 
        | LLVMsyntax.Coq_castop_sitofp -> 
            Llvm.const_sitofp v (Coq2llvm.translate_typ ctx mm t) 
        | LLVMsyntax.Coq_castop_ptrtoint -> 
            Llvm.const_ptrtoint v (Coq2llvm.translate_typ ctx mm t) 
        | LLVMsyntax.Coq_castop_inttoptr -> 
            Llvm.const_inttoptr v (Coq2llvm.translate_typ ctx mm t) 
        | LLVMsyntax.Coq_castop_bitcast -> 
            Llvm.const_bitcast v (Coq2llvm.translate_typ ctx mm t))
      | None -> None)
    | Coq_const_gep (ib, c, cs) -> 
      (match const2llvalue td gl c, list_const2list_llvalue td gl cs with
      | Some v, Some vs -> 
        Some (match ib with
        | true -> Llvm.const_in_bounds_gep v (Array.of_list vs)
        | false -> Llvm.const_gep v (Array.of_list vs))
      | _, _ -> None)
    |  Coq_const_select (c0, c1, c2) -> 
      (match const2llvalue td gl c0, const2llvalue td gl c1, 
             const2llvalue td gl c2 with
      | Some v0, Some v1, Some v2 ->
        Some (Llvm.const_select v0 v1 v2)
      | _, _, _ -> None) 
    |  Coq_const_icmp (cond, c1, c2) -> 
      (match const2llvalue td gl c1, const2llvalue td gl c2 with
      | Some v1, Some v2 ->
        Some (Llvm.const_icmp (coqcond_2_llvmicmp cond) v1 v2)
      | _, _ -> None)
    |  Coq_const_fcmp (cond, c1, c2) -> 
      (match const2llvalue td gl c1, const2llvalue td gl c2 with
      | Some v1, Some v2 ->
        Some (Llvm.const_fcmp (coqcond_2_llvmfcmp cond) v1 v2)
      | _, _ -> None)
    | Coq_const_extractvalue (c, cs) -> 
      (match const2llvalue td gl c, list_const2list_llvalue td gl cs with
      | Some v, Some vs -> 
        (match list_llvalue2list_int vs with
        | Some is -> Some (Llvm.const_extractvalue v (Array.of_list is))
        | None -> None)
      | _, _ -> None)
    | Coq_const_insertvalue (c1, c2, cs) -> 
      (match const2llvalue td gl c1, const2llvalue td gl c2, 
             list_const2list_llvalue td gl cs with
      | Some v1, Some v2, Some vs -> 
        (match list_llvalue2list_int vs with
        | Some is -> Some (Llvm.const_insertvalue v1 v2 (Array.of_list is))
        | None -> None)
      | _, _, _ -> None)
    | Coq_const_bop (op, c1, c2) ->  
      (match const2llvalue td gl c1, const2llvalue td gl c2 with
      | Some v1, Some v2 -> 
        Some (match op with 
        | LLVMsyntax.Coq_bop_add -> Llvm.const_add v1 v2       
        | LLVMsyntax.Coq_bop_sub -> Llvm.const_sub v1 v2
        | LLVMsyntax.Coq_bop_mul -> Llvm.const_mul v1 v2
        | LLVMsyntax.Coq_bop_udiv -> Llvm.const_udiv v1 v2
        | LLVMsyntax.Coq_bop_sdiv -> Llvm.const_sdiv v1 v2
        | LLVMsyntax.Coq_bop_urem -> Llvm.const_urem v1 v2
        | LLVMsyntax.Coq_bop_srem -> Llvm.const_srem v1 v2
        | LLVMsyntax.Coq_bop_shl -> Llvm.const_shl v1 v2
        | LLVMsyntax.Coq_bop_lshr -> Llvm.const_lshr v1 v2
        | LLVMsyntax.Coq_bop_ashr -> Llvm.const_ashr v1 v2
        | LLVMsyntax.Coq_bop_and -> Llvm.const_and v1 v2
        | LLVMsyntax.Coq_bop_or -> Llvm.const_or v1 v2
        | LLVMsyntax.Coq_bop_xor -> Llvm.const_xor v1 v2)
      | _, _ -> None)
    | Coq_const_fbop (op, c1, c2) ->  
      (match const2llvalue td gl c1, const2llvalue td gl c2 with
      | Some v1, Some v2 -> 
        Some (match op with 
        | LLVMsyntax.Coq_fbop_fadd -> Llvm.const_fadd v1 v2      
        | LLVMsyntax.Coq_fbop_fsub -> Llvm.const_fsub v1 v2
        | LLVMsyntax.Coq_fbop_fmul -> Llvm.const_fmul v1 v2
        | LLVMsyntax.Coq_fbop_fdiv -> Llvm.const_fdiv v1 v2
        | LLVMsyntax.Coq_fbop_frem -> Llvm.const_frem v1 v2)
      | _, _ -> None)
  and list_const2list_llvalue (td:TargetData.t) gl (cs:list_const) 
      : (Llvm.llvalue list) option =
    match cs with
    | LLVMsyntax.Cons_list_const (c, cs') -> 
      (match const2llvalue td gl c, list_const2list_llvalue td gl cs' with
      | Some gv, Some gvs -> Some (gv::gvs)
      | _, _ -> None)
    | LLVMsyntax.Nil_list_const -> Some []

  let rec llconst2GV (td:TargetData.t) (c:llvalue) : t =   
    let (ee, _) = td in
    match (classify_value c) with
    | ValueTy.UndefValueVal -> ExecutionEngine.get_constant_value c ee 
    | ValueTy.ConstantExprVal -> llconstexpr2GV td c
    | ValueTy.ConstantAggregateZeroVal -> ExecutionEngine.get_constant_value c ee
    | ValueTy.ConstantIntVal -> ExecutionEngine.get_constant_value c ee
    | ValueTy.ConstantFPVal ->  ExecutionEngine.get_constant_value c ee
    | ValueTy.ConstantArrayVal -> ExecutionEngine.get_constant_value c ee
    | ValueTy.ConstantStructVal -> ExecutionEngine.get_constant_value c ee
    | ValueTy.ConstantVectorVal -> failwith "ConstantVector: Not_Supported." 
    | ValueTy.ConstantPointerNullVal -> ExecutionEngine.get_constant_value c ee
    | ValueTy.GlobalVariableVal -> ExecutionEngine.get_constant_value c ee
    | ValueTy.FunctionVal -> ExecutionEngine.get_constant_value c ee
    | _ -> failwith (string_of_valuety (classify_value c) ^ " isnt Constant")
  and llconstexpr2GV td c =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    match (classify_constantexpr c) with
    | InstrOpcode.Ret ->
      failwith "Ret isnt a const expr"
    | InstrOpcode.Br ->
      failwith "Br isnt a const expr"
    | InstrOpcode.Switch ->
      failwith "Switch isnt a const expr"
    | InstrOpcode.Invoke ->      
      failwith "Invoke isnt a const expr"
    | InstrOpcode.Unwind ->
      failwith "Unwind isnt a const expr"
    | InstrOpcode.Unreachable ->
      failwith "Unreachable isnt a const expr"
    | InstrOpcode.Add ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Add must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.FAdd ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FAdd must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.Sub ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Sub must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.FSub ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FSub must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.Mul ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Mul must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.FMul ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FMul must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.UDiv ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const UDiv must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.SDiv ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const SDiv must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.FDiv ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FDiv must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.URem ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const URem must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.SRem ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const SRem must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.FRem ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FRem must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.Shl ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Shl must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.LShr ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const LShr must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.AShr ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const AShr must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.And ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const And must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.Or ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Or must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.Xor ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const XOr must have 2 operand."
      else
        GenericValue.binary_op 
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (type_of c)
          (classify_constantexpr c)
    | InstrOpcode.Malloc ->
      failwith "Malloc isnt a const expr"
    | InstrOpcode.Free ->
      failwith "Free isnt a const expr"
    | InstrOpcode.Alloca ->
       failwith "Alloca isnt a const expr"
    | InstrOpcode.Load ->
      failwith "Load isnt a const expr"
    | InstrOpcode.Store ->
      failwith "Store isnt a const expr"
    | InstrOpcode.GetElementPtr ->        
      let n = num_operand c in
      if n < 2
      then failwith "Const GEP must have >=2 operand."
      else
        let ops = operands c in
         let n = num_operand c in
        let rec range b e ops =
          if b < e
          then
            (llconst2GV td (Array.get ops b))::(range (b + 1) e ops)
          else
            [] in
        let (ee, _) = td in    
        let ltd = ExecutionEngine.target_data ee in
        GenericValue.gep ltd 
          (llconst2GV td (Array.get ops 0)) 
          (type_of (Array.get ops 0)) 
          (Array.of_list (range 1 n ops))    
    | InstrOpcode.Trunc ->        
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const Trunc must have 1 operand."
      else
        GenericValue.trunc (llconst2GV td (Array.get ops 0)) (type_of c)
    | InstrOpcode.ZExt ->        
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const ZExt must have 1 operand."
      else
        GenericValue.zext (llconst2GV td (Array.get ops 0)) (type_of c)
    | InstrOpcode.SExt ->        
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const SExt must have 1 operand."
      else
        GenericValue.sext (llconst2GV td (Array.get ops 0)) (type_of c)
    |  InstrOpcode.FPToUI ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const FPToUI must have 1 operand."
      else
        GenericValue.fptoui (llconst2GV td (Array.get ops 0)) 
          (type_of (Array.get ops 0)) (type_of c)
    |  InstrOpcode.FPToSI ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const FPToSI must have 1 operand."
      else
        GenericValue.fptosi (llconst2GV td (Array.get ops 0)) 
          (type_of (Array.get ops 0)) (type_of c)
    |  InstrOpcode.UIToFP ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const UIToFP must have 1 operand."
      else
        GenericValue.uitofp (llconst2GV td (Array.get ops 0)) (type_of c)
    |  InstrOpcode.SIToFP ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const SIToFP must have 1 operand."
      else
        GenericValue.sitofp (llconst2GV td (Array.get ops 0)) (type_of c)
    |  InstrOpcode.FPTrunc ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const FPTrunc must have 1 operand."
      else
        GenericValue.fptrunc (llconst2GV td (Array.get ops 0)) 
          (type_of (Array.get ops 0)) ctx (type_of c)
    |  InstrOpcode.FPExt ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const FPExt must have 1 operand."
      else
        GenericValue.fpext (llconst2GV td (Array.get ops 0)) 
          (type_of (Array.get ops 0)) ctx (type_of c)
    |  InstrOpcode.PtrToInt ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const PtrToInt must have 1 operand."
      else
        GenericValue.ptrtoint (llconst2GV td (Array.get ops 0)) 
          (type_of (Array.get ops 0)) (type_of c)
    |  InstrOpcode.IntToPtr ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const IntToPtr must have 1 operand."
      else
        let (ee, _) = td in
        let ltd = ExecutionEngine.target_data ee in
        GenericValue.inttoptr ltd (llconst2GV td (Array.get ops 0)) (type_of c) 
    |  InstrOpcode.BitCast ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const BitCast must have 1 operand."
      else
        GenericValue.bitcast (llconst2GV td (Array.get ops 0)) 
          (type_of (Array.get ops 0)) ctx (type_of c)
    | InstrOpcode.ICmp ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const ICmp must have 2 operand."
      else
        GenericValue.icmp 
          (llconst2GV td (Array.get ops 0)) 
          (llconst2GV td (Array.get ops 1)) 
          (type_of (Array.get ops 0)) 
          (ICmpInst.const_get_predicate c)
    | InstrOpcode.FCmp ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FCmp must have 2 operand."
      else
        GenericValue.fcmp 
          (llconst2GV td (Array.get ops 0)) 
          (llconst2GV td (Array.get ops 1)) 
          (type_of (Array.get ops 0)) 
          (FCmpInst.const_get_predicate c)
    |  InstrOpcode.PHI ->
      failwith "PHI isnt a const expr"
    | InstrOpcode.Call ->
      failwith "Call isnt a const expr"
    | InstrOpcode.Select ->      
      let ops = operands c in
      let n = num_operand c in
      if n != 3
      then failwith "Const Select must have 3 operand."
      else
        GenericValue.select
          (llconst2GV td (Array.get ops 0))
          (llconst2GV td (Array.get ops 1))
          (llconst2GV td (Array.get ops 2))
    | InstrOpcode.UserOp1 ->      
      failwith "UserOp1 isnt a const expr"
    | InstrOpcode.UserOp2 ->      
      failwith "UserOp2 isnt a const expr"
    | InstrOpcode.VAArg ->      
      failwith "VAArg isnt a const expr"
    | InstrOpcode.ExtractElement ->      
      failwith "Const ExtractElement: Not_Supported"
    | InstrOpcode.InsertElement ->      
      failwith "Const InsertElement: Not_Supported"
    | InstrOpcode.ShuffleVector ->      
      failwith "Const ShuffleVector: Not_Supported"
    | InstrOpcode.ExtractValue ->      
      failwith "Const InstrOpcode.ExtractValue: Not_Supported"  
    | InstrOpcode.InsertValue ->      
      failwith "Const InstrOpcode.InsertValue: Not_Supported"  
                        
  (** llvm::ExecutionEngine::getConstantValue also implements how to deal with 
      function pointers and global variables 
      ...
      else if (const Function *F = dyn_cast<Function>(C))
        Result = PTOGV(getPointerToFunctionOrStub(const_cast<Function*>(F)));
      else if (const GlobalVariable* GV = dyn_cast<GlobalVariable>(C))
        Result = PTOGV(getOrEmitGlobalVariable(const_cast<GlobalVariable*>(GV)))
      ...
  *)
  let gep (td:TargetData.t) (t1:LLVMsyntax.typ) (ma:t) (vidxs:t list) 
    (inbounds:bool) : t option =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    let ltd = ExecutionEngine.target_data ee in
    (if !Globalstates.debug then
      eprintf "  Gep ptr=%s type=%s" (GenericValue.to_string ma) 
        (Coq_pretty_printer.string_of_typ t1); flush_all());          

    let gv = GenericValue.gep ltd ma (Llvm.pointer_type 
      (coqtype_2_llvmtype ctx mm t1)) (Array.of_list vidxs) in
    
    (if !Globalstates.debug then eprintf " r=%s\n" (GenericValue.to_string gv);
      flush_all());          
    Some gv

  let extractGenericValue x y z w = failwith "extractGenericValue undef"

  let insertGenericValue x y z a b = failwith "extractGenericValue undef"

  let mbop (td:TargetData.t) (op:LLVMsyntax.bop) (bsz:LLVMsyntax.sz) (gv1:t) 
    (gv2:t) = 
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then
      eprintf "  M%s i%d gv1=%s gv2=%s" (Coq_pretty_printer.string_of_bop op) bsz
       (GenericValue.to_string gv1) (GenericValue.to_string gv2);flush_all());
      
    let gv = (GenericValue.binary_op gv1 gv2 (Llvm.integer_type ctx bsz) 
      (coqbop_2_llvmopcode op)) in
    
    (if !Globalstates.debug then eprintf " r=%s\n" (GenericValue.to_string gv);
     flush_all());
    Some gv

  let mfbop (td:TargetData.t) (op:LLVMsyntax.fbop) (fp:LLVMsyntax.floating_point)
    (gv1:t) (gv2:t) = 
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then
      eprintf "  M%s %s gv1=%s gv2=%s"
      (Coq_pretty_printer.string_of_fbop op) 
        (Coq_pretty_printer.string_of_floating_point fp)
      (GenericValue.to_string gv1) (GenericValue.to_string gv2);flush_all());
      
    let gv = (GenericValue.binary_op gv1 gv2 
                (Coq2llvm.translate_floating_point ctx fp) 
                (coqfbop_2_llvmopcode op)) in
                
    (if !Globalstates.debug then eprintf " r=%s\n" (GenericValue.to_string gv);
      flush_all());
    Some gv

  let mcast (td:TargetData.t) (op:LLVMsyntax.castop) (t1:LLVMsyntax.typ) 
      (t2:LLVMsyntax.typ) (gv1:t) =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then
      eprintf "  M%s gv1=%s t1=%s t2=%s" (Coq_pretty_printer.string_of_castop op)
      (Coq_pretty_printer.string_of_typ t1) (Coq_pretty_printer.string_of_typ t2)
      (GenericValue.to_string gv1);flush_all());

    let gv =
    (match op with
    | Coq_castop_fptoui -> GenericValue.fptoui gv1 (coqtype_2_llvmtype ctx mm t1)
        (coqtype_2_llvmtype ctx mm t2)
    | Coq_castop_fptosi -> GenericValue.fptosi gv1 (coqtype_2_llvmtype ctx mm t1)
        (coqtype_2_llvmtype ctx mm t2)
    | Coq_castop_uitofp -> GenericValue.uitofp gv1 (coqtype_2_llvmtype ctx mm t2)
    | Coq_castop_sitofp -> GenericValue.sitofp gv1 (coqtype_2_llvmtype ctx mm t2)
    | Coq_castop_ptrtoint -> GenericValue.ptrtoint gv1 
        (coqtype_2_llvmtype ctx mm t1) (coqtype_2_llvmtype ctx mm t2)
    | Coq_castop_inttoptr -> let (ee, _) = td in
                             let ltd = ExecutionEngine.target_data ee in
                             GenericValue.inttoptr ltd gv1 
                             (coqtype_2_llvmtype ctx mm t2)
    | Coq_castop_bitcast -> GenericValue.bitcast gv1 
                              (coqtype_2_llvmtype ctx mm t1) 
                              ctx 
                              (coqtype_2_llvmtype ctx mm t2)
    ) in
    
    (if !Globalstates.debug then eprintf " r=%s\n" (GenericValue.to_string gv);
     flush_all());
    Some gv

  let mtrunc (td:TargetData.t) (op:truncop) (t1:typ) (t2:typ) (gv1:t) =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then
      eprintf "  M%s gv1=%s t1=%s t2=%s" 
      (Coq_pretty_printer.string_of_truncop op)
      (Coq_pretty_printer.string_of_typ t1) (Coq_pretty_printer.string_of_typ t2)
      (GenericValue.to_string gv1);flush_all());
      
    let gv =
    (match op with
    | Coq_truncop_int -> GenericValue.trunc gv1 (coqtype_2_llvmtype ctx mm t2) 
    | Coq_truncop_fp -> GenericValue.fptrunc gv1 (coqtype_2_llvmtype ctx mm t1) 
                          ctx (coqtype_2_llvmtype ctx mm t2)
    ) in
    
    (if !Globalstates.debug then eprintf " r=%s\n" (GenericValue.to_string gv);
     flush_all());
    Some gv

  let mext (td:TargetData.t) (op:extop) (t1:typ) (t2:typ) (gv1:t) =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then
      eprintf "  M%s gv1=%s t1=%s t2=%s" (Coq_pretty_printer.string_of_extop op)
      (Coq_pretty_printer.string_of_typ t1) (Coq_pretty_printer.string_of_typ t2)
      (GenericValue.to_string gv1);flush_all());
      
    let gv =
    (match op with
    | Coq_extop_z -> GenericValue.zext gv1 (coqtype_2_llvmtype ctx mm t2)
    | Coq_extop_s -> GenericValue.sext gv1 (coqtype_2_llvmtype ctx mm t2)
    | Coq_extop_fp -> GenericValue.fpext gv1 (coqtype_2_llvmtype ctx mm t1) ctx 
                        (coqtype_2_llvmtype ctx mm t2)
    ) in
    
    (if !Globalstates.debug then eprintf " r=%s\n" (GenericValue.to_string gv);
     flush_all());
    Some gv

  let micmp (td:TargetData.t) (c:cond) (t:typ) (gv1:t) (gv2:t) =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then 
      eprintf "  Micmp t=%s gv1=%s gv2=%s" (Coq_pretty_printer.string_of_typ t)
      (GenericValue.to_string gv1) (GenericValue.to_string gv2);flush_all());
      
    let gv = GenericValue.icmp gv1 gv2 (coqtype_2_llvmtype ctx mm t) 
       (coqcond_2_llvmicmp c) in
    
    (if !Globalstates.debug then eprintf " r=%s\n" (GenericValue.to_string gv);
      flush_all());
    Some gv

  let mfcmp (td:TargetData.t) (c:fcond) (fp:LLVMsyntax.floating_point) (gv1:t) 
      (gv2:t) =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then 
      eprintf "  Mfcmp t=%s gv1=%s gv2=%s" 
      (Coq_pretty_printer.string_of_floating_point fp)
      (GenericValue.to_string gv1) (GenericValue.to_string gv2);flush_all());
      
    let gv = GenericValue.fcmp gv1 gv2 
               (Coq2llvm.translate_floating_point ctx fp) 
               (coqcond_2_llvmfcmp c) in
              
    (if !Globalstates.debug then eprintf " r=%s\n" (GenericValue.to_string gv);
     flush_all());
    Some gv


  let dump (gv:t) = GenericValue.dump gv
  let to_string (gv:t) = GenericValue.to_string gv
  let of_int = GenericValue.of_int

  let lookupFdefViaGVFromFunTable fs (fptr:t) = 
     (if !Globalstates.debug then 
       eprintf "  lookupFdefViaGVFromFunTable fptr=%s" 
       (GenericValue.to_string fptr);flush_all());
        
    match GenericValue.as_function_pointer fptr with
    | Some fv ->
      (** FIXME: Llvm.value_name can fail at runtime, since the binding 
       * does not check if fv can be safely casted into Value. *)
      let fn = "@"^(escaped_value_name fv) in  
      (if !Globalstates.debug then eprintf " fname=%s\n" fn;flush_all());
      Some fn
    | None -> 
      (if !Globalstates.debug then eprintf " None";flush_all());
      None 

  (* let initmem = failwith "initmem undef" *)

  let malloc (td:TargetData.t) m size num (a:LLVMsyntax.align) = 
    let (ee, _) = m in

     (if !Globalstates.debug then 
       eprintf "  Malloc s=%d n=%s a=%d" size (GenericValue.to_string num) a;
       flush_all());      
    
    match (ExecutionEngine.malloc_memory size num ee) with
    | Some gv -> 
        (if !Globalstates.debug then eprintf " ptr=%s\n" 
         (GenericValue.to_string gv);flush_all());        
        Some (m, gv)
    | None -> 
        (if !Globalstates.debug then eprintf " None";flush_all());
        None

  let malloc_one (td:TargetData.t) m size (a:LLVMsyntax.align) = 
    let (ee, mm) = m in
    let ctx = Llvm.module_context mm in

     (if !Globalstates.debug then 
       eprintf "  Malloc s=%d n=1 a=%d" size a;flush_all());      
    
    match (ExecutionEngine.malloc_memory size (GenericValue.of_int 
      (Llvm.integer_type ctx 32) 32) ee) with
    | Some gv -> 
        (if !Globalstates.debug then eprintf " ptr=%s\n" 
         (GenericValue.to_string gv);flush_all());        
        Some (m, gv)
    | None -> 
        (if !Globalstates.debug then eprintf " None";flush_all());
        None

  let free (td:TargetData.t) m ptr =
    let (ee, _) = m in
    (if !Globalstates.debug then 
      eprintf "  Mfree ptr=%s\n" (GenericValue.to_string ptr);flush_all());     
  
    let _ = ExecutionEngine.free_memory ptr ee in
    Some m
 
  let flatten_typ x y = failwith "flatten_typ:na"  
  let flatten_typs x y = failwith "flatten_typs:na"  
  let mload_aux x y z w = failwith "mload_aux:na"
  let mstore_aux x y z w = failwith "mstore_aux:na" 

  let mload (td:TargetData.t) m ptr t (a:LLVMsyntax.align) =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then 
      eprintf "  Mload ptr=%s" (GenericValue.to_string ptr);flush_all());
      
    let gv = ExecutionEngine.load_value_from_memory ptr 
      (coqtype_2_llvmtype ctx mm t) ee in
    
    (if !Globalstates.debug then  eprintf " r=%s\n" (GenericValue.to_string gv);
     flush_all());
    Some gv

  let mstore (td:TargetData.t) m ptr t gv (a:LLVMsyntax.align) =
    let (ee, mm) = td in
    let ctx = Llvm.module_context mm in
    (if !Globalstates.debug then 
      eprintf "  Mstore ptr=%s v=%s\n" (GenericValue.to_string ptr) 
      (GenericValue.to_string gv);flush_all());
    let (ee, _) = m in
    let _ = ExecutionEngine.store_value_to_memory gv ptr 
      (coqtype_2_llvmtype ctx mm t) ee in
    Some m
    
  let initGlobal (td:TargetData.t) gl m (id0:LLVMsyntax.id) 
               (t:LLVMsyntax.typ)(c:LLVMsyntax.const)(align0:LLVMsyntax.align) =
    let (ee, mm) = m in
    
     (if !Globalstates.debug then 
       eprintf "  InitGlobal id=%s" (getRealName id0);flush_all());      
        
    match Llvm.lookup_global (getRealName id0) mm with
    | Some v -> 
       (match ExecutionEngine.get_pointer_to_global_if_available v ee with
       | Some gv -> 
         (if !Globalstates.debug then eprintf " ptr=%s\n" 
          (GenericValue.to_string gv);flush_all());
         Some (gv, m)
       | None -> 
          (if !Globalstates.debug then eprintf " None";flush_all());
         None
       )
    | None -> None

  let getExternalGlobal m (id0:LLVMsyntax.id) =
    let (ee, mm) = m in
    
     (if !Globalstates.debug then 
       eprintf "  getExternalGlobal id=%s" (getRealName id0);flush_all());      
        
    match Llvm.lookup_global (getRealName id0) mm with
    | Some v -> 
       (match ExecutionEngine.get_pointer_to_global_if_available v ee with
       | Some gv -> 
         (if !Globalstates.debug then eprintf " ptr=%s\n" 
          (GenericValue.to_string gv);flush_all());
         Some gv
       | None -> 
          (if !Globalstates.debug then eprintf " None";flush_all());
         None
       )
    | None -> None

  let initTargetData (los:LLVMsyntax.layouts) (nts:LLVMsyntax.namedts) (m:mem) = 
    m

  let callExternalFunction m (fid:LLVMsyntax.id) (args:GenericValue.t list) = 
    (if !Globalstates.debug then 
      eprintf "  Mcall external fun=%s\n" fid;flush_all());
    let (ee, mm) = m in
    match Llvm.lookup_function (getRealName fid) mm with
    | Some fv -> Some (Some (ExecutionEngine.call_external_function fv 
                   (Array.of_list args) ee), m)
    | None -> failwith "callExternalFunction: cannot find function"

  let initFunTable m (fid:LLVMsyntax.id) = 
    (if !Globalstates.debug then 
      eprintf "  initFunTable fun=%s" fid;flush_all());
    let (ee, mm) = m in
    match Llvm.lookup_function (getRealName fid) mm with
    | Some fv -> 
       let fptr = (ExecutionEngine.get_pointer_to_function fv ee) in
       (if !Globalstates.debug then eprintf " fptr=%s\n" 
        (GenericValue.to_string fptr);flush_all());
       Some fptr
    | None -> failwith "initFunTable: cannot find function"
    
  let _const2GV (td:TargetData.t) gl (c:const) : 
    (GenericValue.t * LLVMsyntax.typ) option =
    match const2llvalue td gl c with
    | Some v -> Some (llconst2GV td v, LLVMsyntax.Coq_typ_void)
    | None -> None

  let const2GV (td:TargetData.t) gl (c:const) : GenericValue.t option =
    match const2llvalue td gl c with
    | Some v -> Some (llconst2GV td v)
    | None -> None      

  let getOperandValue (tD:TargetData.t) (v:LLVMsyntax.value) 
    (locals:(LLVMsyntax.id*GenericValue.t) list) 
    (globals:(LLVMsyntax.id*GenericValue.t) list) : GenericValue.t option =
    match v with
    | Coq_value_id id0 -> Alist.lookupAL locals id0
    | Coq_value_const c -> const2GV tD globals c

end
