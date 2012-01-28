open Llvm

let string_of_icmp op =
  match op with
  | Icmp.Eq -> "eq"
  | Icmp.Ne -> "ne"
  | Icmp.Ugt -> "ugt"
  | Icmp.Uge -> "uge"
  | Icmp.Ult -> "ult"
  | Icmp.Ule -> "ule"
  | Icmp.Sgt -> "sgt"
  | Icmp.Sge -> "sge"
  | Icmp.Slt -> "slt"
  | Icmp.Sle -> "slt"

let string_of_fcmp op =
  match op with
  | Fcmp.False -> "false"
  | Fcmp.Oeq -> "oeq"
  | Fcmp.Ogt -> "ogt"
  | Fcmp.Oge -> "oge"
  | Fcmp.Olt -> "olt"
  | Fcmp.Ole -> "ole"
  | Fcmp.One -> "one"
  | Fcmp.Ord -> "ord"
  | Fcmp.Uno -> "uno"
  | Fcmp.Ueq -> "ueq"
  | Fcmp.Ugt -> "ugt"
  | Fcmp.Uge -> "uge"
  | Fcmp.Ult -> "ult"
  | Fcmp.Ule -> "ule"
  | Fcmp.Une -> "une"
  | Fcmp.True -> "true"

let is_instruction v =
  match (classify_value v) with
  | ValueTy.Ret -> true       
  | ValueTy.Br -> true 
  | ValueTy.Switch -> true 
  | ValueTy.Invoke -> true
  | ValueTy.Unwind -> true
  | ValueTy.Unreachable -> true
  | ValueTy.Add -> true
  | ValueTy.FAdd -> true 
  | ValueTy.Sub -> true
  | ValueTy.FSub -> true
  | ValueTy.Mul -> true
  | ValueTy.FMul -> true
  | ValueTy.UDiv -> true
  | ValueTy.SDiv -> true
  | ValueTy.FDiv -> true
  | ValueTy.URem -> true
  | ValueTy.SRem -> true
  | ValueTy.FRem -> true
  | ValueTy.Shl -> true
  | ValueTy.LShr -> true
  | ValueTy.AShr -> true
  | ValueTy.And -> true
  | ValueTy.Or -> true
  | ValueTy.Xor -> true
  | ValueTy.Malloc -> true
  | ValueTy.Free -> true
  | ValueTy.Alloca -> true
  | ValueTy.Load -> true
  | ValueTy.Store -> true
  | ValueTy.GetElementPtr -> true
  | ValueTy.Trunc -> true
  | ValueTy.ZExt -> true
  | ValueTy.SExt -> true
  | ValueTy.FPToUI -> true
  | ValueTy.FPToSI -> true
  | ValueTy.UIToFP -> true
  | ValueTy.SIToFP -> true
  | ValueTy.FPTrunc -> true
  | ValueTy.FPExt -> true
  | ValueTy.PtrToInt -> true
  | ValueTy.IntToPtr -> true
  | ValueTy.BitCast -> true
  | ValueTy.ICmp -> true
  | ValueTy.FCmp -> true
  | ValueTy.PHI -> true
  | ValueTy.Call -> true
  | ValueTy.Select -> true
  | ValueTy.UserOp1 -> true
  | ValueTy.UserOp2 -> true
  | ValueTy.VAArg -> true
  | ValueTy.ExtractElement -> true
  | ValueTy.InsertElement -> true
  | ValueTy.ShuffleVector -> true
  | ValueTy.ExtractValue -> true
  | ValueTy.InsertValue  -> true
  | _ -> false

let is_cast_instruction v =
  match (classify_value v) with
  | ValueTy.Trunc -> true
  | ValueTy.ZExt -> true
  | ValueTy.SExt -> true
  | ValueTy.FPToUI -> true
  | ValueTy.FPToSI -> true
  | ValueTy.UIToFP -> true
  | ValueTy.SIToFP -> true
  | ValueTy.FPTrunc -> true
  | ValueTy.FPExt -> true
  | ValueTy.PtrToInt -> true
  | ValueTy.IntToPtr -> true
  | ValueTy.BitCast -> true
  | _ -> false

let is_terminater v =
  match (classify_value v) with
  | ValueTy.Ret -> true       
  | ValueTy.Br -> true 
  | ValueTy.Switch -> true 
  | ValueTy.Invoke -> true
  | ValueTy.Unwind -> true
  | ValueTy.Unreachable -> true
  | _ -> false

let is_binary v =
  match (classify_value v) with
  | ValueTy.Add -> true
  | ValueTy.FAdd -> true 
  | ValueTy.Sub -> true
  | ValueTy.FSub -> true
  | ValueTy.Mul -> true
  | ValueTy.FMul -> true
  | ValueTy.UDiv -> true
  | ValueTy.SDiv -> true
  | ValueTy.FDiv -> true
  | ValueTy.URem -> true
  | ValueTy.SRem -> true
  | ValueTy.FRem -> true 
  | _ -> false

let is_unary_instuction v =
  match (classify_value v) with
  | ValueTy.Malloc -> true
  | ValueTy.Free -> true
  | ValueTy.Alloca -> true
  | ValueTy.Load -> true
  | ValueTy.Store -> true
  | ValueTy.Trunc -> true
  | ValueTy.ZExt -> true
  | ValueTy.SExt -> true
  | ValueTy.FPToUI -> true
  | ValueTy.FPToSI -> true
  | ValueTy.UIToFP -> true
  | ValueTy.SIToFP -> true
  | ValueTy.FPTrunc -> true
  | ValueTy.FPExt -> true
  | ValueTy.PtrToInt -> true
  | ValueTy.IntToPtr -> true
  | ValueTy.BitCast -> true
  | ValueTy.VAArg -> true
  | ValueTy.ExtractValue
  | _ -> false

let is_i1_type t =
  match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 1
  | _ -> false 

let is_i8_type t =
  match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 8
  | _ -> false 

let is_i16_type t =
  match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 16
  | _ -> false 

let is_i32_type t =
  match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 32
  | _ -> false 

let is_i64_type t =
  match (classify_type t) with
  | TypeKind.Integer -> integer_bitwidth t == 64
  | _ -> false 

let concat2 sep arr =
  let s = ref "" in
  if 0 < Array.length arr then begin
    s := !s ^ arr.(0);
    for i = 1 to (Array.length arr) - 1 do
      s := !s ^ sep ^ arr.(i)
    done
  end;
  !s
	
let rec string_of_lltype_safe m ty =
  let nt = name_of_type ty m in
  if nt <> ""
  then nt
  else 
    match classify_type ty with
    TypeKind.Integer -> "i" ^ string_of_int (integer_bitwidth ty)
    | TypeKind.Pointer -> (string_of_lltype_safe m (element_type ty)) ^ "*"
    | TypeKind.Struct ->
      let s = "{ " ^ (concat2 ", " (
                Array.map (string_of_lltype_safe m) (struct_element_types ty)
              )) ^ " }" in
      if is_packed ty
        then "<" ^ s ^ ">"
        else s
    | TypeKind.Array -> "["   ^ (string_of_int (array_length ty)) ^
                        " x " ^ (string_of_lltype_safe m (element_type ty)) ^ "]"
    | TypeKind.Vector -> "<"   ^ (string_of_int (vector_size ty)) ^
                         " x " ^ (string_of_lltype_safe m (element_type ty)) ^ ">"
    | TypeKind.Opaque -> "opaque"
    | TypeKind.Function -> string_of_lltype_safe m (return_type ty) ^
                           " (" ^ (concat2 ", " (
                             Array.map (string_of_lltype_safe m) (param_types ty)
                           )) ^ ")"
    | TypeKind.Label -> "label"
    | TypeKind.Ppc_fp128 -> "ppc_fp128"
    | TypeKind.Fp128 -> "fp128"
    | TypeKind.X86fp80 -> "x86_fp80"
    | TypeKind.Double -> "double"
    | TypeKind.Float -> "float"
    | TypeKind.Void -> "void"
    | TypeKind.Metadata -> "metadata"  

let string_type_of m v =
  string_of_lltype_safe m (type_of v)

let string_of_instr_opcode i = string_of_opcode (classify_instr i)

let string_of_endian e =
  match e with
  | Llvm_target.Endian.Big -> "big"
  | Llvm_target.Endian.Little -> "little"

let string_of_aligntype at =
  match at with
  | Llvm_target.AlignType.Integer_align -> "i" 
  | Llvm_target.AlignType.Vector_align -> "v"
  | Llvm_target.AlignType.Float_align -> "f"
  | Llvm_target.AlignType.Aggregate_align -> "a"
  | Llvm_target.AlignType.Stack_align -> "s"

let string_of_valuety op =
  match op with
  | ValueTy.ArgumentVal -> "ArgumentVal"
  | ValueTy.BasicBlockVal -> "BasicBlockVal"
  | ValueTy.FunctionVal -> "FunctionVal"                  
  | ValueTy.GlobalAliasVal -> "GlobalAliasVal"
  | ValueTy.GlobalVariableVal -> "GlobalVariableVal"
  | ValueTy.UndefValueVal -> "UndefValueVal"
  | ValueTy.ConstantExprVal -> "ConstantExprVal"
  | ValueTy.ConstantAggregateZeroVal -> "ConstantAggregateZeroVal"
  | ValueTy.ConstantIntVal -> "ConstantIntVal"
  | ValueTy.ConstantFPVal -> "ConstantFPVal"
  | ValueTy.ConstantArrayVal -> "ConstantArrayVal"
  | ValueTy.ConstantStructVal -> "ConstantStructVal"
  | ValueTy.ConstantVectorVal -> "ConstantVectorVal"
  | ValueTy.ConstantPointerNullVal -> "ConstantPointerNullVal"
  | ValueTy.MDNodeVal -> "MDNodeVal"
  | ValueTy.MDStringVal -> "MDStringVal"
  | ValueTy.NamedMDNodeVal -> "NamedMDNodeVal"
  | ValueTy.InlineAsmVal -> "InlineAsmVal"
  | ValueTy.PseudoSourceValueVal -> "PseudoSourceValueVal"
  | ValueTy.InstructionVal -> "InstructionVal"
  | ValueTy.Ret -> "Ret"
  | ValueTy.Br -> "Br"
  | ValueTy.Switch -> "Switch"
  | ValueTy.Invoke -> "Invoke"
  | ValueTy.Unwind -> "Unwind"
  | ValueTy.Unreachable -> "Unreachable"
  | ValueTy.Add -> "Add"
  | ValueTy.FAdd -> "FAdd"
  | ValueTy.Sub -> "Sub"
  | ValueTy.FSub -> "FSub"
  | ValueTy.Mul -> "Mul"
  | ValueTy.FMul -> "FMul"
  | ValueTy.UDiv -> "UDiv"
  | ValueTy.SDiv -> "SDiv"
  | ValueTy.FDiv -> "FDiv"
  | ValueTy.URem -> "URem"
  | ValueTy.SRem -> "SRem"
  | ValueTy.FRem -> "FRem"
  | ValueTy.Shl -> "Shl"
  | ValueTy.LShr -> "LShr"
  | ValueTy.AShr -> "AShr"
  | ValueTy.And -> "And"
  | ValueTy.Or -> "Or"
  | ValueTy.Xor -> "Xor"
  | ValueTy.Malloc -> "Malloc"
  | ValueTy.Free -> "Free"
  | ValueTy.Alloca -> "Alloca"
  | ValueTy.Load -> "Load"
  | ValueTy.Store -> "Store"
  | ValueTy.GetElementPtr -> "GetElementPtr"
  | ValueTy.Trunc -> "Trunc"
  | ValueTy.ZExt -> "ZExt"
  | ValueTy.SExt -> "SExt"
  | ValueTy.FPToUI -> "FPToUI"
  | ValueTy.FPToSI -> "FPToSI"
  | ValueTy.UIToFP -> "UIToFP"
  | ValueTy.SIToFP -> "SIToFP"
  | ValueTy.FPTrunc -> "FPTrunc"
  | ValueTy.FPExt -> "FPExt"
  | ValueTy.PtrToInt -> "PtrToInt"
  | ValueTy.IntToPtr -> "IntToPtr"
  | ValueTy.BitCast -> "BitCast"
  | ValueTy.ICmp -> "ICmp"
  | ValueTy.FCmp -> "FCmp"
  | ValueTy.PHI -> "PHI"
  | ValueTy.Call -> "Call"
  | ValueTy.Select -> "Select"
  | ValueTy.UserOp1 -> "UserOp1"
  | ValueTy.UserOp2 -> "UserOp2"
  | ValueTy.VAArg -> "VAArg"
  | ValueTy.ExtractElement -> "ExtractElement"
  | ValueTy.InsertElement -> "InsertElement"
  | ValueTy.ShuffleVector -> "ShuffleVector"
  | ValueTy.ExtractValue -> "ExtractValue"
  | ValueTy.InsertValue -> "InsertValue"

let string_of_linkage lk =
match lk with
  | Linkage.External -> "external"
  | Linkage.Available_externally -> "available_externally"
  | Linkage.Link_once -> "linkonce"
  | Linkage.Link_once_odr -> "linkonce_odr"
  | Linkage.Weak -> "weak"
  | Linkage.Weak_odr -> "weak_odr"
  | Linkage.Appending -> "appending"
  | Linkage.Private -> "private"
  | Linkage.Linker_private -> "linker_private"
  | Linkage.Internal -> "internal"
  | Linkage.Dllimport -> "dllimport"
  | Linkage.Dllexport -> "dllexport"
  | Linkage.External_weak -> "external_weak"
  | Linkage.Ghost -> "ghost"
  | Linkage.Common -> "common"

let escaped_value_name (v:llvalue) : string =
   Llvm.escaped_value_name v



