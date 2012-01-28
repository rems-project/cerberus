open Printf
open Llvm
open Llvm_aux

(** [PrintLLVMName], generate slots if [v] does not have a name. *)
let llvm_name st v =
  if (has_name v)
  then
    if (is_globalvalue v)
    then "@"^value_name v
    else "%"^value_name v
  else
  if (is_globalvalue v)
  then
    "@"^(string_of_int (SlotTracker.get_global_slot st v))
  else
    "%"^(string_of_int (SlotTracker.get_local_slot st v))

let llvm_label st b =
  let v = value_of_block b in
  if (has_name v)
  then
    value_name v
  else
    string_of_int (SlotTracker.get_local_slot st v)

(** [writeConstantInt] *)
let rec string_of_constant m st c = 
  match (classify_value c) with
  | ValueTy.UndefValueVal -> "undef"
  | ValueTy.ConstantExprVal -> string_of_constant_expr m st c
  | ValueTy.ConstantAggregateZeroVal -> "zeroinitializer"
  | ValueTy.ConstantIntVal ->
      if (is_i1_type (type_of c))
      then
        if (Int64.compare (const_int_get_zextvalue c) Int64.zero) == 0 
        then "false"
        else "true"
      else   
        APInt.to_string (APInt.const_int_get_value c)
  | ValueTy.ConstantFPVal -> APFloat.to_string (APFloat.const_float_get_value c)
  | ValueTy.ConstantArrayVal -> 
      let ops = operands c in 
      Array.fold_right (fun c cs -> (string_of_constant m st c)^" "^cs) ops ""   
  | ValueTy.ConstantStructVal ->
      let ops = operands c in 
      Array.fold_right (fun c cs -> (string_of_constant m st c)^" "^cs) ops ""   
  | ValueTy.ConstantVectorVal -> "ConstantVector"
  | ValueTy.ConstantPointerNullVal -> "null"
  | ValueTy.GlobalVariableVal ->  llvm_name st c
  | ValueTy.FunctionVal ->  llvm_name st c
  | _ -> failwith (string_of_valuety (classify_value c) ^ " isnt Constant")
and string_of_constant_expr m st c =
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
        "add ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.FAdd ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FAdd must have 2 operand."
      else
        "fadd ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.Sub ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Sub must have 2 operand."
      else
        "sub ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.FSub ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FSub must have 2 operand."
      else
        "fsub ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.Mul ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Mul must have 2 operand."
      else
        "mul ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.FMul ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FMul must have 2 operand."
      else
        "fmul ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.UDiv ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const UDiv must have 2 operand."
      else
        "udiv ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.SDiv ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const SDiv must have 2 operand."
      else
        "sdiv ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.FDiv ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FDiv must have 2 operand."
      else
        "fdiv ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.URem ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const URem must have 2 operand."
      else
        "urem ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.SRem ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const SRem must have 2 operand."
      else
        "srem ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.FRem ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FRem must have 2 operand."
      else
        "frem ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.Shl ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Shl must have 2 operand."
      else
        "shl ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.LShr ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const LShr must have 2 operand."
      else
        "lshr ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.AShr ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const AShr must have 2 operand."
      else
        "ashr ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.And ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const And must have 2 operand."
      else
        "and ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.Or ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const Or must have 2 operand."
      else
        "or ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.Xor ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const XOr must have 2 operand."
      else
        "xor ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
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
            (string_of_constant m st (Array.get ops b))^" "^(range (b + 1) e ops)
          else
            "" in
        "getelementptr ("^
        string_of_bool (Llvm.GetElementPtrInst.is_in_bounds c)^" "^
        string_of_constant m st (Array.get ops 0)^" "^
        range 1 n ops^")"
  | InstrOpcode.Trunc ->        
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const Trunc must have 1 operand."
      else
        "trunc ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  | InstrOpcode.ZExt ->        
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const ZExt must have 1 operand."
      else
        "zext ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  | InstrOpcode.SExt ->        
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const SExt must have 1 operand."
      else
        "sext ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.FPToUI ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const FPToUI must have 1 operand."
      else
        "fptoui ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.FPToSI ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const FPToSI must have 1 operand."
      else
        "fptosi ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.UIToFP ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const UIToFP must have 1 operand."
      else
        "uitofp ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.SIToFP ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const SIToFP must have 1 operand."
      else
        "sitofp ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.FPTrunc ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const FPTrunc must have 1 operand."
      else
        "fptrunc ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.FPExt ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const FPExt must have 1 operand."
      else
        "fpext ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.PtrToInt ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const PtrToInt must have 1 operand."
      else
        "ptrtoint ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.IntToPtr ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const IntToPtr must have 1 operand."
      else
        "inttoptr ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  |  InstrOpcode.BitCast ->
      let ops = operands c in
      let n = num_operand c in
      if n != 1
      then failwith "Const BitCast must have 1 operand."
      else
        "bitcast ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_type_of m c^")"
  | InstrOpcode.ICmp ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const ICmp must have 2 operand."
      else
        "icmp ("^
        (string_of_icmp (ICmpInst.const_get_predicate c))^" "^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
  | InstrOpcode.FCmp ->
      let ops = operands c in
      let n = num_operand c in
      if n != 2
      then failwith "Const FCmp must have 2 operand."
      else
        "fcmp ("^
        (string_of_fcmp (FCmpInst.const_get_predicate c))^" "^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^")"
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
        "select ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^" "^
        string_of_constant m st (Array.get ops 2)^")"
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
      failwith "Sont ShuffleVector: Not_Supported"
  | InstrOpcode.ExtractValue ->      
      let ops = operands c in
      let n = num_operand c in
      if n < 2
      then failwith "Const ExtractValue must have >=2 operand."
      else
        let rec range b e ops =
          if b < e
          then
            (string_of_constant m st (Array.get ops b))^" "^(range (b + 1) e ops)
          else
            "" in
        "extractvalue ("^
        string_of_constant m st (Array.get ops 0)^" "^
        (range 1 n ops)^")"
  | InstrOpcode.InsertValue ->      
      let ops = operands c in
      let n = num_operand c in
      if n < 3
      then failwith "Const InsertValue must have >=3 operand."
      else
        let rec range b e ops =
          if b < e
          then
            (string_of_constant m st (Array.get ops b))^" "^(range (b + 1) e ops)
          else
            "" in
        "insertvalue ("^
        string_of_constant m st (Array.get ops 0)^" "^
        string_of_constant m st (Array.get ops 1)^" "^
        (range 2 n ops)^")"

(** See [WriteAsOperandInternal] - used by [string_of_operand], it prints out
    the name of [v] without its type. *)
let string_of_operand_internal m st v =
  match (classify_value v) with
  | ValueTy.ArgumentVal -> llvm_name st v
  | ValueTy.BasicBlockVal -> llvm_name st v
  | ValueTy.FunctionVal -> llvm_name st v                  (*GlobalValue*)
  | ValueTy.GlobalAliasVal -> llvm_name st v               (*GlobalValue*)
  | ValueTy.GlobalVariableVal -> llvm_name st v            (*GlobalValue*)
  | ValueTy.UndefValueVal -> string_of_constant m st v
  | ValueTy.ConstantExprVal -> string_of_constant m st v
  | ValueTy.ConstantAggregateZeroVal -> string_of_constant m st v
  | ValueTy.ConstantIntVal -> string_of_constant m st v
  | ValueTy.ConstantFPVal -> string_of_constant m st v
  | ValueTy.ConstantArrayVal -> string_of_constant m st v
  | ValueTy.ConstantStructVal -> string_of_constant m st v
  | ValueTy.ConstantVectorVal -> string_of_constant m st v
  | ValueTy.ConstantPointerNullVal -> string_of_constant m st v
  | ValueTy.MDNodeVal -> "MDNodeVal"
  | ValueTy.MDStringVal -> "MDStringVal"
  | ValueTy.NamedMDNodeVal -> "NamedMDNodeVal"
  | ValueTy.InlineAsmVal -> "InlineAsmVal"
  | ValueTy.PseudoSourceValueVal -> "PseudoSourceValueVal"
  | _ -> llvm_name st v                                    (*Instruction*)

(** See [WriteAsOperand] - Write the name of the specified value out to the specified
    ostream.  This can be useful when you just want to print int %reg126, not
    the whole instruction that generated it. *)
(* optional argument must be followed by at least one non-optional argument,*)
(* at this case, ?(btype = true) cannot be at the end of this argument list. *)    
let string_of_operand ?(btype = true) m st v =
  let s =  string_of_operand_internal m st v in
  if btype
  then (string_type_of m v)^" "^s
  else s

let string_of_operands m st i =
  let ops = operands i in
  let n = num_operand i in
  let rec range b e ops =
    if b + 1 < e 
    then
      (string_of_operand m st (Array.get ops b))^", "^(range (b+1) e ops) 
    else
      (string_of_operand m st (Array.get ops b)) in
  if n == 0 
  then 
    ""
  else
    range 0 n ops

let travel_other_instr m st i =
  eprintf "  %s = %s %s\n" (llvm_name st i) (string_of_instr_opcode i) 
    (string_of_operands m st i);
  flush_all ()
  
let travel_cast_instr m st i =
  eprintf "  %s = %s %s to %s\n"
    (llvm_name st i)
    (string_of_opcode (classify_instr i))
    (string_of_operand m st (operand i 0))
    (string_type_of m i);
  flush_all ()

let travel_instr m st i =
  match (classify_instr i) with
  | InstrOpcode.Br ->
      if (BranchInst.is_conditional i)
      then 
        begin
          eprintf "  %s = br %s, %s, %s\n"
            (llvm_name st i)
            (string_of_operand m st (BranchInst.get_condition i))
            (string_of_operand m st (value_of_block 
              (BranchInst.get_successor i 0)))
            (string_of_operand m st (value_of_block 
              (BranchInst.get_successor i 1)));
          flush_all ()
        end        
      else
        travel_other_instr m st i
  | InstrOpcode.Malloc ->
      eprintf "  %s = malloc %s, %s, align %n\n"
        (llvm_name st i)
        (string_of_lltype_safe m (AllocationInst.get_allocated_type i))
        (string_of_operand m st (AllocationInst.get_array_size i))
        (AllocationInst.get_alignment i);
      flush_all ()
  | InstrOpcode.Alloca ->
      eprintf "  %s = alloca %s, %s, align %n\n"
        (llvm_name st i)
        (string_of_lltype_safe m (AllocationInst.get_allocated_type i))
        (string_of_operand m st (AllocationInst.get_array_size i))
        (AllocationInst.get_alignment i);
      flush_all ()    
  | InstrOpcode.Load ->
      eprintf "  %s = load %s, align %n\n" 
        (llvm_name st i)  
        (string_of_operands m st i) 
        (LoadInst.get_alignment i);
      flush_all ()            
  | InstrOpcode.Store ->
      eprintf "  %s = store %s, align %n\n" 
        (llvm_name st i)  
        (string_of_operands m st i) 
        (StoreInst.get_alignment i);
      flush_all ()    
  | InstrOpcode.ICmp ->
      eprintf "  %s = icmp %s %s\n" 
        (llvm_name st i) 
        (string_of_icmp (ICmpInst.get_predicate i))
        (string_of_operands m st i);
      flush_all ()            
  | InstrOpcode.FCmp ->
      eprintf "  %s = fcmp %s %s\n" 
        (llvm_name st i)  
        (string_of_fcmp (FCmpInst.get_predicate i))
        (string_of_operands m st i);
      flush_all ()            
  | InstrOpcode.Call ->
      let fv = operand i 0 in
      let fname = string_of_operands m st fv in
      let ptyp = type_of fv in
      let ftyp = element_type ptyp in
      let rtyp = return_type ftyp in
      let atyp = " (" ^ (concat2 ", " (
                  Array.map (string_of_lltype_safe m) (param_types ftyp)
                 )) ^ ")" in      
      eprintf "  %s = call %s with rtyp=%s atyp=%s fid=%s\n" 
        (llvm_name st i) 
        (string_of_operands m st i)
        (string_of_lltype_safe m rtyp) 
        atyp
        fname;
      flush_all ()                             
  | _ ->
      if is_cast_instruction i 
      then travel_cast_instr m st i
      else travel_other_instr m st i

let travel_block m st b =
  prerr_string "label: ";
  prerr_endline (llvm_label st b);
  iter_instrs (travel_instr m st) b;
  prerr_newline ()

let travel_function m st f =
  SlotTracker.incorporate_function st f;
  prerr_string (if (is_declaration f)  then "declare " else "define "); 
  prerr_string "fname: ";
  prerr_string (llvm_name st f);
  prerr_string " with ftyp: ";
  prerr_string (string_of_lltype_safe m (type_of f));
  prerr_string " with params: ";
  Array.iter 
    (fun param -> 
      prerr_string (string_of_operand m st param); 
      prerr_string ", "
    ) 
    (params f);
  prerr_newline ();
  iter_blocks (travel_block m st) f;
  SlotTracker.purge_function st
  
let travel_global m st g =
  match (classify_value g) with
  | ValueTy.GlobalVariableVal -> 
    prerr_string (llvm_name st g);
    prerr_string " = ";
    prerr_string (string_of_linkage (linkage g));
    prerr_string (if (is_global_constant g) then  " constant " else " global ");
    if (has_initializer g)
    then
      prerr_string (string_of_operand m st (get_initializer g));
    prerr_newline ()
  | ValueTy.GlobalAliasVal -> dump_value g
  | ValueTy.FunctionVal -> travel_function m st g
  | _ -> failwith "Not_Global"

let travel_layout dlt =
  let tg = Llvm_target.TargetData.create dlt in
  let n = Llvm_target.get_num_alignment tg in
  prerr_string "layouts: ";
  prerr_endline dlt;
  eprintf "byteorde=%s\n"
    (string_of_endian (Llvm_target.byte_order tg));
  eprintf "p size=%s abi=%s pref=%s\n"
    (string_of_int ((Llvm_target.pointer_size tg)*8))
    (string_of_int ((Llvm_target.pointer_abi_alignment tg)*8))
    (string_of_int ((Llvm_target.pointer_pref_alignment tg)*8));
  for i = 0 to n-1 do
    eprintf "typ=%s bitwidth=%s abi=%s pref=%s\n"
      (string_of_aligntype (Llvm_target.get_align_type_enum tg i))
      (string_of_int (Llvm_target.get_type_bitwidth tg i))
      (string_of_int ((Llvm_target.get_abi_align tg i)*8))
      (string_of_int ((Llvm_target.get_pref_align tg i)*8));
    flush_all()
  done;
  Llvm_target.TargetData.dispose tg
  
let string_of_namedt m ty =
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
    
let travel_namedt m nt =
  match type_by_name m nt with
  | Some ty -> eprintf "%s=%s\n" nt (string_of_namedt m ty)
  | None -> failwith "Cannot find a named type!"    

let travel_module st m =
  prerr_endline "Travel LLVM module:";  
  travel_layout (data_layout m);
  iter_named_types (travel_namedt m) m;
  iter_globals (travel_global m st) m;
  iter_functions (travel_function m st) m

