open Printf
open Llvm
open Llvm_aux
open Syntax
(*open Ssa_lib*)

(** Coq Pretty Printer *)
let translate_floating_point (ctx:llcontext) (fp:LLVMsyntax.floating_point) 
    : lltype =
  match fp with
  | LLVMsyntax.Coq_fp_float -> float_type ctx
  | LLVMsyntax.Coq_fp_double -> double_type ctx
  | LLVMsyntax.Coq_fp_x86_fp80 -> x86fp80_type ctx
  | LLVMsyntax.Coq_fp_fp128 -> fp128_type ctx
  | LLVMsyntax.Coq_fp_ppc_fp128 -> ppc_fp128_type ctx

let rec translate_typ (ctx:llcontext) (m:llmodule) (ty:LLVMsyntax.typ) : lltype =
  match ty with
  | LLVMsyntax.Coq_typ_int sz -> integer_type ctx sz
  | LLVMsyntax.Coq_typ_floatpoint fp -> translate_floating_point ctx fp
  | LLVMsyntax.Coq_typ_void -> void_type ctx
  | LLVMsyntax.Coq_typ_label -> label_type ctx
  | LLVMsyntax.Coq_typ_metadata -> failwith "Metadata: Not_Supported."
  | LLVMsyntax.Coq_typ_array (sz, t) -> array_type (translate_typ ctx m t) sz
  | LLVMsyntax.Coq_typ_function (t, ts, va) -> 
      if va then
        var_arg_function_type (translate_typ ctx m t) 
          (Array.of_list (LLVMsyntax.map_list_typ (translate_typ ctx m) ts))  
      else
        function_type (translate_typ ctx m t) 
          (Array.of_list (LLVMsyntax.map_list_typ (translate_typ ctx m) ts))  
  | LLVMsyntax.Coq_typ_struct ts -> 
       struct_type ctx 
         (Array.of_list (LLVMsyntax.map_list_typ (translate_typ ctx m) ts))
  | LLVMsyntax.Coq_typ_pointer t -> pointer_type (translate_typ ctx m t)
  | LLVMsyntax.Coq_typ_opaque -> opaque_type ctx
  | LLVMsyntax.Coq_typ_namedt id ->  
    begin
      (* FIXME: The alternative way is manually building the named types, but 
         that needs to reimplementing what BitcodeReader::ParserTypeSymbolTable 
         does to deal with recursive types. That sounds out of the scope for the
         current lynx. Lets see if we really need to do so later... *)
      match type_by_name m id with
      | Some ty -> ty
      | None -> failwith "Cannot find a named type."
    end

let rec translate_constant (ctx:llcontext) (m:llmodule) (c:LLVMsyntax.const) 
    : llvalue = 
  match c with
  | LLVMsyntax.Coq_const_zeroinitializer t ->  
      (* FIXME: This is a hack, which maps to zeroconst to a null ptr. *)
      Llvm.const_null (pointer_type (translate_typ ctx m t))
  | LLVMsyntax.Coq_const_int (sz, i) -> Llvm.APInt.const_apint ctx i
  | LLVMsyntax.Coq_const_floatpoint (fp, f) -> Llvm.APFloat.const_apfloat ctx f
  | LLVMsyntax.Coq_const_undef t -> undef (translate_typ ctx m t)
  | LLVMsyntax.Coq_const_null t ->  
      const_null (pointer_type (translate_typ ctx m t))
  | LLVMsyntax.Coq_const_arr (t, cs) -> 
      const_array 
        (translate_typ ctx m t) 
        (Array.of_list (LLVMsyntax.map_list_const (translate_constant ctx m) cs))
  | LLVMsyntax.Coq_const_struct cs -> 
      const_struct ctx 
       (Array.of_list (LLVMsyntax.map_list_const (translate_constant ctx m) cs))
  | LLVMsyntax.Coq_const_gid (_,id) -> failwith "const_gid: Not_Supported."
  | _ -> failwith "const_expr: Not_Supported."
  
let translate_value v =
  match v with
  | LLVMsyntax.Coq_value_id id ->  failwith "Not_Supported."
  | LLVMsyntax.Coq_value_const c ->  failwith "Not_Supported."

let rec translate_params ps =
  match ps with
  | [] -> ""
  | (t, v)::ps' -> failwith "Not_Supported."

let rec translate_list_value vs = failwith "Not_Supported."

let translate_bop bop =
  match bop with
  | LLVMsyntax.Coq_bop_add -> InstrOpcode.Add    
  | LLVMsyntax.Coq_bop_sub -> InstrOpcode.Sub  
  | LLVMsyntax.Coq_bop_mul -> InstrOpcode.Mul
  | LLVMsyntax.Coq_bop_udiv -> InstrOpcode.UDiv
  | LLVMsyntax.Coq_bop_sdiv -> InstrOpcode.SDiv
  | LLVMsyntax.Coq_bop_urem -> InstrOpcode.URem
  | LLVMsyntax.Coq_bop_srem -> InstrOpcode.SRem
  | LLVMsyntax.Coq_bop_shl -> InstrOpcode.Shl
  | LLVMsyntax.Coq_bop_lshr -> InstrOpcode.LShr
  | LLVMsyntax.Coq_bop_ashr -> InstrOpcode.AShr
  | LLVMsyntax.Coq_bop_and -> InstrOpcode.And
  | LLVMsyntax.Coq_bop_or -> InstrOpcode.Or
  | LLVMsyntax.Coq_bop_xor -> InstrOpcode.Xor
                  
let translate_fbop fbop =
  match fbop with
  | LLVMsyntax.Coq_fbop_fadd -> InstrOpcode.FAdd    
  | LLVMsyntax.Coq_fbop_fsub -> InstrOpcode.FSub    
  | LLVMsyntax.Coq_fbop_fmul -> InstrOpcode.FMul    
  | LLVMsyntax.Coq_fbop_fdiv -> InstrOpcode.FDiv    
  | LLVMsyntax.Coq_fbop_frem -> InstrOpcode.FRem    

let translate_extop extop =
  match extop with
  | LLVMsyntax.Coq_extop_s -> failwith "Not_Supported."       
  | LLVMsyntax.Coq_extop_z -> failwith "Not_Supported."
  | LLVMsyntax.Coq_extop_fp -> failwith "Not_Supported."

let translate_castop castop =
  match castop with
  | LLVMsyntax.Coq_castop_fptoui -> failwith "Not_Supported."       
  | LLVMsyntax.Coq_castop_fptosi -> failwith "Not_Supported."   
  | LLVMsyntax.Coq_castop_uitofp -> failwith "Not_Supported."
  | LLVMsyntax.Coq_castop_sitofp -> failwith "Not_Supported."
  | LLVMsyntax.Coq_castop_ptrtoint -> failwith "Not_Supported."
  | LLVMsyntax.Coq_castop_inttoptr -> failwith "Not_Supported."
  | LLVMsyntax.Coq_castop_bitcast -> failwith "Not_Supported."

let translate_icond cond =
  match cond with
  | LLVMsyntax.Coq_cond_eq -> Icmp.Eq    
  | LLVMsyntax.Coq_cond_ne -> Icmp.Ne       
  | LLVMsyntax.Coq_cond_ugt -> Icmp.Ugt    
  | LLVMsyntax.Coq_cond_uge -> Icmp.Uge  
  | LLVMsyntax.Coq_cond_ult -> Icmp.Ult  
  | LLVMsyntax.Coq_cond_ule -> Icmp.Ule  
  | LLVMsyntax.Coq_cond_sgt -> Icmp.Sgt  
  | LLVMsyntax.Coq_cond_sge -> Icmp.Sge  
  | LLVMsyntax.Coq_cond_slt -> Icmp.Slt  
  | LLVMsyntax.Coq_cond_sle -> Icmp.Sle  

let translate_fcond fcond =
  match fcond with
  | LLVMsyntax.Coq_fcond_false -> Fcmp.False       
  | LLVMsyntax.Coq_fcond_oeq -> Fcmp.Oeq
  | LLVMsyntax.Coq_fcond_ogt -> Fcmp.Ogt       
  | LLVMsyntax.Coq_fcond_oge -> Fcmp.Oge       
  | LLVMsyntax.Coq_fcond_olt -> Fcmp.Olt       
  | LLVMsyntax.Coq_fcond_ole -> Fcmp.Ole       
  | LLVMsyntax.Coq_fcond_one -> Fcmp.One       
  | LLVMsyntax.Coq_fcond_ord -> Fcmp.Ord       
  | LLVMsyntax.Coq_fcond_ueq -> Fcmp.Ueq       
  | LLVMsyntax.Coq_fcond_ugt -> Fcmp.Ugt       
  | LLVMsyntax.Coq_fcond_uge -> Fcmp.Uge       
  | LLVMsyntax.Coq_fcond_ult -> Fcmp.Ult       
  | LLVMsyntax.Coq_fcond_ule -> Fcmp.Ule       
  | LLVMsyntax.Coq_fcond_une -> Fcmp.Une
  | LLVMsyntax.Coq_fcond_uno -> Fcmp.Uno       
  | LLVMsyntax.Coq_fcond_true -> Fcmp.True 

let rec translate_list_value_l vls =
  match vls with
  | LLVMsyntax.Cons_list_value_l (v, l, vls') ->  failwith "Not_Supported."
  | LLVMsyntax.Nil_list_value_l -> failwith "Not_Supported."

let rec translate_args args =
  match args with
  | [] -> ""
  | (t, id)::args' -> failwith "Not_Supported."

let translate_terminator i =
  match i with 
  | LLVMsyntax.Coq_insn_br (id, v, l1, l2) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_br_uncond (id, l) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_return (id, t, v) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_return_void id -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_unreachable id -> failwith "Not_Supported."

let translate_cmd i =
  match i with
  | LLVMsyntax.Coq_insn_bop (id, bop, sz, v1, v2) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_fbop (id, fbop, fp, v1, v2) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_extractvalue (id, t, v, cs) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_insertvalue (id, t1, v1, t2, v2, cs) -> 
      failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_malloc (id, t, sz, align) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_alloca (id, t, sz, align) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_free (id, t, v) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_load (id, t, v, a) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_store (id, t, v1, v2, a) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_gep (id, inbounds, t, v, vs) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_trunc (id, truncop, t1, v, t2) -> 
      failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_ext (id, extop, t1, v, t2) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_cast (id, castop, t1, v, t2) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_icmp (id, cond, t, v1, v2) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_fcmp (id, cond, t, v1, v2) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_select (id, v, t, v1, v2) -> failwith "Not_Supported."
  | LLVMsyntax.Coq_insn_call (id, noret, tailc, t, fid, ps) -> 
      failwith "Not_Supported."
          
let translate_phi i =
  match i with
  | LLVMsyntax.Coq_insn_phi (id, t, list_v_l) -> failwith "Not_Supported."
  
let translate_block b =
  match b with
  | LLVMsyntax.Coq_block_intro (l, ps, cs, tmn) -> failwith "Not_Supported."

let translate_fdec f =
  match f with
  | LLVMsyntax.Coq_fheader_intro (_, t, fid, args, var) -> 
      failwith "Not_Supported."

let translate_fdef f =
  match f with
  | LLVMsyntax.Coq_fdef_intro 
      (LLVMsyntax.Coq_fheader_intro (_, t, fid, args, var), bs) -> 
      failwith "Not_Supported."
              
let translate_product g =
  match g with
  | LLVMsyntax.Coq_product_gvar (LLVMsyntax.Coq_gvar_intro 
      (id, lk, spec, t, c, a)) -> failwith "Not_Supported." 
  | LLVMsyntax.Coq_product_gvar (LLVMsyntax.Coq_gvar_external (id, spec, t)) -> 
      failwith "Not_Supported." 
  | LLVMsyntax.Coq_product_fdec f -> failwith "Not_Supported."
  | LLVMsyntax.Coq_product_fdef f -> failwith "Not_Supported."  
  
let translate_layout dlt =
  match dlt with
  | LLVMsyntax.Coq_layout_be -> "E-"
  | LLVMsyntax.Coq_layout_le -> "e-"
  | LLVMsyntax.Coq_layout_ptr (sz, a1, a2) -> "p:" ^ (string_of_int sz) ^ 
                                               ":" ^ (string_of_int a1) ^      
                                               ":" ^ (string_of_int a2) ^
                                               "-"
  | LLVMsyntax.Coq_layout_int (sz, a1, a2) -> "i:" ^ (string_of_int sz) ^ 
                                               ":" ^ (string_of_int a1) ^        
                                               ":" ^ (string_of_int a2) ^
                                               "-"  
  | LLVMsyntax.Coq_layout_float (sz, a1, a2) -> "f:" ^ (string_of_int sz) ^ 
                                                ":" ^ (string_of_int a1) ^      
                                                ":" ^ (string_of_int a2) ^
                                                "-"  
  | LLVMsyntax.Coq_layout_aggr (sz, a1, a2) -> "a:" ^ (string_of_int sz) ^ 
                                                ":" ^ (string_of_int a1) ^      
                                                ":" ^ (string_of_int a2) ^
                                                "-"
  | LLVMsyntax.Coq_layout_stack (sz, a1, a2) -> "s:" ^ (string_of_int sz) ^ 
                                                 ":" ^ (string_of_int a1) ^      
                                                 ":" ^ (string_of_int a2) ^
                                                 "-"
  | LLVMsyntax.Coq_layout_vector (sz, a1, a2) -> "v:" ^ (string_of_int sz) ^ 
                                                 ":" ^ (string_of_int a1) ^      
                                                 ":" ^ (string_of_int a2) ^
                                                 "-"

let rec _translate_layouts dlts =
  match dlts with
  | [] -> ""
  | dlt::dlts' -> translate_layout dlt ^ _translate_layouts dlts'

let translate_layouts dlts =
  let td = _translate_layouts dlts in
  let len = String.length td in
  if len = 0 then td else String.sub td 0 (len - 1)

let translate_module m =
  prerr_endline "Translate module (Coq2LLVM):";
  match m with
  | LLVMsyntax.Coq_module_intro (dlts, nts, ps) -> ()
  
