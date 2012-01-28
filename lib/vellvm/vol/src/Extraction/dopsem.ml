open Genericvalues
open Syntax

module MDGVs = 
 struct 
  type t = LLVMgv.coq_GenericValue
  
  (** val cundef_gvs :
      LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> LLVMgv.coq_GenericValue **)
  
  let cundef_gvs =
    LLVMgv.cundef_gv
  
  (** val undef_gvs : t -> LLVMsyntax.typ -> t **)
  
  let undef_gvs gv ty =
    gv
  
  (** val cgv2gvs :
      LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> LLVMgv.coq_GenericValue **)
  
  let cgv2gvs =
    LLVMgv.cgv2gv
  
  (** val gv2gvs : LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> t **)
  
  let gv2gvs gv ty =
    gv
  
  (** val lift_op1 :
      (LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> t ->
      LLVMsyntax.typ -> t option **)
  
  let lift_op1 f gvs1 ty =
    f gvs1
  
  (** val lift_op2 :
      (LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue ->
      LLVMgv.coq_GenericValue option) -> t -> t -> LLVMsyntax.typ -> t option **)
  
  let lift_op2 f gvs1 gvs2 ty =
    f gvs1 gvs2
 end

(** val coq_DGVs : Opsem.coq_GenericValues **)

let coq_DGVs =
  { Opsem.cgv2gvs = (Obj.magic MDGVs.cgv2gvs); Opsem.gv2gvs =
    (Obj.magic MDGVs.gv2gvs); Opsem.lift_op1 = (Obj.magic MDGVs.lift_op1);
    Opsem.lift_op2 = (Obj.magic MDGVs.lift_op2) }

