open Genericvalues
open Syntax

module MDGVs : 
 sig 
  type t = LLVMgv.coq_GenericValue
  
  val cundef_gvs :
    LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> LLVMgv.coq_GenericValue
  
  val undef_gvs : t -> LLVMsyntax.typ -> t
  
  val cgv2gvs :
    LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> LLVMgv.coq_GenericValue
  
  val gv2gvs : LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> t
  
  val lift_op1 :
    (LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> t ->
    LLVMsyntax.typ -> t option
  
  val lift_op2 :
    (LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue ->
    LLVMgv.coq_GenericValue option) -> t -> t -> LLVMsyntax.typ -> t option
 end

val coq_DGVs : Opsem.coq_GenericValues

