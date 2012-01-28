open BinInt
open Compare_dec
open Coqlib
open Datatypes
open Zdiv
open Syntax

module LLVMtd : 
 sig 
  type coq_TargetData = Llvmcaml.TargetData.t
  
  val coq_DTD : LLVMsyntax.layout list
  
  val coq_RoundUpAlignment : nat -> nat -> nat
  
  val _getIntAlignmentInfo :
    LLVMsyntax.layouts -> nat -> bool -> (nat*(nat*nat)) option ->
    (nat*(nat*nat)) option -> nat option
  
  val getIntDefaultAlignmentInfo : nat -> bool -> nat
  
  val getIntAlignmentInfo : LLVMsyntax.layouts -> nat -> bool -> nat
  
  val _getPointerAlignmentInfo : LLVMsyntax.layouts -> bool -> nat option
  
  val getPointerAlignmentInfo : LLVMsyntax.layouts -> bool -> nat
  
  val _getStructAlignmentInfo : LLVMsyntax.layouts -> bool -> nat option
  
  val getStructAlignmentInfo : LLVMsyntax.layouts -> bool -> nat
  
  val _getPointerSize : LLVMsyntax.layouts -> LLVMsyntax.sz option
  
  val getPointerSize0 : LLVMsyntax.layouts -> LLVMsyntax.sz
  
  val getPointerSize : coq_TargetData -> LLVMsyntax.sz
  
  val getPointerSizeInBits : LLVMsyntax.layouts -> LLVMsyntax.sz
  
  val getFloatAlignmentInfo : LLVMsyntax.layouts -> nat -> bool -> nat
  
  val _getTypeSizeInBits_and_Alignment :
    LLVMsyntax.layouts -> (LLVMsyntax.id*(nat*nat)) list -> bool ->
    LLVMsyntax.typ -> (nat*nat) option
  
  val _getListTypeSizeInBits_and_Alignment :
    LLVMsyntax.layouts -> (LLVMsyntax.id*(nat*nat)) list ->
    LLVMsyntax.list_typ -> (nat*nat) option
  
  val _getTypeSizeInBits_and_Alignment_for_namedts :
    LLVMsyntax.layouts -> LLVMsyntax.namedts -> bool ->
    (LLVMsyntax.id*(nat*nat)) list
  
  val getTypeSizeInBits_and_Alignment_for_namedts :
    coq_TargetData -> bool -> (LLVMsyntax.id*(nat*nat)) list
  
  val getTypeSizeInBits_and_Alignment :
    coq_TargetData -> bool -> LLVMsyntax.typ -> (nat*nat) option
  
  val getListTypeSizeInBits_and_Alignment :
    coq_TargetData -> bool -> LLVMsyntax.list_typ -> (nat*nat) option
  
  val getAlignment : coq_TargetData -> LLVMsyntax.typ -> bool -> nat option
  
  val getABITypeAlignment : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val getPrefTypeAlignment : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val getTypeSizeInBits : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val getTypeStoreSize : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val getTypeStoreSizeInBits : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val getTypeAllocSize :
    coq_TargetData -> LLVMsyntax.typ -> LLVMsyntax.sz option
  
  val getTypeAllocSizeInBits : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val getStructSizeInBytes : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val getStructSizeInBits : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val getStructAlignment : coq_TargetData -> LLVMsyntax.typ -> nat option
  
  val _getStructElementOffset :
    coq_TargetData -> LLVMsyntax.list_typ -> nat -> nat -> nat option
  
  val getStructElementOffset :
    coq_TargetData -> LLVMsyntax.typ -> nat -> nat option
  
  val getStructElementOffsetInBits :
    coq_TargetData -> LLVMsyntax.typ -> nat -> nat option
  
  val _getStructElementContainingOffset :
    coq_TargetData -> LLVMsyntax.list_typ -> nat -> nat -> nat -> nat option
  
  val getStructElementContainingOffset :
    coq_TargetData -> LLVMsyntax.typ -> nat -> nat option
 end

