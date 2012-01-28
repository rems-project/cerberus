open BinInt
open Compare_dec
open Coqlib
open Datatypes
open Zdiv
open Syntax

module LLVMtd = 
 struct 
  type coq_TargetData = Llvmcaml.TargetData.t
  
  (** val coq_DTD : LLVMsyntax.layout list **)
  
  let coq_DTD =
    LLVMsyntax.Coq_layout_be::((LLVMsyntax.Coq_layout_int
      (LLVMsyntax.Size.coq_One, LLVMsyntax.Align.coq_One,
      LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_layout_int
      (LLVMsyntax.Size.coq_Eight, LLVMsyntax.Align.coq_One,
      LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_layout_int
      (LLVMsyntax.Size.coq_Sixteen, LLVMsyntax.Align.coq_Two,
      LLVMsyntax.Align.coq_Two))::((LLVMsyntax.Coq_layout_int
      (LLVMsyntax.Size.coq_ThirtyTwo, LLVMsyntax.Align.coq_Four,
      LLVMsyntax.Align.coq_Four))::((LLVMsyntax.Coq_layout_int
      (LLVMsyntax.Size.coq_SixtyFour, LLVMsyntax.Align.coq_Four,
      LLVMsyntax.Align.coq_Four))::((LLVMsyntax.Coq_layout_float
      (LLVMsyntax.Size.coq_ThirtyTwo, LLVMsyntax.Align.coq_Four,
      LLVMsyntax.Align.coq_Four))::((LLVMsyntax.Coq_layout_float
      (LLVMsyntax.Size.coq_SixtyFour, LLVMsyntax.Align.coq_Four,
      LLVMsyntax.Align.coq_Four))::((LLVMsyntax.Coq_layout_aggr
      (LLVMsyntax.Size.coq_Zero, LLVMsyntax.Align.coq_Zero,
      LLVMsyntax.Align.coq_Eight))::((LLVMsyntax.Coq_layout_ptr
      (LLVMsyntax.Size.coq_ThirtyTwo, LLVMsyntax.Align.coq_Four,
      LLVMsyntax.Align.coq_Four))::[])))))))))
  
  (** val coq_RoundUpAlignment : nat -> nat -> nat **)
  
  let coq_RoundUpAlignment val0 alignment =
    let zv = coq_Z_of_nat val0 in
    let za = coq_Z_of_nat alignment in
    let zr = coq_Zplus zv za in nat_of_Z (coq_Zmult (coq_Zdiv zr za) za)
  
  (** val _getIntAlignmentInfo :
      LLVMsyntax.layouts -> nat -> bool -> (nat*(nat*nat)) option ->
      (nat*(nat*nat)) option -> nat option **)
  
  let rec _getIntAlignmentInfo = Llvmcaml.TargetData._getIntAlignmentInfo
  
  (** val getIntDefaultAlignmentInfo : nat -> bool -> nat **)
  
  let getIntDefaultAlignmentInfo bitWidth aBIInfo =
    if le_lt_dec (S O) bitWidth
    then S O
    else if le_lt_dec (S (S (S (S (S (S (S (S O)))))))) bitWidth
         then S O
         else if le_lt_dec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O)))))))))))))))) bitWidth
              then S (S O)
              else if le_lt_dec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        O)))))))))))))))))))))))))))))))) bitWidth
                   then S (S (S (S O)))
                   else (match bitWidth with
                           | O -> S (S (S (S O)))
                           | S x -> S (S (S (S (S (S (S (S O))))))))
  
  (** val getIntAlignmentInfo : LLVMsyntax.layouts -> nat -> bool -> nat **)
  
  let getIntAlignmentInfo = Llvmcaml.TargetData.getIntAlignmentInfo
  
  (** val _getPointerAlignmentInfo :
      LLVMsyntax.layouts -> bool -> nat option **)
  
  let rec _getPointerAlignmentInfo = Llvmcaml.TargetData._getPointerAlignmentInfo
  
  (** val getPointerAlignmentInfo : LLVMsyntax.layouts -> bool -> nat **)
  
  let getPointerAlignmentInfo = Llvmcaml.TargetData.getPointerAlignmentInfo
  
  (** val _getStructAlignmentInfo :
      LLVMsyntax.layouts -> bool -> nat option **)
  
  let rec _getStructAlignmentInfo = Llvmcaml.TargetData._getStructAlignmentInfo
  
  (** val getStructAlignmentInfo : LLVMsyntax.layouts -> bool -> nat **)
  
  let getStructAlignmentInfo = Llvmcaml.TargetData.getStructAlignmentInfo
  
  (** val _getPointerSize : LLVMsyntax.layouts -> LLVMsyntax.sz option **)
  
  let rec _getPointerSize = Llvmcaml.TargetData._getPointerSize
  
  (** val getPointerSize0 : LLVMsyntax.layouts -> LLVMsyntax.sz **)
  
  let getPointerSize0 = Llvmcaml.TargetData.getPointerSize0
  
  (** val getPointerSize : coq_TargetData -> LLVMsyntax.sz **)
  
  let getPointerSize = Llvmcaml.TargetData.getPointerSize
  
  (** val getPointerSizeInBits : LLVMsyntax.layouts -> LLVMsyntax.sz **)
  
  let getPointerSizeInBits = Llvmcaml.TargetData.getPointerSizeInBits
  
  (** val getFloatAlignmentInfo :
      LLVMsyntax.layouts -> nat -> bool -> nat **)
  
  let rec getFloatAlignmentInfo = Llvmcaml.TargetData.getFloatAlignmentInfo
  
  (** val _getTypeSizeInBits_and_Alignment :
      LLVMsyntax.layouts -> (LLVMsyntax.id*(nat*nat)) list -> bool ->
      LLVMsyntax.typ -> (nat*nat) option **)
  
  let rec _getTypeSizeInBits_and_Alignment = Llvmcaml.TargetData._getTypeSizeInBits_and_Alignment
  
  (** val _getListTypeSizeInBits_and_Alignment :
      LLVMsyntax.layouts -> (LLVMsyntax.id*(nat*nat)) list ->
      LLVMsyntax.list_typ -> (nat*nat) option **)
  
  and _getListTypeSizeInBits_and_Alignment = Llvmcaml.TargetData._getListTypeSizeInBits_and_Alignment
  
  (** val _getTypeSizeInBits_and_Alignment_for_namedts :
      LLVMsyntax.layouts -> LLVMsyntax.namedts -> bool ->
      (LLVMsyntax.id*(nat*nat)) list **)
  
  let rec _getTypeSizeInBits_and_Alignment_for_namedts = Llvmcaml.TargetData._getTypeSizeInBits_and_Alignment_for_namedts
  
  (** val getTypeSizeInBits_and_Alignment_for_namedts :
      coq_TargetData -> bool -> (LLVMsyntax.id*(nat*nat)) list **)
  
  let getTypeSizeInBits_and_Alignment_for_namedts = Llvmcaml.TargetData.getTypeSizeInBits_and_Alignment_for_namedts
  
  (** val getTypeSizeInBits_and_Alignment :
      coq_TargetData -> bool -> LLVMsyntax.typ -> (nat*nat) option **)
  
  let getTypeSizeInBits_and_Alignment = Llvmcaml.TargetData.getTypeSizeInBits_and_Alignment
  
  (** val getListTypeSizeInBits_and_Alignment :
      coq_TargetData -> bool -> LLVMsyntax.list_typ -> (nat*nat) option **)
  
  let getListTypeSizeInBits_and_Alignment = Llvmcaml.TargetData.getListTypeSizeInBits_and_Alignment
  
  (** val getAlignment :
      coq_TargetData -> LLVMsyntax.typ -> bool -> nat option **)
  
  let getAlignment = Llvmcaml.TargetData.getAlignment
  
  (** val getABITypeAlignment :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getABITypeAlignment = Llvmcaml.TargetData.getABITypeAlignment
  
  (** val getPrefTypeAlignment :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getPrefTypeAlignment = Llvmcaml.TargetData.getPrefTypeAlignment
  
  (** val getTypeSizeInBits :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getTypeSizeInBits = Llvmcaml.TargetData.getTypeSizeInBits
  
  (** val getTypeStoreSize :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getTypeStoreSize = Llvmcaml.TargetData.getTypeStoreSize
  
  (** val getTypeStoreSizeInBits :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getTypeStoreSizeInBits = Llvmcaml.TargetData.getTypeStoreSizeInBits
  
  (** val getTypeAllocSize :
      coq_TargetData -> LLVMsyntax.typ -> LLVMsyntax.sz option **)
  
  let getTypeAllocSize = Llvmcaml.TargetData.getTypeAllocSize
  
  (** val getTypeAllocSizeInBits :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getTypeAllocSizeInBits = Llvmcaml.TargetData.getTypeAllocSizeInBits
  
  (** val getStructSizeInBytes :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getStructSizeInBytes = Llvmcaml.TargetData.getStructSizeInBytes
  
  (** val getStructSizeInBits :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getStructSizeInBits = Llvmcaml.TargetData.getStructSizeInBits
  
  (** val getStructAlignment :
      coq_TargetData -> LLVMsyntax.typ -> nat option **)
  
  let getStructAlignment = Llvmcaml.TargetData.getStructAlignment
  
  (** val _getStructElementOffset :
      coq_TargetData -> LLVMsyntax.list_typ -> nat -> nat -> nat option **)
  
  let rec _getStructElementOffset = Llvmcaml.TargetData._getStructElementOffset
  
  (** val getStructElementOffset :
      coq_TargetData -> LLVMsyntax.typ -> nat -> nat option **)
  
  let getStructElementOffset = Llvmcaml.TargetData.getStructElementOffset
  
  (** val getStructElementOffsetInBits :
      coq_TargetData -> LLVMsyntax.typ -> nat -> nat option **)
  
  let getStructElementOffsetInBits = Llvmcaml.TargetData.getStructElementOffsetInBits
  
  (** val _getStructElementContainingOffset :
      coq_TargetData -> LLVMsyntax.list_typ -> nat -> nat -> nat -> nat
      option **)
  
  let rec _getStructElementContainingOffset = Llvmcaml.TargetData._getStructElementContainingOffset
  
  (** val getStructElementContainingOffset :
      coq_TargetData -> LLVMsyntax.typ -> nat -> nat option **)
  
  let getStructElementContainingOffset = Llvmcaml.TargetData.getStructElementContainingOffset
 end

