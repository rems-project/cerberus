Require Import List.

Require Import AilSyntax AilAux AilWf AilTypingAux Implementation.

Inductive eTypeL : P -> gamma -> sigma -> expressionL -> typeCategory -> Prop :=
 | ETypeLDef : forall P G S l e tyC,
     eType  P G S e tyC ->
     eTypeL P G S (ExpLDef l e) tyC
with eType : P -> gamma -> sigma -> expression -> typeCategory -> Prop :=
 | ETypeVariable : forall P G S ty v,
     GammaMap.find v G = Some ty ->
     SigmaMap.find v S = None ->
     eType P G S (ExpVariable v) (LvalueT ty)
 | ETypeFunction : forall P G S v ty sL,
     SigmaMap.find v S = Some (ty, sL) ->
     GammaMap.find v G = None ->
     eType P G S (ExpVariable v) (ExpressionT ty)
 | ETypeConstantInt : forall P G S n,
     inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed Int))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantSuffix n))) (ExpressionT (Basic QualifierSet.empty (Integer (Signed Int))))
 | ETypeConstantLong : forall P G S n,
      ~ inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed Int))) ->
        inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed Long))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantSuffix n))) (ExpressionT (Basic QualifierSet.empty (Integer (Signed Long))))
 | ETypeConstantLongLong : forall P G S n,
      ~ inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed Long))) ->
        inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed LongLong))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantSuffix n))) (ExpressionT (Basic QualifierSet.empty (Integer (Signed Long))))
 | ETypeConstantUInt : forall P G S n,
     inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned Int))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixUnsigned))) (ExpressionT (Basic QualifierSet.empty (Integer (Unsigned Int))))
 | ETypeConstantULong : forall P G S n,
      ~ inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned Int ))) ->
        inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned Long))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixUnsigned))) (ExpressionT (Basic QualifierSet.empty (Integer (Unsigned Long))))
 | ETypeConstantULongLong : forall P G S n,
      ~ inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned Long    ))) ->
        inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned LongLong))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixUnsigned))) (ExpressionT (Basic QualifierSet.empty (Integer (Unsigned LongLong))))
 | ETypeConstantLLong : forall P G S n,
     inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed Long))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixLong))) (ExpressionT (Basic QualifierSet.empty (Integer (Signed Long))))
 | ETypeConstantLLongLong : forall P G S n,
      ~ inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed Long    )))  ->
        inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed LongLong))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixLong))) (ExpressionT (Basic QualifierSet.empty (Integer (Signed LongLong))))
 | ETypeConstantULLong : forall P G S n,
     inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned Long))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixLong))) (ExpressionT (Basic QualifierSet.empty (Integer (Unsigned Long))))
 | ETypeConstantULLongLong : forall P G S n,
      ~ inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned Long    ))) ->
        inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned LongLong))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixLong))) (ExpressionT (Basic QualifierSet.empty (Integer (Unsigned LongLong))))
 | ETypeConstantLL : forall P G S n,
     inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Signed LongLong))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixLong))) (ExpressionT (Basic QualifierSet.empty (Integer (Signed LongLong))))
 | ETypeConstantULL : forall P G S n,
     inRange P (Z_of_nat n) (Basic QualifierSet.empty (Integer (Unsigned LongLong))) ->
     eType P G S (ExpConstant (ConstantInteger (IntegerConstantPlain n SuffixLong))) (ExpressionT (Basic QualifierSet.empty (Integer (Unsigned LongLong))))
 | ETypeCall : forall P G S eL eL_list ty ty_list n,
     length eL_list = n ->
     length ty_list = n ->
     eTypeT P G S eL (Pointer QualifierSet.empty (Function ty ty_list)) ->
     (forall eL ty, In (eL, ty) (combine eL_list ty_list) -> (isAssignable P G S eL ty)) ->
     eType P G S (ExpCall eL eL_list) (ExpressionT ty)
 | ETypeAddressFunction : forall P G S eL ty ty_list,
     eTypeL P G S eL (ExpressionT (Function ty ty_list)) ->
     eType P G S (ExpUnary Address eL) (ExpressionT (Pointer QualifierSet.empty (Function ty ty_list)))
 | ETypeAddressLvalue : forall P G S eL ty,
     eTypeL P G S eL (LvalueT ty) ->
(*
      ~ (  isRegister ty  )  ->
*)
     eType P G S (ExpUnary Address eL) (ExpressionT (Pointer QualifierSet.empty ty))
 | ETypeIndirectionObject : forall P G S eL ty,
     eTypeT P G S eL (Pointer QualifierSet.empty ty) ->
     isComplete ty ->
     isObject ty ->
     eType P G S (ExpUnary Indirection eL) (LvalueT ty)
 | ETypeIndirectionFunction : forall P G S eL ty ty_list,
     eTypeT P G S eL (Pointer QualifierSet.empty (Function ty ty_list)) ->
     eType P G S (ExpUnary Indirection eL) (LvalueT (Pointer QualifierSet.empty (Function ty ty_list)))
 | ETypePostfixIncrementPointer : forall P G S eL qs ty' ty,
     lvalueType P G S eL (Pointer qs ty') ->
     eTypeT P G S eL ty ->
     isModifiable (Pointer qs ty') ->
     isComplete ty' ->
     eType P G S (ExpUnary PostfixIncr eL) (ExpressionT ty)
 | ETypePostfixIncrementReal : forall P G S eL ty' ty,
     lvalueType P G S eL ty' ->
     eTypeT P G S eL ty ->
     isReal ty' ->
     isModifiable ty' ->
     eType P G S (ExpUnary PostfixIncr eL) (ExpressionT ty)
 | ETypePostfixDecrementPointer : forall P G S eL qs ty' ty,
     lvalueType P G S eL (Pointer qs ty') ->
     eTypeT P G S eL ty ->
     isModifiable (Pointer qs ty') ->
     isComplete ty' ->
     eType P G S (ExpUnary PostfixDecr eL) (ExpressionT ty)
 | ETypePostfixDecrementReal : forall P G S eL ty' ty,
     lvalueType P G S eL ty' ->
     eTypeT P G S eL ty ->
     isReal ty' ->
     isModifiable ty' ->
     eType P G S (ExpUnary PostfixDecr eL) (ExpressionT ty)
 | ETypePlus : forall P G S eL ty ty',
     eTypeT P G S eL ty' ->
     isArithmetic ty' ->
     isPromotion P ty' ty ->
     eType P G S (ExpUnary Plus eL) (ExpressionT ty)
 | ETypeMinus : forall P G S eL ty ty',
     eTypeT P G S eL ty' ->
     isArithmetic ty' ->
     isPromotion P ty' ty ->
     eType P G S (ExpUnary Minus eL) (ExpressionT ty)
 | ETypeBnot : forall P G S eL ty ty',
     eTypeT P G S eL ty' ->
     isInteger ty' ->
     isPromotion P ty' ty ->
     eType P G S (ExpUnary Bnot eL) (ExpressionT ty)
 | ETypeSizeOf : forall P G S ty ty',
     ~ isFunction ty ->
     ~ isIncomplete ty ->
     size_t P =  ty' ->
     eType P G S (ExpSizeof ty) (ExpressionT ty')
 | ETypeAlignOf : forall P G S ty ty',
     ~ isFunction ty ->
     ~ isIncomplete ty ->
     size_t P =  ty' ->
     eType P G S (ExpAlignof ty) (ExpressionT ty')
 | ETypeCastScalar : forall P G S ty eL ty',
     eTypeT P G S eL ty' ->
     isScalar ty' ->
     isScalar ty ->
     eType P G S (ExpCast ty eL) (ExpressionT (Unqualify ty))
 | ETypeCastVoid : forall P G S qs eL ty,
     eTypeT P G S eL ty ->
     eType P G S (ExpCast (Void qs) eL) (ExpressionT (Void QualifierSet.empty))
 | ETypeMult : forall P G S eL1 eL2 ty ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isArithmetic ty1 ->
     isArithmetic ty2 ->
     isUsualArithmetic P ty1 ty2 ty ->
     eType P G S (ExpBinary eL1 (Arithmetic Mul) eL2) (ExpressionT ty)
 | ETypeDiv : forall P G S eL1 eL2 ty ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isArithmetic ty1 ->
     isArithmetic ty2 ->
     isUsualArithmetic P ty1 ty2 ty ->
     eType P G S (ExpBinary eL1 (Arithmetic Div) eL2) (ExpressionT ty)
 | ETypeMod : forall P G S eL1 eL2 ty ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isInteger ty1 ->
     isInteger ty2 ->
     isUsualArithmetic P ty1 ty2 ty ->
     eType P G S (ExpBinary eL1 (Arithmetic Mod) eL2) (ExpressionT ty)
 | ETypeAddArithmetic : forall P G S eL1 eL2 ty ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isArithmetic ty1 ->
     isArithmetic ty2 ->
     isUsualArithmetic P ty1 ty2 ty ->
     eType P G S (ExpBinary eL1 (Arithmetic Add) eL2) (ExpressionT ty)
 | ETypeAddPointer1 : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 ty2 ->
     isComplete ty1 ->
     isInteger ty2 ->
     eType P G S (ExpBinary eL1 (Arithmetic Add) eL2) (ExpressionT (Pointer QualifierSet.empty ty1))
 | ETypeAddPointer2 : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isInteger ty1 ->
     isComplete ty2 ->
     eType P G S (ExpBinary eL1 (Arithmetic Add) eL2) (ExpressionT (Pointer QualifierSet.empty ty2))
 | ETypeSubArithmetic : forall P G S eL1 eL2 ty1 ty2 ty,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isArithmetic ty1 ->
     isArithmetic ty2 ->
     isUsualArithmetic P ty1 ty2 ty ->
     eType P G S (ExpBinary eL1 (Arithmetic Sub) eL2) (ExpressionT ty)
 | ETypeSubPointer : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 ty2 ->
     isComplete ty1 ->
     isInteger ty2 ->
     eType P G S (ExpBinary eL1 (Arithmetic Sub) eL2) (ExpressionT (Pointer QualifierSet.empty ty1))
 | ETypeSubPointerDiff : forall P G S eL1 eL2 ty1 ty2 ty,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isComplete ty1 ->
     isComplete ty2 ->
     isCompatible   (Unqualify ty1 )     (Unqualify ty2 )   ->
      ptrdiff_t P =  ty  ->
     eType P G S (ExpBinary eL1 (Arithmetic Sub) eL2) (ExpressionT ty)
 | ETypeShiftL : forall P G S eL1 eL2 ty1' ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     eType P G S (ExpBinary eL1 (Arithmetic Shl) eL2) (ExpressionT ty1')
 | ETypeShiftR : forall P G S eL1 eL2 ty1' ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     eType P G S (ExpBinary eL1 (Arithmetic Shr) eL2) (ExpressionT ty1')
 | ETypeLtReal : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isReal ty1 ->
     isReal ty2 ->
     eType P G S (ExpBinary eL1 Lt eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeLtPointer : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isObject ty1 ->
     isObject ty2 ->
     isCompatible   (Unqualify ty1 )     (Unqualify ty2 )   ->
     eType P G S (ExpBinary eL1 Lt eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeGtReal : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isReal ty1 ->
     isReal ty2 ->
     eType P G S (ExpBinary eL1 Gt eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeGtPointer : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isObject ty1 ->
     isObject ty2 ->
     isCompatible   (Unqualify ty1 )     (Unqualify ty2 )   ->
     eType P G S (ExpBinary eL1 Gt eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeLeReal : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isReal ty1 ->
     isReal ty2 ->
     eType P G S (ExpBinary eL1 Le eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeLePointer : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isObject ty1 ->
     isObject ty2 ->
     isCompatible   (Unqualify ty1 )     (Unqualify ty2 )   ->
     eType P G S (ExpBinary eL1 Le eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeGeReal : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isReal ty1 ->
     isReal ty2 ->
     eType P G S (ExpBinary eL1 Ge eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeGePointer : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isObject ty1 ->
     isObject ty2 ->
     isCompatible   (Unqualify ty1 )     (Unqualify ty2 )   ->
     eType P G S (ExpBinary eL1 Ge eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeEqArithmetic : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isArithmetic ty1 ->
     isArithmetic ty2 ->
     eType P G S (ExpBinary eL1 Eq eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeEqPointer : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isCompatible   (Unqualify ty1 )     (Unqualify ty2 )   ->
     eType P G S (ExpBinary eL1 Eq eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeEqVoid1 : forall P G S eL1 eL2 qs ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty  (Void qs) ) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isObject ty2 ->
     eType P G S (ExpBinary eL1 Eq eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeEqVoid2 : forall P G S eL1 eL2 ty1 qs,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty  (Void qs) ) ->
     isObject ty1 ->
     eType P G S (ExpBinary eL1 Eq eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeEqNull1 : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isNullPointerConstant eL1 ->
     eType P G S (ExpBinary eL1 Eq eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeEqNull2 : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 ty2 ->
     isNullPointerConstant eL2 ->
     eType P G S (ExpBinary eL1 Eq eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeNeArithmetic : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isArithmetic ty1 ->
     isArithmetic ty2 ->
     eType P G S (ExpBinary eL1 Ne eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeNePointer : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isCompatible   (Unqualify ty1 )     (Unqualify ty2 )   ->
     eType P G S (ExpBinary eL1 Ne eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeNeVoid1 : forall P G S eL1 eL2 qs ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty  (Void qs) ) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isObject ty2 ->
     eType P G S (ExpBinary eL1 Ne eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeNeVoid2 : forall P G S eL1 eL2 ty1 qs,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty  (Void qs) ) ->
     isObject ty1 ->
     eType P G S (ExpBinary eL1 Ne eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeNeNull1 : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isNullPointerConstant eL1 ->
     eType P G S (ExpBinary eL1 Ne eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeNeNull2 : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 ty2 ->
     isNullPointerConstant eL2 ->
     eType P G S (ExpBinary eL1 Ne eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeBand : forall P G S eL1 eL2 ty1 ty2 ty,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isInteger ty1 ->
     isInteger ty2 ->
     isUsualArithmetic P ty1 ty2 ty ->
     eType P G S (ExpBinary eL1 (Arithmetic Band) eL2) (ExpressionT ty)
 | ETypeXor : forall P G S eL1 eL2 ty1 ty2 ty,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isInteger ty1 ->
     isInteger ty2 ->
     isUsualArithmetic P ty1 ty2 ty ->
     eType P G S (ExpBinary eL1 (Arithmetic Xor) eL2) (ExpressionT ty)
 | ETypeBor : forall P G S eL1 eL2 ty1 ty2 ty,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isInteger ty1 ->
     isInteger ty2 ->
     isUsualArithmetic P ty1 ty2 ty ->
     eType P G S (ExpBinary eL1 (Arithmetic Bor) eL2) (ExpressionT ty)
 | ETypeAnd : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isScalar ty1 ->
     isScalar ty2 ->
     eType P G S (ExpBinary eL1 And eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeOr : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isScalar ty1 ->
     isScalar ty2 ->
     eType P G S (ExpBinary eL1 Or eL2) (ExpressionT  (Basic QualifierSet.empty (Integer (Signed Int))) )
 | ETypeConditionalArithmetic : forall P G S eL1 eL2 eL3 ty ty1 ty2 ty3,
     eTypeT P G S eL1 ty1 ->
     isScalar ty1 ->
     eTypeT P G S eL2 ty2 ->
     eTypeT P G S eL3 ty3 ->
     isArithmetic ty2 ->
     isArithmetic ty3 ->
     isUsualArithmetic P ty2 ty3 ty ->
     eType P G S (ExpConditional eL1 eL2 eL3) (ExpressionT ty)
 | ETypeConditionalVoid : forall P G S eL1 eL2 eL3 ty1,
     eTypeT P G S eL1 ty1 ->
     isScalar ty1 ->
     eTypeT P G S eL2 (Void QualifierSet.empty) ->
     eTypeT P G S eL3 (Void QualifierSet.empty) ->
     eType P G S (ExpConditional eL1 eL2 eL3) (ExpressionT (Void QualifierSet.empty))
 | ETypeConditionalPointer : forall P G S (eL1 eL2 eL3:expressionL) ty2 ty3 ty ty1,
     eTypeT P G S eL1 ty1 ->
     isScalar ty1 ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     eTypeT P G S eL3 (Pointer QualifierSet.empty ty3) ->
     isCompatible   (Unqualify ty2 )     (Unqualify ty3 )   ->
     isComposite   (Unqualify ty2 )     (Unqualify ty3 )   ty ->
     eType P G S (ExpConditional eL1 eL2 eL3) (ExpressionT (Pointer QualifierSet.empty   (addQualifiers   (MergeQualifiers ty2 ty3 )   ty )  ))
 | ETypeConditionalNullPointer1 : forall P G S eL1 eL2 eL3 ty1 ty2 ty3,
     eTypeT P G S eL1 ty1 ->
     isScalar ty1 ->
     eTypeT P G S eL2 ty2 ->
     eTypeT P G S eL3 ty3 ->
     isPointer ty3 ->
      ~ (  isCompatible ty2 ty3  )  ->
     isNullPointerConstant eL2 ->
     eType P G S (ExpConditional eL1 eL2 eL3) (ExpressionT ty3)
 | ETypeConditionalNullPointer2 : forall P G S eL1 eL2 eL3 ty1 ty2 ty3,
     eTypeT P G S eL1 ty1 ->
     isScalar ty1 ->
     eTypeT P G S eL2 ty2 ->
     eTypeT P G S eL3 ty3 ->
     isPointer ty2 ->
      ~ (  isCompatible ty2 ty3  )  ->
     isNullPointerConstant eL2 ->
     eType P G S (ExpConditional eL1 eL2 eL3) (ExpressionT ty2)
 | ETypeConditionalPointerVoid1 : forall P G S eL1 eL2 eL3 ty1 ty2 ty3,
     eTypeT P G S eL1 ty1 ->
     isScalar ty1 ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     eTypeT P G S eL3 (Pointer QualifierSet.empty ty3) ->
     isVoid ty2 ->
     isObject ty3 ->
      ~ (  isCompatible ty2 ty3  )  ->
     eType P G S (ExpConditional eL1 eL2 eL3) (ExpressionT (Pointer QualifierSet.empty ty2))
 | ETypeConditionalPointerVoid2 : forall P G S eL1 eL2 eL3 ty1 ty2 ty3,
     eTypeT P G S eL1 ty1 ->
     isScalar ty1 ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     eTypeT P G S eL3 (Pointer QualifierSet.empty ty3) ->
     isObject ty2 ->
     isVoid ty3 ->
      ~ (  isCompatible ty2 ty3  )  ->
     eType P G S (ExpConditional eL1 eL2 eL3) (ExpressionT (Pointer QualifierSet.empty ty3))
 | ETypeAssignArithmetic : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isArithmetic ty1' ->
     isArithmetic ty2 ->
     eType P G S (ExpAssign eL1 eL2) (ExpressionT ty1)
 | ETypeAssignPointer : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isModifiable ty1' ->
     isPointer ty1' ->
     isCompatible ty1 ty2 ->
     qualifiersSub ty2 ty1 ->
     eType P G S (ExpAssign eL1 eL2) (ExpressionT (Pointer QualifierSet.empty ty1))
 | ETypeAssignVoidPointer1 : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isModifiable ty1' ->
     isPointer ty1' ->
     isVoid ty1 ->
     isObject ty2 ->
     qualifiersSub ty2 ty1 ->
     eType P G S (ExpAssign eL1 eL2) (ExpressionT (Pointer QualifierSet.empty ty1))
 | ETypeAssignVoidPointer2 : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 (Pointer QualifierSet.empty ty2) ->
     isModifiable ty1' ->
     isPointer ty1' ->
     isObject ty1 ->
     isVoid ty2 ->
     qualifiersSub ty2 ty1 ->
     eType P G S (ExpAssign eL1 eL2) (ExpressionT (Pointer QualifierSet.empty ty1))
 | ETypeAssignNullPointerConstant : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isPointer ty1' ->
     isNullPointerConstant eL2 ->
     eType P G S (ExpAssign eL1 eL2) (ExpressionT (Pointer QualifierSet.empty ty1))
 | ETypeAssignBool : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 (Pointer QualifierSet.empty ty1) ->
     eTypeT P G S eL2 ty2 ->
     isBool ty1' ->
     isPointer ty2 ->
     eType P G S (ExpAssign eL1 eL2) (ExpressionT (Pointer QualifierSet.empty ty1))
 | ETypeCompoundAssignPlusArithmetic : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isArithmetic ty1' ->
     isArithmetic ty2 ->
     eType P G S (ExpCompoundAssign eL1 Add eL2) (ExpressionT ty1)
 | ETypeCompoundAssignPlusPointer : forall P G S eL1 eL2 qs ty1 ty1' ty2,
     lvalueType P G S eL1 (Pointer qs ty1') ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable (Pointer qs ty1') ->
     isComplete ty1' ->
     isInteger ty2 ->
     eType P G S (ExpCompoundAssign eL1 Add eL2) (ExpressionT ty1)
 | ETypeCompoundAssignMinusArithmetic : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isArithmetic ty1' ->
     isArithmetic ty2 ->
     eType P G S (ExpCompoundAssign eL1 Sub eL2) (ExpressionT ty1)
 | ETypeCompoundAssignMinusPointer : forall P G S eL1 eL2 qs ty1 ty1' ty2,
     lvalueType P G S eL1 (Pointer qs ty1') ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable (Pointer qs ty1') ->
     isComplete ty1' ->
     isInteger ty2 ->
     eType P G S (ExpCompoundAssign eL1 Add eL2) (ExpressionT ty1)
 | ETypeCompoundAssignMult : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isArithmetic ty1' ->
     isArithmetic ty2 ->
     eType P G S (ExpCompoundAssign eL1 Mul eL2) (ExpressionT ty1)
 | ETypeCompoundAssignDiv : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isArithmetic ty1' ->
     isArithmetic ty2 ->
     eType P G S (ExpCompoundAssign eL1 Div eL2) (ExpressionT ty1)
 | ETypeCompoundAssignMod : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isInteger ty1' ->
     isInteger ty2 ->
     eType P G S (ExpCompoundAssign eL1 Mod eL2) (ExpressionT ty1)
 | ETypeCompoundAssignShiftL : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isInteger ty1' ->
     isInteger ty2 ->
     eType P G S (ExpCompoundAssign eL1 Shl eL2) (ExpressionT ty1)
 | ETypeCompoundAssignShiftR : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isInteger ty1' ->
     isInteger ty2 ->
     eType P G S (ExpCompoundAssign eL1 Shr eL2) (ExpressionT ty1)
 | ETypeCompoundAssignBand : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isInteger ty1' ->
     isInteger ty2 ->
     eType P G S (ExpCompoundAssign eL1 Band eL2) (ExpressionT ty1)
 | ETypeCompoundAssignBor : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isInteger ty1' ->
     isInteger ty2 ->
     eType P G S (ExpCompoundAssign eL1 Bor eL2) (ExpressionT ty1)
 | ETypeCompoundAssignXor : forall P G S eL1 eL2 ty1 ty1' ty2,
     lvalueType P G S eL1 ty1' ->
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     isModifiable ty1' ->
     isInteger ty1' ->
     isInteger ty2 ->
     eType P G S (ExpCompoundAssign eL1 Xor eL2) (ExpressionT ty1)
 | ETypeComma : forall P G S eL1 eL2 ty1 ty2,
     eTypeT P G S eL1 ty1 ->
     eTypeT P G S eL2 ty2 ->
     eType P G S (ExpBinary eL1 Comma eL2) (ExpressionT ty2)
with eTypeT : P -> gamma -> sigma -> expressionL -> type -> Prop :=    (* defn eTypeT *)
 | ExpTypeExpressionT : forall P G S l e ty,
     eType P G S e (ExpressionT ty) ->
     eTypeT P G S  (ExpLDef l e)  ty
 | ExpressionTypeLvalueT : forall P G S eL ty ty',
     eTypeL P G S eL (LvalueT ty') ->
     isLvalueConversion ty' ty ->
     eTypeT P G S eL ty
with lvalueType : P -> gamma -> sigma -> expressionL -> type -> Prop :=    (* defn lvalueType *)
 | LvalueTypeDef : forall P G S eL ty,
     eTypeL P G S eL (LvalueT ty) ->
     lvalueType P G S eL  (PointerConvert ty)
with typeable : P -> gamma -> sigma -> expression -> Prop :=    (* defn typeable *)
 | TypeableDef : forall P G S e tc,
     eType P G S e tc ->
     typeable P G S e
with typeableL : P -> gamma -> sigma -> expressionL -> Prop :=    (* defn typeableL *)
 | TypeableLDef : forall P G S eL tc,
     eTypeL P G S eL tc ->
     typeableL P G S eL
with isAssignable : P -> gamma -> sigma -> expressionL -> type -> Prop :=    (* defn isAssignable *)
 | IsAssignableDef : forall P G S eL ty id e l,
      ~ fv id e->
     typeable P (GammaMap.add id (Unqualify ty) G) S (ExpAssign (ExpLDef l (ExpVariable id)) eL)  ->
     isAssignable P G S eL ty.

Inductive sTypeL : P -> gamma -> sigma -> statementL -> Prop :=    (* defn sTypeL *)
 | STypeLDef : forall P G S l s,
     sType P G S s ->
     sTypeL P G S  (StmtLDef l s) 
with sType : P -> gamma -> sigma -> statement -> Prop :=    (* defn sType *)
 | STypeLabel : forall P G S id sL,
     sTypeL P G S sL ->
     sType P G S (StmtLabel id sL)
 | STypeCase : forall P G S n sL,
     sTypeL P G S sL ->
     typeable P G S (ExpConstant (ConstantInteger n)) ->
     sType P G S (StmtCase n sL)
 | STypeDefault : forall P G S sL,
     sTypeL P G S sL ->
     sType P G S (StmtDefault sL)
 | STypeBlock : forall sL_list P G S G',
     (forall sL, In sL sL_list -> sTypeL P (GammaMap.update _ G G')  S sL) ->
     sType P G S (StmtBlock G' sL_list)
 | STypeSkip : forall P G S,
     sType P G S StmtSkip
 | STypeExp : forall P G S eL,
     typeableL P G S eL ->
     sType P G S (StmtExp eL)
 | STypeIf : forall P G S eL sL1 sL2 ty,
     eTypeT P G S eL ty ->
     isScalar ty ->
     sTypeL P G S sL1 ->
     sTypeL P G S sL2 ->
     sType P G S (StmtIf eL sL1 sL2)
 | STypeSwitch : forall P G S eL sL ty,
     eTypeT P G S eL ty ->
     isInteger ty ->
     sTypeL P G S sL ->
     sType P G S (StmtSwitch eL sL)
 | STypeWhile : forall P G S eL sL ty,
     eTypeT P G S eL ty ->
     isScalar ty ->
     sTypeL P G S sL ->
     sType P G S (StmtWhile eL sL)
 | STypeDo : forall P G S sL eL ty,
     eTypeT P G S eL ty ->
     isScalar ty ->
     sTypeL P G S sL ->
     sType P G S (StmtDo sL eL)
 | STypeGoto : forall P G S id,
     sType P G S (StmtGoto id)
 | STypeContinue : forall P G S,
     sType P G S StmtContinue
 | STypeBreak : forall P G S,
     sType P G S StmtBreak
 | STypeReturnVoid : forall P G S,
     sType P G S StmtReturnVoid
 | STypeReturn : forall P G S eL,
     typeableL P G S eL ->
     sType P G S (StmtReturn eL)
 | STypeDeclaration : forall P G S definitions,
     (forall definition, In definition definitions -> dType P G S definition) ->
     sType P G S (StmtDeclaration definitions)
with dType : P -> gamma -> sigma -> definition -> Prop :=    (* defn dType *)
 | DTypeDef : forall P G S v eL a,
     typeable P G S  (ExpAssign (ExpLDef a (ExpVariable v)) eL)  ->
     dType P G S (DefinitionDef v eL)
with sigmaType : sigma -> sigma -> Prop :=    (* defn sigmaType *)
 | SigmaTypeEmpty : forall S,
     sigmaType S (SigmaMap.empty _)
 | SigmaTypeCtx : forall S S' v ty sL P,
     sTypeL P (GammaMap.empty _) S sL ->
     sigmaType S S' ->
     sigmaType S (SigmaMap.add v (ty, sL) S')
with pType : P -> program -> Prop :=    (* defn pType *)
 | PTypeDef : forall P id S sL,
     sigmaType S S ->
     (SigmaMap.find id S = Some (Function (Basic QualifierSet.empty (Integer (Signed Int))) nil, sL)) ->
     pType P (Program id S).

Hint Constructors eTypeL typeable typeableL isAssignable lvalueType dType pType.

Lemma eTypeL_def P G S e tyC l: eTypeL P G S (ExpLDef l e) tyC <-> eType P G S e tyC.
  split.
    intros H.
    inversion H; subst.
    trivial.

    intros H.
    constructor.
    trivial.
Qed.

Lemma eType_EL_False P G S e : forall ty1 ty2,
  eType P G S e (ExpressionT ty1) -> eType P G S e (LvalueT ty2) -> False.
Proof.
  apply (e_ind
          (fun e =>
             forall ty1 ty2
                    (He : eType P G S e (ExpressionT ty1))
                    (Hl : eType P G S e (LvalueT     ty2)),
             False)
          (fun eL_list =>
             forall eL e (Hex : exists l, eL = ExpLDef l e) (Hin : In eL eL_list)
                    ty1 ty2
                    (He : eType P G S e (ExpressionT ty1))
                    (Hl : eType P G S e (LvalueT     ty2)),
             False)
        );
  intros;
  abstract (
  inversion He; subst;
  abstract (
  inversion Hl; subst;
  abstract (
  congruence))).
Qed.

Lemma eTypeT_def P G S e l ty : eTypeT P G S (ExpLDef l e) ty <-> 
  (eType P G S e (ExpressionT ty) /\ eTypeT P G S (ExpLDef l e) ty \/
   exists ty', eTypeL P G S (ExpLDef l e) (LvalueT ty') /\ isLvalueConversion ty' ty /\ eTypeT P G S (ExpLDef l e) ty).
Proof.
  split.
    intros H.
    inversion H; subst;
    now firstorder.

    intros.
    firstorder.
Qed.

Lemma eTypeT_inj P G S e l ty1 ty2
         (HInj : forall tc1 tc2,
                   eType P G S e tc1 ->
                   eType P G S e tc2 ->
                   tc1 = tc2) : forall
         (Hty1 : eTypeT P G S (ExpLDef l e) ty1)
         (Hty2 : eTypeT P G S (ExpLDef l e) ty2),
    ty1 = ty2.
Proof.
  intros.
  inversion Hty1; subst;
  inversion Hty2; subst.
    injection (HInj _ _ H5 H6).
    now auto.

    rewrite eTypeL_def in H.
    exfalso.
    now apply (eType_EL_False _ _ _ _ _ _ H5 H).

    rewrite eTypeL_def in H.
    exfalso.
    now apply (eType_EL_False _ _ _ _ _ _ H7 H).

    rewrite eTypeL_def in *.    
    injection (HInj _ _ H H1).
    intros Heq.
    subst.
    exact (isLvalueConversion_inj _ _ _ H0 H2).
Qed.

Lemma eType_fun_False P G S e ty ty_list :
  wfGamma G -> eType P G S e (LvalueT (Function ty ty_list)) -> False.
Proof.
  intros Hgamma Htype.
  inversion Htype; subst.
    inversion Hgamma; subst.
    destruct (H v _ H0) as [_ [_ [Hcontra _]]].
    apply Hcontra.
    now constructor.

    now inversion H1.
Qed.

Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

Ltac eType_False :=
  match goal with
  | [ He : eType ?P ?G ?S ?e (ExpressionT _)
    , Hl : eType ?P ?G ?S ?e (LvalueT     _) |- _] =>
      exfalso; now apply (eType_EL_False P G S e _ _ He Hl)
  end.

Ltac eTypeT_simp :=
  match goal with
  | [ Hty1 : eTypeT ?P ?G ?S (ExpLDef ?l ?e) _
    , Hty2 : eTypeT ?P ?G ?S (ExpLDef ?l ?e) _
    , Hinj : forall tc1 tc2,
               eType ?P ?G ?S ?e tc1 ->
               eType ?P ?G ?S ?e tc2 -> tc1 = tc2 |- _ ] =>
      injection (eTypeT_inj P G S e l _ _ Hinj Hty1 Hty2) as ?; subst
  end.

Hint Rewrite eTypeL_def.
Hint Resolve eType_EL_False eType_fun_False.


Ltac eType_inj_ind :=
  match goal with
  | [ H1 : eType ?P ?G ?S ?e _
    , H2 : eType ?P ?G ?S ?e _
    , IH : forall tc1 tc2,
             eType ?P ?G ?S ?e tc1 ->
             eType ?P ?G ?S ?e tc2 -> tc1 = tc2 |- _] =>
      injection (IH _ _ H1 H2); subst
  end.

Lemma eType_inj P G S (WfG : wfGamma G): forall e tc1 tc2,
  eType P G S e tc1 ->
  eType P G S e tc2 ->
  tc1 = tc2.
Proof.
   apply (e_ind
            (fun e =>
               forall tc1 tc2
                      (Htc1 : eType P G S e tc1)
                      (Htc2 : eType P G S e tc2),
                 tc1 = tc2)
            (fun eL_list =>
               forall eL e (Hex : exists l, eL = ExpLDef l e) (Hin : In eL eL_list)
                      tc1 tc2
                      (Htc1 : eType P G S e tc1)
                      (Htc2 : eType P G S e tc2), 
                 tc1 = tc2));
     intros.
       inversion Htc1; subst;
       inversion Htc2; subst;
       try rewrite eTypeL_def in *;
       try eTypeT_simp;
       try isPromotion_simp;
       try eType_False;
       try isObject_function;
       try eType_inj_ind;
       try congruence.

Admitted.

