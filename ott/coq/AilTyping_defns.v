Require Import Common.
Require Import Implementation.
Require Import AilTypes.
Require Import AilSyntax.
Require Import AilTypesAux.

Require Import Context_defns.
Require Import AilSyntaxAux_defns.
Require Import AilWf_defns.
Require Import AilTypesAux_defns.

Inductive wellTypedBinaryArithmetic : ctype -> arithmeticOperator -> ctype -> Prop :=    (* defn eType *)
 | WellTypedBinaryArithmetic_Mul :
     forall {t1 t2},
       arithmetic t1 ->
       arithmetic t2 ->
       wellTypedBinaryArithmetic t1 Mul t2
 | WellTypedBinaryArithmetic_Div :
     forall {t1 t2},
       arithmetic t1 ->
       arithmetic t2 ->
       wellTypedBinaryArithmetic t1 Div t2
 | WellTypedBinaryArithmetic_Mod :
     forall {t1 t2},
       integer t1 ->
       integer t2 ->
       wellTypedBinaryArithmetic t1 Mod t2
 | WellTypedBinaryArithmetic_AddArithmetic : forall (t1 t2:ctype),
     forall {t1 t2},
       arithmetic t1 ->
       arithmetic t2 ->
       wellTypedBinaryArithmetic t1 Add t2
 | WellTypedBinaryArithmetic_SubArithmetic :
     forall {t1 t2},
       arithmetic t1 ->
       arithmetic t2 ->
       wellTypedBinaryArithmetic t1 Sub t2
 | WellTypedBinaryArithmetic_ShiftL :
     forall {t1 t2},
       integer t1 ->
       integer t2 ->
       wellTypedBinaryArithmetic t1 Shl t2
 | WellTypedBinaryArithmetic_ShiftR :
     forall {t1 t2},
       integer t1 ->
       integer t2 ->
       wellTypedBinaryArithmetic t1 Shr t2
 | WellTypedBinaryArithmetic_Band :
     forall {t1 t2},
       integer t1 ->
       integer t2 ->
       wellTypedBinaryArithmetic t1 Band t2
 | WellTypedBinaryArithmetic_Xor :
     forall {t1 t2},
       integer t1 ->
       integer t2 ->
       wellTypedBinaryArithmetic t1 Xor t2
 | WellTypedBinaryArithmetic_Bor :
     forall {t1 t2},
       integer t1 ->
       integer t2 ->
       wellTypedBinaryArithmetic t1 Bor t2.

Inductive typeOfConstant : implementation -> integerConstant -> integerType -> Prop :=
 | TypeOfConstant_NoneInt P : forall (n:nat),
     inIntegerRange P n (Signed Int) ->
     typeOfConstant P (n , None) (Signed Int)
 | TypeOfConstant_NoneLong P : forall (n:nat),
     ~ inIntegerRange P n (Signed Int)  ->
     inIntegerRange P n (Signed Long) ->
     typeOfConstant P (n , None) (Signed Long)
 | TypeOfConstant_NoneLongLong P : forall (n:nat),
     ~ inIntegerRange P n (Signed Long)  ->
     inIntegerRange P n (Signed LongLong) ->
     typeOfConstant P (n , None) (Signed LongLong)
 | TypeOfConstant_UInt P : forall (n:nat),
     inIntegerRange P n (Unsigned Int) ->
     typeOfConstant P (n , Some U) (Unsigned Int)
 | TypeOfConstant_ULong P : forall (n:nat),
     ~ inIntegerRange P n (Unsigned Int)  ->
     inIntegerRange P n (Unsigned Long) ->
     typeOfConstant P (n , Some U) (Unsigned Long)
 | TypeOfConstant_ULongLong P : forall (n:nat),
     ~ inIntegerRange P n (Unsigned Long)  ->
     inIntegerRange P n (Unsigned LongLong) ->
     typeOfConstant P (n , Some U) (Unsigned LongLong)
 | TypeOfConstant_LLong P : forall (n:nat),
     inIntegerRange P n (Signed Long) ->
     typeOfConstant P (n , Some L) (Signed Long)
 | TypeOfConstant_LLongLong P : forall (n:nat),
     ~ inIntegerRange P n (Signed Long)  ->
     inIntegerRange P n (Signed LongLong) ->
     typeOfConstant P (n , Some L) (Signed LongLong)
 | TypeOfConstant_ULLong P : forall (n:nat),
     inIntegerRange P n (Unsigned Long) ->
     typeOfConstant P (n , Some UL) (Unsigned Long)
 | TypeOfConstant_ULLongLong P : forall (n:nat),
     ~ inIntegerRange P n (Unsigned Long)  ->
     inIntegerRange P n (Unsigned LongLong) ->
     typeOfConstant P (n , Some UL) (Unsigned LongLong)
 | TypeOfConstant_LLLongLong P : forall (n:nat),
     inIntegerRange P n (Signed LongLong) ->
     typeOfConstant P (n , Some LL) (Signed LongLong)
 | TypeOfConstant_ULLLongLong P : forall (n:nat),
     inIntegerRange P n (Unsigned LongLong) ->
     typeOfConstant P (n , Some ULL) (Unsigned LongLong).

Inductive typeOfExpression' {A B} {P} {G} {S : sigma A B} : expression' B -> typeCategory -> Prop :=    (* defn typeOfExpression' *)
 | TypeOfExpression'_Variable : forall (v:identifier) (q:qualifiers) (t:ctype),
     lookup G v (q, t)  ->
     typeOfExpression' (Var v) (LValueType q t)
 | TypeOfExpression'_Function : forall (v:identifier) (t:ctype) p,
     lookup S v p ->
     type_from_sigma p = t ->
     typeOfExpression' (Var v) (RValueType t)
 | TypeOfExpression'_Constant : forall ic it,
     typeOfConstant P ic it ->
     typeOfExpression' (Constant (ConstantInteger ic)) (RValueType (Basic (Integer it)))
 | TypeOfExpression'_Call : forall es p e q t,
     unqualified q ->
     typeOfRValue e (Pointer q (Function t p)) ->
     typeOfArguments es p ->
     typeOfExpression' (Call e es) (RValueType t)
 | TypeOfExpression'_AddressFunction : forall p e q t,
     typeOfExpression e (RValueType (Function t p)) ->
     unqualified q ->
     typeOfExpression' (Unary Address e) (RValueType (Pointer q (Function t p)))
 | TypeOfExpression'_AddressLvalue : forall e (q:qualifiers) (t:ctype),
     typeOfLValue e q t ->
     typeOfExpression' (Unary Address e) (RValueType (Pointer q t))
 | TypeOfExpression'_IndirectionObject : forall e (q:qualifiers) (t:ctype),
     typeOfRValue e (Pointer q t) ->
     complete t ->
     object t ->
     typeOfExpression' (Unary Indirection e) (LValueType q t)
 | TypeOfExpression'_IndirectionFunction : forall p e q (t:ctype),
     unqualified q ->
     typeOfRValue e (Pointer q (Function t p)) ->
     typeOfExpression' (Unary Indirection e) (RValueType (Pointer q (Function t p)))
 | TypeOfExpression'_PostfixIncrementPointer : forall e (t:ctype) (q':qualifiers) (t':ctype),
     typeOfLValue e q' t' ->
     lvalueConversion t' t ->
     pointer t' ->
     modifiable q' t' ->
     typeOfExpression' (Unary PostfixIncr e) (RValueType t)
 | TypeOfExpression'_PostfixIncrementReal : forall e (t:ctype) (q':qualifiers) (t':ctype),
     typeOfLValue e q' t' ->
     lvalueConversion t' t ->
     real t' ->
     modifiable q' t' ->
     typeOfExpression' (Unary PostfixIncr e) (RValueType t)
 | TypeOfExpression'_PostfixDecrementPointer : forall e (t:ctype) (q':qualifiers) (t':ctype),
     typeOfLValue e q' t' ->
     lvalueConversion t' t ->
     pointer t' ->
     modifiable q' t' ->
     typeOfExpression' (Unary PostfixDecr e) (RValueType t)
 | TypeOfExpression'_PostfixDecrementReal : forall e (t:ctype) (q':qualifiers) (t':ctype),
     typeOfLValue e q' t' ->
     lvalueConversion t' t ->
     real t' ->
     modifiable q' t' ->
     typeOfExpression' (Unary PostfixDecr e) (RValueType t)
 | TypeOfExpression'_Plus : forall e (t t':ctype),
     typeOfRValue e t' ->
     arithmetic t' ->
     promotion P t' t ->
     typeOfExpression' (Unary Plus e) (RValueType t)
 | TypeOfExpression'_Minus : forall e (t t':ctype),
     typeOfRValue e t' ->
     arithmetic t' ->
     promotion P t' t ->
     typeOfExpression' (Unary Minus e) (RValueType t)
 | TypeOfExpression'_Bnot : forall e (t t':ctype),
     typeOfRValue e t' ->
     integer t' ->
     promotion P t' t ->
     typeOfExpression' (Unary Bnot e) (RValueType t)
 | TypeOfExpression'_SizeOf : forall (q:qualifiers) (t t':ctype),
     wfLvalue q t ->
     neg (function t) ->
     neg (incomplete t) ->
     Basic (Integer (size_t P)) = t' ->
     typeOfExpression' (SizeOf q t) (RValueType t')
 | TypeOfExpression'_AlignOf : forall (q:qualifiers) (t t':ctype),
     wfLvalue q t ->
     neg (function t) ->
     neg (incomplete t) ->
     Basic (Integer (size_t P)) = t' ->
     typeOfExpression' (AlignOf q t) (RValueType t')
 | TypeOfExpression'_CastScalar : forall (q:qualifiers) (t:ctype) e (t':ctype),
     wfLvalue q t ->
     typeOfRValue e t' ->
     scalar t' ->
     scalar t ->
     typeOfExpression' (Cast q t e) (RValueType t)
 | TypeOfExpression'_CastVoid : forall (q:qualifiers) e (t:ctype),
     wfLvalue q Void ->
     typeOfRValue e t ->
     typeOfExpression' (Cast q Void e) (RValueType Void)
 | TypeOfExpression'_Mul : forall e1 e2 (t t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Mul t2 ->
     usualArithmetic P t1 t2 t ->
     typeOfExpression' (Binary e1 (Arithmetic Mul) e2) (RValueType t)
 | TypeOfExpression'_Div : forall e1 e2 (t t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Div t2 ->
     usualArithmetic P t1 t2 t ->
     typeOfExpression' (Binary e1 (Arithmetic Div) e2) (RValueType t)
 | TypeOfExpression'_Mod : forall e1 e2 (t t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Mod t2 ->
     usualArithmetic P t1 t2 t ->
     typeOfExpression' (Binary e1 (Arithmetic Mod) e2) (RValueType t)
 | TypeOfExpression'_AddArithmetic : forall e1 e2 (t t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Add t2 ->
     usualArithmetic P t1 t2 t ->
     typeOfExpression' (Binary e1 (Arithmetic Add) e2) (RValueType t)
 | TypeOfExpression'_AddPointer1 : forall e1 e2 (q1:qualifiers) (t1 t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 t2 ->
     complete t1 ->
     integer t2 ->
     typeOfExpression' (Binary e1 (Arithmetic Add) e2) (RValueType (Pointer q1 t1))
 | TypeOfExpression'_AddPointer2 : forall e1 e2 (q2:qualifiers) (t2 t1:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     integer t1 ->
     complete t2 ->
     typeOfExpression' (Binary e1 (Arithmetic Add) e2) (RValueType (Pointer q2 t2))
 | TypeOfExpression'_SubArithmetic : forall e1 e2 (t t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Sub t2 ->
     usualArithmetic P t1 t2 t ->
     typeOfExpression' (Binary e1 (Arithmetic Sub) e2) (RValueType t)
 | TypeOfExpression'_SubPointer : forall e1 e2 (q1:qualifiers) (t1 t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 t2 ->
     complete t1 ->
     integer t2 ->
     typeOfExpression' (Binary e1 (Arithmetic Sub) e2) (RValueType (Pointer q1 t1))
 | TypeOfExpression'_SubPointerDiff : forall e1 e2 (t:ctype) (q1:qualifiers) (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     complete t1 ->
     complete t2 ->
     compatible t1 t2 ->
     Basic (Integer (ptrdiff_t P)) = t ->
     typeOfExpression' (Binary e1 (Arithmetic Sub) e2) (RValueType t)
 | TypeOfExpression'_ShiftL : forall e1 e2 (t1' t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Shl t2 ->
     promotion P t1 t1' ->
     typeOfExpression' (Binary e1 (Arithmetic Shl) e2) (RValueType t1')
 | TypeOfExpression'_ShiftR : forall e1 e2 (t1' t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Shr t2 ->
     promotion P t1 t1' ->
     typeOfExpression' (Binary e1 (Arithmetic Shr) e2) (RValueType t1')
 | TypeOfExpression'_LtReal : forall e1 e2 (t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     real t1 ->
     real t2 ->
     typeOfExpression' (Binary e1 Lt e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_LtPointer : forall e1 e2 (q1:qualifiers) (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     object t1 ->
     object t2 ->
     compatible t1 t2 ->
     typeOfExpression' (Binary e1 Lt e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_GtReal : forall e1 e2 (t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     real t1 ->
     real t2 ->
     typeOfExpression' (Binary e1 Gt e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_GtPointer : forall e1 e2 (q1:qualifiers) (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     object t1 ->
     object t2 ->
     compatible t1 t2 ->
     typeOfExpression' (Binary e1 Gt e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_LeReal : forall e1 e2 (t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     real t1 ->
     real t2 ->
     typeOfExpression' (Binary e1 Le e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_LePointer : forall e1 e2 (q1:qualifiers) (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     object t1 ->
     object t2 ->
     compatible t1 t2 ->
     typeOfExpression' (Binary e1 Le e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_GeReal : forall e1 e2 (t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     real t1 ->
     real t2 ->
     typeOfExpression' (Binary e1 Ge e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_GePointer : forall e1 e2 (q1:qualifiers) (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     object t1 ->
     object t2 ->
     compatible t1 t2 ->
     typeOfExpression' (Binary e1 Ge e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_EqArithmetic : forall e1 e2 (t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     arithmetic t1 ->
     arithmetic t2 ->
     typeOfExpression' (Binary e1 Eq e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_EqPointer : forall e1 e2 (q1:qualifiers) (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     compatible t1 t2 ->
     typeOfExpression' (Binary e1 Eq e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_EqVoid1 : forall e1 e2 (q1 q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 Void) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     object t2 ->
     typeOfExpression' (Binary e1 Eq e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_EqVoid2 : forall e1 e2 (q1:qualifiers) (t1:ctype) (q2:qualifiers),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 Void) ->
     object t1 ->
     typeOfExpression' (Binary e1 Eq e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_EqNull1 : forall e1 e2 (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     nullPointerConstant e1 ->
     typeOfExpression' (Binary e1 Eq e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_EqNull2 : forall e1 e2 (q1:qualifiers) (t1 t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 t2 ->
     nullPointerConstant e2 ->
     typeOfExpression' (Binary e1 Eq e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_NeArithmetic : forall e1 e2 (t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     arithmetic t1 ->
     arithmetic t2 ->
     typeOfExpression' (Binary e1 Ne e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_NePointer : forall e1 e2 (q1:qualifiers) (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     compatible t1 t2 ->
     typeOfExpression' (Binary e1 Ne e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_NeVoid1 : forall e1 e2 (q1 q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (Pointer q1 Void) ->
     typeOfRValue e2 (Pointer q2 t2) ->
     object t2 ->
     typeOfExpression' (Binary e1 Ne e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_NeVoid2 : forall e1 e2 (q1:qualifiers) (t1:ctype) (q2:qualifiers),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 (Pointer q2 Void) ->
     object t1 ->
     typeOfExpression' (Binary e1 Ne e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_NeNull1 : forall e1 e2 (t1:ctype) (q2:qualifiers) (t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     nullPointerConstant e1 ->
     typeOfExpression' (Binary e1 Ne e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_NeNull2 : forall e1 e2 (q1:qualifiers) (t1 t2:ctype),
     typeOfRValue e1 (Pointer q1 t1) ->
     typeOfRValue e2 t2 ->
     nullPointerConstant e2 ->
     typeOfExpression' (Binary e1 Ne e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_Band : forall e1 e2 (t t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Band t2 ->
     usualArithmetic P t1 t2 t ->
     typeOfExpression' (Binary e1 (Arithmetic Band) e2) (RValueType t)
 | TypeOfExpression'_Xor : forall e1 e2 (t t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Xor t2 ->
     usualArithmetic P t1 t2 t ->
     typeOfExpression' (Binary e1 (Arithmetic Xor) e2) (RValueType t)
 | TypeOfExpression'_Bor : forall e1 e2 (t t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     wellTypedBinaryArithmetic t1 Bor t2 ->
     usualArithmetic P t1 t2 t ->
     typeOfExpression' (Binary e1 (Arithmetic Bor) e2) (RValueType t)
 | TypeOfExpression'_And : forall e1 e2 (t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     scalar t1 ->
     scalar t2 ->
     typeOfExpression' (Binary e1 And e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_Or : forall e1 e2 (t1 t2:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     scalar t1 ->
     scalar t2 ->
     typeOfExpression' (Binary e1 Or e2) (RValueType (Basic (Integer (Signed Int))) )
 | TypeOfExpression'_ConditionalArithmetic : forall e1 e2 e3 (t t1 t2 t3:ctype),
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 t2 ->
     typeOfRValue e3 t3 ->
     arithmetic t2 ->
     arithmetic t3 ->
     usualArithmetic P t2 t3 t ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType t)
 | TypeOfExpression'_ConditionalVoid : forall e1 e2 e3 (t1:ctype),
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 Void ->
     typeOfRValue e3 Void ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType Void)
 | TypeOfExpression'_ConditionalPointer : forall e1 e2 e3 (q2 q3 q:qualifiers) (t t1 t2 t3:ctype),
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     typeOfRValue e3 (Pointer q3 t3) ->
     compatible t2 t3 ->
     composite t2 t3 t ->
     combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType (Pointer q t))
 | TypeOfExpression'_ConditionalNullPointer1_Pointer : forall e1 e2 e3 (t3 t1 t2:ctype) q2 q3 q,
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     typeOfRValue e3 (Pointer q3 t3) ->
     nullPointerConstant e2 ->
     combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType (Pointer q t3))
 | TypeOfExpression'_ConditionalNullPointer1_Other : forall e1 e2 e3 (t3 t1 t2:ctype),
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 t2 ->
     typeOfRValue e3 t3 ->
     neg (pointer t2) ->
     pointer t3 ->
     nullPointerConstant e2 ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType t3)
 | TypeOfExpression'_ConditionalNullPointer2_Pointer : forall e1 e2 e3 (t2 t1 t3:ctype) q2 q3 q,
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     typeOfRValue e3 (Pointer q3 t3) ->
     nullPointerConstant e3 ->
     combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType (Pointer q t2))
 | TypeOfExpression'_ConditionalNullPointer2_Other : forall e1 e2 e3 (t2 t1 t3:ctype),
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 t2 ->
     typeOfRValue e3 t3 ->
     pointer t2 ->
     neg (pointer t3) ->
     nullPointerConstant e3 ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType t2)
 | TypeOfExpression'_ConditionalPointerVoid1 : forall e1 e2 e3 (q2 q3 q:qualifiers) (t2 t1 t3:ctype),
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     typeOfRValue e3 (Pointer q3 t3) ->
     neg (compatible t2 t3) ->
     neg (nullPointerConstant e2) ->
     void t2 ->
     object t3 ->
     combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType (Pointer q t2))
 | TypeOfExpression'_ConditionalPointerVoid2 : forall e1 e2 e3 (q2 q3 q:qualifiers) (t3 t1 t2:ctype),
     typeOfRValue e1 t1 ->
     scalar t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     typeOfRValue e3 (Pointer q3 t3) ->
     neg (compatible t2 t3) ->
     neg (nullPointerConstant e3) ->
     object t2 ->
     void t3 ->
     combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (RValueType (Pointer q t3))
 | TypeOfExpression'_Assign : forall e1 e2 (q1:qualifiers) (t1 t:ctype),
     typeOfLValue e1 q1 t1 ->
     modifiable q1 t1 ->
     pointerConversion t1 t ->
     assignable t e2 ->
     typeOfExpression' (Assign e1 e2) (RValueType t)
 | TypeOfExpression'_CompoundAssignPlusMinusArithmetic : forall aop e1 e2 (t1:ctype) (q:qualifiers) (t t2 :ctype),
     (aop = Add) + (aop = Sub) ->
     typeOfLValue e1 q t ->
     lvalueConversion t t1 ->
     typeOfRValue e2 t2 ->
     modifiable q t ->
     arithmetic t1 ->
     arithmetic t2 ->
     typeOfExpression' (CompoundAssign e1 aop e2) (RValueType t1)
 | TypeOfExpression'_CompoundAssignPlusMinusPointer : forall aop e1 e2 (t1:ctype) (q' q:qualifiers) (t t2:ctype),
     (aop = Add) + (aop = Sub) ->
     typeOfLValue e1 q' (Pointer q t) ->
     lvalueConversion (Pointer q t) t1 ->
     typeOfRValue e2 t2 ->
     modifiable q' (Pointer q t)  ->
     complete t ->
     integer t2 ->
     typeOfExpression' (CompoundAssign e1 aop e2) (RValueType t1)
 | TypeOfExpression'_CompoundAssign : forall aop e1 e2 (t1:ctype) (q:qualifiers) (t t2:ctype),
     neg ((aop = Add) + (aop = Sub)) ->
     typeOfLValue e1 q t ->
     lvalueConversion t t1 ->
     typeOfRValue e2 t2 ->
     modifiable q t ->
     wellTypedBinaryArithmetic t1 aop t2 ->
     typeOfExpression' (CompoundAssign e1 aop e2) (RValueType t1)
 | TypeOfExpression'_Comma : forall e1 e2 (t2 t1:ctype),
     typeOfRValue e1 t1 ->
     typeOfRValue e2 t2 ->
     typeOfExpression' (Binary e1 Comma e2) (RValueType t2)
with typeOfExpression {A B} {P} {G} {S : sigma A B} : expression B -> typeCategory -> Prop :=
 | TypeOfExpression_Annotated : forall a e t,
     typeOfExpression' e t ->
     typeOfExpression (AnnotatedExpression a e) t
with typeOfRValue {A B} {P} {G} {S : sigma A B} : expression B -> ctype -> Prop :=    (* defn typeOfRValue *)
 | typeOfRValue_RValueType : forall e (t t':ctype),
     typeOfExpression e (RValueType t') ->
     pointerConversion t' t ->
     typeOfRValue e t
 | typeOfRValue_LValueType : forall e (t t':ctype) (q:qualifiers),
     typeOfLValue e q t' ->
     lvalueConversion t' t ->
     typeOfRValue e t
with typeOfLValue {A B} {P} {G} {S : sigma A B} : expression B -> qualifiers -> ctype -> Prop :=
 | TypeOfLValue : forall e q t,
     typeOfExpression e (LValueType q t) ->
     typeOfLValue e q t
with typeable {A B} {P} {G} {S : sigma A B} : expression B -> Prop :=    (* defn typeable *)
 | Typeable : forall e t,
     typeOfExpression e t ->
     typeable e
with typeOfArguments {A B} {P} {G} {S : sigma A B} : list (expression B) -> list (qualifiers * ctype) -> Prop :=    (* defn assignable *)
 | TypeOfArguments_nil : typeOfArguments nil nil
 | TypeOfArguments_cons es p : forall e q t t',
     pointerConversion t t' ->
     assignable t' e ->
     typeOfArguments es p ->
     typeOfArguments (e :: es) ((q, t) :: p)
with assignable {A B} {P} {G} {S : sigma A B}: ctype -> expression B -> Prop :=
 | Assignable_Arithmetic : forall e2 t1 t2,
     typeOfRValue e2 t2 ->
     arithmetic t1 ->
     arithmetic t2 ->
     assignable t1 e2
 | Assignable_Pointer : forall e2 (q1 q2:qualifiers) (t1 t2:ctype),
     typeOfRValue e2 (Pointer q2 t2) ->
     compatible t1 t2 ->
     sub_qualifiers q2 q1 = true ->
     assignable (Pointer q1 t1) e2
 | Assignable_VoidPointer1 : forall e2 (q1 q2:qualifiers) (t1 t2:ctype),
     void t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     object t2 ->
     sub_qualifiers q2 q1 = true ->
     assignable (Pointer q1 t1) e2
 | Assignable_VoidPointer2 : forall e2 (q1 q2:qualifiers) (t1 t2:ctype),
     object t1 ->
     typeOfRValue e2 (Pointer q2 t2) ->
     void t2 ->
     sub_qualifiers q2 q1 = true ->
     assignable (Pointer q1 t1) e2
 | Assignable_NullPointerConstant : forall e2 (t1 t2:ctype),
     pointer t1 ->
     typeOfRValue e2 t2 ->
     nullPointerConstant e2 ->
     assignable t1 e2
 | Assignable_Bool : forall e2 (t1 t2:ctype),
     boolean t1 ->
     typeOfRValue e2 t2 ->
     pointer t2 ->
     assignable t1 e2.
Arguments typeOfExpression' : default implicits.
Arguments typeOfExpression  : default implicits.
Arguments typeOfArguments   : default implicits.
Arguments typeOfLValue      : default implicits.
Arguments typeOfRValue      : default implicits.
Arguments assignable        : default implicits.
Arguments typeable          : default implicits.

Inductive wellFormedBinding : identifier * (qualifiers * ctype) -> Prop :=
 | WellFormedBinding v q t :
     wfLvalue q t ->
     wellFormedBinding (v, (q, t)).

Inductive wellFormedBindings : bindings -> Prop :=
 | WellFormedBindings bs :
     disjointBindings bs ->
     allList wellFormedBinding bs ->
     wellFormedBindings bs.

Inductive wellTypedDefinition {A B} P G (S : sigma  A B) : identifier * expression B -> Prop :=
  | WellTypedDefinition :
      forall v e q t,
        lookup G v (q, t) ->
        assignable P G S t e ->
        wellTypedDefinition P G S (v, e).

Inductive wellTypedStatement' {A B} P G (S : sigma A B) : ctype -> statement' A B -> Prop :=    (* defn wellTypedStatement *)
 | WellTypedStatement'_Label : forall t_return l s,
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Label l s)
 | WellTypedStatement'_Case : forall t_return ic it s,
     typeOfConstant P ic it ->
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Case ic s)
 | WellTypedStatement'_Default : forall t_return s,
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Default s)
 | WellTypedStatement'_Block : forall t_return bs ss,
     wellFormedBindings bs ->
     freshBindings bs S ->
     allList (wellTypedStatement P (Context.add_bindings bs G) S t_return) ss ->
     wellTypedStatement' P G S t_return (Block bs ss)
 | WellTypedStatement'_Skip : forall t_return,
     wellTypedStatement' P G S t_return Skip
 | WellTypedStatement'_Expression : forall t_return e,
     typeable P G S e ->
     wellTypedStatement' P G S t_return (Expression e)
 | WellTypedStatement'_If : forall t_return e s1 s2 t,
     typeOfRValue P G S e t ->
     scalar t ->
     wellTypedStatement  P G S t_return s1 ->
     wellTypedStatement  P G S t_return s2 ->
     wellTypedStatement' P G S t_return (If e s1 s2)
 | WellTypedStatement'_Switch : forall t_return e s t,
     typeOfRValue P G S e t ->
     integer t ->
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Switch e s)
 | WellTypedStatement'_While : forall t_return e s t,
     typeOfRValue P G S e t ->
     scalar t ->
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (While e s)
 | WellTypedStatement'_Do : forall t_return s e t,
     typeOfRValue P G S e t ->
     scalar t ->
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Do s e)
 | WellTypedStatement'_Goto : forall t_return l,
     wellTypedStatement' P G S t_return (Goto l)
 | WellTypedStatement'_Continue : forall t_return,
     wellTypedStatement' P G S t_return Continue
 | WellTypedStatement'_Break : forall t_return,
     wellTypedStatement' P G S t_return Break
 | WellTypedStatement'_ReturnVoid :
     wellTypedStatement' P G S Void ReturnVoid
 | WellTypedStatement'_Return : forall t_return e,
     assignable P G S t_return e ->
     wellTypedStatement' P G S t_return (Return e)
 | WellTypedStatement'_Declaration : forall t_return ds,
     allList (wellTypedDefinition P G S) ds ->
     wellTypedStatement' P G S t_return (Declaration ds)
with wellTypedStatement {A B} P G (S : sigma A B) : ctype -> statement A B -> Prop :=
 | WellTypedStatement_AnnotatedStatement : forall t_return a s,
     wellTypedStatement' P G S t_return s ->
     wellTypedStatement  P G S t_return (AnnotatedStatement a s).

Inductive wellTypedFunction {A B} P (S : sigma A B) : (ctype * bindings) * statement A B -> Prop :=
  | WellTypedFunction t_return bs s :
      wellFormedBindings bs ->
      freshBindings bs S ->
      wfType (Function t_return (parameters_of_bindings bs)) ->
      wellTypedStatement P (Context.add_bindings bs nil) S t_return s ->
      wellTypedFunction P S (t_return, bs, s).      

Inductive wellTypedSigma {A B} P (S : sigma A B) : Prop :=
 | WellTypedSigma :
     (forall v p, lookup S v p -> wellTypedFunction P S p) ->
     wellTypedSigma P S.

Inductive wellTypedProgram {A B} P : program A B -> Prop :=    (* defn wellTypedProgram *)
 | WellTypedProgram main S s:
       lookup S main (Basic (Integer (Signed Int)), nil, s) ->
       wellTypedSigma P S ->
       wellTypedProgram P (main, S).
