Require Import Common.
Require Import AilTypes.
Require Import AilSyntax.
Require Import GenTypes.
Require Import Annotation.

Require Import Context_defns.
Require Import AilWf_defns.
Require Import AilSyntaxAux_defns.
Require Import GenTypesAux_defns.

Require AilTypesAux_defns.

Inductive typeOfConstant : integerConstant -> genIntegerType -> Prop := 
 | TypeOfConstant_None_Int n :
     AilTypesAux_defns.inMinIntegerRange n (Signed Int) ->
     typeOfConstant (n, None) (Concrete (Signed Int))
 | TypeOfConstant_None_Unknown n :
     ~ AilTypesAux_defns.inMinIntegerRange n (Signed Int) ->
     typeOfConstant (n, None) (Unknown (n, None))
 | TypeOfConstant_U_Int n :
     AilTypesAux_defns.inMinIntegerRange n (Unsigned Int) ->
     typeOfConstant (n, Some U) (Concrete (Unsigned Int))
 | TypeOfConstant_U_Unknown n :
     ~ AilTypesAux_defns.inMinIntegerRange n (Unsigned Int) ->
     typeOfConstant (n, Some U) (Unknown (n, Some U))
 | TypeOfConstant_L_Long n :
     AilTypesAux_defns.inMinIntegerRange n (Signed Long) ->
     typeOfConstant (n, Some L) (Concrete (Signed Long))
 | TypeOfConstant_L_Unknown n :
     ~ AilTypesAux_defns.inMinIntegerRange n (Signed Long) ->
     typeOfConstant (n, Some L) (Unknown (n, Some L))
 | TypeOfConstant_UL_Long n :
     AilTypesAux_defns.inMinIntegerRange n (Unsigned Long) ->
     typeOfConstant (n, Some UL) (Concrete (Unsigned Long))
 | TypeOfConstant_UL_Unknown n :
     ~ AilTypesAux_defns.inMinIntegerRange n (Unsigned Long) ->
     typeOfConstant (n, Some UL) (Unknown (n, Some UL))
 | TypeOfConstant_LL_LongLong n :
     typeOfConstant (n, Some LL) (Concrete (Signed LongLong))
 | TypeOfConstant_ULLLongLong n :
     typeOfConstant (n, Some ULL) (Concrete (Unsigned LongLong)).

Inductive wellTypedBinaryArithmetic : genType -> arithmeticOperator -> genType -> Prop :=
 | WellTypedBinaryArithmetic_Mul :
     forall {gt1 gt2},
       arithmetic gt1 ->
       arithmetic gt2 ->
       wellTypedBinaryArithmetic gt1 Mul gt2
 | WellTypedBinaryArithmetic_Div :
     forall {gt1 gt2},
       arithmetic gt1 ->
       arithmetic gt2 ->
       wellTypedBinaryArithmetic gt1 Div gt2
 | WellTypedBinaryArithmetic_Mod :
     forall {gt1 gt2},
       integer gt1 ->
       integer gt2 ->
       wellTypedBinaryArithmetic gt1 Mod gt2
 | WellTypedBinaryArithmetic_AddArithmetic :
     forall {gt1 gt2},
       arithmetic gt1 ->
       arithmetic gt2 ->
       wellTypedBinaryArithmetic gt1 Add gt2
 | WellTypedBinaryArithmetic_SubArithmetic :
     forall {gt1 gt2},
       arithmetic gt1 ->
       arithmetic gt2 ->
       wellTypedBinaryArithmetic gt1 Sub gt2
 | WellTypedBinaryArithmetic_ShiftL :
     forall {gt1 gt2},
       integer gt1 ->
       integer gt2 ->
       wellTypedBinaryArithmetic gt1 Shl gt2
 | WellTypedBinaryArithmetic_ShiftR :
     forall {gt1 gt2},
       integer gt1 ->
       integer gt2 ->
       wellTypedBinaryArithmetic gt1 Shr gt2
 | WellTypedBinaryArithmetic_Band :
     forall {gt1 gt2},
       integer gt1 ->
       integer gt2 ->
       wellTypedBinaryArithmetic gt1 Band gt2
 | WellTypedBinaryArithmetic_Xor :
     forall {gt1 gt2},
       integer gt1 ->
       integer gt2 ->
       wellTypedBinaryArithmetic gt1 Xor gt2
 | WellTypedBinaryArithmetic_Bor :
     forall {gt1 gt2},
       integer gt1 ->
       integer gt2 ->
       wellTypedBinaryArithmetic gt1 Bor gt2.

Inductive typeOfExpression' {A B1 B2: Set} {S : sigma B1 B2} {G : gamma} : expression' A -> genTypeCategory -> Prop :=
 | TypeOfExpression'_Variable : forall (v:identifier) (q:qualifiers) (t:ctype),
     lookup G v (q, t)  ->
     typeOfExpression' (Var v) (GenLValueType q t)
 | TypeOfExpression'_Function : forall (v:identifier) (t:ctype) p,
     lookup S v p ->
     type_from_sigma p = t ->
     typeOfExpression' (Var v) (GenRValueType (inject_type t))
 | TypeOfExpression'_Constant : forall ic git,
     typeOfConstant ic git ->
     typeOfExpression' (Constant (ConstantInteger ic)) (GenRValueType (GenBasic (GenInteger git)))
 | TypeOfExpression'_Call : forall es p e q t,
     AilTypesAux_defns.unqualified q ->
     typeOfRValue e (GenPointer q (Function t p)) ->
     typeOfArguments es p ->
     typeOfExpression' (Call e es) (GenRValueType (inject_type t))
 | TypeOfExpression'_AddressFunction : forall p e q t,
     typeOfExpression e (GenRValueType (GenFunction t p)) ->
     AilTypesAux_defns.unqualified q ->
     typeOfExpression' (Unary Address e) (GenRValueType (GenPointer q (Function t p)))
 | TypeOfExpression'_AddressLvalue : forall e q t,
     typeOfLValue e q t ->
     typeOfExpression' (Unary Address e) (GenRValueType (GenPointer q t))
 | TypeOfExpression'_IndirectionObject : forall e q t,
     typeOfRValue e (GenPointer q t) ->
     AilTypesAux_defns.complete t ->
     AilTypesAux_defns.object t ->
     typeOfExpression' (Unary Indirection e) (GenLValueType q t)
 | TypeOfExpression'_IndirectionFunction : forall p e q t,
     AilTypesAux_defns.unqualified q ->
     typeOfRValue e (GenPointer q (Function t p)) ->
     typeOfExpression' (Unary Indirection e) (GenRValueType (GenPointer q (Function t p)))
 | TypeOfExpression'_PostfixIncrementPointer : forall e t q' t',
     typeOfLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     AilTypesAux_defns.pointer t' ->
     AilTypesAux_defns.modifiable q' t' ->
     typeOfExpression' (Unary PostfixIncr e) (GenRValueType (inject_type t))
 | TypeOfExpression'_PostfixIncrementReal : forall e t q' t',
     typeOfLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     AilTypesAux_defns.real t' ->
     AilTypesAux_defns.modifiable q' t' ->
     typeOfExpression' (Unary PostfixIncr e) (GenRValueType (inject_type t))
 | TypeOfExpression'_PostfixDecrementPointer : forall e t q' t',
     typeOfLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     AilTypesAux_defns.pointer t' ->
     AilTypesAux_defns.modifiable q' t' ->
     typeOfExpression' (Unary PostfixDecr e) (GenRValueType (inject_type t))
 | TypeOfExpression'_PostfixDecrementReal : forall e t q' t',
     typeOfLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     AilTypesAux_defns.real t' ->
     AilTypesAux_defns.modifiable q' t' ->
     typeOfExpression' (Unary PostfixDecr e) (GenRValueType (inject_type t))
 | TypeOfExpression'_Plus : forall e gt gt',
     typeOfRValue e gt' ->
     arithmetic gt' ->
     promotion gt' gt ->
     typeOfExpression' (Unary Plus e) (GenRValueType gt)
 | TypeOfExpression'_Minus : forall e gt gt',
     typeOfRValue e gt' ->
     arithmetic gt' ->
     promotion gt' gt ->
     typeOfExpression' (Unary Minus e) (GenRValueType gt)
 | TypeOfExpression'_Bnot : forall e gt gt',
     typeOfRValue e gt' ->
     integer gt' ->
     promotion gt' gt ->
     typeOfExpression' (Unary Bnot e) (GenRValueType gt)
 | TypeOfExpression'_SizeOf : forall q t,
     wfLvalue q t ->
     ~ AilTypesAux_defns.function t ->
     ~ AilTypesAux_defns.incomplete t ->
     typeOfExpression' (SizeOf q t) (GenRValueType (GenBasic (GenInteger SizeT)))
 | TypeOfExpression'_AlignOf : forall q t,
     wfLvalue q t ->
     ~ AilTypesAux_defns.function t ->
     ~ AilTypesAux_defns.incomplete t ->
     typeOfExpression' (AlignOf q t) (GenRValueType (GenBasic (GenInteger SizeT)))
 | TypeOfExpression'_CastScalar : forall q t e gt',
     wfLvalue q t ->
     typeOfRValue e gt' ->
     scalar gt' ->
     AilTypesAux_defns.scalar t ->
     typeOfExpression' (Cast q t e) (GenRValueType (inject_type t))
 | TypeOfExpression'_CastVoid : forall (q:qualifiers) e gt,
     wfLvalue q Void ->
     typeOfRValue e gt ->
     typeOfExpression' (Cast q Void e) (GenRValueType GenVoid)
 | TypeOfExpression'_Mul : forall e1 e2 gt gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Mul gt2 ->
     usualArithmetic gt1 gt2 gt ->
     typeOfExpression' (Binary e1 (Arithmetic Mul) e2) (GenRValueType gt)
 | TypeOfExpression'_Div : forall e1 e2 gt gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Div gt2 ->
     usualArithmetic gt1 gt2 gt ->
     typeOfExpression' (Binary e1 (Arithmetic Div) e2) (GenRValueType gt)
 | TypeOfExpression'_Mod : forall e1 e2 gt gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Mod gt2 ->
     usualArithmetic gt1 gt2 gt ->
     typeOfExpression' (Binary e1 (Arithmetic Mod) e2) (GenRValueType gt)
 | TypeOfExpression'_AddArithmetic : forall e1 e2 gt gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Add gt2 ->
     usualArithmetic gt1 gt2 gt ->
     typeOfExpression' (Binary e1 (Arithmetic Add) e2) (GenRValueType gt)
 | TypeOfExpression'_AddPointer1 : forall e1 e2 q1 t1 gt2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 gt2 ->
     AilTypesAux_defns.complete t1 ->
     integer gt2 ->
     typeOfExpression' (Binary e1 (Arithmetic Add) e2) (GenRValueType (GenPointer q1 t1))
 | TypeOfExpression'_AddPointer2 : forall e1 e2 q2 t2 gt1,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     integer gt1 ->
     AilTypesAux_defns.complete t2 ->
     typeOfExpression' (Binary e1 (Arithmetic Add) e2) (GenRValueType (GenPointer q2 t2))
 | TypeOfExpression'_SubArithmetic : forall e1 e2 gt gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Sub gt2 ->
     usualArithmetic gt1 gt2 gt ->
     typeOfExpression' (Binary e1 (Arithmetic Sub) e2) (GenRValueType gt)
 | TypeOfExpression'_SubPointer : forall e1 e2 (q1:qualifiers) t1 gt2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 gt2 ->
     AilTypesAux_defns.complete t1 ->
     integer gt2 ->
     typeOfExpression' (Binary e1 (Arithmetic Sub) e2) (GenRValueType (GenPointer q1 t1))
 | TypeOfExpression'_SubPointerDiff : forall e1 e2 (q1:qualifiers) t1 q2 t2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.complete t1 ->
     AilTypesAux_defns.complete t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     typeOfExpression' (Binary e1 (Arithmetic Sub) e2) (GenRValueType (GenBasic (GenInteger PtrdiffT)))
 | TypeOfExpression'_ShiftL : forall e1 e2 gt1' gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Shl gt2 ->
     promotion gt1 gt1' ->
     typeOfExpression' (Binary e1 (Arithmetic Shl) e2) (GenRValueType gt1')
 | TypeOfExpression'_ShiftR : forall e1 e2 gt1' gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Shr gt2 ->
     promotion gt1 gt1' ->
     typeOfExpression' (Binary e1 (Arithmetic Shr) e2) (GenRValueType gt1')
 | TypeOfExpression'_LtReal : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     real gt1 ->
     real gt2 ->
     typeOfExpression' (Binary e1 Lt e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_LtPointer : forall e1 e2 q1 t1 q2 t2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t1 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     typeOfExpression' (Binary e1 Lt e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_GtReal : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     real gt1 ->
     real gt2 ->
     typeOfExpression' (Binary e1 Gt e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_GtPointer : forall e1 e2 q1 t1 q2 t2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t1 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     typeOfExpression' (Binary e1 Gt e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_LeReal : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     real gt1 ->
     real gt2 ->
     typeOfExpression' (Binary e1 Le e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_LePointer : forall e1 e2 q1 t1 q2 t2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t1 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     typeOfExpression' (Binary e1 Le e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_GeReal : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     real gt1 ->
     real gt2 ->
     typeOfExpression' (Binary e1 Ge e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_GePointer : forall e1 e2 q1 t1 q2 t2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t1 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     typeOfExpression' (Binary e1 Ge e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_EqArithmetic : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     arithmetic gt1 ->
     arithmetic gt2 ->
     typeOfExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_EqPointer : forall e1 e2 q1 t1 q2 t2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.compatible t1 t2 ->
     typeOfExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_EqVoid1 : forall e1 e2 q1 q2 t2,
     typeOfRValue e1 (GenPointer q1 Void) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t2 ->
     typeOfExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_EqVoid2 : forall e1 e2 q1 t1 q2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 Void) ->
     AilTypesAux_defns.object t1 ->
     typeOfExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_EqNull1 : forall e1 e2 gt1 q2 t2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     nullPointerConstant e1 ->
     typeOfExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_EqNull2 : forall e1 e2 q1 t1 t2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 t2 ->
     nullPointerConstant e2 ->
     typeOfExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_NeArithmetic : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     arithmetic gt1 ->
     arithmetic gt2 ->
     typeOfExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_NePointer : forall e1 e2 q1 t1 q2 t2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.compatible t1 t2 ->
     typeOfExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_NeVoid1 : forall e1 e2 (q1 q2:qualifiers) (t2:ctype),
     typeOfRValue e1 (GenPointer q1 Void) ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t2 ->
     typeOfExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_NeVoid2 : forall e1 e2 q1 t1 q2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 (GenPointer q2 Void) ->
     AilTypesAux_defns.object t1 ->
     typeOfExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_NeNull1 : forall e1 e2 gt1 q2 t2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     nullPointerConstant e1 ->
     typeOfExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_NeNull2 : forall e1 e2 q1 t1 gt2,
     typeOfRValue e1 (GenPointer q1 t1) ->
     typeOfRValue e2 gt2 ->
     nullPointerConstant e2 ->
     typeOfExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_Band : forall e1 e2 gt gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Band gt2 ->
     usualArithmetic gt1 gt2 gt ->
     typeOfExpression' (Binary e1 (Arithmetic Band) e2) (GenRValueType gt)
 | TypeOfExpression'_Xor : forall e1 e2 gt gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Xor gt2 ->
     usualArithmetic gt1 gt2 gt ->
     typeOfExpression' (Binary e1 (Arithmetic Xor) e2) (GenRValueType gt)
 | TypeOfExpression'_Bor : forall e1 e2 gt gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Bor gt2 ->
     usualArithmetic gt1 gt2 gt ->
     typeOfExpression' (Binary e1 (Arithmetic Bor) e2) (GenRValueType gt)
 | TypeOfExpression'_And : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     scalar gt1 ->
     scalar gt2 ->
     typeOfExpression' (Binary e1 And e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_Or : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     scalar gt1 ->
     scalar gt2 ->
     typeOfExpression' (Binary e1 Or e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | TypeOfExpression'_ConditionalArithmetic : forall e1 e2 e3 gt gt1 gt2 gt3,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 gt2 ->
     typeOfRValue e3 gt3 ->
     arithmetic gt2 ->
     arithmetic gt3 ->
     usualArithmetic gt2 gt3 gt ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType gt)
 | TypeOfExpression'_ConditionalVoid : forall e1 e2 e3 gt1,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 GenVoid ->
     typeOfRValue e3 GenVoid ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType GenVoid)
 | TypeOfExpression'_ConditionalPointer : forall e1 e2 e3 q2 q3 q gt1 t2 t3 t,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     typeOfRValue e3 (GenPointer q3 t3) ->
     AilTypesAux_defns.compatible t2 t3 ->
     AilTypesAux_defns.composite t2 t3 t ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t))
 | TypeOfExpression'_ConditionalNullPointer1_Pointer : forall e1 e2 e3 gt1 t2 t3 q2 q3 q,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     typeOfRValue e3 (GenPointer q3 t3) ->
     nullPointerConstant e2 ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t3))
 | TypeOfExpression'_ConditionalNullPointer1_Other : forall e1 e2 e3 gt3 gt1 gt2,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 gt2 ->
     typeOfRValue e3 gt3 ->
     ~ pointer gt2 ->
     pointer gt3 ->
     nullPointerConstant e2 ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType gt3)
 | TypeOfExpression'_ConditionalNullPointer2_Pointer : forall e1 e2 e3 gt1 t2 t3 q2 q3 q,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     typeOfRValue e3 (GenPointer q3 t3) ->
     nullPointerConstant e3 ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t2))
 | TypeOfExpression'_ConditionalNullPointer2_Other : forall e1 e2 e3 gt1 gt2 gt3,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 gt2 ->
     typeOfRValue e3 gt3 ->
     pointer gt2 ->
     ~ pointer gt3 ->
     nullPointerConstant e3 ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType gt2)
 | TypeOfExpression'_ConditionalPointerVoid1 : forall e1 e2 e3 q2 q3 q gt1 t2 t3,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     typeOfRValue e3 (GenPointer q3 t3) ->
     ~ AilTypesAux_defns.compatible t2 t3 ->
     ~ nullPointerConstant e2 ->
     AilTypesAux_defns.void t2 ->
     AilTypesAux_defns.object t3 ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t2))
 | TypeOfExpression'_ConditionalPointerVoid2 : forall e1 e2 e3 q2 q3 q gt1 t2 t3,
     typeOfRValue e1 gt1 ->
     scalar gt1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     typeOfRValue e3 (GenPointer q3 t3) ->
     ~ AilTypesAux_defns.compatible t2 t3 ->
     ~ nullPointerConstant e3 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.void t3 ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     typeOfExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t3))
 | TypeOfExpression'_Assign : forall e1 e2 q1 t1 t,
     typeOfLValue e1 q1 t1 ->
     AilTypesAux_defns.modifiable q1 t1 ->
     AilTypesAux_defns.pointerConversion t1 t ->
     assignable t e2 ->
     typeOfExpression' (Assign e1 e2) (GenRValueType (inject_type t))
 | TypeOfExpression'_CompoundAssignPlusMinusArithmetic : forall aop e1 e2 (t1:ctype) (q:qualifiers) t t1 gt2,
     (aop = Add) \/ (aop = Sub) ->
     typeOfLValue e1 q t ->
     AilTypesAux_defns.lvalueConversion t t1 ->
     typeOfRValue e2 gt2 ->
     AilTypesAux_defns.modifiable q t ->
     AilTypesAux_defns.arithmetic t1 ->
     arithmetic gt2 ->
     typeOfExpression' (CompoundAssign e1 aop e2) (GenRValueType (inject_type t1))
 | TypeOfExpression'_CompoundAssignPlusMinusPointer : forall aop e1 e2 t1 q' q t gt2,
     (aop = Add) \/ (aop = Sub) ->
     typeOfLValue e1 q' (Pointer q t) ->
     AilTypesAux_defns.lvalueConversion (Pointer q t) t1 ->
     typeOfRValue e2 gt2 ->
     AilTypesAux_defns.modifiable q' (Pointer q t)  ->
     AilTypesAux_defns.complete t ->
     integer gt2 ->
     typeOfExpression' (CompoundAssign e1 aop e2) (GenRValueType (inject_type t1))
 | TypeOfExpression'_CompoundAssign : forall aop e1 e2 t1 q t gt2,
     ~ (aop = Add \/ aop = Sub) ->
     typeOfLValue e1 q t ->
     AilTypesAux_defns.lvalueConversion t t1 ->
     typeOfRValue e2 gt2 ->
     AilTypesAux_defns.modifiable q t ->
     wellTypedBinaryArithmetic (inject_type t1) aop gt2 ->
     typeOfExpression' (CompoundAssign e1 aop e2) (GenRValueType (inject_type t1))
 | TypeOfExpression'_Comma : forall e1 e2 gt1 gt2,
     typeOfRValue e1 gt1 ->
     typeOfRValue e2 gt2 ->
     typeOfExpression' (Binary e1 Comma e2) (GenRValueType gt2)
with typeOfExpression {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} : expression A -> genTypeCategory -> Prop :=
 | TypeOfExpression_Annotated : forall a e gt,
     typeOfExpression' e gt ->
     typeOfExpression (AnnotatedExpression a e) gt
with typeOfRValue {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} : expression A -> genType -> Prop :=
 | typeOfRValue_RValueType : forall e gt gt',
     typeOfExpression e (GenRValueType gt') ->
     pointerConversion gt' gt ->
     typeOfRValue e gt
 | typeOfRValue_LValueType : forall e t t' q',
     typeOfLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     typeOfRValue e (inject_type t)
with typeOfLValue {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} : expression A -> qualifiers -> ctype -> Prop :=
 | TypeOfLValue : forall e q t,
     typeOfExpression e (GenLValueType q t) ->
     typeOfLValue e q t
with typeable {A B1 B2: Set} {S : sigma B1 B2} {G : gamma} : expression A -> Prop :=
 | Typeable : forall e gt,
     typeOfExpression e gt ->
     typeable e
with typeOfArguments {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} : list (expression A) -> list (qualifiers * ctype) -> Prop :=
 | TypeOfArguments_nil :
     typeOfArguments nil nil
 | TypeOfArguments_cons es p : forall e q t t',
     AilTypesAux_defns.pointerConversion t t' ->
     assignable t' e ->
     typeOfArguments es p ->
     typeOfArguments (e :: es) ((q, t) :: p)
with assignable {A B1 B2: Set} {S : sigma B1 B2} {G : gamma}: ctype -> expression A -> Prop :=
 | Assignable_Arithmetic : forall e2 t1 gt2,
     typeOfRValue e2 gt2 ->
     AilTypesAux_defns.arithmetic t1 ->
     arithmetic gt2 ->
     assignable t1 e2
 | Assignable_Pointer : forall e2 q1 q2 t1 t2,
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.compatible t1 t2 ->
     AilTypesAux.sub_qualifiers q2 q1 = true ->
     assignable (Pointer q1 t1) e2
 | Assignable_VoidPointer1 : forall e2 q1 q2 t1 t2,
     AilTypesAux_defns.void t1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux.sub_qualifiers q2 q1 = true ->
     assignable (Pointer q1 t1) e2
 | Assignable_VoidPointer2 : forall e2 q1 q2 t1 t2,
     AilTypesAux_defns.object t1 ->
     typeOfRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.void t2 ->
     AilTypesAux.sub_qualifiers q2 q1 = true ->
     assignable (Pointer q1 t1) e2
 | Assignable_NullPointerConstant : forall e2 t1 gt2,
     AilTypesAux_defns.pointer t1 ->
     typeOfRValue e2 gt2 ->
     nullPointerConstant e2 ->
     assignable t1 e2
 | Assignable_Bool : forall e2 t1 gt2,
     AilTypesAux_defns.boolean t1 ->
     typeOfRValue e2 gt2 ->
     pointer gt2 ->
     assignable t1 e2.
Arguments typeOfExpression' : default implicits.
Arguments typeOfExpression  : default implicits.
Arguments typeOfArguments   : default implicits.
Arguments typeOfLValue      : default implicits.
Arguments typeOfRValue      : default implicits.
Arguments assignable    : default implicits.
Arguments typeable            : default implicits.

Inductive wellTypedDefinition {A B1 B2 : Set} (S : sigma  B1 B2) G : identifier * expression A -> Prop :=
  | WellTypedDefinition :
      forall v e q t,
        lookup G v (q, t) ->
        assignable S G t e ->
        wellTypedDefinition S G (v, e).

Inductive wellTypedStatement' {A B B1 B2: Set} {S : sigma B1 B2} (G : gamma) : ctype -> statement' B A -> Prop :=    (* defn wellTypedStatement *)
 | WellTypedStatement'_Label : forall t_return l s,
     wellTypedStatement  G t_return s ->
     wellTypedStatement' G t_return (Label l s)
 | WellTypedStatement'_Case : forall t_return ic it s,
     typeOfConstant ic it ->
     wellTypedStatement  G t_return s ->
     wellTypedStatement' G t_return (Case ic s)
 | WellTypedStatement'_Default : forall t_return s,
     wellTypedStatement  G t_return s ->
     wellTypedStatement' G t_return (Default s)
 | WellTypedStatement'_Block : forall t_return bs ss,
     AilTyping_defns.wellFormedBindings bs ->
     freshBindings bs S ->
     allList (wellTypedStatement (Context.add_bindings bs G) t_return) ss ->
     wellTypedStatement' G t_return (Block bs ss)
 | WellTypedStatement'_Skip : forall t_return,
     wellTypedStatement' G t_return Skip
 | WellTypedStatement'_Expression : forall t_return e,
     typeable S G e ->
     wellTypedStatement' G t_return (Expression e)
 | WellTypedStatement'_If : forall t_return e s1 s2 t,
     typeOfRValue S G e t ->
     scalar t ->
     wellTypedStatement  G t_return s1 ->
     wellTypedStatement  G t_return s2 ->
     wellTypedStatement' G t_return (If e s1 s2)
 | WellTypedStatement'_Switch : forall t_return e s t,
     typeOfRValue S G e t ->
     integer t ->
     wellTypedStatement  G t_return s ->
     wellTypedStatement' G t_return (Switch e s)
 | WellTypedStatement'_While : forall t_return e s t,
     typeOfRValue S G e t ->
     scalar t ->
     wellTypedStatement  G t_return s ->
     wellTypedStatement' G t_return (While e s)
 | WellTypedStatement'_Do : forall t_return s e t,
     typeOfRValue S G e t ->
     scalar t ->
     wellTypedStatement  G t_return s ->
     wellTypedStatement' G t_return (Do s e)
 | WellTypedStatement'_Goto : forall t_return l,
     wellTypedStatement' G t_return (Goto l)
 | WellTypedStatement'_Continue : forall t_return,
     wellTypedStatement' G t_return Continue
 | WellTypedStatement'_Break : forall t_return,
     wellTypedStatement' G t_return Break
 | WellTypedStatement'_ReturnVoid :
     wellTypedStatement' G Void ReturnVoid
 | WellTypedStatement'_Return : forall t_return e,
     assignable S G t_return e ->
     wellTypedStatement' G t_return (Return e)
 | WellTypedStatement'_Declaration : forall t_return ds,
     allList (wellTypedDefinition S G) ds ->
     wellTypedStatement' G t_return (Declaration ds)
with wellTypedStatement {A B B1 B2: Set} {S : sigma B1 B2} (G : gamma) : ctype -> statement B A -> Prop :=
 | WellTypedStatement_AnnotatedStatement : forall t_return a s,
     wellTypedStatement' G t_return s ->
     wellTypedStatement  G t_return (AnnotatedStatement a s).
Arguments wellTypedStatement' : default implicits.
Arguments wellTypedStatement  : default implicits.

Inductive wellTypedFunction {A B B1 B2: Set} (S : sigma B1 B2) : (ctype * bindings) * statement B A -> Prop :=
  | WellTypedFunction t_return bs s :
      AilTyping_defns.wellFormedBindings bs ->
      freshBindings bs S ->
      wfType (Function t_return (parameters_of_bindings bs)) ->
      wellTypedStatement S (Context.add_bindings bs Context.empty) t_return s ->
      wellTypedFunction S (t_return, bs, s).      

Definition wellTypedSigma {A B : Set} (S : sigma B A) : Prop :=
  forall v p, lookup S v p -> wellTypedFunction S p.

Inductive wellTypedProgram {A1 A2 : Set} : program A1 A2 -> Prop :=
 | WellTypedProgram main S s:
     lookup S main (Basic (Integer (Signed Int)), nil, s) ->
     wellTypedSigma S ->
     wellTypedProgram (main, S).

Inductive wellAnnotatedExpression' {A1 A2 B1 B2: Set} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} : expression' A2 -> genTypeCategory -> Prop :=
 | WellAnnotatedExpression'_Variable : forall (v:identifier) (q:qualifiers) (t:ctype),
     lookup G v (q, t)  ->
     wellAnnotatedExpression' (Var v) (GenLValueType q t)
 | WellAnnotatedExpression'_Function : forall (v:identifier) (t:ctype) p,
     lookup S v p ->
     type_from_sigma p = t ->
     wellAnnotatedExpression' (Var v) (GenRValueType (inject_type t))
 | WellAnnotatedExpression'_Constant : forall ic git,
     typeOfConstant ic git ->
     wellAnnotatedExpression' (Constant (ConstantInteger ic)) (GenRValueType (GenBasic (GenInteger git)))
 | WellAnnotatedExpression'_Call : forall es p e q t,
     AilTypesAux_defns.unqualified q ->
     wellAnnotatedRValue e (GenPointer q (Function t p)) ->
     wellAnnotatedArguments es p ->
     wellAnnotatedExpression' (Call e es) (GenRValueType (inject_type t))
 | WellAnnotatedExpression'_AddressFunction : forall p e q t,
     wellAnnotatedExpression e (GenRValueType (GenFunction t p)) ->
     AilTypesAux_defns.unqualified q ->
     wellAnnotatedExpression' (Unary Address e) (GenRValueType (GenPointer q (Function t p)))
 | WellAnnotatedExpression'_AddressLvalue : forall e q t,
     wellAnnotatedLValue e q t ->
     wellAnnotatedExpression' (Unary Address e) (GenRValueType (GenPointer q t))
 | WellAnnotatedExpression'_IndirectionObject : forall e q t,
     wellAnnotatedRValue e (GenPointer q t) ->
     AilTypesAux_defns.complete t ->
     AilTypesAux_defns.object t ->
     wellAnnotatedExpression' (Unary Indirection e) (GenLValueType q t)
 | WellAnnotatedExpression'_IndirectionFunction : forall p e q t,
     AilTypesAux_defns.unqualified q ->
     wellAnnotatedRValue e (GenPointer q (Function t p)) ->
     wellAnnotatedExpression' (Unary Indirection e) (GenRValueType (GenPointer q (Function t p)))
 | WellAnnotatedExpression'_PostfixIncrementPointer : forall e t q' t',
     wellAnnotatedLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     AilTypesAux_defns.pointer t' ->
     AilTypesAux_defns.modifiable q' t' ->
     wellAnnotatedExpression' (Unary PostfixIncr e) (GenRValueType (inject_type t))
 | WellAnnotatedExpression'_PostfixIncrementReal : forall e t q' t',
     wellAnnotatedLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     AilTypesAux_defns.real t' ->
     AilTypesAux_defns.modifiable q' t' ->
     wellAnnotatedExpression' (Unary PostfixIncr e) (GenRValueType (inject_type t))
 | WellAnnotatedExpression'_PostfixDecrementPointer : forall e t q' t',
     wellAnnotatedLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     AilTypesAux_defns.pointer t' ->
     AilTypesAux_defns.modifiable q' t' ->
     wellAnnotatedExpression' (Unary PostfixDecr e) (GenRValueType (inject_type t))
 | WellAnnotatedExpression'_PostfixDecrementReal : forall e t q' t',
     wellAnnotatedLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     AilTypesAux_defns.real t' ->
     AilTypesAux_defns.modifiable q' t' ->
     wellAnnotatedExpression' (Unary PostfixDecr e) (GenRValueType (inject_type t))
 | WellAnnotatedExpression'_Plus : forall e gt gt',
     wellAnnotatedRValue e gt' ->
     arithmetic gt' ->
     promotion gt' gt ->
     wellAnnotatedExpression' (Unary Plus e) (GenRValueType gt)
 | WellAnnotatedExpression'_Minus : forall e gt gt',
     wellAnnotatedRValue e gt' ->
     arithmetic gt' ->
     promotion gt' gt ->
     wellAnnotatedExpression' (Unary Minus e) (GenRValueType gt)
 | WellAnnotatedExpression'_Bnot : forall e gt gt',
     wellAnnotatedRValue e gt' ->
     integer gt' ->
     promotion gt' gt ->
     wellAnnotatedExpression' (Unary Bnot e) (GenRValueType gt)
 | WellAnnotatedExpression'_SizeOf : forall q t,
     wfLvalue q t ->
     ~ AilTypesAux_defns.function t ->
     ~ AilTypesAux_defns.incomplete t ->
     wellAnnotatedExpression' (SizeOf q t) (GenRValueType (GenBasic (GenInteger SizeT)))
 | WellAnnotatedExpression'_AlignOf : forall q t,
     wfLvalue q t ->
     ~ AilTypesAux_defns.function t ->
     ~ AilTypesAux_defns.incomplete t ->
     wellAnnotatedExpression' (AlignOf q t) (GenRValueType (GenBasic (GenInteger SizeT)))
 | WellAnnotatedExpression'_CastScalar : forall q t e gt',
     wfLvalue q t ->
     wellAnnotatedRValue e gt' ->
     scalar gt' ->
     AilTypesAux_defns.scalar t ->
     wellAnnotatedExpression' (Cast q t e) (GenRValueType (inject_type t))
 | WellAnnotatedExpression'_CastVoid : forall (q:qualifiers) e gt,
     wfLvalue q Void ->
     wellAnnotatedRValue e gt ->
     wellAnnotatedExpression' (Cast q Void e) (GenRValueType GenVoid)
 | WellAnnotatedExpression'_Mul : forall e1 e2 gt gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Mul gt2 ->
     usualArithmetic gt1 gt2 gt ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Mul) e2) (GenRValueType gt)
 | WellAnnotatedExpression'_Div : forall e1 e2 gt gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Div gt2 ->
     usualArithmetic gt1 gt2 gt ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Div) e2) (GenRValueType gt)
 | WellAnnotatedExpression'_Mod : forall e1 e2 gt gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Mod gt2 ->
     usualArithmetic gt1 gt2 gt ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Mod) e2) (GenRValueType gt)
 | WellAnnotatedExpression'_AddArithmetic : forall e1 e2 gt gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Add gt2 ->
     usualArithmetic gt1 gt2 gt ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Add) e2) (GenRValueType gt)
 | WellAnnotatedExpression'_AddPointer1 : forall e1 e2 q1 t1 gt2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 gt2 ->
     AilTypesAux_defns.complete t1 ->
     integer gt2 ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Add) e2) (GenRValueType (GenPointer q1 t1))
 | WellAnnotatedExpression'_AddPointer2 : forall e1 e2 q2 t2 gt1,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     integer gt1 ->
     AilTypesAux_defns.complete t2 ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Add) e2) (GenRValueType (GenPointer q2 t2))
 | WellAnnotatedExpression'_SubArithmetic : forall e1 e2 gt gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Sub gt2 ->
     usualArithmetic gt1 gt2 gt ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Sub) e2) (GenRValueType gt)
 | WellAnnotatedExpression'_SubPointer : forall e1 e2 (q1:qualifiers) t1 gt2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 gt2 ->
     AilTypesAux_defns.complete t1 ->
     integer gt2 ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Sub) e2) (GenRValueType (GenPointer q1 t1))
 | WellAnnotatedExpression'_SubPointerDiff : forall e1 e2 (q1:qualifiers) t1 q2 t2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.complete t1 ->
     AilTypesAux_defns.complete t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Sub) e2) (GenRValueType (GenBasic (GenInteger PtrdiffT)))
 | WellAnnotatedExpression'_ShiftL : forall e1 e2 gt1' gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Shl gt2 ->
     promotion gt1 gt1' ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Shl) e2) (GenRValueType gt1')
 | WellAnnotatedExpression'_ShiftR : forall e1 e2 gt1' gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Shr gt2 ->
     promotion gt1 gt1' ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Shr) e2) (GenRValueType gt1')
 | WellAnnotatedExpression'_LtReal : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     real gt1 ->
     real gt2 ->
     wellAnnotatedExpression' (Binary e1 Lt e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_LtPointer : forall e1 e2 q1 t1 q2 t2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t1 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     wellAnnotatedExpression' (Binary e1 Lt e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_GtReal : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     real gt1 ->
     real gt2 ->
     wellAnnotatedExpression' (Binary e1 Gt e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_GtPointer : forall e1 e2 q1 t1 q2 t2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t1 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     wellAnnotatedExpression' (Binary e1 Gt e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_LeReal : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     real gt1 ->
     real gt2 ->
     wellAnnotatedExpression' (Binary e1 Le e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_LePointer : forall e1 e2 q1 t1 q2 t2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t1 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     wellAnnotatedExpression' (Binary e1 Le e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_GeReal : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     real gt1 ->
     real gt2 ->
     wellAnnotatedExpression' (Binary e1 Ge e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_GePointer : forall e1 e2 q1 t1 q2 t2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t1 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.compatible t1 t2 ->
     wellAnnotatedExpression' (Binary e1 Ge e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_EqArithmetic : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     arithmetic gt1 ->
     arithmetic gt2 ->
     wellAnnotatedExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_EqPointer : forall e1 e2 q1 t1 q2 t2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.compatible t1 t2 ->
     wellAnnotatedExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_EqVoid1 : forall e1 e2 q1 q2 t2,
     wellAnnotatedRValue e1 (GenPointer q1 Void) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t2 ->
     wellAnnotatedExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_EqVoid2 : forall e1 e2 q1 t1 q2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 Void) ->
     AilTypesAux_defns.object t1 ->
     wellAnnotatedExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_EqNull1 : forall e1 e2 gt1 q2 t2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     nullPointerConstant e1 ->
     wellAnnotatedExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_EqNull2 : forall e1 e2 q1 t1 t2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 t2 ->
     nullPointerConstant e2 ->
     wellAnnotatedExpression' (Binary e1 Eq e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_NeArithmetic : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     arithmetic gt1 ->
     arithmetic gt2 ->
     wellAnnotatedExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_NePointer : forall e1 e2 q1 t1 q2 t2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.compatible t1 t2 ->
     wellAnnotatedExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_NeVoid1 : forall e1 e2 (q1 q2:qualifiers) (t2:ctype),
     wellAnnotatedRValue e1 (GenPointer q1 Void) ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t2 ->
     wellAnnotatedExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_NeVoid2 : forall e1 e2 q1 t1 q2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 (GenPointer q2 Void) ->
     AilTypesAux_defns.object t1 ->
     wellAnnotatedExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_NeNull1 : forall e1 e2 gt1 q2 t2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     nullPointerConstant e1 ->
     wellAnnotatedExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_NeNull2 : forall e1 e2 q1 t1 gt2,
     wellAnnotatedRValue e1 (GenPointer q1 t1) ->
     wellAnnotatedRValue e2 gt2 ->
     nullPointerConstant e2 ->
     wellAnnotatedExpression' (Binary e1 Ne e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_Band : forall e1 e2 gt gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Band gt2 ->
     usualArithmetic gt1 gt2 gt ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Band) e2) (GenRValueType gt)
 | WellAnnotatedExpression'_Xor : forall e1 e2 gt gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Xor gt2 ->
     usualArithmetic gt1 gt2 gt ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Xor) e2) (GenRValueType gt)
 | WellAnnotatedExpression'_Bor : forall e1 e2 gt gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellTypedBinaryArithmetic gt1 Bor gt2 ->
     usualArithmetic gt1 gt2 gt ->
     wellAnnotatedExpression' (Binary e1 (Arithmetic Bor) e2) (GenRValueType gt)
 | WellAnnotatedExpression'_And : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     scalar gt1 ->
     scalar gt2 ->
     wellAnnotatedExpression' (Binary e1 And e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_Or : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     scalar gt1 ->
     scalar gt2 ->
     wellAnnotatedExpression' (Binary e1 Or e2) (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
 | WellAnnotatedExpression'_ConditionalArithmetic : forall e1 e2 e3 gt gt1 gt2 gt3,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellAnnotatedRValue e3 gt3 ->
     arithmetic gt2 ->
     arithmetic gt3 ->
     usualArithmetic gt2 gt3 gt ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType gt)
 | WellAnnotatedExpression'_ConditionalVoid : forall e1 e2 e3 gt1,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 GenVoid ->
     wellAnnotatedRValue e3 GenVoid ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType GenVoid)
 | WellAnnotatedExpression'_ConditionalPointer : forall e1 e2 e3 q2 q3 q gt1 t2 t3 t,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     wellAnnotatedRValue e3 (GenPointer q3 t3) ->
     AilTypesAux_defns.compatible t2 t3 ->
     AilTypesAux_defns.composite t2 t3 t ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t))
 | WellAnnotatedExpression'_ConditionalNullPointer1_Pointer : forall e1 e2 e3 gt1 t2 t3 q2 q3 q,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     wellAnnotatedRValue e3 (GenPointer q3 t3) ->
     nullPointerConstant e2 ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t3))
 | WellAnnotatedExpression'_ConditionalNullPointer1_Other : forall e1 e2 e3 gt3 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellAnnotatedRValue e3 gt3 ->
     ~ pointer gt2 ->
     pointer gt3 ->
     nullPointerConstant e2 ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType gt3)
 | WellAnnotatedExpression'_ConditionalNullPointer2_Pointer : forall e1 e2 e3 gt1 t2 t3 q2 q3 q,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     wellAnnotatedRValue e3 (GenPointer q3 t3) ->
     nullPointerConstant e3 ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t2))
 | WellAnnotatedExpression'_ConditionalNullPointer2_Other : forall e1 e2 e3 gt1 gt2 gt3,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellAnnotatedRValue e3 gt3 ->
     pointer gt2 ->
     ~ pointer gt3 ->
     nullPointerConstant e3 ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType gt2)
 | WellAnnotatedExpression'_ConditionalPointerVoid1 : forall e1 e2 e3 q2 q3 q gt1 t2 t3,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     wellAnnotatedRValue e3 (GenPointer q3 t3) ->
     ~ AilTypesAux_defns.compatible t2 t3 ->
     ~ nullPointerConstant e2 ->
     AilTypesAux_defns.void t2 ->
     AilTypesAux_defns.object t3 ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t2))
 | WellAnnotatedExpression'_ConditionalPointerVoid2 : forall e1 e2 e3 q2 q3 q gt1 t2 t3,
     wellAnnotatedRValue e1 gt1 ->
     scalar gt1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     wellAnnotatedRValue e3 (GenPointer q3 t3) ->
     ~ AilTypesAux_defns.compatible t2 t3 ->
     ~ nullPointerConstant e3 ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux_defns.void t3 ->
     AilTypesAux.combine_qualifiers q2 q3 = q ->
     wellAnnotatedExpression' (Conditional e1 e2 e3) (GenRValueType (GenPointer q t3))
 | WellAnnotatedExpression'_Assign : forall e1 e2 q1 t1 t,
     wellAnnotatedLValue e1 q1 t1 ->
     AilTypesAux_defns.modifiable q1 t1 ->
     AilTypesAux_defns.pointerConversion t1 t ->
     wellAnnotatedAssignee t e2 ->
     wellAnnotatedExpression' (Assign e1 e2) (GenRValueType (inject_type t))
 | WellAnnotatedExpression'_CompoundAssignPlusMinusArithmetic : forall aop e1 e2 (q:qualifiers) t t1 gt2,
     (aop = Add) \/ (aop = Sub) ->
     wellAnnotatedLValue e1 q t ->
     AilTypesAux_defns.lvalueConversion t t1 ->
     wellAnnotatedRValue e2 gt2 ->
     AilTypesAux_defns.modifiable q t ->
     AilTypesAux_defns.arithmetic t1 ->
     arithmetic gt2 ->
     wellAnnotatedExpression' (CompoundAssign e1 aop e2) (GenRValueType (inject_type t1))
 | WellAnnotatedExpression'_CompoundAssignPlusMinusPointer : forall aop e1 e2 t1 q' q t gt2,
     (aop = Add) \/ (aop = Sub) ->
     wellAnnotatedLValue e1 q' (Pointer q t) ->
     AilTypesAux_defns.lvalueConversion (Pointer q t) t1 ->
     wellAnnotatedRValue e2 gt2 ->
     AilTypesAux_defns.modifiable q' (Pointer q t)  ->
     AilTypesAux_defns.complete t ->
     integer gt2 ->
     wellAnnotatedExpression' (CompoundAssign e1 aop e2) (GenRValueType (inject_type t1))
 | WellAnnotatedExpression'_CompoundAssign : forall aop e1 e2 t1 q t gt2,
     ~ ((aop = Add) \/ (aop = Sub)) ->
     wellAnnotatedLValue e1 q t ->
     AilTypesAux_defns.lvalueConversion t t1 ->
     wellAnnotatedRValue e2 gt2 ->
     AilTypesAux_defns.modifiable q t ->
     wellTypedBinaryArithmetic (inject_type t1) aop gt2 ->
     wellAnnotatedExpression' (CompoundAssign e1 aop e2) (GenRValueType (inject_type t1))
 | WellAnnotatedExpression'_Comma : forall e1 e2 gt1 gt2,
     wellAnnotatedRValue e1 gt1 ->
     wellAnnotatedRValue e2 gt2 ->
     wellAnnotatedExpression' (Binary e1 Comma e2) (GenRValueType gt2)
with wellAnnotatedExpression {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} : expression A2 -> genTypeCategory -> Prop :=
 | WellAnnotatedExpression_Annotated : forall a e gtc,
     get_type A a = gtc ->
     wellAnnotatedExpression' e gtc ->
     wellAnnotatedExpression (AnnotatedExpression a e) gtc
with wellAnnotatedRValue {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} : expression A2 -> genType -> Prop :=
 | wellAnnotatedRValue_RValueType : forall e gt gt',
     wellAnnotatedExpression e (GenRValueType gt') ->
     pointerConversion gt' gt ->
     wellAnnotatedRValue e gt
 | wellAnnotatedRValue_LValueType : forall e t t' q',
     wellAnnotatedLValue e q' t' ->
     AilTypesAux_defns.lvalueConversion t' t ->
     wellAnnotatedRValue e (inject_type t)
with wellAnnotatedLValue {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} : expression A2 -> qualifiers -> ctype -> Prop :=
 | WellAnnotatedLValue : forall e q t,
     wellAnnotatedExpression e (GenLValueType q t) ->
     wellAnnotatedLValue e q t
with wellAnnotated {A1 A2 B1 B2: Set} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} : expression A2 -> Prop :=
 | WellAnnotated : forall e gt,
     wellAnnotatedExpression e gt ->
     wellAnnotated e
with wellAnnotatedArguments {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} : list (expression A2) -> list (qualifiers * ctype) -> Prop :=
 | WellAnnotatedArguments_nil :
     wellAnnotatedArguments nil nil
 | WellAnnotatedArguments_cons es p : forall e q t t',
     AilTypesAux_defns.pointerConversion t t' ->
     wellAnnotatedAssignee t' e ->
     wellAnnotatedArguments es p ->
     wellAnnotatedArguments (e :: es) ((q, t) :: p)
with wellAnnotatedAssignee {A1 A2 B1 B2: Set} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma}: ctype -> expression A2 -> Prop :=
 | WellAnnotatedAssignee_Arithmetic : forall e2 t1 gt2,
     wellAnnotatedRValue e2 gt2 ->
     AilTypesAux_defns.arithmetic t1 ->
     arithmetic gt2 ->
     wellAnnotatedAssignee t1 e2
 | WellAnnotatedAssignee_Pointer : forall e2 q1 q2 t1 t2,
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.compatible t1 t2 ->
     AilTypesAux.sub_qualifiers q2 q1 = true ->
     wellAnnotatedAssignee (Pointer q1 t1) e2
 | WellAnnotatedAssignee_VoidPointer1 : forall e2 q1 q2 t1 t2,
     AilTypesAux_defns.void t1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.object t2 ->
     AilTypesAux.sub_qualifiers q2 q1 = true ->
     wellAnnotatedAssignee (Pointer q1 t1) e2
 | WellAnnotatedAssignee_VoidPointer2 : forall e2 q1 q2 t1 t2,
     AilTypesAux_defns.object t1 ->
     wellAnnotatedRValue e2 (GenPointer q2 t2) ->
     AilTypesAux_defns.void t2 ->
     AilTypesAux.sub_qualifiers q2 q1 = true ->
     wellAnnotatedAssignee (Pointer q1 t1) e2
 | WellAnnotatedAssignee_NullPointerConstant : forall e2 t1 gt2,
     AilTypesAux_defns.pointer t1 ->
     wellAnnotatedRValue e2 gt2 ->
     nullPointerConstant e2 ->
     wellAnnotatedAssignee t1 e2
 | WellAnnotatedAssignee_Bool : forall e2 t1 gt2,
     AilTypesAux_defns.boolean t1 ->
     wellAnnotatedRValue e2 gt2 ->
     pointer gt2 ->
     wellAnnotatedAssignee t1 e2.
Arguments wellAnnotatedExpression' : default implicits.
Arguments wellAnnotatedExpression  : default implicits.
Arguments wellAnnotatedArguments   : default implicits.
Arguments wellAnnotatedLValue      : default implicits.
Arguments wellAnnotatedRValue      : default implicits.
Arguments wellAnnotatedAssignee    : default implicits.
Arguments wellAnnotated            : default implicits.

Inductive wellAnnotatedDefinition {A1 A2 B1 B2 : Set} (A : annotation A1 A2) (S : sigma  B1 B2) G : identifier * expression A2 -> Prop :=
  | WellAnnotatedDefinition :
      forall v e q t,
        lookup G v (q, t) ->
        wellAnnotatedAssignee A S G t e ->
        wellAnnotatedDefinition A S G (v, e).

Inductive wellAnnotatedStatement' {A1 A2 B B1 B2: Set} {A : annotation A1 A2} {S : sigma B1 B2} (G : gamma) : ctype -> statement' B A2 -> Prop :=    (* defn wellAnnotatedStatement *)
 | WellAnnotatedStatement'_Label : forall t_return l s,
     wellAnnotatedStatement  G t_return s ->
     wellAnnotatedStatement' G t_return (Label l s)
 | WellAnnotatedStatement'_Case : forall t_return ic it s,
     typeOfConstant ic it ->
     wellAnnotatedStatement  G t_return s ->
     wellAnnotatedStatement' G t_return (Case ic s)
 | WellAnnotatedStatement'_Default : forall t_return s,
     wellAnnotatedStatement  G t_return s ->
     wellAnnotatedStatement' G t_return (Default s)
 | WellAnnotatedStatement'_Block : forall t_return bs ss,
     AilTyping_defns.wellFormedBindings bs ->
     freshBindings bs S ->
     allList (wellAnnotatedStatement (Context.add_bindings bs G) t_return) ss ->
     wellAnnotatedStatement' G t_return (Block bs ss)
 | WellAnnotatedStatement'_Skip : forall t_return,
     wellAnnotatedStatement' G t_return Skip
 | WellAnnotatedStatement'_Expression : forall t_return e,
     wellAnnotated A S G e ->
     wellAnnotatedStatement' G t_return (Expression e)
 | WellAnnotatedStatement'_If : forall t_return e s1 s2 t,
     wellAnnotatedRValue A S G e t ->
     scalar t ->
     wellAnnotatedStatement  G t_return s1 ->
     wellAnnotatedStatement  G t_return s2 ->
     wellAnnotatedStatement' G t_return (If e s1 s2)
 | WellAnnotatedStatement'_Switch : forall t_return e s t,
     wellAnnotatedRValue A S G e t ->
     integer t ->
     wellAnnotatedStatement  G t_return s ->
     wellAnnotatedStatement' G t_return (Switch e s)
 | WellAnnotatedStatement'_While : forall t_return e s t,
     wellAnnotatedRValue A S G e t ->
     scalar t ->
     wellAnnotatedStatement  G t_return s ->
     wellAnnotatedStatement' G t_return (While e s)
 | WellAnnotatedStatement'_Do : forall t_return s e t,
     wellAnnotatedRValue A S G e t ->
     scalar t ->
     wellAnnotatedStatement  G t_return s ->
     wellAnnotatedStatement' G t_return (Do s e)
 | WellAnnotatedStatement'_Goto : forall t_return l,
     wellAnnotatedStatement' G t_return (Goto l)
 | WellAnnotatedStatement'_Continue : forall t_return,
     wellAnnotatedStatement' G t_return Continue
 | WellAnnotatedStatement'_Break : forall t_return,
     wellAnnotatedStatement' G t_return Break
 | WellAnnotatedStatement'_ReturnVoid :
     wellAnnotatedStatement' G Void ReturnVoid
 | WellAnnotatedStatement'_Return : forall t_return e,
     wellAnnotatedAssignee A S G t_return e ->
     wellAnnotatedStatement' G t_return (Return e)
 | WellAnnotatedStatement'_Declaration : forall t_return ds,
     allList (wellAnnotatedDefinition A S G) ds ->
     wellAnnotatedStatement' G t_return (Declaration ds)
with wellAnnotatedStatement {A1 A2 B B1 B2: Set} {A : annotation A1 A2} {S : sigma B1 B2} (G : gamma) : ctype -> statement B A2 -> Prop :=
 | WellAnnotatedStatement_AnnotatedStatement : forall t_return a s,
     wellAnnotatedStatement' G t_return s ->
     wellAnnotatedStatement  G t_return (AnnotatedStatement a s).
Arguments wellAnnotatedStatement' : default implicits.
Arguments wellAnnotatedStatement  : default implicits.

Inductive wellAnnotatedFunction {A1 A2 B B1 B2: Set} (A : annotation A1 A2) (S : sigma B1 B2) : (ctype * bindings) * statement B A2 -> Prop :=
  | WellAnnotatedFunction t_return bs s :
      AilTyping_defns.wellFormedBindings bs ->
      freshBindings bs S ->
      wfType (Function t_return (parameters_of_bindings bs)) ->
      wellAnnotatedStatement A S (Context.add_bindings bs Context.empty) t_return s ->
      wellAnnotatedFunction A S (t_return, bs, s).      

Definition wellAnnotatedSigma {A1 A2 B : Set} (A : annotation A1 A2) (S : sigma B A2) : Prop :=
  forall v p, lookup S v p -> wellAnnotatedFunction A S p.

Inductive wellAnnotatedProgram {A1 A2 B : Set} (A : annotation A1 A2) : program A1 A2 -> Prop :=
 | WellAnnotatedProgram main S s:
     lookup S main (Basic (Integer (Signed Int)), nil, s) ->
     wellAnnotatedSigma A S ->
     wellAnnotatedProgram A (main, S).
