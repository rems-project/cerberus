Require Import ZArith.

Require Import Common.
Require Import AilTypes.
Require Import Implementation.
Require Import Range_defns.

Require AilTypesAux_defns.
Require AilTyping_defns.

Require Import GenTypes.

Local Open Scope Z.

Inductive array : genType -> Prop :=
 | Array_GenArray : forall (t:ctype) (n:nat),
     array (GenArray t n).

Inductive function : genType -> Prop :=
 | Function_GenFunction : forall q p,
     function (GenFunction q p).

Inductive pointerConversion : genType -> genType -> Prop :=
  | PointerConversion_GenArray :
      forall {t} {n} {q},
        AilTypesAux_defns.unqualified q ->
        pointerConversion (GenArray t n) (GenPointer q t)
  | PointerConversion_GenFunction :
      forall {t} {q q'},
        AilTypesAux_defns.unqualified q' ->
        pointerConversion (GenFunction t q) (GenPointer q' (Function t q))
  | PointerConversion_other :
      forall {gt},
        ~ array    gt ->
        ~ function gt ->
        pointerConversion gt gt.

Inductive integer : genType -> Prop :=
 | Integer_GenInteger : forall (git:genIntegerType),
     integer (GenBasic (GenInteger git)).

Inductive real : genType -> Prop :=    (* defn real *)
 | Real_integer : forall (gt:genType),
     integer gt ->
     real gt.

Inductive pointer : genType -> Prop :=
 | Pointer_GenPointer : forall (q:qualifiers) (t:ctype),
     pointer (GenPointer q t).

Inductive arithmetic : genType -> Prop :=
 | Arithmetic_Integer : forall (gt:genType),
     integer    gt ->
     arithmetic gt.

Inductive scalar : genType -> Prop :=
 | Scalar_Pointer : forall (gt:genType),
     pointer gt ->
     scalar  gt
 | Scalar_Arithmetic : forall (gt:genType),
     arithmetic gt ->
     scalar gt.

Inductive void : genType -> Prop :=
 | Void_GenVoid : 
     void GenVoid.

Inductive promoted : genIntegerType -> Prop :=
  | Promoted_Promote git : promoted (Promote git).

Inductive integerPromotion : genIntegerType -> genIntegerType -> Prop :=
 | IntegerPromotion_Promote git: 
     integerPromotion git (Promote git).

Inductive promotion : genType -> genType -> Prop :=
 | Promotion_Promote git git':
     integerPromotion git git' ->
     promotion (GenBasic (GenInteger git)) (GenBasic (GenInteger git')).

Inductive usualArithmeticPromotedInteger : genIntegerType -> genIntegerType -> genIntegerType -> Prop :=
 | UsualArithmeticPromotedInteger git1 git2 :
     usualArithmeticPromotedInteger git1 git2 (Usual git1 git2).

Inductive usualArithmeticInteger : genIntegerType -> genIntegerType -> genIntegerType -> Prop :=
 | UsualArithmeticInteger git1 git1' git2 git2' git :
     integerPromotion git1 git1' ->
     integerPromotion git2 git2' ->
     usualArithmeticPromotedInteger git1' git2' git ->
     usualArithmeticInteger git1 git2 git.

Inductive usualArithmetic : genType -> genType -> genType -> Prop :=
 | UsualArithmetic_GenInteger git1 git2 git :
     usualArithmeticInteger git1 git2 git ->
     usualArithmetic (GenBasic (GenInteger git1))
                     (GenBasic (GenInteger git2))
                     (GenBasic (GenInteger git)).

Inductive interpretGenIntegerType P : genIntegerType -> integerType -> Prop :=
 | InterpretGenIntegerType_Concrete it :
     interpretGenIntegerType P (Concrete it) it
 | InterpretGenIntegerType_SizeT :
     interpretGenIntegerType P SizeT (size_t P)
 | InterpretGenIntegerType_PtrdiffT :
     interpretGenIntegerType P PtrdiffT (ptrdiff_t P)
 | InterpretGenIntegerType_Unknown ic it :
     AilTyping_defns.typeOfConstant P ic it ->
     interpretGenIntegerType P (Unknown ic) it
 | InterpretGenIntegerType_Promote git it it' :
     interpretGenIntegerType P git it ->
     AilTypesAux_defns.integerPromotion P it it' ->
     interpretGenIntegerType P (Promote git) it'
 | InterpretGenIntegerType_Usual git1 git2 it1 it2 it :
     interpretGenIntegerType P git1 it1 ->
     interpretGenIntegerType P git2 it2 ->
     AilTypesAux_defns.usualArithmeticInteger P it1 it2 it ->
     interpretGenIntegerType P (Usual git1 git2) it.

Inductive interpretGenBasicType P : genBasicType -> basicType -> Prop :=
 | InterpretGenBasicType_GenInteger git it :
     interpretGenIntegerType P git it ->
     interpretGenBasicType P (GenInteger git) (Integer it).

Inductive interpretGenType P : genType -> ctype -> Prop :=
 | InterpretGenType_GenVoid :
     interpretGenType P GenVoid Void
 | InterpretGenType_GenBasic gbt bt :
     interpretGenBasicType P gbt bt -> interpretGenType P (GenBasic gbt) (Basic bt)
 | InterpretGenType_GenArray    t n : interpretGenType P (GenArray    t n) (Array    t n)
 | InterpretGenType_GenFunction t p : interpretGenType P (GenFunction t p) (Function t p)
 | InterpretGenType_GenPointer  q t : interpretGenType P (GenPointer  q t) (Pointer  q t).

Inductive interpretGenTypeCategory P : genTypeCategory -> typeCategory -> Prop :=
  | InterpretGenTypeCategory_GenRValueType gt t :
      interpretGenType P gt t ->
      interpretGenTypeCategory P (GenRValueType gt) (RValueType t)
  | InterpretGenTypeCategory_GenLValueType q t :
      interpretGenTypeCategory P (GenLValueType q t) (LValueType q t).
