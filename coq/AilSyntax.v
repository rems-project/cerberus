Require Import List.

Require Import NatMap.
Require Export AilTypes.

Parameter a : Set.
Axiom a_ex : exists l : a, True.

Inductive integerSuffix : Set := 
 | SuffixUnsigned : integerSuffix
 | SuffixUnsignedLong : integerSuffix
 | SuffixUnsignedLongLong : integerSuffix
 | SuffixLong : integerSuffix
 | SuffixLongLong : integerSuffix.

Inductive arithmeticOperator : Set :=  (*r 6.5.5 Multiplicative operators *)
 | Mul : arithmeticOperator
 | Div : arithmeticOperator
 | Mod : arithmeticOperator (*r 6.5.6 Additive operators *)
 | Add : arithmeticOperator
 | Sub : arithmeticOperator (*r 6.5.7 Bitwise shift operators *)
 | Shl : arithmeticOperator
 | Shr : arithmeticOperator (*r 6.5.10 Bitwise AND operator *)
 | Band : arithmeticOperator (*r 6.5.11 Bitwise exclusive OR operator *)
 | Bor : arithmeticOperator (*r 6.5.12 Bitwise inclusive OR operator *)
 | Xor : arithmeticOperator (*r Binary operators from 6.5.5-14, 6.5.17 *).

Inductive integerConstant : Set := 
 | IntegerConstantSuffix : nat -> integerConstant
 | IntegerConstantPlain : nat -> integerSuffix -> integerConstant (*r 6.4.4 Constants *).

Inductive binaryOperator : Set :=  (*r Group of operators also used for assigments *)
 | Arithmetic : arithmeticOperator -> binaryOperator (*r 6.5.17 Comma operator *)
 | Comma : binaryOperator (*r 6.5.13 Logical AND operator *)
 | And : binaryOperator (*r 6.5.14 Logical OR operator *)
 | Or : binaryOperator (*r 6.5.8 Relational operators *)
 | Lt : binaryOperator
 | Gt : binaryOperator
 | Le : binaryOperator
 | Ge : binaryOperator (*r 6.5.9 Equality operators *)
 | Eq : binaryOperator
 | Ne : binaryOperator.

Inductive unaryOperator : Set := 
 | Plus : unaryOperator
 | Minus : unaryOperator
 | Bnot : unaryOperator
 | Address : unaryOperator
 | Indirection : unaryOperator
 | PostfixIncr : unaryOperator
 | PostfixDecr : unaryOperator.

Inductive constant : Set := 
 | ConstantInteger : integerConstant -> constant.

Inductive expression := 
 | ExpUnary : unaryOperator -> expressionL -> expression
 | ExpBinary : expressionL -> binaryOperator -> expressionL -> expression
 | ExpAssign : expressionL -> expressionL -> expression
 | ExpCompoundAssign : expressionL -> arithmeticOperator -> expressionL -> expression
 | ExpConditional : expressionL -> expressionL -> expressionL -> expression
 | ExpCast : type -> expressionL -> expression
 | ExpCall : expressionL -> list expressionL -> expression
 | ExpConstant : constant -> expression
 | ExpVariable : nat -> expression
 | ExpSizeof : type -> expression
 | ExpAlignof : type -> expression
with expressionL := 
 | ExpLDef : a -> expression -> expressionL.

Module GammaMap := NatMap.NatMap.
Definition gamma := GammaMap.t type.

Inductive definition := 
 | DefinitionDef : nat -> expressionL -> definition (*r Statements *).

Inductive statement := 
 | StmtSkip : statement
 | StmtExp : expressionL -> statement
 | StmtBlock : gamma -> list statementL -> statement
 | StmtIf : expressionL -> statementL -> statementL -> statement
 | StmtWhile : expressionL -> statementL -> statement
 | StmtDo : statementL -> expressionL -> statement
 | StmtBreak : statement
 | StmtContinue : statement
 | StmtReturnVoid : statement
 | StmtReturn : expressionL -> statement
 | StmtSwitch : expressionL -> statementL -> statement
 | StmtCase : integerConstant -> statementL -> statement
 | StmtDefault : statementL -> statement
 | StmtLabel : nat -> statementL -> statement
 | StmtGoto : nat -> statement
 | StmtDeclaration : list definition -> statement
with statementL := 
 | StmtLDef : a -> statement -> statementL.

Inductive storageDuration : Set :=  (*r storage duration (\S6.2.4\#1) *)
 | Static : storageDuration
 | Thread : storageDuration
 | Automatic : storageDuration
 | Allocated : storageDuration.

Inductive typeCategory := 
 | LvalueT : type -> typeCategory
 | ExpressionT : type -> typeCategory.

Inductive declaration := 
 | Def : type -> option storageDuration -> declaration.

Module SigmaMap := NatMap.NatMap.
Definition sigma := SigmaMap.t (type * statementL)%type.

Inductive program := 
 | Program : nat -> sigma -> program.

Section expressionL_expression_rect.

Set Implicit Arguments.

Variables
  (Pe : expression -> Prop)
  (PeL : expressionL -> Prop)
  (PeL_list : list expressionL -> Prop).

Hypothesis
  (H_ExpLDef : forall l e, Pe e -> PeL (ExpLDef l e))
  (H_ExpUnary : forall op eL, PeL eL -> Pe (ExpUnary op eL))
  (H_ExpBinary : forall op eL1 eL2, PeL eL1 -> PeL eL2 -> Pe (ExpBinary eL1 op eL2))
  (H_ExpAssign : forall eL1 eL2, PeL eL1 -> PeL eL2 -> Pe (ExpAssign eL1 eL2))
  (H_ExpCompoundAssign : forall op eL1 eL2, PeL eL1 -> PeL eL2 -> Pe (ExpCompoundAssign eL1 op eL2))
  (H_ExpConditional : forall eL1 eL2 eL3, PeL eL1 -> PeL eL2 -> PeL eL3 -> Pe (ExpConditional eL1 eL2 eL3))
  (H_ExpCast : forall ty eL, PeL eL -> Pe (ExpCast ty eL))
  (H_ExpCall : forall eL_list eL, PeL_list eL_list -> PeL eL -> Pe (ExpCall eL eL_list))
  (H_ExpConstant : forall constant, Pe (ExpConstant constant))
  (H_ExpVariable : forall id, Pe (ExpVariable id))
  (H_ExpSizeof : forall ty, Pe (ExpSizeof ty))
  (H_ExpAlignof : forall ty, Pe (ExpAlignof ty))
  (H_eL_nil : PeL_list nil)
  (H_eL_cons : forall eL, PeL eL -> forall eL_list, PeL_list eL_list -> PeL_list (cons eL eL_list)).

Fixpoint e_ott_ind (n:expression) : Pe n :=
  match n as x return Pe x with
  | (ExpUnary op eL) => H_ExpUnary op (eL_ott_ind eL)
  | (ExpBinary eL1 op eL2) => H_ExpBinary op (eL_ott_ind eL1) (eL_ott_ind eL2)
  | (ExpAssign eL1 eL2) => H_ExpAssign (eL_ott_ind eL1) (eL_ott_ind eL2)
  | (ExpCompoundAssign eL1 op eL2) =>
      H_ExpCompoundAssign op (eL_ott_ind eL1) (eL_ott_ind eL2)
  | (ExpConditional eL1 eL2 eL3) =>
      H_ExpConditional (eL_ott_ind eL1) (eL_ott_ind eL2) (eL_ott_ind eL3)
  | (ExpCast t eL) => H_ExpCast t (eL_ott_ind eL)
  | (ExpCall eL eL_list) =>
      H_ExpCall
        ((fix eL_list_ott_ind eL_list :=
           match eL_list as x return PeL_list x with
           | nil           => H_eL_nil
           | cons eL' eL_list' => H_eL_cons (eL_ott_ind eL') (eL_list_ott_ind eL_list')
         end) eL_list)
      (eL_ott_ind eL)
  | (ExpConstant n) => H_ExpConstant n
  | (ExpVariable v) => H_ExpVariable v
  | (ExpSizeof t) => H_ExpSizeof t
  | (ExpAlignof t) => H_ExpAlignof t
end
with eL_ott_ind (n:expressionL) : PeL n :=
  match n as x return PeL x with
  | (ExpLDef l e) => H_ExpLDef l (e_ott_ind e)
end.

End expressionL_expression_rect.



Section e_ind.
Set Implicit Arguments.

Variables
  (Pe : expression -> Prop)
  (PeL_list : list expressionL -> Prop).

Hypothesis
  (H_ExpVariable : forall v, Pe (ExpVariable v))
  (H_ExpCall : forall l e eL_list, Pe e -> PeL_list eL_list -> Pe (ExpCall (ExpLDef l e) eL_list))
  (H_ExpUnary : forall l op e, Pe e -> Pe (ExpUnary op (ExpLDef l e)))
  (H_ExpBinary : forall l1 l2 op e1 e2, Pe e1 -> Pe e2 -> Pe (ExpBinary (ExpLDef l1 e1) op (ExpLDef l2 e2)))
  (H_ExpAssign : forall l1 l2 e1 e2, Pe e1 -> Pe e2 -> Pe (ExpAssign (ExpLDef l1 e1) (ExpLDef l2 e2)))
  (H_ExpCompoundAssign : forall l1 l2 op e1 e2, Pe e1 -> Pe e2 -> Pe (ExpCompoundAssign (ExpLDef l1 e1) op (ExpLDef l2 e2)))
  (H_ExpConditional : forall l1 l2 l3 e1 e2 e3, Pe e1 -> Pe e2 -> Pe e3 -> Pe (ExpConditional (ExpLDef l1 e1) (ExpLDef l2 e2) (ExpLDef l3 e3)))
  (H_ExpCast : forall l ty e, Pe e -> Pe (ExpCast ty (ExpLDef l e)))
  (H_ExpConstant : forall n, Pe (ExpConstant n))
  (H_ExpSizeof : forall ty, Pe (ExpSizeof ty))
  (H_ExpAlignof : forall ty, Pe (ExpAlignof ty))
  (H_nil : PeL_list nil)
  (H_cons : forall l e eL_list, Pe e -> PeL_list eL_list -> PeL_list (cons (ExpLDef l e) eL_list)).

Fixpoint e_ind expression : Pe expression :=
  match expression as x return Pe x with
  | (ExpVariable v) => H_ExpVariable v
  | (ExpCall (ExpLDef l e) eL_list) =>
      H_ExpCall l (e_ind e)
        ((fix eL_list_ott_ind2 eL_list :=
           match eL_list as x return PeL_list x with
           | nil => H_nil
           | cons (ExpLDef l' e') eL_list' => H_cons l' (e_ind e') (eL_list_ott_ind2 eL_list')
           end) eL_list)
  | (ExpUnary op (ExpLDef l e)) => H_ExpUnary l op (e_ind e)
  | (ExpBinary (ExpLDef l1 e1) op (ExpLDef l2 e2)) => H_ExpBinary l1 l2 op (e_ind e1) (e_ind e2)
  | (ExpAssign (ExpLDef l1 e1) (ExpLDef l2 e2)) => H_ExpAssign l1 l2 (e_ind e1) (e_ind e2)
  | (ExpCompoundAssign (ExpLDef l1 e1) op (ExpLDef l2 e2)) =>
      H_ExpCompoundAssign l1 l2 op (e_ind e1) (e_ind e2)
  | (ExpConditional (ExpLDef l1 e1) (ExpLDef l2 e2) (ExpLDef l3 e3)) =>
      H_ExpConditional l1 l2 l3 (e_ind e1) (e_ind e2) (e_ind e3)
  | (ExpCast t (ExpLDef l e)) => H_ExpCast l t (e_ind e)
  | (ExpConstant n) => H_ExpConstant n
  | (ExpSizeof t) => H_ExpSizeof t
  | (ExpAlignof t) => H_ExpAlignof t
end.

End e_ind.

Section statementL_statement_rect.

Set Implicit Arguments.

Variables
  (Ps : statement -> Prop)
  (PsL_list : list statementL -> Prop)
  (PsL : statementL -> Prop).

Hypothesis
  (H_StmtLDef : forall a s, Ps s -> PsL (StmtLDef a s))
  (H_StmtSkip : Ps StmtSkip)
  (H_StmtExp : forall eL, Ps (StmtExp eL))
  (H_StmtBlock : forall sL_list G, PsL_list sL_list -> Ps (StmtBlock G sL_list))
  (H_StmtIf : forall eL sL1 sL2, PsL sL1 -> PsL sL2 -> Ps (StmtIf eL sL1 sL2))
  (H_StmtWhile : forall eL sL, PsL sL -> Ps (StmtWhile eL sL))
  (H_StmtDo : forall sL eL, PsL sL -> Ps (StmtDo sL eL))
  (H_StmtBreak : Ps StmtBreak)
  (H_StmtContinue : Ps StmtContinue)
  (H_StmtReturnVoid : Ps StmtReturnVoid)
  (H_StmtReturn : forall eL, Ps (StmtReturn eL))
  (H_StmtSwitch : forall eL, forall (sL:statementL), PsL sL -> Ps (StmtSwitch eL sL))
  (H_StmtCase : forall n sL, PsL sL -> Ps (StmtCase n sL))
  (H_StmtDefault : forall sL, PsL sL -> Ps (StmtDefault sL))
  (H_StmtLabel : forall l sL, PsL sL -> Ps (StmtLabel l sL))
  (H_StmtGoto : forall l, Ps (StmtGoto l))
  (H_StmtDeclaration : forall definitions, Ps (StmtDeclaration definitions))
  (H_sL_nil : PsL_list nil)
  (H_sL_cons : forall sL sL_list, PsL sL -> PsL_list sL_list -> PsL_list (cons sL sL_list)).

Fixpoint s_ott_ind (n:statement) : Ps n :=
  match n as x return Ps x with
  | StmtSkip => H_StmtSkip 
  | (StmtExp eL) => H_StmtExp eL
  | (StmtBlock G sL_list) =>
      H_StmtBlock G
        ((fix sL_list_ott_ind sL_list : PsL_list sL_list :=
          match sL_list as x return PsL_list x with
          | nil => H_sL_nil
          | cons sL' sL_list' => H_sL_cons (sL_ott_ind sL') (sL_list_ott_ind sL_list')
          end) sL_list)
  | (StmtIf eL sL1 sL2) => H_StmtIf eL (sL_ott_ind sL1) (sL_ott_ind sL2)
  | (StmtWhile eL sL) => H_StmtWhile eL (sL_ott_ind sL)
  | (StmtDo sL eL) => H_StmtDo eL (sL_ott_ind sL)
  | StmtBreak => H_StmtBreak 
  | StmtContinue => H_StmtContinue 
  | StmtReturnVoid => H_StmtReturnVoid 
  | (StmtReturn eL) => H_StmtReturn eL
  | (StmtSwitch eL sL) => H_StmtSwitch eL (sL_ott_ind sL)
  | (StmtCase integerConstant5 sL) => H_StmtCase integerConstant5 (sL_ott_ind sL)
  | (StmtDefault sL) => H_StmtDefault (sL_ott_ind sL)
  | (StmtLabel l sL) => H_StmtLabel l (sL_ott_ind sL)
  | (StmtGoto l) => H_StmtGoto l
  | (StmtDeclaration definitions) => H_StmtDeclaration definitions
end
with sL_ott_ind (n:statementL) : PsL n :=
  match n as x return PsL x with
  | (StmtLDef l s) => H_StmtLDef l (s_ott_ind s)
end.

End statementL_statement_rect.
