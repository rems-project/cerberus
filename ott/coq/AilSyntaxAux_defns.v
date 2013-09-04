Require Import Common.
Require Import AilTypes.
Require Import AilSyntax.

Require Import AilTypesAux_defns.
Require Import Context_defns.

(* defns Jfv *)
Inductive fv' {A} : identifier -> expression' A -> Prop :=    (* defn fv *)
 | Fv'_Unary {v} {uop} {e} :
     fv v e ->
     fv' v (Unary uop e)
 | Fv'_Binary1 {v} {e1} {bop} {e2} :
     fv v e1 ->
     fv' v (Binary e1 bop e2)
 | Fv'_Binary2 {v} {e1} {bop} {e2} :
     fv v e2 ->
     fv' v (Binary e1 bop e2)
 | Fv'_Assign1 {v} {e1 e2} :
     fv v e1 ->
     fv' v (Assign e1 e2)
 | Fv'_Assign2 {v} {e1 e2} :
     fv v e2 ->
     fv' v (Assign e1 e2)
 | Fv'_CompoundAssign1 {v} {e1} {aop} {e2} :
     fv v e1 ->
     fv' v (CompoundAssign e1 aop e2)
 | Fv'_CompoundAssign2 {v} {e1} {aop} {e2} :
     fv v e2 ->
     fv' v (CompoundAssign e1 aop e2)
 | Fv'_Conditional1 {v} {e1 e2 e3} :
     fv v e1 ->
     fv' v (Conditional e1 e2 e3)
 | Fv'_Conditional2 {v} {e1 e2 e3} :
     fv v e2 ->
     fv' v (Conditional e1 e2 e3)
 | Fv'_Conditional3 {v} {e1 e2 e3} :
     fv v e3 ->
     fv' v (Conditional e1 e2 e3)
 | Fv'_Cast {v} {q} {t} {e} :
     fv v e ->
     fv' v (Cast q t e)
 | Fv'_Call {v} {e} {es} :
     fv v e ->
     fv' v (Call e es)
 | Fv'_CallArgument {v} {e} {es} :
     fvArguments v es ->
     fv' v (Call e es)
 | Fv'_Var {v} :
     fv' v (Var v)
with fv {A} : identifier -> expression A -> Prop :=
 | Fv_AnnotatedExpression {v} {a} {e} :
     fv' v e ->
     fv v (AnnotatedExpression a e)
with fvArguments {A} : identifier -> list (expression A) -> Prop :=
 | FvArguments_head {v} {e} {es} :
     fv v e ->
     fvArguments v (e :: es)
 | FvArguments_tail {v} {e} {es} :
     fvArguments v es ->
     fvArguments v (e :: es).
(** definitions *)

(* defns JisNullPointerConstant *)
Inductive nullPointerConstant' {A} : expression' A -> Prop :=    (* defn isNullPointerConstant *)
 | NullPointerConstant'_Zero : 
     nullPointerConstant' (Constant (ConstantInteger  ( 0 , None) ))
 | NullPointerConstant'_Pointer {q q'} {e} :
     nullPointerConstant e ->
     unqualified q  ->
     unqualified q' ->
     nullPointerConstant' (Cast q (Pointer q' Void) e)
with nullPointerConstant {A} : expression A -> Prop :=
 | NullPointerConstant_AnnotatedExpression {a} {e} :
     nullPointerConstant' e ->
     nullPointerConstant (AnnotatedExpression a e).

Inductive constantExpressionContext' {A} (ic : integerConstant) : expression' A -> Prop :=
 | ConstantExpressionContext'_Unary uop e :
     constantExpressionContext ic e ->
     constantExpressionContext' ic (Unary uop e)
 | ConstantExpressionContext'_Binary1 e1 bop e2 :
     constantExpressionContext ic e1 ->
     constantExpressionContext' ic (Binary e1 bop e2)
 | ConstantExpressionContext'_Binary2 e1 bop e2 :
     constantExpressionContext ic e2 ->
     constantExpressionContext' ic (Binary e1 bop e2)
 | ConstantExpressionContext'_Assign1 e1 e2 :
     constantExpressionContext ic e1 ->
     constantExpressionContext' ic (Assign e1 e2)
 | ConstantExpressionContext'_Assign2 e1 e2 :
     constantExpressionContext ic e2 ->
     constantExpressionContext' ic (Assign e1 e2)
 | ConstantExpressionContext'_CompoundAssign1 e1 aop e2 :
     constantExpressionContext ic e1 ->
     constantExpressionContext' ic (CompoundAssign e1 aop e2)
 | ConstantExpressionContext'_CompoundAssign2 e1 aop e2 :
     constantExpressionContext ic e2 ->
     constantExpressionContext' ic (CompoundAssign e1 aop e2)
 | ConstantExpressionContext'_Conditional1 e1 e2 e3 :
     constantExpressionContext ic e1 ->
     constantExpressionContext' ic (Conditional e1 e2 e3)
 | ConstantExpressionContext'_Conditional2 e1 e2 e3 :
     constantExpressionContext ic e2 ->
     constantExpressionContext' ic (Conditional e1 e2 e3)
 | ConstantExpressionContext'_Conditional3 e1 e2 e3 :
     constantExpressionContext ic e3 ->
     constantExpressionContext' ic (Conditional e1 e2 e3)
 | ConstantExpressionContext'_Cast q t e :
     constantExpressionContext ic e ->
     constantExpressionContext' ic (Cast q t e)
 | ConstantExpressionContext'_Call e es :
     constantExpressionContext ic e ->
     constantExpressionContext' ic (Call e es)
 | ConstantExpressionContext'_CallArgument e es :
     constantArgumentsContext ic es ->
     constantExpressionContext' ic (Call e es)
 | ConstantExpressionContext'_Constant :
     constantExpressionContext' ic (Constant (ConstantInteger ic))
with constantExpressionContext {A} (ic : integerConstant) : expression A -> Prop :=
 | ConstantContex_AnnotatedExpression a e :
     constantExpressionContext' ic e ->
     constantExpressionContext ic (AnnotatedExpression a e)
with constantArgumentsContext {A} (ic : integerConstant) : list (expression A) -> Prop :=
 | ConstantArgumentsContext_head e es :
     constantExpressionContext ic e ->
     constantArgumentsContext ic (e :: es)
 | ConstantArgumentsContext_tail e es :
     constantArgumentsContext ic es ->
     constantArgumentsContext ic (e :: es).

Inductive constantDeclarationContext {A : Set} (ic : integerConstant) : list (identifier * expression A) -> Prop :=
 | ConstantDeclarationContext_head v e ds:
     constantExpressionContext ic e ->
     constantDeclarationContext ic ((v, e) :: ds)
 | ConstantDeclarationContext_tail d ds:
     constantDeclarationContext ic ds ->
     constantDeclarationContext ic (d :: ds).

Inductive constantStatementContext' {A B : Set} (ic : integerConstant) : statement' A B -> Prop := 
 | ConstantStatementContext'_Expression e :
     constantExpressionContext ic e ->
     constantStatementContext' ic (Expression e)
 | ConstantStatementContext'_Block b ss :
     constantBlockContext ic ss ->
     constantStatementContext' ic (Block b ss)
 | ConstantStatementContext'_If1 e s1 s2 :
     constantExpressionContext ic e ->
     constantStatementContext' ic (If e s1 s2)
 | ConstantStatementContext'_If2 e s1 s2 :
     constantStatementContext ic s1 ->
     constantStatementContext' ic (If e s1 s2)
 | ConstantStatementContext'_If3 e s1 s2 :
     constantStatementContext ic s2 ->
     constantStatementContext' ic (If e s1 s2)
 | ConstantStatementContext'_While1 e s :
     constantExpressionContext ic e ->
     constantStatementContext' ic (While e s)
 | ConstantStatementContext'_While2 e s :
     constantStatementContext ic s ->
     constantStatementContext' ic (While e s)
 | ConstantStatementContext'_Do1 s e :
     constantStatementContext ic s ->
     constantStatementContext' ic (Do s e)
 | ConstantStatementContext'_Do2 s e :
     constantExpressionContext ic e ->
     constantStatementContext' ic (Do s e)
 | ConstantStatementContext'_Return e :
     constantExpressionContext ic e ->
     constantStatementContext' ic (Return e)
 | ConstantStatementContext'_Switch1 e s :
     constantExpressionContext ic e ->
     constantStatementContext' ic (Switch e s)
 | ConstantStatementContext'_Switch2 e s :
     constantStatementContext ic s ->
     constantStatementContext' ic (Switch e s)
 | ConstantStatementContext'_Case1 s :
     constantStatementContext' ic (Case ic s)
 | ConstantStatementContext'_Case2 ic' s :
     constantStatementContext ic s ->
     constantStatementContext' ic (Case ic' s)
 | ConstantStatementContext'_Default s :
     constantStatementContext ic s ->
     constantStatementContext' ic (Default s)
 | ConstantStatementContext'_Label v s :
     constantStatementContext' ic (Label v s)
 | ConstantStatementContext'_Declaration d :
     constantDeclarationContext ic d ->
     constantStatementContext' ic (Declaration d)
with constantStatementContext {A B : Set} (ic : integerConstant) : statement A B -> Prop :=
 | ConstantStatementContext_AnnotatedStatement a s :
     constantStatementContext' ic s ->
     constantStatementContext ic (AnnotatedStatement a s)
with constantBlockContext {A B : Set} (ic : integerConstant) : list (statement A B) -> Prop :=
 | ConstantBlockContext_head s ss:
     constantStatementContext ic s ->
     constantBlockContext ic (s :: ss)
 | ConstantBlockContext_tail s ss:
     constantBlockContext ic ss ->
     constantBlockContext ic (s :: ss).

Inductive constantFunctionContext {A1 A2 : Set} (ic : integerConstant) : (ctype * bindings) * statement A1 A2 -> Prop :=
  | ConstantFunctionContext t_return bs s :
      constantStatementContext ic s ->
      constantFunctionContext ic (t_return, bs, s).      

Inductive constantSigmaContext {A1 A2 : Set} (ic : integerConstant) : sigma A1 A2 -> Prop :=
  | ConstantSigmaContext S v p :
      lookup S v p ->
      constantFunctionContext ic p ->
      constantSigmaContext ic S.

Inductive constantProgramContext {A1 A2: Set} (ic : integerConstant) : program A1 A2 -> Prop :=    (* defn wellTypedProgram *)
 | ConstantProgramContext main S v t p s:
     lookup S v (t, p, s) ->
     constantSigmaContext ic S ->
     constantProgramContext ic (main, S).
