Require Import Common.
Require Import AilSyntax.
Require Import AilTypes.
Require Context_defns.

Inductive equivExpression' {A} : expression' A -> expression' A -> Set := 
  | EquivExpression'_Unary :
      forall {uop} {e1 e2},
        equivExpression e1 e2 ->
        equivExpression' (Unary uop e1) (Unary uop e2)
  | EquivExpression'_Binary:
      forall {e1_1 e1_2} {bop} {e2_1 e2_2},
        equivExpression e1_1 e1_2 ->
        equivExpression e2_1 e2_2 ->
        equivExpression' (Binary e1_1 bop e2_1) (Binary e1_2 bop e2_2)
  | EquivExpression'_Assign :
      forall {e1_1 e1_2 e2_1 e2_2}, 
        equivExpression e1_1 e1_2 ->
        equivExpression e2_1 e2_2 ->
        equivExpression' (Assign e1_1 e2_1) (Assign e1_2 e2_2)
  | EquivExpression'_CompoundAssign :
      forall {e1_1 e1_2} {aop} {e2_1 e2_2},
        equivExpression e1_1 e1_2 ->
        equivExpression e2_1 e2_2 ->
        equivExpression' (CompoundAssign e1_1 aop e2_1) (CompoundAssign e1_2 aop e2_2)        
  | EquivExpression'_Conditional :
      forall {e1_1 e1_2 e2_1 e2_2 e3_1 e3_2},
        equivExpression e1_1 e1_2 ->
        equivExpression e2_1 e2_2 ->
        equivExpression e3_1 e3_2 ->
        equivExpression' (Conditional e1_1 e2_1 e3_1) (Conditional e1_2 e2_2 e3_2)
  | EquivExpression'_Cast :
      forall {q} {t} {e1 e2},
        equivExpression e1 e2 ->
        equivExpression' (Cast q t e1) (Cast q t e2)
  | EquivExpression'_Call :
      forall {e1 e2} {es1 es2},
        equivExpression e1 e2 ->
        equivArguments es1 es2 ->
        equivExpression' (Call e1 es1) (Call e2 es2)
  | EquivExpression'_Constant :
      forall {c},
        equivExpression' (Constant c) (Constant c)
  | EquivExpression'_Var :
      forall {v},
        equivExpression' (Var v) (Var v)
  | EquivExpression'_SizeOf :
      forall {q} {t},
        equivExpression' (SizeOf q t) (SizeOf q t)
  | EquivExpression'_AlignOf :
      forall {q} {t},
        equivExpression' (AlignOf q t) (AlignOf q t)
with equivArguments {A} : list (expression A) -> list (expression A) -> Set :=
  | EquivArguments_nil :
      equivArguments nil nil
  | EquivArguments_cons :
      forall {e1 e2} {es1 es2},
        equivExpression e1 e2 ->
        equivArguments es1 es2 ->
        equivArguments (e1 :: es1) (e2 :: es2)
with equivExpression {A} : expression A -> expression A -> Set :=
  | EquivExpression :
      forall {a1 a2} {e1 e2},
        equivExpression' e1 e2 ->
        equivExpression (AnnotatedExpression a1 e1) (AnnotatedExpression a2 e2).
Arguments equivExpression' : default implicits.
Arguments equivArguments : default implicits.
Arguments equivExpression : default implicits.

Inductive equivDeclaration {A : Set} : list (identifier * expression A) -> list (identifier * expression A) -> Set :=
  | EquivDeclaration_nil :
      equivDeclaration nil nil
  | EquivDeclaration_cons {v} {e1 e2} {d1 d2} :
      equivExpression e1 e2 ->
      equivDeclaration d1 d2 ->
      equivDeclaration ((v, e1) :: d1) ((v, e2) :: d2).
Arguments equivDeclaration : default implicits.

Inductive equivStatement' {A B : Set} : statement' A B -> statement' A B -> Set := 
  | EquivStatement'_Skip :
      equivStatement' Skip Skip
  | EquivStatement'_Expression {e1 e2} :
      equivExpression e1 e2 ->
      equivStatement' (Expression e1) (Expression e2)
  | EquivStatement'_Block {b} {ss1 ss2} :
      equivBlock ss1 ss2 ->
      equivStatement' (Block b ss1) (Block b ss2)
  | EquivStatement'_If {e1 e2} {s1_1 s1_2 s2_1 s2_2} :
      equivExpression e1 e2 ->
      equivStatement s1_1 s1_2 ->
      equivStatement s2_1 s2_2 ->
     equivStatement' (If e1 s1_1 s2_1) (If e2 s1_2 s2_2)
  | EquivStatement'_While {e1 e2} {s1 s2} :
      equivExpression e1 e2 ->
      equivStatement s1 s2 ->
      equivStatement' (While e1 s1) (While e2 s2)
  | EquivStatement'_Do {s1 s2} {e1 e2} :
      equivExpression e1 e2 ->
      equivStatement s1 s2 ->
      equivStatement' (Do s1 e1) (Do s2 e2)
  | EquivStatement'_Break :
      equivStatement' Break Break
  | EquivStatement'_Continue :
      equivStatement' Continue Continue
  | EquivStatement'_ReturnVoid :
      equivStatement' ReturnVoid ReturnVoid
  | EquivStatement'_Return {e1 e2} :
      equivExpression e1 e2 ->
      equivStatement' (Return e1) (Return e2)
  | EquivStatement'_Switch {e1 e2} {s1 s2} :
      equivExpression e1 e2 ->
      equivStatement s1 s2 ->
      equivStatement' (Switch e1 s1) (Switch e2 s2)
  | EquivStatement'_Case {ic} {s1 s2} :
      equivStatement s1 s2 ->
     equivStatement' (Case ic s1) (Case ic s2)
  | EquivStatement'_Default {s1 s2} :
      equivStatement s1 s2 ->
      equivStatement' (Default s1) (Default s2)
  | EquivStatement'_Label {v} {s1 s2} :
      equivStatement s1 s2 ->
      equivStatement' (Label v s1) (Label v s2)
  | EquivStatement'_Goto {v} :
      equivStatement' (Goto v) (Goto v)
  | EquivStatement'_Declaration {d1 d2} :
      equivDeclaration d1 d2 ->
      equivStatement' (Declaration d1) (Declaration d2)
with equivStatement {A B : Set} : statement A B -> statement A B -> Set :=
  | EquivStatement_AnnotatedStatement {a1 a2} {s1 s2:statement' A B} :
      equivStatement' s1 s2 ->
      equivStatement (AnnotatedStatement a1 s1) (AnnotatedStatement a2 s2)
with equivBlock {A B : Set} : list (statement A B) -> list (statement A B) -> Set :=
  | EquivBlock_nil :
      equivBlock nil nil
  | EquivBlock_cons {s1 s2} {b1 b2} :
      equivStatement s1 s2 ->
      equivBlock b1 b2 ->
      equivBlock (s1 :: b1) (s2 :: b2).
Arguments equivStatement' : default implicits.
Arguments equivStatement : default implicits.
Arguments equivBlock : default implicits.

Definition equivSigma {A B : Set} : sigma A B -> sigma A B -> Type :=
  Context_defns.equiv (cross2 eq (@equivStatement A B)).

Definition equivEqSigma {A B : Set} : sigma A B -> sigma A B -> Type :=
  Context_defns.equiv eq.

Definition equivProgram {A B : Set} : program A B -> program A B -> Type :=
  cross2 eq equivSigma.

Definition equivEqProgram {A B : Set} : program A B -> program A B -> Type :=
  cross2 eq equivEqSigma.
