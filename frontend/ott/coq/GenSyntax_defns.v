Require Import Common.
Require Import AilTypes.
Require Import AilSyntax.

Require Import GenTypes.
Require Import Annotation.

Require Import Context_defns.

Inductive equivAnnotationExpression' {A1 A2 A1' A2' : Set} {A : annotation A1 A2} {A' : annotation A1' A2'} : expression' A2 -> expression' A2' -> Prop := 
  | EquivAnnotationExpression'_Unary :
      forall {uop} {e1 e2},
        equivAnnotationExpression e1 e2 ->
        equivAnnotationExpression' (Unary uop e1) (Unary uop e2)
  | EquivAnnotationExpression'_Binary:
      forall {e1_1 e1_2} {bop} {e2_1 e2_2},
        equivAnnotationExpression e1_1 e1_2 ->
        equivAnnotationExpression e2_1 e2_2 ->
        equivAnnotationExpression' (Binary e1_1 bop e2_1) (Binary e1_2 bop e2_2)
  | EquivAnnotationExpression'_Assign :
      forall {e1_1 e1_2 e2_1 e2_2}, 
        equivAnnotationExpression e1_1 e1_2 ->
        equivAnnotationExpression e2_1 e2_2 ->
        equivAnnotationExpression' (Assign e1_1 e2_1) (Assign e1_2 e2_2)
  | EquivAnnotationExpression'_CompoundAssign :
      forall {e1_1 e1_2} {aop} {e2_1 e2_2},
        equivAnnotationExpression e1_1 e1_2 ->
        equivAnnotationExpression e2_1 e2_2 ->
        equivAnnotationExpression' (CompoundAssign e1_1 aop e2_1) (CompoundAssign e1_2 aop e2_2)        
  | EquivAnnotationExpression'_Conditional :
      forall {e1_1 e1_2 e2_1 e2_2 e3_1 e3_2},
        equivAnnotationExpression e1_1 e1_2 ->
        equivAnnotationExpression e2_1 e2_2 ->
        equivAnnotationExpression e3_1 e3_2 ->
        equivAnnotationExpression' (Conditional e1_1 e2_1 e3_1) (Conditional e1_2 e2_2 e3_2)
  | EquivAnnotationExpression'_Cast :
      forall {q} {t} {e1 e2},
        equivAnnotationExpression e1 e2 ->
        equivAnnotationExpression' (Cast q t e1) (Cast q t e2)
  | EquivAnnotationExpression'_Call :
      forall {e1 e2} {es1 es2},
        equivAnnotationExpression e1 e2 ->
        equivAnnotationArguments es1 es2 ->
        equivAnnotationExpression' (Call e1 es1) (Call e2 es2)
  | EquivAnnotationExpression'_Constant :
      forall {c},
        equivAnnotationExpression' (Constant c) (Constant c)
  | EquivAnnotationExpression'_Var :
      forall {v},
        equivAnnotationExpression' (Var v) (Var v)
  | EquivAnnotationExpression'_SizeOf :
      forall {q} {t},
        equivAnnotationExpression' (SizeOf q t) (SizeOf q t)
  | EquivAnnotationExpression'_AlignOf :
      forall {q} {t},
        equivAnnotationExpression' (AlignOf q t) (AlignOf q t)
with equivAnnotationArguments {A1 A2 A1' A2' : Set} {A : annotation A1 A2} {A' : annotation A1' A2'} : list (expression A2) -> list (expression A2') -> Prop :=
  | EquivAnnotationArguments_nil :
      equivAnnotationArguments nil nil
  | EquivAnnotationArguments_cons :
      forall {e1 e2} {es1 es2},
        equivAnnotationExpression e1 e2 ->
        equivAnnotationArguments es1 es2 ->
        equivAnnotationArguments (e1 :: es1) (e2 :: es2)
with equivAnnotationExpression {A1 A2 A1' A2' : Set} {A : annotation A1 A2} {A' : annotation A1' A2'} : expression A2 -> expression A2' -> Prop :=
  | EquivAnnotationExpression :
      forall {a1 a2} {e1 e2},
        get_type A a1 = get_type A' a2 ->
        equivAnnotationExpression' e1 e2 ->
        equivAnnotationExpression (AnnotatedExpression a1 e1) (AnnotatedExpression a2 e2).
Arguments equivAnnotationExpression' : default implicits.
Arguments equivAnnotationArguments : default implicits.
Arguments equivAnnotationExpression : default implicits.

Inductive equivAnnotationDefinition {A1 A2 A1' A2' : Set} {A : annotation A1 A2} {A' : annotation A1' A2'} : identifier * expression A2 -> identifier * expression A2' -> Prop :=
  | EquivAnnotationDefinition v e1 e2 :
      equivAnnotationExpression A A' e1 e2 ->
      equivAnnotationDefinition (v, e1) (v, e2).
Arguments equivAnnotationDefinition : default implicits.

Inductive equivAnnotationDeclaration {A1 A2 A1' A2' : Set} {A : annotation A1 A2} {A' : annotation A1' A2'} : list (identifier * expression A2) -> list (identifier * expression A2') -> Prop :=
  | EquivAnnotationDeclaration_nil :
      equivAnnotationDeclaration nil nil
  | EquivAnnotationDeclaration_cons {d1 d2} {ds1 ds2} :
      equivAnnotationDefinition A A' d1 d2 ->
      equivAnnotationDeclaration ds1 ds2 ->
      equivAnnotationDeclaration (d1 :: ds1) (d2 :: ds2).
Arguments equivAnnotationDeclaration : default implicits.

Inductive equivAnnotationStatement' {A1 A2 A1' A2' B1 B2 : Set} {A : annotation A1 A2} {A' : annotation A1' A2'} : statement' B1 A2 -> statement' B2 A2' -> Prop := 
  | EquivAnnotationStatement'_Skip :
      equivAnnotationStatement' Skip Skip
  | EquivAnnotationStatement'_Expression {e1 e2} :
      equivAnnotationExpression A A' e1 e2 ->
      equivAnnotationStatement' (Expression e1) (Expression e2)
  | EquivAnnotationStatement'_Block {b} {ss1 ss2} :
      equivAnnotationBlock ss1 ss2 ->
      equivAnnotationStatement' (Block b ss1) (Block b ss2)
  | EquivAnnotationStatement'_If {e1 e2} {s1_1 s1_2 s2_1 s2_2} :
      equivAnnotationExpression A A' e1 e2 ->
      equivAnnotationStatement s1_1 s1_2 ->
      equivAnnotationStatement s2_1 s2_2 ->
     equivAnnotationStatement' (If e1 s1_1 s2_1) (If e2 s1_2 s2_2)
  | EquivAnnotationStatement'_While {e1 e2} {s1 s2} :
      equivAnnotationExpression A A' e1 e2 ->
      equivAnnotationStatement s1 s2 ->
      equivAnnotationStatement' (While e1 s1) (While e2 s2)
  | EquivAnnotationStatement'_Do {s1 s2} {e1 e2} :
      equivAnnotationExpression A A' e1 e2 ->
      equivAnnotationStatement s1 s2 ->
      equivAnnotationStatement' (Do s1 e1) (Do s2 e2)
  | EquivAnnotationStatement'_Break :
      equivAnnotationStatement' Break Break
  | EquivAnnotationStatement'_Continue :
      equivAnnotationStatement' Continue Continue
  | EquivAnnotationStatement'_ReturnVoid :
      equivAnnotationStatement' ReturnVoid ReturnVoid
  | EquivAnnotationStatement'_Return {e1 e2} :
      equivAnnotationExpression A A' e1 e2 ->
      equivAnnotationStatement' (Return e1) (Return e2)
  | EquivAnnotationStatement'_Switch {e1 e2} {s1 s2} :
      equivAnnotationExpression A A' e1 e2 ->
      equivAnnotationStatement s1 s2 ->
      equivAnnotationStatement' (Switch e1 s1) (Switch e2 s2)
  | EquivAnnotationStatement'_Case {ic} {s1 s2} :
      equivAnnotationStatement s1 s2 ->
     equivAnnotationStatement' (Case ic s1) (Case ic s2)
  | EquivAnnotationStatement'_Default {s1 s2} :
      equivAnnotationStatement s1 s2 ->
      equivAnnotationStatement' (Default s1) (Default s2)
  | EquivAnnotationStatement'_Label {v} {s1 s2} :
      equivAnnotationStatement s1 s2 ->
      equivAnnotationStatement' (Label v s1) (Label v s2)
  | EquivAnnotationStatement'_Goto {v} :
      equivAnnotationStatement' (Goto v) (Goto v)
  | EquivAnnotationStatement'_Declaration {d1 d2} :
      equivAnnotationDeclaration A A' d1 d2 ->
      equivAnnotationStatement' (Declaration d1) (Declaration d2)
with equivAnnotationStatement {A1 A2 A1' A2' B1 B2 : Set} {A : annotation A1 A2} {A' : annotation A1' A2'} : statement B1 A2 -> statement B2 A2' -> Prop :=
  | EquivAnnotationStatement_AnnotatedStatement {a1 a2} {s1} {s2} :
      equivAnnotationStatement' s1 s2 ->
      equivAnnotationStatement (AnnotatedStatement a1 s1) (AnnotatedStatement a2 s2)
with equivAnnotationBlock {A1 A2 A1' A2' B1 B2 : Set} {A : annotation A1 A2} {A' : annotation A1' A2'} : list (statement B1 A2) -> list (statement B2 A2') -> Prop :=
  | EquivAnnotationBlock_nil :
      equivAnnotationBlock nil nil
  | EquivAnnotationBlock_cons {s1 s2} {b1 b2} :
      equivAnnotationStatement s1 s2 ->
      equivAnnotationBlock b1 b2 ->
      equivAnnotationBlock (s1 :: b1) (s2 :: b2).
Arguments equivAnnotationStatement' : default implicits.
Arguments equivAnnotationStatement : default implicits.
Arguments equivAnnotationBlock : default implicits.

Definition equivAnnotationFunction {A1 A2 A1' A2' B1 B2 : Set} (A : annotation A1 A2) (A' : annotation A1' A2') : ctype * bindings * statement B1 A2 -> ctype * bindings * statement B2 A2' -> Prop :=
  cross2 eq (equivAnnotationStatement A A').

Definition equivAnnotationSigma {A1 A2 A1' A2' B1 B2 : Set} (A : annotation A1 A2) (A' : annotation A1' A2') : sigma B1 A2 -> sigma B2 A2' -> Prop :=
  equiv (fun _ => equivAnnotationFunction A A').

Definition equivAnnotationProgram {A1 A2 A1' A2' B1 B2 : Set} (A : annotation A1 A2) (A' : annotation A1' A2') : program B1 A2 -> program B2 A2' -> Prop :=
  cross2 eq (equivAnnotationSigma A A').

