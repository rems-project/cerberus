Require Import AilSyntax.
Require Import AilTypes.

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
