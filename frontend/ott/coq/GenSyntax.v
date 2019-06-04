Require Import Common.
Require Import AilTypes.
Require Import AilSyntax.

Require Import GenTypes.
Require Import Annotation.

Require Import Context.

Definition equiv_annotation_arguments_aux {A1 A2 A2' : Set} {A : annotation A1 A2} {A' : annotation A1 A2'} equiv_annotation_expression :=
  fix equiv_annotation_arguments (a1 : list (expression A1)) (a2 : list (expression A2)) : option (list (expression A2')) :=
    match a1, a2 with
    | nil     , nil      => Some nil
    | e1 :: a1, e2 :: a2 => equiv_annotation_expression e1 e2 >>= fun e =>
                            equiv_annotation_arguments  a1 a2 >>= fun a =>
                            Some (e :: a)
    | _       , _        => None
    end.
Arguments equiv_annotation_arguments_aux : default implicits.

Fixpoint equiv_annotation_expression' {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (e1 : expression' A1) (e2 : expression' A2) {struct e1} : option (expression' A2') :=
  let equiv_annotation_arguments := equiv_annotation_arguments_aux A A' (equiv_annotation_expression A A') in
  match e1, e2 with
  | Unary uop1 e1, Unary uop2 e2 =>
      if eq_unaryOperator uop1 uop2 then
        equiv_annotation_expression A A' e1 e2 >>= fun e =>
        Some (Unary uop1 e)
      else
        None
  | Binary e1_1 bop1 e2_1, Binary e1_2 bop2 e2_2 =>
      if eq_binaryOperator bop1 bop2 then
        equiv_annotation_expression A A' e1_1 e1_2 >>= fun e1 =>
        equiv_annotation_expression A A' e2_1 e2_2 >>= fun e2 =>
        Some (Binary e1 bop1 e2)
      else
        None
  | Assign e1_1 e2_1, Assign e1_2 e2_2 =>
      equiv_annotation_expression A A' e1_1 e1_2 >>= fun e1 =>
      equiv_annotation_expression A A' e2_1 e2_2 >>= fun e2 =>
      Some (Assign e1 e2)
  | CompoundAssign e1_1 aop1 e2_1, CompoundAssign e1_2 aop2 e2_2 =>
      if eq_arithmeticOperator aop1 aop2 then
        equiv_annotation_expression A A' e1_1 e1_2 >>= fun e1 =>
        equiv_annotation_expression A A' e2_1 e2_2 >>= fun e2 =>
        Some (CompoundAssign e1 aop1 e2)
      else
        None
  | Conditional e1_1 e2_1 e3_1, Conditional e1_2 e2_2 e3_2 =>
      equiv_annotation_expression A A' e1_1 e1_2 >>= fun e1 =>
      equiv_annotation_expression A A' e2_1 e2_2 >>= fun e2 =>
      equiv_annotation_expression A A' e3_1 e3_2 >>= fun e3 =>
      Some (Conditional e1 e2 e3)
  | Cast q1 t1 e1, Cast q2 t2 e2 =>
      if eq_qualifiers q1 q2 && eq_ctype t1 t2 then
        equiv_annotation_expression A A' e1 e2 >>= fun e =>
        Some (Cast q1 t1 e)
      else
        None
  | Call e1 es1, Call e2 es2 =>
      equiv_annotation_expression A A' e1  e2  >>= fun e  =>
      equiv_annotation_arguments  es1 es2 >>= fun es =>
      Some (Call e es)
  | Constant c1, Constant c2 =>
      if eq_constant c1 c2 then
        Some (Constant c1)
      else
        None
  | Var v1, Var v2 =>
      if eq_identifier v1 v2 then
        Some (Var v1)
      else
        None
  | SizeOf q1 t1, SizeOf q2 t2 =>
      if eq_qualifiers q1 q2 && eq_ctype t1 t2 then
        Some (SizeOf q1 t1)
      else
        None
  | AlignOf q1 t1, AlignOf q2 t2 =>
      if eq_qualifiers q1 q2 && eq_ctype t1 t2 then
        Some (AlignOf q1 t1)
      else
        None
  | _, _ => None
  end
with equiv_annotation_expression {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (e1 : expression A1) (e2 : expression A2) {struct e1} : option (expression A2') :=
  match e1, e2 with
  | AnnotatedExpression a1 e1, AnnotatedExpression a2 e2 =>
      equiv_annotation_expression' A A' e1 e2 >>= fun e =>
      Some (AnnotatedExpression (add_type A' (get_type A a2) a1) e)
  end.

Definition equiv_annotation_arguments {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (a1 : list (expression A1)) (a2 : list (expression A2)) : option (list (expression A2')) :=
  equiv_annotation_arguments_aux A A' (equiv_annotation_expression A A') a1 a2.


Definition equiv_annotation_definition {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (d1 : identifier * expression A1) (d2 : identifier * expression A2) : option (identifier * expression A2') :=
  let '(v1, e1) := d1 in
  let '(v2, e2) := d2 in
  if eq_identifier v1 v2 then
    equiv_annotation_expression A A' e1 e2 >>= fun e =>
    Some (v1, e)
  else
    None.

Fixpoint equiv_annotation_declaration {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (ds1 : list (identifier * expression A1)) (ds2 : list (identifier * expression A2)) : option (list (identifier * expression A2')) :=
  match ds1, ds2 with
  | nil      , nil       => Some nil
  | d1 :: ds1, d2 :: ds2 => equiv_annotation_definition  A A' d1  d2  >>= fun d  =>
                            equiv_annotation_declaration A A' ds1 ds2 >>= fun ds =>
                            Some (d :: ds)
  | _        , _         => None
  end.

Definition equiv_annotation_block_aux {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') equiv_annotation_statement :=
  fix equiv_annotation_block (ss1 : list (statement B A1)) (ss2 : list (statement B A2)) : option (list (statement B A2')) :=
    match ss1, ss2 with
    | nil      , nil       => Some nil
    | s1 :: ss1, s2 :: ss2 => equiv_annotation_statement s1  s2  >>= fun s  =>
                              equiv_annotation_block     ss1 ss2 >>= fun ss =>
                              Some (s :: ss)
    | _        , _         => None
    end.

Fixpoint equiv_annotation_statement' {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (s1 : statement' B A1) (s2 : statement' B A2) : option (statement' B A2') :=
  let equiv_annotation_block := equiv_annotation_block_aux A A' (equiv_annotation_statement A A') in
  match s1, s2 with
  | Skip, Skip => Some Skip
  | Expression e1, Expression e2 =>
      equiv_annotation_expression A A' e1 e2 >>= fun e =>
      Some (Expression e)
  | Block b1 ss1, Block b2 ss2 =>
      if eq_bindings b1 b2 then
        equiv_annotation_block ss1 ss2 >>= fun ss =>
        Some (Block b1 ss)
      else
        None
  | If e1 s1_1 s2_1, If e2 s1_2 s2_2 =>
      equiv_annotation_expression A A' e1   e2   >>= fun e  =>
      equiv_annotation_statement  A A' s1_1 s1_2 >>= fun s1 =>
      equiv_annotation_statement  A A' s2_1 s2_2 >>= fun s2 =>
      Some (If e s1 s2)
  | While e1 s1, While e2 s2 =>
      equiv_annotation_expression A A' e1 e2 >>= fun e =>
      equiv_annotation_statement  A A' s1 s2 >>= fun s =>
      Some (While e s)
  | Do s1 e1, Do s2 e2 =>
      equiv_annotation_statement  A A' s1 s2 >>= fun s =>
      equiv_annotation_expression A A' e1 e2 >>= fun e =>
      Some (Do s e)
  | Break, Break => Some Break
  | Continue, Continue => Some Continue
  | ReturnVoid, ReturnVoid => Some ReturnVoid
  | Return e1, Return e2 =>
      equiv_annotation_expression A A' e1 e2 >>= fun e =>
      Some (Return e)
  | Switch e1 s1, Switch e2 s2 =>
      equiv_annotation_expression A A' e1 e2 >>= fun e =>
      equiv_annotation_statement  A A' s1 s2 >>= fun s =>
      Some (Switch e s)
  | Case ic1 s1, Case ic2 s2 =>
      if eq_integerConstant ic1 ic2 then
        equiv_annotation_statement A A' s1 s2 >>= fun s =>
        Some (Case ic1 s)
      else
        None
  | Default s1, Default s2 =>
      equiv_annotation_statement A A' s1 s2 >>= fun s =>
      Some (Default s)
  | Label v1 s1, Label v2 s2 =>
      if eq_identifier v1 v2 then
        equiv_annotation_statement A A' s1 s2 >>= fun s =>
        Some (Label v1 s)
      else
        None
  | Goto v1, Goto v2 =>
      if eq_identifier v1 v2 then
        Some (Goto v1)
      else
        None
  | Declaration ds1, Declaration ds2 =>
      equiv_annotation_declaration A A' ds1 ds2 >>= fun ds =>
      Some (Declaration ds)
  | _, _ => None
  end
with equiv_annotation_statement {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (s1 : statement B A1) (s2 : statement B A2) : option (statement B A2') :=
  match s1, s2 with
  | AnnotatedStatement b s1, AnnotatedStatement _ s2 =>
      equiv_annotation_statement' A A' s1 s2 >>= fun s =>
      Some (AnnotatedStatement b s)
  end.

Definition equiv_annotation_block {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (ss1 : list (statement B A1)) (ss2 : list (statement B A2)) := equiv_annotation_block_aux A A' (equiv_annotation_statement A A') ss1 ss2.

Definition equiv_annotation_function {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (p1 : _ * _ * statement B A1) (p2 : _ * _ * statement B A2) : option (_ * _ * statement B A2') :=
  let '(t1, bs1, s1) := p1 in
  let '(t2, bs2, s2) := p2 in
  if eq_ctype t1 t2 && eq_bindings  bs1 bs2 then
    equiv_annotation_statement A A' s1 s2 >>= fun s =>
    Some (t1, bs1, s)
  else
    None.

Definition equiv_annotation_sigma_map {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (S1 : sigma B A1) v (p2 : _ * _ * statement B A2) :=
  AilSyntax.lookup S1 v >>= fun p1 => equiv_annotation_function A A' p1 p2.

Definition equiv_annotation_sigma {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (S1 : sigma B A1) (S2 : sigma B A2) : option (sigma B A2') :=
  if equiv_sigma S1 S2 then
    mapP eq_identifier (equiv_annotation_sigma_map A A' S1) S2
  else
    None.

Definition equiv_annotation_program {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (p1 : program B A1) (p2 : program B A2) :=
  let '(v1, S1) := p1 in
  let '(v2, S2) := p2 in
  if eq_identifier v1 v2 then
    equiv_annotation_sigma A A' S1 S2 >>= fun S =>
    Some (v1, S)
  else
    None.
