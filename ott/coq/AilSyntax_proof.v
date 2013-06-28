Require Import Common.
Require Import AilTypes AilTypes_proof.
Require Import AilSyntax AilSyntax_defns.
Require Import Context_proof.

Lemma eq_identifier_correct x y :
  boolSpec (eq_identifier x y) (x = y).
Proof. apply eq_nat_correct. Qed.

Lemma eq_integerSuffix_correct x y :
  boolSpec (eq_integerSuffix x y) (x = y).
Proof. destruct x, y; my_auto. Qed.

Lemma eq_integerConstant_correct :
  forall x y, boolSpec (eq_integerConstant x y) (x = y).
Proof.
 exact (eq_pair_correct eq_nat_correct (eq_option_correct eq_integerSuffix_correct)).
Qed.

Lemma eq_arithmeticOperator_correct :
  forall x y, boolSpec (eq_arithmeticOperator x y) (x = y).
Proof. destruct x, y; my_auto. Qed.

Lemma eq_constant_correct :
  forall x y, boolSpec (eq_constant x y) (x = y).
Proof.
  do 2 unfold_goal.
  destruct x as [ic1], y as [ic2].
  set (eq_integerConstant_correct ic1 ic2).
  boolSpec_destruct; my_auto.
Qed.

Lemma eq_unaryOperator_correct :
  forall x y, boolSpec (eq_unaryOperator x y) (x = y).
Proof. destruct x, y; my_auto. Qed.


Lemma eq_binaryOperator_correct :
  forall x y, boolSpec (eq_binaryOperator x y) (x = y).
Proof.
  do 2 unfold_goal.
  destruct x as [a1| | | | | | | | | ],
           y as [a2| | | | | | | | | ];
  [set (eq_arithmeticOperator_correct a1 a2); boolSpec_destruct |..];
  my_auto.
Qed.

Definition expression_nrect
         {A}
         (P : expression' A -> Type)
         (Q : expression  A  -> Type)
         (R : list (expression A) -> Type)

         (HUnary : forall {uop} {e}, Q e -> P (Unary uop e))
         (HBinary : forall {e1} {bop} {e2}, Q e1 -> Q e2 -> P (Binary e1 bop e2))
         (HAssign : forall {e1 e2}, Q e1 -> Q e2 -> P (Assign e1 e2))
         (HCompoundAssign : forall {e1} {aop} {e2}, Q e1 -> Q e2 -> P (CompoundAssign e1 aop e2))
         (HConditional : forall {e1 e2 e3}, Q e1 -> Q e2 -> Q e3 -> P (Conditional e1 e2 e3))
         (HCast : forall {q} {t} {e}, Q e -> P (Cast q t e))
         (HCall : forall {e} {es}, Q e -> R es -> P (Call e es))
         (HConstant : forall {c}, P (Constant c))
         (HVar : forall {v}, P (Var v))
         (HSizeOf : forall {q} {t}, P (SizeOf q t))
         (HAlignOf : forall {q} {t}, P (AlignOf q t))
         (Hnil : R nil)
         (Hcons : forall {e} {a}, Q e -> R a -> R (cons e a))
         (HAnnotatedExpression : forall {a} {e}, P e -> Q (AnnotatedExpression a e)) :
  forall e : @expression A, Q e
:=
  fix f e : P e :=
    match e return P e with
    | Unary _ _ => HUnary (g _)
    | Binary _ _ _ => HBinary (g _) (g _)
    | Assign _ _ => HAssign (g _) (g _)
    | CompoundAssign _ _ _ => HCompoundAssign (g _) (g _)
    | Conditional _ _ _ => HConditional (g _) (g _) (g _)
    | Cast _ _ _ => HCast (g _)
    | Call _ _ =>
        let fix h a : R a :=
          match a return R a with
          | nil       => Hnil
          | cons e a => Hcons (g e) (h a)
          end in
        HCall (g _) (h _)
    | Constant _ => HConstant
    | Var _ => HVar
    | SizeOf _ _ => HSizeOf
    | AlignOf _ _ => HAlignOf
    end
with g e : Q e :=
  match e return Q e with
  | AnnotatedExpression _ _ => HAnnotatedExpression (f _)
  end
for g.


Lemma eq_expression_correct {A : Set} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall (x y : expression A), boolSpec (eq_expression eq_A x y) (x = y).
Proof.
  intros eq_A_correct.
  apply (expression_nrect (fun x => forall y, boolSpec (eq_expression' eq_A x y) (x = y))
                          (fun x => forall y, boolSpec (eq_expression  eq_A x y) (x = y))
                          (fun x => forall y, boolSpec (eq_arguments   eq_A x y) (x = y)));
  intros; destruct y;
  unfold_goal; simpl;
  match goal with
  | |- context[eq_arguments_aux _ _ ?es1 ?es2] => fold (eq_arguments eq_A es1 es2)
  | _ => idtac
  end; unfold andb;
  repeat match goal with
  | |- eq_unaryOperator ?x ?y = _ -> _ => case_fun (eq_unaryOperator_correct x y)
  | |- eq_binaryOperator ?x ?y = _ -> _ => case_fun (eq_binaryOperator_correct x y)
  | |- eq_arithmeticOperator ?x ?y = _ -> _ => case_fun (eq_arithmeticOperator_correct x y)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | |- eq_qualifiers ?x ?y = _ -> _ => case_fun (eq_qualifiers_correct x y)
  | |- eq_constant ?x ?y = _ -> _ => case_fun (eq_constant_correct x y)
  | |- eq_A ?x ?y = _ -> _ => case_fun (eq_A_correct x y)
  | IH : forall _, boolSpec (eq_expression _ ?x _) _|- eq_expression _ ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, boolSpec (eq_expression' _ ?x _) _|- eq_expression' _ ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, boolSpec (eq_arguments _ ?x _) _|- eq_arguments _ ?x ?y = _ -> _ => case_fun (IH y)
  | _ => context_destruct
  end; now my_auto.
Qed.

Lemma equiv_expression_correct {A} :
  forall (x y : expression A), boolSpec (equiv_expression x y) (equivExpression x y).
Proof.
  apply (expression_nrect (fun x => forall y, boolSpec (equiv_expression' x y) (equivExpression' x y))
                          (fun x => forall y, boolSpec (equiv_expression  x y) (equivExpression  x y))
                          (fun x => forall y, boolSpec (equiv_arguments   x y) (equivArguments   x y)));
  intros; destruct y;
  unfold_goal; simpl;
  match goal with
  | |- context[equiv_arguments_aux _ ?es1 ?es2] => fold (equiv_arguments es1 es2)
  | _ => idtac
  end; unfold andb;
  repeat match goal with
  | |- eq_unaryOperator ?x ?y = _ -> _ => case_fun (eq_unaryOperator_correct x y)
  | |- eq_binaryOperator ?x ?y = _ -> _ => case_fun (eq_binaryOperator_correct x y)
  | |- eq_arithmeticOperator ?x ?y = _ -> _ => case_fun (eq_arithmeticOperator_correct x y)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | |- eq_qualifiers ?x ?y = _ -> _ => case_fun (eq_qualifiers_correct x y)
  | |- eq_constant ?x ?y = _ -> _ => case_fun (eq_constant_correct x y)
  | IH : forall _, boolSpec (equiv_expression ?x _) _|- equiv_expression ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, boolSpec (equiv_expression' ?x _) _|- equiv_expression' ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, boolSpec (equiv_arguments ?x _) _|- equiv_arguments ?x ?y = _ -> _ => case_fun (IH y)
  | _ => context_destruct
  end; now my_auto.
Qed.

Lemma eq_bindings_correct x y :
  boolSpec (eq_bindings x y) (x = y).
Proof.
  apply (eq_list_correct
           (eq_pair_correct eq_identifier_correct
                            (eq_pair_correct
                               eq_qualifiers_correct
                               eq_ctype_correct))
        ).
Qed.

Lemma eq_declaration_correct {A : Set} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall x y, boolSpec (eq_declaration eq_A x y) (x = y).
Proof.
  intros eq_A_correct.
  apply (eq_list_correct (eq_pair_correct eq_identifier_correct (eq_expression_correct eq_A_correct))).
Qed.

Fixpoint equiv_declaration_correct {A : Set} (x y : list (identifier * expression A)) :
    boolSpec (equiv_declaration x y) (equivDeclaration x y).
Proof.
  unfold_goal.
  destruct x, y; simpl; unfold andb; intuition;
  repeat match goal with
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | |- equiv_expression ?x ?y = _ -> _ => case_fun (equiv_expression_correct x y)
  | |- equiv_declaration ?x ?y = _ -> _ => case_fun (equiv_declaration_correct A x y)
  | _ => context_destruct
  end; my_auto.
Qed.

Definition statement_nrect
           {A B}
           (P : statement' A B -> Type)
           (Q : statement A B  -> Type)
           (R : list (statement A B) -> Type)

           (HSkip : P Skip)
           (HExpression : forall {e}, P (Expression e))
           (HBlock : forall {b} {ss}, R ss -> P (Block b ss))
           (HIf : forall {e} {s1 s2}, Q s1 -> Q s2 -> P (If e s1 s2))
           (HWhile : forall {e} {s}, Q s -> P (While e s))
           (HDo : forall {s} {e}, Q s -> P (Do s e))
           (HBreak : P Break)
           (HContinue : P Continue)
           (HReturnVoid : P ReturnVoid)
           (HReturn : forall {e}, P (Return e))
           (HSwitch : forall {e} {s}, Q s -> P (Switch e s))
           (HCase : forall {ic} {s}, Q s -> P (Case ic s))
           (HDefault : forall {s}, Q s -> P (Default s))
           (HLabel : forall {v} {s}, Q s -> P (Label v s))
           (HGoto : forall {v}, P (Goto v))
           (HDeclaration : forall {d}, P (Declaration d))
           (Hnil : R nil)
           (Hcons : forall {s} {ss}, Q s -> R ss -> R (s :: ss))
           (HAnnotatedStatement : forall {a} {s}, P s -> Q (AnnotatedStatement a s)) :
  forall s : statement A B, Q s
:=
  fix f s : P s :=
    match s return P s with
    | Skip => HSkip
    | Expression _ => HExpression
    | Block _ _ =>
        let fix h ss : R ss :=
          match ss return R ss with
          | nil     => Hnil
          | s :: ss => Hcons (g s) (h ss)
          end in
        HBlock (h _)
    | If _ _ _ => HIf (g _) (g _)
    | While _ _ => HWhile (g _)
    | Do _ _ => HDo (g _)
    | Break => HBreak
    | Continue => HContinue
    | ReturnVoid => HReturnVoid
    | Return _ => HReturn
    | Switch _ _ => HSwitch (g _)
    | Case _ _ => HCase (g _)
    | Default _ => HDefault (g _)
    | Label _ _ => HLabel (g _)
    | Goto _ => HGoto
    | Declaration _ => HDeclaration
    end
with g s : Q s :=
  match s return Q s with
  | AnnotatedStatement _ _ => HAnnotatedStatement (f _)
  end
for g.

Lemma equiv_statement_correct {A B} :
  forall (x y : statement A B), boolSpec (equiv_statement x y) (equivStatement x y).
Proof.
  apply (statement_nrect (fun x => forall y, boolSpec (equiv_statement' x y) (equivStatement' x y))
                         (fun x => forall y, boolSpec (equiv_statement  x y) (equivStatement  x y))
                         (fun x => forall y, boolSpec (equiv_block      x y) (equivBlock      x y)));
  intros;
  unfold_goal; destruct y; simpl; unfold andb;
  repeat match goal with
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | |- eq_qualifiers ?x ?y = _ -> _ => case_fun (eq_qualifiers_correct x y)
  | |- eq_bindings ?x ?y = _ -> _ => case_fun (eq_bindings_correct x y)
  | |- eq_integerConstant ?x ?y = _ -> _ => case_fun (eq_integerConstant_correct x y)
  | |- equiv_declaration ?x ?y = _ -> _ => case_fun (equiv_declaration_correct x y)
  | |- equiv_expression ?x ?y = _ -> _ => case_fun (equiv_expression_correct x y)
  | IH : forall _, boolSpec (equiv_statement ?x _) _|- equiv_statement ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, boolSpec (equiv_statement' ?x _) _|- equiv_statement' ?x ?y = _ -> _ => case_fun (IH y)
  | |- equiv_block_aux _ ?x ?y = _ -> _ => fold (equiv_block x y)
  | IH : forall _, boolSpec (equiv_block ?x _) _|- equiv_block ?x ?y = _ -> _ => case_fun (IH y)
  | _ => context_destruct
  end; now my_auto.
Qed.

Lemma eq_statement_correct {A B : Set} {eq_A} {eq_B} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  (forall x y : B, boolSpec (eq_B x y) (x = y)) ->
  forall (x y : statement A B), boolSpec (eq_statement eq_A eq_B x y) (x = y).
Proof.
  intros eq_A_correct eq_B_correct.
  apply (statement_nrect (fun x => forall y, boolSpec (eq_statement' eq_A eq_B x y) (x = y))
                         (fun x => forall y, boolSpec (eq_statement  eq_A eq_B x y) (x = y))
                         (fun x => forall y, boolSpec (eq_block      eq_A eq_B x y) (x = y)));
  intros;
  unfold_goal; destruct y; simpl; unfold andb;
  repeat match goal with
  | |- eq_A ?x ?y = _ -> _ => case_fun (eq_A_correct x y)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | |- eq_qualifiers ?x ?y = _ -> _ => case_fun (eq_qualifiers_correct x y)
  | |- eq_bindings ?x ?y = _ -> _ => case_fun (eq_bindings_correct x y)
  | |- eq_integerConstant ?x ?y = _ -> _ => case_fun (eq_integerConstant_correct x y)
  | |- eq_declaration eq_B ?x ?y = _ -> _ => case_fun (eq_declaration_correct eq_B_correct x y)
  | |- eq_expression _ ?x ?y = _ -> _ => case_fun (eq_expression_correct eq_B_correct x y)
  | IH : forall _, boolSpec (eq_statement _ _ ?x _) _|- eq_statement _ _ ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, boolSpec (eq_statement' _ _ ?x _) _|- eq_statement' _ _ ?x ?y = _ -> _ => case_fun (IH y)
  | |- eq_block_aux _ _ _ ?x ?y = _ -> _ => fold (eq_block eq_A eq_B x y)
  | IH : forall _, boolSpec (eq_block _ _ ?x _) _|- eq_block _ _ ?x ?y = _ -> _ => case_fun (IH y)
  | _ => context_destruct
  end; now my_auto.
Qed.


Lemma eq_sigma_correct {A B : Set} {eq_A} {eq_B} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  (forall x y : B, boolSpec (eq_B x y) (x = y)) ->
  forall (x y : sigma A B), boolSpec (eq_sigma eq_A eq_B x y) (x = y).
Proof.
  intros eq_A_correct eq_B_correct.
  apply (eq_context_correct eq_identifier_correct
                            (eq_pair_correct
                               (eq_pair_correct eq_ctype_correct eq_bindings_correct)
                               (eq_statement_correct eq_A_correct eq_B_correct))).
Qed.

Lemma equiv_sigma_correct {A B : Set} :
  forall (x y : sigma A B), boolSpec (equiv_sigma x y) (equivSigma x y).
Proof.
  apply (equiv_correct eq_identifier_correct).
  destruct x as [x1 x2], y as [y1 y2]; simpl.
  set (eq_pair_correct eq_ctype_correct eq_bindings_correct x1 y1).
  set (equiv_statement_correct x2 y2).
  repeat boolSpec_destruct; my_auto.
Qed.

Lemma equiv_eq_sigma_correct {A B : Set} {eq_A} {eq_B} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  (forall x y : B, boolSpec (eq_B x y) (x = y)) ->
  forall (x y : sigma A B), boolSpec (equiv_eq_sigma eq_A eq_B x y) (equivEqSigma x y).
Proof.
  intros eq_A_correct eq_B_correct.
  apply (equiv_correct eq_identifier_correct
                       (eq_pair_correct
                          (eq_pair_correct eq_ctype_correct eq_bindings_correct)
                          (eq_statement_correct eq_A_correct eq_B_correct))).
Qed.

Lemma equiv_program_correct {A B : Set} :
  forall x y : program A B, boolSpec (equiv_program x y) (equivProgram x y).
Proof.
  intros [x1 x2] [y1 y2]; simpl.
  set (eq_identifier_correct x1 y1).
  set (equiv_sigma_correct x2 y2).
  repeat boolSpec_destruct; my_auto.
Qed.

Lemma equiv_eq_program_correct {A B : Set} {eq_A} {eq_B} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  (forall x y : B, boolSpec (eq_B x y) (x = y)) ->
  forall x y : program A B, boolSpec (equiv_eq_program eq_A eq_B x y) (equivEqProgram x y).
Proof.
  intros eq_A_correct eq_B_correct [x1 x2] [y1 y2]; simpl.
  set (eq_identifier_correct x1 y1).
  set (equiv_eq_sigma_correct eq_A_correct eq_B_correct x2 y2).
  repeat boolSpec_destruct; my_auto.
Qed.
