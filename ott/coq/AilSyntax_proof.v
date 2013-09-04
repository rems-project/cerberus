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

Lemma equiv_expression_correct {A1 A2} :
  forall (x : expression A1) (y : expression A2), boolSpec (equiv_expression x y) (equivExpression x y).
Proof.
  apply (
    expression_nrect
      (fun x => forall y : expression' A2      , boolSpec (equiv_expression' x y) (equivExpression' x y))
      (fun x => forall y : expression  A2      , boolSpec (equiv_expression  x y) (equivExpression  x y))
      (fun x => forall y : list (expression A2), boolSpec (equiv_arguments   x y) (equivArguments   x y)));
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

Lemma eq_definition_correct {A : Set} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall x y, boolSpec (eq_definition eq_A x y) (x = y).
Proof.
  intros eq_A_correct.
  apply (eq_pair_correct eq_identifier_correct (eq_expression_correct eq_A_correct)).
Qed.

Lemma eq_declaration_correct {A : Set} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall x y, boolSpec (eq_declaration eq_A x y) (x = y).
Proof.
  intros eq_A_correct.
  apply (eq_list_correct (eq_definition_correct eq_A_correct)).
Qed.

Lemma equiv_definition_correct {A1 A2 : Set} (x : identifier * expression A1) (y : identifier * expression A2) :
  boolSpec (equiv_definition x y) (equivDefinition x y).
Proof.
  unfold_goal.
  destruct x, y; simpl; unfold andb.
  repeat match goal with
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | |- equiv_expression ?x ?y = _ -> _ => case_fun (equiv_expression_correct x y)
  | _ => context_destruct
  end; now my_auto.
Qed.

Fixpoint equiv_declaration_correct {A1 A2 : Set} (x : list (identifier * expression A1)) (y : list (identifier * expression A2)) :
    boolSpec (equiv_declaration x y) (equivDeclaration x y).
Proof.
  unfold_goal.
  destruct x, y; simpl; unfold andb;
  repeat match goal with
  | |- equiv_definition ?x ?y = _ -> _ => case_fun (equiv_definition_correct x y)
  | |- equiv_declaration ?x ?y = _ -> _ => case_fun (equiv_declaration_correct A1 A2 x y)
  | _ => context_destruct
  end; now my_auto.
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

Lemma equiv_statement_correct {A1 A2 B1 B2} :
  forall (x : statement A1 B1) (y : statement A2 B2), boolSpec (equiv_statement x y) (equivStatement x y).
Proof.
  apply (
    statement_nrect
      (fun x => forall y : statement' A2 B2      , boolSpec (equiv_statement' x y) (equivStatement' x y))
      (fun x => forall y : statement  A2 B2      , boolSpec (equiv_statement  x y) (equivStatement  x y))
      (fun x => forall y : list (statement A2 B2), boolSpec (equiv_block      x y) (equivBlock      x y)));
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

Lemma equiv_sigma_correct {A1 A2 B1 B2 : Set} :
  forall (x : sigma A1 B1) (y : sigma A2 B2), boolSpec (equiv_sigma x y) (equivSigma x y).
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
  apply (
    equiv_correct
      eq_identifier_correct
      (fun _ => (
        eq_pair_correct
          (eq_pair_correct eq_ctype_correct eq_bindings_correct)
          (eq_statement_correct eq_A_correct eq_B_correct)
         )
      )
  ).
Qed.

Lemma equiv_program_correct {A1 A2 B1 B2 : Set} :
  forall (x : program A1 B1) (y : program A2 B2), boolSpec (equiv_program x y) (equivProgram x y).
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

Lemma eq_gamma_correct x y :
  boolSpec (eq_gamma x y) (x = y).
Proof.
  apply (eq_context_correct eq_identifier_correct (eq_pair_correct eq_qualifiers_correct eq_ctype_correct)).
Qed.

Lemma equiv_gamma_correct x y :
  boolSpec (equiv_gamma x y) (Context_defns.equiv (fun _ => eq) x y).
Proof.
  apply (equiv_correct eq_identifier_correct (fun _ => (eq_pair_correct eq_qualifiers_correct eq_ctype_correct))).
Qed.

Lemma lookup_correct {B} (C : Context.context identifier B) v :
  optionSpec (lookup C v) (Context_defns.lookup C v).
Proof. apply (lookup_correct eq_identifier_correct). Qed.

Definition lookup_unique {B} {C : Context.context identifier B} {v} :
  optionUnique (lookup C v) (Context_defns.lookup C v).
Proof. apply (lookup_unique eq_identifier_correct). Qed.

Definition lookup_functional {B} {C : Context.context identifier B} {v}:
  forall {p1 p2},
    Context_defns.lookup C v p1 ->
    Context_defns.lookup C v p2 ->
    p1 = p2.
Proof.
  intros ? ? H1 H2.
  set (lookup_unique _ H1).
  set (lookup_unique _ H2).
  congruence.
Qed.

Lemma mem_correct {B} (C : Context.context identifier B) v :
  boolSpec (mem v C) (Context_defns.mem v C).
Proof.
  exact (mem_correct eq_identifier_correct v C).
Qed.

Lemma fresh_correct {B} (C : Context.context identifier B) v :
  boolSpec (fresh v C) (Context_defns.fresh v C).
Proof.
  exact (fresh_correct eq_identifier_correct v C).
Qed.

Lemma fresh_bindings_correct {B} (C : Context.context identifier B) bs :
  boolSpec (fresh_bindings bs C) (Context_defns.freshBindings bs C).
Proof.
  exact (fresh_bindings_correct eq_identifier_correct bs C).
Qed.

Lemma disjoint_correct {B1 B2 : Set} (C1 : Context.context identifier B1) (C2 : Context.context identifier B1) :
  boolSpec (disjoint C1 C2) (Context_defns.disjoint C1 C2).
Proof.
  exact (disjoint_correct eq_identifier_correct C1 C2).
Qed.

Lemma equivExpression_refl {A} :
  forall (e : expression A), equivExpression e e.
Proof.
  apply (
    expression_nrect
      (fun e => equivExpression' e e)
      (fun e => equivExpression e e)
      (fun es => equivArguments es es)
  ); intros; constructor; assumption.
Qed.

Lemma equivExpression'_refl {A} :
  forall (e : expression' A), equivExpression' e e.
Proof.
  destruct e; constructor; 
  solve [
    apply equivExpression_refl
  | induction es;
    constructor;
    [apply equivExpression_refl | assumption]
  ].
Qed.

Lemma equivExpression_symm {A B} :
  forall {e1 : expression A} {e2 : expression B},
    equivExpression e1 e2 ->
    equivExpression e2 e1.
Proof.
  apply (
    expression_nrect
      (fun x => forall (y : expression' B) (Hequiv : equivExpression' x y), equivExpression' y x)
      (fun x => forall y (Hequiv : equivExpression x y), equivExpression y x)
      (fun x => forall (y : list (expression B)) (Hequiv : equivArguments x y), equivArguments y x)
  ); intros; inversion Hequiv; subst; constructor;
  match goal with
  | IH : forall _, _ -> ?C _ ?e1 |- ?C _ ?e1 => apply IH; assumption
  end.
Qed.

Lemma equivExpression_trans {A B C} :
  forall {e1 : expression A} {e2 : expression B} {e3 : expression C},
    equivExpression e1 e2 ->
    equivExpression e2 e3 ->
    equivExpression e1 e3.
Proof.
  apply (
    expression_nrect
      (fun x => forall (y : expression' B) (z : expression' C) (Hequiv1 : equivExpression' x y) (Hequiv2 : equivExpression' y z), equivExpression' x z)
      (fun x => forall y z (Hequiv1 : equivExpression x y) (Hequiv2 : equivExpression y z), equivExpression x z)
      (fun x => forall (y : list (expression B)) (z : list (expression C)) (Hequiv1 : equivArguments x y) (Hequiv2 : equivArguments y z), equivArguments x z)
  ); intros; inversion Hequiv1; subst; inversion Hequiv2; subst; constructor;
  match goal with
  | IH : forall _ _, _ -> _ -> ?C ?e1 _ |- ?C ?e1 _ => eapply IH; eassumption
  end.
Qed.

Lemma equivDefinition_refl {A} (d : identifier * expression A) :
  equivDefinition d d.
Proof. destruct d as [? ?]; constructor; solve [assumption | apply equivExpression_refl]. Qed.

Lemma equivDefinition_symm {A B} {d1 : identifier * expression A} {d2 : identifier * expression B} :
  equivDefinition d1 d2 ->
  equivDefinition d2 d1.
Proof. inversion_clear 1; constructor; apply equivExpression_symm; assumption. Qed.

Lemma equivDeclaration_refl {A} (ds : list (identifier * expression A)) :
  equivDeclaration ds ds.
Proof. induction ds; constructor; solve [assumption | apply equivDefinition_refl]. Qed.

Lemma equivDeclaration_symm {A B} {ds1 : list (identifier * expression A)} {ds2 : list (identifier * expression B)} :
  equivDeclaration ds1 ds2 ->
  equivDeclaration ds2 ds1.
Proof. revert ds2; induction ds1; inversion_clear 1; constructor; [apply equivDefinition_symm| apply IHds1]; assumption. Qed.
  
Lemma equivStatement_refl {A B} (s : statement A B) :
  equivStatement s s.
Proof.
  apply (
    statement_nrect
      (fun s => equivStatement' s s)
      (fun s => equivStatement s s)
      (fun ss => equivBlock ss ss)
  ); intros; constructor; solve [assumption|apply equivExpression_refl|apply equivDeclaration_refl].
Qed.

Lemma equivStatement_symm {A1 A2 B1 B2} {s1 : statement A1 A2} {s2 : statement B1 B2} :
  equivStatement s1 s2 ->
  equivStatement s2 s1.
Proof.
  apply (
    statement_nrect
      (fun x => forall (y : statement' B1 B2) (Hequiv : equivStatement' x y), equivStatement' y x)
      (fun x => forall y (Hequiv : equivStatement  x y), equivStatement  y x)
      (fun x => forall (y : list (statement B1 B2)) (Hequiv : equivBlock      x y), equivBlock      y x)
  ); intros; inversion_clear Hequiv; constructor; repeat first [assumption |apply equivExpression_symm|apply equivDeclaration_symm]; now firstorder.
Qed.

Lemma equivFunction_symm {A1 A2 B1 B2} {p1 : _ * _ * statement A1 A2} {p2 : _ * _ * statement B1 B2} :
  equivFunction p1 p2 ->
  equivFunction p2 p1.
Proof. inversion_clear 1; constructor; [congruence | apply equivStatement_symm; assumption]. Qed.

Lemma equivSigma_refl {A B} (S : sigma A B) :
  equivSigma S S.
Proof.
  split;
  intros v b Hlookup;
  exists b;
  repeat first [split | assumption | reflexivity | apply equivStatement_refl].
Qed.

Lemma equivSigma_symm {A1 A2 B1 B2} {S1 : sigma A1 A2} {S2 : sigma B1 B2} :
  equivSigma S1 S2 ->
  equivSigma S2 S1.
Proof.
  intros Hequiv.
  split;
  intros v p Hlookup;
  [apply proj2 in Hequiv | apply proj1 in Hequiv];
  pose proof (Hequiv v p Hlookup) as [p' [Hlookup' Hequiv']];
  exists p'; (split; [| apply equivFunction_symm]; assumption).
Qed.
