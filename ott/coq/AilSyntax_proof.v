Require Import Common.
Require Import AilTypes AilTypes_proof.
Require Import AilSyntax AilSyntax_defns.

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
