Require Import Bool.
Require Import List.
Require Import Arith.
Require Export ZArith.

Require Import Common.
Require Import AilTypes.
Require Import AilTypesAux AilTypesAux_fun AilTypesAux_proof.
Require Import AilSyntax.
Require Import AilSyntaxAux AilSyntaxAux_fun AilSyntaxAux_proof.
Require Import Implementation.
Require Import AilTyping.

Inductive sType : impl -> gamma -> sigma -> type -> statement -> Prop :=    (* defn sType *)
 | STypeLabel : forall (P:impl) (G:gamma) (S:sigma) t (id:identifier) (s:statement),
     sType P G S t s ->
     sType P G S t (Label id s)
 | STypeCase : forall (P:impl) (G:gamma) (S:sigma) t (ic:integerConstant) it (s:statement),
     cType P ic it ->
     sType P G S t s ->
     sType P G S t (Case ic s)
 | STypeDefault : forall (P:impl) (G:gamma) (S:sigma) t (s:statement),
     sType P G S t s ->
     sType P G S t (Default s)
 | STypeBlock : forall (P:impl) (G:gamma) (S:sigma) t (G':gamma) (b:block),
     Disjoint G' S ->
     bType P (G' ++ G) S t b ->
     sType P G S t (Block G' b)
 | STypeSkip : forall (P:impl) (G:gamma) (S:sigma) t,
     sType P G S t Skip
 | STypeExpression : forall (P:impl) (G:gamma) (S:sigma) t (e:expression),
     typeable P G S e ->
     sType P G S t (Expression e)
 | STypeIf : forall (P:impl) (G:gamma) (S:sigma) t (e:expression) (s1 s2:statement) (ty:type),
     expressionType P G S e ty ->
     isScalar ty ->
     sType P G S t s1 ->
     sType P G S t s2 ->
     sType P G S t (If e s1 s2)
 | STypeSwitch : forall (P:impl) (G:gamma) (S:sigma) t (e:expression) (s:statement) (ty:type),
     expressionType P G S e ty ->
     isInteger ty ->
     sType P G S t s ->
     sType P G S t (Switch e s)
 | STypeWhile : forall (P:impl) (G:gamma) (S:sigma) t (e:expression) (s:statement) (ty:type),
     expressionType P G S e ty ->
     isScalar ty ->
     sType P G S t s ->
     sType P G S t (While e s)
 | STypeDo : forall (P:impl) (G:gamma) (S:sigma) t (s:statement) (e:expression) (ty:type),
     expressionType P G S e ty ->
     isScalar ty ->
     sType P G S t s ->
     sType P G S t (Do s e)
 | STypeGoto : forall (P:impl) (G:gamma) (S:sigma) t (id:identifier),
     sType P G S t (Goto id)
 | STypeContinue : forall (P:impl) (G:gamma) (S:sigma) t,
     sType P G S t Continue
 | STypeBreak : forall (P:impl) (G:gamma) (S:sigma) t,
     sType P G S t Break
 | STypeReturnVoid : forall (P:impl) (G:gamma) (S:sigma),
     sType P G S Void ReturnVoid
 | STypeReturn : forall (P:impl) (G:gamma) (S:sigma) t (e:expression),
     isAssignable P G S t e ->
     sType P G S t (Return e)
 | STypeDeclaration : forall (P:impl) (G:gamma) (S:sigma) t (d:definitions),
     dType P G S d ->
     sType P G S t (Declaration d)
with dType : impl -> gamma -> sigma -> definitions -> Prop :=
 | DTypeNil  P G S        :
     dType P G S DefinitionNil
 | DTypeCons P G S :
     forall id e d qs ty,
     Lookup G id (qs, ty) ->
     isAssignable P G S ty e ->
     dType P G S (DefinitionCons id e d)
with bType : impl -> gamma -> sigma -> type -> block -> Prop :=
 | BTypeNil  P G S t : bType P G S t BlockNil
 | BTypeCons P G S t : 
     forall s b,
     sType P G S t s ->
     bType P G S t b ->
     bType P G S t (BlockCons s b).

Fixpoint isDisjoint_fun {B1 B2} (E1 : list (identifier * B1)) (E2 : list (identifier * B2)) : bool :=
  match E1 with
  | nil           => true
  | (id, _) :: E1 => match lookup_id E2 id with
                     | Some _ => false
                     | None   => isDisjoint_fun E1 E2
                     end
  end.

Fixpoint isDisjoint_fun_correct {B1 B2} (E1 : list (identifier * B1)) (E2 : list (identifier * B2)) {struct E1} :
  boolSpec (isDisjoint_fun E1 E2) (Disjoint E1 E2).
Proof.
  unfold_goal.
  destruct E1; simpl.
  - inversion 1.
  - do 2 context_destruct.
    match goal with
    | [|- lookup_id E2 ?id = _ -> _] => case_fun (lookup_id_correct E2 id)
    end.
    + intros Hfalse; eapply Hfalse; finish eassumption.
    + context_destruct; case_fun (isDisjoint_fun_correct _ _ E1 E2); unfold boolSpec in *.
      * inversion 1; subst; firstorder.
      * match goal with
        | [H : neg (Disjoint _ _)|- neg (Disjoint ((?id, _) :: _) E2)] =>
            intros Hfalse;
            eapply H;
            intros id' ? ? ?;
            destruct (decide id id' : Decision (_ = _)); [
                subst; firstorder
              | eapply Hfalse; finish eassumption
            ]
        end.
Qed.

Fixpoint sType_fun P G S t s {struct s} : bool :=
  match s with
  | Label _ s => sType_fun P G S t s
  | Case ic s => match cType_find P ic with
                 | Some _ => sType_fun P G S t s 
                 | None   => false
                 end
  | Default s => sType_fun P G S t s
  | Block G' b => isDisjoint_fun G' S && bType_fun P (G' ++ G) S t b
  | Skip      => true
  | Expression e => typeable_fun P G S e
  | If e s1 s2 => match expressionType_find P G S e with
                          | Some ty => isScalar_fun ty && sType_fun P G S t s1
                                                       && sType_fun P G S t s2
                          | None    => false
                          end
  | Switch e s => match expressionType_find P G S e with
                  | Some ty => isInteger_fun ty && sType_fun P G S t s
                  | None    => false
                  end
  | While e s => match expressionType_find P G S e with
                 | Some ty => isScalar_fun ty && sType_fun P G S t s
                 | None    => false
                 end
  | Do s e => match expressionType_find P G S e with
              | Some ty => isScalar_fun ty && sType_fun P G S t s
              | None    => false
              end
  | Goto _    => true
  | Continue  => true
  | Break     => true
  | ReturnVoid => bool_of_decision (type_DecEq t Void)
  | Return e   => isAssignable_fun P G S t e
  | Declaration d => dType_fun P G S d
  end
with bType_fun P G S t b {struct b} : bool :=
  match b with
  | BlockNil      => true
  | BlockCons s b => sType_fun P G S t s && bType_fun P G S t b
  end
with dType_fun P G S d {struct d} : bool :=
  match d with
  | DefinitionNil => true
  | DefinitionCons id e d => match lookup_id G id with
                             | Some (_, ty1) => isAssignable_fun P G S ty1 e
                             | _             => false
                             end
  end.

Ltac case_fun G :=
  match goal with
  | [|- _ = ?o -> _] =>
      is_var o;
      let Heq := fresh in
      let H := fresh in
      destruct o;
      intros Heq;
      generalize G;
      rewrite Heq;
      intros H;
      simpl in H
  end.

Lemma Disjoint_cons_left_Lookup {A B C} {a} {b} {E1 : list (A * B)} {E : list (A * C)} :
  Disjoint ((a,b) :: E1) E -> forall c, neg (Lookup E a c).
Proof.
  intros Hdisjoint.
  assert (Lookup ((a,b) :: E1) a b) as Hlookup by constructor.
  exact (fun c => Hdisjoint a b c Hlookup).
Qed.

Lemma Disjoint_cons_left_Lookup_inv {A B C} {a} {b} {E1 : list (A * B)} {E : list (A * C)} :
  Disjoint E1 E -> (forall c, neg (Lookup E a c)) -> Disjoint ((a,b) :: E1) E.
Proof.
  intros Hdisjoint Hnlookup.
  intros a' b' c'.
  inversion 1; subst.
  - apply Hnlookup.
  - eapply Hdisjoint.
    eassumption.
Qed.

Lemma Disjoint_cons_left {A B C} p {E1 E2 : list (A * B)} {E : list (A * C)} :
  Disjoint (p :: E1) E -> Disjoint E2 E -> Disjoint (p :: E2) E.
Proof.
  intros; destruct p.
  eapply Disjoint_cons_left_Lookup_inv.
  - assumption.
  - eapply Disjoint_cons_left_Lookup; eassumption.
Qed.

Lemma Disjoint_weaken {A B C} {eq_dec : DecidableEq A} {p} {E1 : list (A * B)} {E : list (A * C)}:
  Disjoint (p :: E1) E ->
  Disjoint E1 E.
Proof.
  destruct p.
  intros Hdisjoint a' b' c' Hlookup.
  destruct (decide a a' : Decision (a = a')).
  + subst.
    eapply (Hdisjoint a').
    constructor 1.
  + eapply (Hdisjoint a').
    constructor 2; eassumption.
Qed.

Lemma Disjoint_app {A B C} {eq_dec : DecidableEq A} {E1 E2 : list (A * B)} {E : list (A * C)}:
  Disjoint E1 E ->
  Disjoint E2 E ->
  Disjoint (E1++E2) E.
Proof.
  induction E1.
  - intros; assumption.
  - intros H1 H2.
    assert (Disjoint E1 E) as H
      by (eapply Disjoint_weaken; eassumption).
    eapply Disjoint_cons_left.
    + eassumption.
    + exact (IHE1 H H2).
Qed.

Fixpoint sType_fun_correct P G S t s {struct s} :
  Disjoint G S ->
  boolSpec (sType_fun P G S t s) (sType P G S t s)
with dType_fun_correct P G S d {struct d} :
  Disjoint G S ->
  boolSpec (dType_fun P G S d) (dType P G S d)
with bType_fun_correct P G S t b {struct b} :
  Disjoint G S ->
  boolSpec (bType_fun P G S t b) (bType P G S t b).
Proof.
- intros Hdisjoint.
  destruct s; simpl;
  unfold boolSpec; unfold andb;
  repeat match goal with
  | [|- typeable_fun P G S ?e = _ -> _] => case_fun (typeable_fun_correct P G S e Hdisjoint)
  | [|- expressionType_find P G S ?e = _ -> _] => case_fun (expressionType_find_correct P G S e Hdisjoint)
  | [|- isAssignable_fun P G S ?t1 ?e2 = _ -> _] => case_fun (isAssignable_fun_correct P G S t1 e2 Hdisjoint)
  | [|- sType_fun P G S ?t ?s = _ -> _] => case_fun (sType_fun_correct P G S t s Hdisjoint)
  | [|- dType_fun P G S ?d = _ -> _] => case_fun (dType_fun_correct P G S d Hdisjoint)
  | [H1 : Disjoint ?G' S, H2 : Disjoint ?G S |- bType_fun P (?G' ++ ?G) S ?t ?b = _ -> _ ] =>
      case_fun (bType_fun_correct P _ S t b (Disjoint_app H1 H2))
  | [|- cType_find P ?ic = _ -> _] => case_fun (cType_find_correct P ic); match goal with [H: _ * _|- _] => destruct H |_ => idtac end
  | [|- isScalar_fun ?t = _ -> _] => case_fun (isScalar_fun_correct t)
  | [|- isInteger_fun ?t = _ -> _] => case_fun (isInteger_fun_correct t)
  | [|- isDisjoint_fun ?E1 ?E2 = _ -> _] => case_fun (isDisjoint_fun_correct E1 E2)
  | [|- bool_of_decision ?d = _ -> _] => case_fun (Decision_boolSpec d); try subst
  | [Hfalse : forall _, neg (expressionType P G S ?e _), H : expressionType P G S ?e _ |- _] => destruct (Hfalse _ H)
  | [Hfalse : forall _, neg (cType P ?ic _), H : cType P ?ic _ |- _] => destruct (Hfalse _ H)
  | [H1 : expressionType P G S ?e ?t1, H2 : expressionType P G S ?e ?t2 |- _] => notSame t1 t2; set (expressionType_unique Hdisjoint H1 H2); try congruence
  | [|- neg _] => inversion 1; subst; try congruence
  | [|- sType _ _ _ _ _] => econstructor (eassumption)
  | _ => context_destruct
  end.
- intros Hdisjoint.
  do 2 unfold_goal.
  destruct d.
  + constructor.
  + repeat match goal with
    | [|- lookup_id G id = _ -> _] => case_fun (lookup_id_correct G id)
    | [|- isAssignable_fun P G S ?t ?e = _ -> _] => case_fun (isAssignable_fun_correct P G S t e Hdisjoint)
    | [Hfalse : forall _, neg (Lookup G ?id _), H : Lookup G ?id _ |- _] => destruct (Hfalse _ H)
    | _ => context_destruct
    | [H1 : Lookup G ?id ?t1, H2 : Lookup G ?id ?t2 |- False] => notSame t1 t2; set (Lookup_unique _ _ _ _ H1 H2); congruence
    | [|- dType P G S _] => econstructor (eassumption)
    | [|- neg _] => inversion 1; subst
    end.
- intros Hdisjoint.
  destruct b; simpl;
  unfold boolSpec; unfold andb.
  + constructor.
  + repeat match goal with
    | [|- sType_fun P G S ?t ?s = _ -> _] => case_fun (sType_fun_correct P G S t s Hdisjoint)
    | [|- bType_fun P G S ?t ?b = _ -> _ ] => case_fun (bType_fun_correct P G S t b Hdisjoint)
    | _ => context_destruct
    | [|- bType P G S _ _] => econstructor (eassumption)
    | [|- neg _] => inversion 1; congruence
    end.
Qed.
