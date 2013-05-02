Require Import Bool List.

Require Import Common.

Definition add {A B} (E : list (A * B)) a b :=
  (a, b) :: E.

Inductive Lookup {A B : Type} : list (A * B) -> A -> B -> Type :=
  | Lookup_hd     a b E :                           Lookup (cons (a,b) E) a b
  | Lookup_tl x y a b E : x <> a -> Lookup E a b -> Lookup (cons (x,y) E) a b.

Fixpoint Lookup_unique {A B : Type} E (a : A) (b1 b2 : B) (L1 : Lookup E a b1) (L2 : Lookup E a b2) {struct E} : b1 = b2.
Proof.
  destruct E; simple inversion L1; simple inversion L2; try congruence; intros.
  + match goal with
    | [L1 : Lookup ?E1 _ _, L2 : Lookup ?E2 _ _ |- _] =>
        is_var E1; is_var E2;
        assert (E1 = E) by congruence;
        assert (E2 = E) by congruence
    end.
    eapply (Lookup_unique A B E a b1 b2); subst; eassumption.
Qed.

Fixpoint lookup_find {A B} (eq : A -> A -> bool) (E : list (A * B)) (a : A) : option B :=
  match E with
  | nil          => None
  | cons (x,b) E => if eq x a then Some b
                              else lookup_find eq E a
  end.

Fixpoint lookup_find_correct {A B} {eq : A -> A -> bool} (E : list (A * B)) (a : A) {struct E} :
  (forall x y, boolSpec (eq x y) (x = y)) ->
  match lookup_find eq E a with
  | Some b => Lookup E a b
  | None   => forall b, neg (Lookup E a b)
  end.
Proof.
  intros eq_correct.
  unfold_goal.
  destruct E; simpl.
  + intros ?; inversion 1.
  + destruct p as [x b]; simpl.
    set (eq_correct x a).
    case_eq (eq x a); boolSpec_simpl; simpl.
    - my_auto.
    - fold (lookup_find eq E a).
      set (lookup_find_correct A B eq E a eq_correct).
      case_eq (lookup_find eq E a).
      * intros ? Heq.
        rewrite Heq in *; my_auto.
      * intros Heq.
        rewrite Heq in *.
        intros ?; inversion 1; firstorder.
Defined.

Fixpoint lookup_find_unique {A B} {eq : A -> A -> bool} (E : list (A * B)) (a : A) (b : B) {struct E} :
  (forall x y, boolSpec (eq x y) (x = y)) ->
  Lookup E a b ->
  lookup_find eq E a = Some b.
Proof.
  intros eq_correct.
  destruct E.
  + my_auto.
  + inversion 1; simpl; set (eq_correct a a); boolSpec_destruct; my_auto.
    set (eq_correct x a); boolSpec_simpl; my_auto.
Defined.

Definition Disjoint {A B1 B2} E1 E2 : Type :=
  forall (a : A) (b1 : B1) (b2 : B2), Lookup E1 a b1 -> Lookup E2 a b2 -> False.

Definition env_sub {A B} (P : A -> Type) (E1 E2 : list (A * B)) :=
  forall id, P id -> forall b, Lookup E1 id b -> Lookup E2 id b.

Definition env_equiv {A B} (P : A -> Type) (E1 E2 : list (A * B)) :=
  env_sub P E1 E2 * env_sub P E2 E1.

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

Definition context_ind {A B} (P : list (A * B) -> Type) :
  (P nil) ->
  (forall a b E, P E -> P (add E a b)) ->
  (forall E, P E).
Proof.
  intros Hnil Hcons.
  induction E as [|[? ?]].
  + exact Hnil.
  + eapply Hcons; assumption.
Qed.


Inductive linear {A B} : list (A * B) -> Type :=
  | LinearNil        : linear nil
  | LinearCons a b E : (forall b, neg (Lookup E a b)) -> linear E -> linear ((a, b) :: E).

Fixpoint remove_var {A B} {eq_dec : DecidableEq A} a E : list (A * B) :=
  match E with
  | nil             => nil
  | cons (a', b') E => match decide a a' : Decision (a = a') with
                       | inl _ => (remove_var a E)
                       | inr _ => (a', b') :: (remove_var a E)
                       end
  end.

Fixpoint remove_var_fun {A B} (eq_fun : A -> A -> bool) a E : list (A * B) :=
  match E with
  | nil             => nil
  | cons (a', b') E => if eq_fun a a' 
                         then remove_var_fun eq_fun a E
                         else (a', b') :: remove_var_fun eq_fun a E
  end.

Lemma remove_var_fun_complete {A B} (eq_fun : A -> A -> bool) a (E : list (A * B)) :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->
  forall a' b', 
    neg (a = a') ->
    Lookup E a' b' ->
    Lookup (remove_var_fun eq_fun a E) a' b'.
Proof.
  intros eq_fun_correct.
  induction E as [|[? ?] E IH]; simpl.
  - inversion 2.
  - inversion 2;
    match goal with
    | [|- context[eq_fun ?a1 ?a2]] =>
        generalize (eq_fun_correct a1 a2);
        destruct (eq_fun a1 a2)
    end; my_auto.
Qed.

Lemma remove_var_complete {A B} {eq_dec : DecidableEq A} a (E : list (A * B)) :
  forall a' b', 
    neg (a = a') ->
    Lookup E a' b' ->
    Lookup (remove_var a E) a' b'.
Proof. induction E; inversion 2; my_auto. Qed.

Lemma remove_var_fun_sound {A B} (eq_fun : A -> A -> bool) a (E : list (A * B)) :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->
  forall a' b', 
    neg (a = a') ->
    Lookup (remove_var_fun eq_fun a E) a' b' ->
    Lookup E a' b'.
Proof.
  intros eq_fun_correct ? ? ?.
  induction E as [|[? ?] E IH]; simpl.
  - inversion 1.
  - match goal with
    | [|- context[eq_fun ?a1 ?a2]] =>
        generalize (eq_fun_correct a1 a2);
        destruct (eq_fun a1 a2);
        simpl
    end.
    + intros;      my_auto.
    + inversion 2; my_auto.
Qed.

Lemma remove_var_sound {A B} {eq_dec : DecidableEq A} a (E : list (A * B)) :
  forall a' b',
    neg (a = a') ->
    Lookup (remove_var a E) a' b' ->
    Lookup E a' b'.
Proof.
  intros a' b' Hneq.
  induction E as [| [a'' b'']]; simpl.
  - inversion 1.
  - decide_destruct;
    inversion 1;
    my_auto.
Qed.

Lemma remove_var_fun_Lookup {A B} (eq_fun : A -> A -> bool) a (E : list (A * B)) :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->
  forall b, neg (Lookup (remove_var_fun eq_fun a E) a b).
Proof.
  intros eq_fun_correct.
  induction E as [|[? ?] E IH]; simpl.
  - inversion 1.
  - match goal with
    | [|- context[eq_fun ?a1 ?a2]] =>
        generalize (eq_fun_correct a1 a2);
        destruct (eq_fun a1 a2);
        simpl
    end.
    + my_auto.
    + inversion 2.
      * my_auto.
      * firstorder.
Qed.

Lemma remove_var_Lookup {A B} {eq_dec : DecidableEq A} a (E : list (A * B)) :
  forall b, neg (Lookup (remove_var a E) a b).
Proof.
  induction E as [| [? ?]]; simpl.
  - inversion 1.
  - destruct_decide.
    + assumption.
    + inversion 1; my_auto; firstorder.
Qed.

Fixpoint linearize {A B} {eq_dec : DecidableEq A} E : list (A * B) :=
  match E with
  | nil           => nil
  | cons (a, b) E => cons (a, b) (remove_var a (linearize E))
  end.

Fixpoint linearize_fun {A B} (eq_fun : A -> A -> bool) E : list (A * B) :=
  match E with
  | nil           => nil
  | cons (a, b) E => cons (a, b) (remove_var_fun eq_fun a (linearize_fun eq_fun E))
  end.

Lemma linearize_fun_sound {A B} {eq_fun : A -> A -> bool} (E : list (A * B)) :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->
  forall a' b',
    Lookup (linearize_fun eq_fun E) a' b' ->
    Lookup E a' b'.
Proof.
  intros eq_fun_correct.
  induction E as [|[? ?]]; simpl.
  - inversion 1.
  - inversion 1; subst.
    + constructor.
    + constructor 2.
      * assumption.
      * apply IHE.
        eapply remove_var_fun_sound; eassumption.
Qed.

Lemma linearize_sound {A B} {eq_dec : DecidableEq A} (E : list (A * B)) :
  forall a' b',
    Lookup (linearize E) a' b' ->
    Lookup E a' b'.
Proof.
  induction E as [|[? ?]]; simpl.
  - inversion 1.
  - inversion 1; subst.
    + constructor.
    + constructor 2.
      * assumption.
      * apply IHE.
        eapply remove_var_sound; eassumption.
Qed.

Lemma linearize_fun_complete {A B} {eq_fun : A -> A -> bool} (E : list (A * B)) :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->
  forall a' b',
    Lookup E a' b' ->
    Lookup (linearize_fun eq_fun E) a' b'.
Proof.
  intros eq_fun_correct.
  induction E as [|[? ?]]; simpl.
  - inversion 1.
  - inversion 1; subst.
    + constructor.
    + constructor 2.
      * assumption.
      * eapply remove_var_fun_complete; my_auto.
Qed.  

Lemma linearize_complete {A B} {eq_dec : DecidableEq A} (E : list (A * B)) :
  forall a' b',
    Lookup E a' b' ->
    Lookup (linearize E) a' b'.
Proof.
  induction E as [|[? ?]]; simpl.
  - inversion 1.
  - inversion 1; subst.
    + constructor.
    + constructor 2.
      * assumption.
      * eapply remove_var_complete; my_auto.
Qed.  

Lemma linear_remove_var_fun {A B} {eq_fun : A -> A -> bool} a (E : list (A * B)) :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->
  linear E -> linear (remove_var_fun eq_fun a E).
Proof.
  intros eq_fun_correct.
  induction E as [|[? ?]]; simpl.
  - my_auto.
  - match goal with
    | [|- context[eq_fun ?a1 ?a2] ] =>
        generalize (eq_fun_correct a1 a2);
        destruct (eq_fun a1 a2);
        simpl; intros ?
    end.
    + inversion 1; my_auto.
    + inversion 1; subst.
      constructor.
      * intros ? ?.
        match goal with
        | [H : forall _, neg (Lookup E _ _) |- _] =>
            eapply H;
            eapply remove_var_fun_sound;
            eassumption
        end.
      * my_auto.
Qed.

Lemma linear_remove_var {A B} {eq_dec : DecidableEq A} a (E : list (A * B)) :
  linear E -> linear (remove_var a E).
Proof.
  induction E as [|[? ?]]; simpl.
  - my_auto.
  - decide_destruct.
    + inversion 1; my_auto.
    + inversion 1; subst.
      constructor.
      * intros ? ?.
        match goal with
        | [H : forall _, neg (Lookup E _ _) |- _] =>
            eapply H;
            eapply remove_var_sound;
            eassumption
        end.
      * my_auto.
Qed.

Lemma linearize_fun_linear {A B} {eq_fun : A -> A -> bool} (E : list (A * B)) :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->  
  linear (linearize_fun eq_fun E).
Proof.
  intros eq_fun_correct.
  induction E as [|[? ?]]; simpl.
  - constructor.
  - econstructor.
    + apply remove_var_fun_Lookup; assumption.
    + apply linear_remove_var_fun; assumption.
Qed.

Lemma linearize_linear {A B} {eq_dec : DecidableEq A} (E : list (A * B)) :
  linear (linearize E).
Proof.
  induction E as [|[? ?]]; simpl.
  - constructor.
  - econstructor.
    + apply remove_var_Lookup.
    + apply linear_remove_var; assumption.
Qed.

Fixpoint context_linear_all_fun {A B} (eq_fun : A -> A -> bool) (P_fun : A -> B -> bool) E : bool :=
  match E with
  | nil           => true
  | cons (a, b) E => andb (P_fun a b) (context_linear_all_fun eq_fun P_fun E)
  end.

Fixpoint context_linear_all_fun_correct {A B} {eq_fun : A -> A -> bool} {P_fun : A -> B -> bool} {P : A -> B -> Type} {E} :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->
  (forall x y, boolSpec (P_fun  x y) (P x y)) ->
  linear E ->
  boolSpec (context_linear_all_fun eq_fun P_fun E) (forall a b, Lookup E a b -> P a b).
Proof.
  intros eq_fun_correct P_fun_correct.
  induction E as [| [a b] E IH]; simpl.
  - my_auto.
  - match goal with
    | [|- context[P_fun ?a1 ?a2] ] =>
        generalize (P_fun_correct a1 a2);
        destruct (P_fun a1 a2);
        simpl; [intros ?| intros P_neg]
    end.
    + inversion 1 as [| ? ? ? Hfalse Hlinear]; subst.
      match goal with
      | [|- context[context_linear_all_fun eq_fun P_fun ?E] ] =>
          generalize (context_linear_all_fun_correct _ _ _ _ _ E eq_fun_correct P_fun_correct Hlinear);
          destruct (context_linear_all_fun eq_fun P_fun E);
          simpl; intros ?
      end.
      inversion 1; my_auto.
      intros Hlookup.
      apply (IH Hlinear); intros.
      apply Hlookup.
      constructor 2.
      * intros ?; subst; firstorder.
      * assumption.
    + intros Hlinear Hfalse.
      apply P_neg.
      apply Hfalse.
      constructor.
Qed.

Definition lookup_linear_dec {A B} {eq_dec : DecidableEq A} {P : A -> B -> Type} (P_dec : forall a b, Decision (P a b)) E :
  linear E ->
  Decision (forall a b, Lookup E a b -> P a b).
Proof.
  induction E as [| [a b] E IH].
  - left; inversion 1.
  - destruct (P_dec a b) as [P_pos | P_neg].
    + inversion 1 as [| ? ? ? Hfalse Hlinear]; subst.
      destruct (IH Hlinear) as [IH_pos | IH_neg].
      * left; inversion 1; subst.
          assumption.
          apply IH_pos; assumption.
      * right; intros H.
        apply IH_neg; intros.
        apply H.
        constructor 2.
          intros ?; subst; firstorder.
          assumption.
    + right.
      intros Hfalse.
      apply P_neg.
      apply Hfalse.
      constructor.
Qed.

Definition context_linear_ind {A B} {eq_dec : DecidableEq A} (P : list (A * B) -> Type) :
  P nil ->
  (forall a (b : B) E, (forall b, neg (Lookup E a b)) -> linear E -> P (add E a b)) ->
  forall E, linear E -> P E.
Proof.
  intros Hempty Hadd.
  induction E as [|[? ?]]; simpl.
  - auto.
  - inversion 1; subst.
    apply Hadd; assumption.
Qed.

Definition context_all_fun {A B} (eq_fun : A -> A -> bool) (P_fun : A -> B -> bool) E : bool :=
  context_linear_all_fun eq_fun P_fun (linearize_fun eq_fun E).

Lemma context_all_fun_correct {A B} {eq_fun : A -> A -> bool} {P_fun : A -> B -> bool} {P : A -> B -> Type} E :
  (forall x y, boolSpec (eq_fun x y) (x = y)) ->
  (forall x y, boolSpec (P_fun  x y) (P x y)) ->
  boolSpec (context_all_fun eq_fun P_fun E) (forall a b, Lookup E a b -> P a b).
Proof.
  intros eq_fun_correct P_fun_correct.
  do 2 unfold_goal.
  generalize (context_linear_all_fun_correct eq_fun_correct P_fun_correct (linearize_fun_linear E eq_fun_correct)).
  destruct (context_linear_all_fun eq_fun P_fun (linearize_fun eq_fun E)); simpl; intros H.
  - intros.
    apply H.
    apply linearize_fun_complete; assumption.
  - intros Hlookup.
    apply H; intros.
    apply Hlookup.
    eapply linearize_fun_sound; eassumption.
Qed.

Definition lookup_dec {A B} {eq_dec : DecidableEq A} {P : A -> B -> Type} (P_dec : forall a b, Decision (P a b)) E :
  Decision (forall a b, Lookup E a b -> P a b).
Proof.
  destruct (lookup_linear_dec P_dec (linearize E) (linearize_linear E)) as [Y|N].
  - left; intros.
    apply Y.
    apply linearize_complete.
    assumption.
  - right; intros H.
    apply N; intros.
    apply H.
    apply linearize_sound.
    assumption.
Qed.
