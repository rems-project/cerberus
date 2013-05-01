Require Import Bool List.

Require Import Common.

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
