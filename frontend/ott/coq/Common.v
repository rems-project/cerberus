Require Import List.
Require Import Bool.
Require Import Arith.
Require Import ZArith.

Require Relations.
Require Import Classes.SetoidClass.

Open Scope type.
Open Scope list.
Open Scope bool.

(*Definition neg P := P -> False.*)
Definition boolSpec (b : bool) (P : Prop) := if b then P else ~ P.

Definition optionBoolSpec {A} (o : option bool) (P : A -> Prop) :=
  match o with
  | Some true  => forall a, P a
  | Some false => forall a, ~ (P a)
  | None   => ~ (forall a, P a) /\ ~ (forall a, ~ (P a))
  end.

Lemma boolSpec_true {p} : boolSpec true p = p.
Proof. reflexivity. Defined.

Lemma boolSpec_false {p} : boolSpec false p = ~ p.
Proof. reflexivity. Defined.

Ltac boolSpec_destruct :=
  match goal with
  | [ H : boolSpec ?b _ |- _] =>
      match b with
      | true  => fail 1
      | false => fail 1
      | _     =>
          let Heq := fresh in
          case_eq b; intros Heq; rewrite Heq in *; clear Heq; simpl in H
      end
  end.

Ltac boolSpec_destruct_hyp H :=
  match H with
  | boolSpec ?b _ =>
      match b with
      | true  => fail 1
      | false => fail 1
      | _     =>
          let Heq := fresh in
          case_eq b; intros Heq; rewrite Heq in *; clear Heq; simpl in H
      end
  end.

Ltac or_destruct :=
  match goal with
  | [|- _ \/ _ -> _] =>
      let Heq := fresh in
      intros [Heq|Heq]; revert Heq
  | [|- _ -> _] =>
      let Heq := fresh in
      intros Heq; or_destruct; revert Heq
  end.

Ltac and_destruct :=
  match goal with
  | [|- _ /\ _ -> _] =>
      apply and_rect
  | [|- _ -> _] =>
      let Heq := fresh in
      intros Heq; and_destruct; revert Heq
  end.

Ltac bool_simpl :=
  repeat match goal with
  | [|- context[_ || _ = true]] =>
      rewrite orb_true_iff; or_destruct
  | [|- context[_ || _ = false]] =>
      rewrite orb_false_iff; and_destruct
  | [|- context[_ && _ = true]] =>
      rewrite andb_true_iff; and_destruct
  | [|- context[_ && _ = false]] =>
      rewrite andb_false_iff; or_destruct
  | [|- context[negb _ = true ]] =>
      rewrite negb_true_iff
  | [|- context[negb _ = false]] =>
      rewrite negb_false_iff
  end.

Ltac boolSpec_simpl :=
  repeat match goal with
  | [H : boolSpec ?B _ |- ?B = _ -> _] =>
      let Heq := fresh in
      intros Heq; rewrite Heq in H
  | [H : boolSpec ?B _ |- _] =>
      match B with
      | true  => rewrite boolSpec_true  in H
      | false => rewrite boolSpec_false in H
      | _     => let b := fresh in
                 progress (set B as b in H; simpl in b; subst b)
      end
  end.

(*
Definition decidable P := P + neg P.
Class Decision (P : Type) := decision : decidable P.

Definition boolSpec_Decision {b : bool} {P : Prop} (B : boolSpec b P) : Decision P.
Proof. destruct b; [left | right]; assumption. Defined.
*)

Definition boolSpec_elim1 {b : bool} {P : Prop} : boolSpec b P -> b = true -> P.
Proof. intros; subst; assumption. Defined.
Definition boolSpec_elim2 {b : bool} {P : Prop} : boolSpec b P -> b = false -> ~ P.
Proof. intros; subst; assumption. Defined.
Definition boolSpec_elim1_inv {b : bool} {P : Prop} : boolSpec b P -> P -> b = true.
Proof. destruct b; solve [reflexivity | contradiction]. Defined.
Definition boolSpec_elim2_inv {b : bool} {P : Prop} : boolSpec b P -> ~ P -> b = false.
Proof. destruct b; solve [reflexivity | contradiction]. Defined.
Lemma boolSpec_elim {b : bool} {P : Prop} : boolSpec b P -> (P <-> b = true).
Proof. intros B; generalize (boolSpec_elim1 B), (boolSpec_elim1_inv B); tauto. Defined.

Definition optionSpec {A} (o : option A) (P : A -> Prop) : Prop :=
  match o with
  | Some a => P a
  | None   => forall a, ~ P a
  end.

Ltac optionSpec_destruct :=
  match goal with
  | H:optionSpec ?o _
    |- _ =>
        match o with
        | Some _ => fail 1
        | None   => fail 1
        | _ =>
            let Heq := fresh in
            case_eq o; [intros ?|]; intros Heq; rewrite Heq in *; clear Heq; simpl in H
        end
  end.

Ltac optionSpec_destruct_hyp v :=
  match goal with
  | H:optionSpec ?o _
    |- _ =>
        match o with
        | Some _ => fail 1
        | None   => fail 1
        | _ =>
            let Heq := fresh in
            try (let v' := fresh in rename v into v');
            case_eq o; [intros v|]; intros Heq; rewrite Heq in *; clear Heq; simpl in H
        end
  end.

Definition optionSpec_elim1 {A} {o : option A} {P : A -> Prop} {a : A} : optionSpec o P -> o = Some a -> P a.
Proof. intros; subst; assumption. Defined.
Definition optionSpec_elim2 {A} {o : option A} {P : A -> Prop}         : optionSpec o P -> o = None   -> forall a, ~ P a.
Proof. intros ? ?; subst; assumption. Defined.

Definition optionUnique {A} (o : option A) (P : A -> Prop) : Prop :=
  forall a, P a -> o = Some a.

Definition findSpec {A} (a : A) (P : A -> Prop) : Prop := P a.

Definition findUnique {A} (a : A) (P : A -> Prop) : Prop :=
  forall a', P a' -> a = a'.

(*
Definition bool_of_decision {P} : Decision P -> bool :=
  fun d => match d with
           | inl _ => true
           | inr _ => false
           end.

Definition relation A := A -> A -> Type.
Definition complement {A} (R : relation A) x y := neg (R x y).
Class Reflexive {A} (R : relation A) :=
  reflexive x : R x x.
Class Irreflexive {A} (R : relation A) :=
  irreflexive : Reflexive (complement R).
Class Asymmetric {A} (R : relation A) :=
  asymmetric x y : R x y -> R y x -> False.

Class DecidableRelation {A} (R : Relation_Definitions.relation A) :=
  decide : forall x y : A, Decision (R x y).
Class DecidableEq (A : Type) :=
  Decidable_Equality :> DecidableRelation (@eq A).
*)

Ltac finish t := solve [ congruence | discriminate | reflexivity | t
                       | econstructor (solve [eauto])
                       | intros; inversion 1; solve [contradiction | congruence | discriminate]
                       | inversion 1; solve [contradiction | congruence | discriminate] 
                       ].
Ltac decide_destruct :=
  match goal with
  | [ |- context[match ?d with _ => _ end] ] =>
      match type of d with
      | bool => (
          let H := fresh "H" in
          assert {H : bool & d = H};
          [ exists d; reflexivity 
          | destruct H as [H Heq];
            replace d with H;
            destruct H;
            revert Heq ]
          ) || fail 1
      | _ => destruct d
      end
(*  | [ |- context[decide ?a ?b] ] => destruct (decide a b)*)
  | [ |- ?a = ?a -> _] => intros _
  end.
Ltac scatter d := subst; simpl; first [d | decide_destruct].
Ltac finish_scatter_loop f d := repeat (first [finish f | scatter d | constructor]).
Ltac my_auto' f d := repeat (subst; simpl; auto; try (now finish_scatter_loop f d); try scatter d).
Ltac my_auto := my_auto' fail fail.
Obligation Tactic := my_auto.

(*
Definition Decision_elim {P} {A} : Decision P -> (P -> A) -> (neg P -> A) -> A :=
  fun d pos neg =>
    match d with
    | inl p => pos p
    | inr n => neg n
    end.

Ltac destruct_decide :=
  match goal with
  | [ |- context[decide ?a ?b] ] => destruct (decide a b)
  end.

Lemma decision_sumbool {P : Prop} : Decision P -> {P} + {~P}.
Proof. destruct 1; auto. Defined.

Lemma decision_sumbool_inv {P : Prop} : {P} + {~P} -> Decision P.
Proof. destruct 1; [left | right]; auto. Defined.

Lemma decidableRelation_sumbool {A} {R : Relation_Definitions.relation A} : DecidableRelation R -> forall x y, {R x y} + {~R x y}.
Proof. intros dec_R. intros x y. destruct (dec_R x y); auto. Defined.

Lemma decidableRelation_sumbool_inv {A} {R : Relation_Definitions.relation A} : (forall x y, {R x y} + {~R x y}) -> DecidableRelation R.
Proof. intros sum_R. intros x y. destruct (sum_R x y); [left | right]; auto. Defined.

Definition decidableEq_sumbool {A} : DecidableEq A -> (forall x y : A, {x = y} + {x <> y}) := decidableRelation_sumbool.
Definition decidableEq_sumbool_inv {A} : (forall x y : A, {x = y} + {x <> y}) -> DecidableEq A := decidableRelation_sumbool_inv.

Program Instance makeDecidableRelation {A} {R : Relation_Definitions.relation A} `{d : forall x y : A, Decision (R x y)} : DecidableRelation R.
Program Instance makeDecidableEq       {A}                  `{d : forall x y : A, Decision (x = y)} : DecidableEq A.

Ltac decision_eq :=
  match goal with [ |- Decision (eq ?a ?b) ] =>
    match a with appcontext C1 [?c ?t1] =>
    match b with appcontext C2 [ c ?t2] =>
      let H := fresh in
      assert (Decision (t1 = t2)) as H by apply decide;
      destruct H;
      [subst | right; inversion 1; contradiction]
    end end
  end.

Ltac decision_eq_destruct :=
  match goal with [ |- forall x y, _] =>
    destruct x; destruct y; try solve [left; reflexivity | right; inversion 1]
  end.
*)

Ltac notHyp P :=
  match goal with
  | [ _ : P |- _ ] => fail 1
  | _ => idtac
  end.

(*
Ltac decision_eq_fix :=
  match goal with
  | [|- forall x y :?A, _] =>
      notHyp (forall x y : A, Decision (x = y));
      let IH := fresh in
      fix IH 1
  | _ => idtac
  end.

Ltac decidable_eq :=
  match goal with
  | [ |- DecidableEq ?A] =>
    cut (forall x y : A, Decision (x = y)); [now trivial|]
  | [ |- Decision (?x = ?y)] =>
    revert x y
  | [ |- forall x y : ?A, Decision (x = y)] =>
    idtac
  end.

Ltac dec_eq :=
  decidable_eq;
  decision_eq_fix;
  decision_eq_destruct;
  repeat decision_eq;
  left; reflexivity.
*)

Require Import RelationClasses.

Class Trichotomous {A} (R: Relation_Definitions.relation A) := {
  trichotomous : forall x y : A, {R x y} + {R y x} + {x = y}
}.

Class StrictTotalOrder {A} (R : Relation_Definitions.relation A) := {
  strict_STO       :> StrictOrder R ;
  trichotomous_STO :> Trichotomous R
}.

Ltac hyp H :=
  match goal with
  | [ H : _ |- _ ] => idtac
  | _ => fail 1
  end.

Ltac unfold_goal :=
  match goal with
  | [ |- appcontext[?d] ] =>
      unfold d
  end.

Ltac destruct_sum :=
  repeat match goal with
  | [ H : sum _ _ |- _          ] => destruct H
  | [             |- _ + _ -> _ ] => destruct 1
  end.

Ltac apply_ctx :=
  match goal with
  | [ f : _ -> ?t |- ?t ] => apply f
  end.

(*
Lemma Decision_boolSpec {P : Prop} (D : Decision P) : boolSpec (bool_of_decision D) P.
Proof. destruct D; assumption. Qed.
*)

Ltac var_destruct_inner c :=
  match c with
  | _ => is_var c; destruct c; try finish fail
  | match ?c with _ => _ end => var_destruct_inner c
  end.

Ltac var_destruct :=
  match goal with
  | [|- match ?c with _ => _ end] =>
      var_destruct_inner c
  end.

Ltac not_var H :=
  match goal with
  | _ => is_var H; fail 1
  | _ => idtac
  end.

Ltac pull_out T c :=
  ( let H   := fresh in
    let t   := fresh in
    let Heq := fresh in
    assert {t : T & c = t} as H by (exists c; reflexivity);
    destruct H as [t Heq];
    replace c with t;
    revert Heq
  ) || fail 1.

Ltac context_destruct_inner c :=
  match c with
  | _                        =>
      is_var c; destruct c; try finish fail
  | match ?c with _ => _ end =>
      context_destruct_inner c
  | _ =>
      match type of c with
      | bool      => pull_out bool c
      | option ?A => pull_out (option A) c
      end
  end.

Ltac context_destruct :=
  match goal with
  | [|- match ?c with _ => _ end] =>
      context_destruct_inner c
  | [|- ((match ?c with _ => _ end) = _)] =>
      context_destruct_inner c
  | [|- ((match ?c with _ => _ end) = _) -> _] =>
      context_destruct_inner c
  | [|- (match ?c with _ => _ end) -> _] =>
      context_destruct_inner c
  end.

Ltac case_fun G :=
  match goal with
  | |- ?t = ?o -> _ =>
      is_var o;
      let H := fresh in
      match type of G with
      | boolSpec _ _ =>
          intros H;
          destruct o; [
            apply (boolSpec_elim1 G) in H
          | apply (boolSpec_elim2 G) in H]
      | optionSpec _ _ =>
          intros H;
          destruct o; [
            apply (optionSpec_elim1 G) in H
          | lapply (optionSpec_elim2 G); [clear H; intros H|exact H]]
      | _ =>
          intros ?;
          subst o;
          pose proof G as H;
          destruct t;
          simpl in H
      end
  end.

(*Ltac case_fun G :=
  match goal with
  | |- _ = ?o -> _ =>
      is_var o;
      let Heq := fresh in
      match type of o with
      | bool =>
          intros Heq;
          destruct o; [
            apply (boolSpec_elim1 G) in Heq
          | apply (boolSpec_elim2 G) in Heq]
      | option _ =>
          intros Heq;
          destruct o; [
            apply (optionSpec_elim1 G) in Heq
          | lapply (optionSpec_elim2 G); [clear Heq; intros Heq|exact Heq]]
      | _ =>
          let H := fresh in
          destruct o;
          intros Heq;
          generalize G;
          rewrite Heq;
          intros H;
          simpl in H
      end
  end.
*)

Ltac case_fun_tac G tpos tneg :=
  match goal with
  | |- _ = ?o -> _ =>
      is_var o;
      let Heq := fresh in
      match type of o with
      | bool =>
          intros Heq;
          destruct o; [
            apply (boolSpec_elim1 G) in Heq; tpos Heq
          | apply (boolSpec_elim2 G) in Heq; tneg Heq]
      | option _ =>
          intros Heq;
          destruct o; [
            apply (optionSpec_elim1 G) in Heq; tpos Heq
          | lapply (optionSpec_elim2 G); [clear Heq; intros Heq|exact Heq]; tneg Heq]
      | _ =>
          let H := fresh in
          destruct o;
          intros Heq;
          generalize G;
          rewrite Heq;
          intros H;
          simpl in H;
          [tpos H|tneg H];
          clear Heq
      end
  end.

Ltac autodestruct_hyp H :=
  match type of H with
  | { _ : _ & _} =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      autodestruct_hyp H1;
      autodestruct_hyp H2
  | exists _ , _ =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      autodestruct_hyp H1;
      autodestruct_hyp H2
  | _ * _ =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      autodestruct_hyp H1;
      autodestruct_hyp H2
  | _ /\ _ =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      autodestruct_hyp H1;
      autodestruct_hyp H2
  | _ => idtac
  end.

Ltac autodestruct H :=
  autodestruct_hyp H; Tactics.subst_no_fail; Tactics.autoinjections.

Ltac id_tac H := idtac.

Ltac case_fun_hyp G :=
  match goal with
  | [|- _ = ?o -> _] =>
      let Heq := fresh in
      is_var o;
      destruct o;
      intros Heq;
      revert G;
      rewrite Heq;
      intros G
  end.

Ltac case_fun_destruct :=
  match goal with
  | [|- ?t = ?o -> _] =>
      is_var o;
      let Heq := fresh in
      destruct t; intros Heq; rewrite <- Heq; clear Heq
  end.

Ltac context_destruct_all :=
  repeat (context_destruct; try case_fun_destruct).

Ltac notSame x y :=
  try (unify x y; fail 1); notHyp (x = y); notHyp (y = x).

Definition option_bind {A B} : option A -> (A -> option B) -> option B :=
  fun o f =>
    match o with
    | Some a => f a
    | None   => None
    end.

Infix ">>=" := option_bind (at level 42, left associativity).

Definition option_bool {A} : option A -> (A -> bool) -> bool :=
  fun o f =>
    match o with
    | Some a => f a
    | None   => false
    end.

Lemma negb_correct {P} {p} :
  boolSpec p P ->
  boolSpec (negb p) (~ P).
Proof.
  intros p_correct.
  boolSpec_destruct; my_auto.
Qed.

Definition eq_bool := Bool.eqb.

Lemma eq_bool_correct x y :
  boolSpec (eq_bool x y) (x = y).
Proof.
  do 2 unfold_goal.
  case_eq (eqb x y).
  + apply eqb_true_iff.
  + apply eqb_false_iff.
Qed.

Definition eq_list {A} (eq_A : A -> A -> bool) :=
  fix eq_list (l1 l2 : list A) : bool :=
    match l1, l2 with
    | nil     , nil      => true
    | a1 :: l1, a2 :: l2 => eq_A a1 a2 && eq_list l1 l2
    | _       , _        => false
    end.

Definition eq_list_correct {A} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall x y, boolSpec (eq_list eq_A x y) (x = y).
Proof.
  intros eq_A_correct.
  fix eq_list_correct 1.
  destruct x, y; simpl;
  unfold andb;
  unfold boolSpec;
  repeat match goal with
  | |- eq_A ?x ?y = _ -> _ => case_fun (eq_A_correct x y)
  | |- eq_list eq_A ?x ?y = _ -> _ => case_fun (eq_list_correct x y)
  | _ => context_destruct
  end; my_auto.
Qed.

Definition cross {A B C D} f g : A * B -> C * D := 
  fun p => (f (fst p), g (snd p)).

Definition cross2 {A B C D} f g : A * B -> C * D -> Prop  :=
  fun p1 p2 => f (fst p1) (fst p2) /\  g (snd p1) (snd p2).

Definition equiv_pair {A1 A2 B1 B2} (equiv_A : A1 -> A2 -> bool) (equiv_B : B1 -> B2 -> bool) : A1 * B1 -> A2 * B2 -> bool :=
  fun p1 p2 => 
    let '(a1, b1) := p1 in
    let '(a2, b2) := p2 in
    equiv_A a1 a2 && equiv_B b1 b2.

Definition equiv_pair_correct {A1 A2 B1 B2} {equiv_A : A1 -> A2 -> bool} {equiv_B : B1 -> B2 -> bool} {E1 : A1 -> A2 -> Prop} {E2 : B1 -> B2 -> Prop} :
  (forall x y, boolSpec (equiv_A x y) (E1 x y)) ->
  (forall x y, boolSpec (equiv_B x y) (E2 x y)) ->
  forall x y, boolSpec (equiv_pair equiv_A equiv_B x y) (cross2 E1 E2 x y).
Proof.
  intros equiv_A_correct equiv_B_correct.
  destruct x as [a1 b1], y as [a2 b2]; simpl.
  set (equiv_A_correct a1 a2).
  set (equiv_B_correct b1 b2).
  repeat (boolSpec_destruct; my_auto).
Qed.

Definition eq_pair {A B} (eq_A : A -> A -> bool) (eq_B : B -> B -> bool) : A * B -> A * B -> bool :=
  fun p1 p2 => 
    let '(a1, b1) := p1 in
    let '(a2, b2) := p2 in
    eq_A a1 a2 && eq_B b1 b2.

Definition eq_pair_correct {A B} {eq_A} {eq_B} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  (forall x y : B, boolSpec (eq_B x y) (x = y)) ->
  forall x y, boolSpec (eq_pair eq_A eq_B x y) (x = y).
Proof.
  intros eq_A_correct eq_B_correct.
  destruct x as [a1 b1], y as [a2 b2]; simpl.
  set (eq_A_correct a1 a2).
  set (eq_B_correct b1 b2).
  repeat (boolSpec_destruct; my_auto).
Qed.

Definition eq_option {A} (eq_A : A -> A -> bool) : option A -> option A -> bool :=
  fun o1 o2 => 
    match o1, o2 with
    | Some a1, Some a2 => eq_A a1 a2
    | None   , None    => true
    | _      , _       => false
    end.

Definition eq_option_correct {A} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall x y, boolSpec (eq_option eq_A x y) (x = y).
Proof.
  intros eq_A_correct.
  destruct x as [a1|], y as [a2|]; simpl;
  [set (eq_A_correct a1 a2); boolSpec_destruct|..]; my_auto.
Qed.

Definition eq_nat := beq_nat.
Definition le_nat := leb.

Lemma eq_nat_correct x y :
  boolSpec (eq_nat x y) (x = y).
Proof.
  pull_out bool (eq_nat x y).
  match goal with
  | b : bool |- _ => destruct b
  end.
  - apply beq_nat_true.
  - apply beq_nat_false.
Qed.

Fixpoint le_nat_correct x y : boolSpec (le_nat x y) (x <= y).
Proof.
  do 2 unfold_goal.
  case_eq (leb x y); intros Heq.
  - exact (leb_complete _ _ Heq).
  - intros H.
    set (leb_correct _ _ H).
    congruence.
Qed.

Fixpoint in_list {A:Set} (eq : A -> A -> bool) (a : A) (ls : list A) : bool :=
  match ls with
  | nil   => false
  | x::xs => orb (eq x a) (in_list eq a xs)
  end.

Definition in_list_correct {A:Set} {eq_A : A -> A -> bool}  :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall a l, boolSpec (in_list eq_A a l) (List.In a l)).
Proof.
  intros eq_A_correct.
  fix in_list_correct 2.
  do 2 unfold_goal;
  destruct l; simpl;
  fold (@in_list A); unfold orb;
  repeat match goal with
  | [|- eq_A ?x ?a = _ -> _] => case_fun (eq_A_correct x a)
  | [|- in_list eq_A ?a ?l = _ -> _] => case_fun (in_list_correct a l)
  | _ => context_destruct
  end; my_auto.
Qed.

Inductive allList {A : Set} (P : A -> Prop) : list A -> Prop :=
  | AllList_nil  : allList P nil
  | AllList_cons {x} {l} : P x -> allList P l -> allList P (x :: l).
Arguments AllList_nil [A P].
Arguments AllList_cons [A P x l] _ _.

Lemma allList_cons1 {A : Set} {P} {x:A} {xs} :
  allList P (x :: xs) ->
  P x.
Proof. inversion_clear 1; assumption. Qed.

Lemma allList_cons2 {A : Set} {P} {x:A} {xs} :
  allList P (x :: xs) ->
  allList P xs.
Proof. inversion_clear 1; assumption. Qed.

Definition all_list {A:Set} (dec : A -> bool) :=
  fix all_list (l : list A) : bool :=
    match l with
    | nil   => true
    | x::xs => andb (dec x) (all_list xs)
    end.

Lemma all_list_correct {A : Set} {P : A -> Prop} {dec} :
  (forall a, boolSpec (dec a) (P a)) ->
  (forall l, boolSpec (all_list dec l) (allList P l)).
Proof.
  intros dec_correct.
  fix all_list_correct 1.
  intros l.
  do 2 unfold_goal;
  destruct l; simpl;
  fold (@all_list A dec); unfold andb;
  repeat match goal with
  | |- dec ?a = _ -> _ => case_fun (dec_correct a)
  | |- all_list dec ?l = _ -> _ => case_fun (all_list_correct l)
  | _ => context_destruct
  end; my_auto.
Defined.

Definition subList {A:Set} (l1 l2 : list A) :=
  allList (fun x => List.In x l2) l1.

Definition sub_list {A:Set} (eq : A -> A -> bool) (l1 l2 : list A) :=
  all_list (fun x => in_list eq x l2) l1.

Lemma sub_list_correct  {A:Set} {eq : A -> A -> bool} :
  (forall x y, boolSpec (eq x y) (x = y)) ->
  (forall x y, boolSpec (sub_list eq x y) (subList x y)).
Proof.
  intros eq_correct.
  set (fun l2 x => in_list_correct eq_correct x l2) as Hinner.
  exact (fun l1 l2 => all_list_correct (Hinner l2) l1).
Defined.

Definition equivList {A : Set} (l1 l2 : list A) :=
  subList l1 l2 * subList l2 l1.

Definition equiv_list {A : Set} (eq_A : A -> A -> bool) (l1 l2 : list A) :=
  andb (sub_list eq_A l1 l2) (sub_list eq_A l2 l1).

Lemma equiv_list_correct {A : Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x y, boolSpec (equiv_list eq_A x y) (equivList x y)).
Proof.
  intros eq_correct x y.
  do 3 unfold_goal.
  set (sub_list_correct eq_correct x y).
  set (sub_list_correct eq_correct y x).
  repeat boolSpec_destruct; my_auto.
Qed.

Definition subList_weaken1 {A : Set} {a} {xs ys : list A} : subList (a :: xs) ys -> subList xs ys.
Proof.
  destruct ys; inversion_clear 1.
  + match goal with
    | [H : In _ nil |- _] => now inversion H
    end.
  + assumption.
Qed.

Fixpoint subList_weaken2 {A : Set} {a} {xs ys : list A} : subList xs ys -> subList xs (a :: ys).
  destruct xs; intros H.
  + constructor.
  + inversion_clear H.
    constructor.
    * econstructor (now my_auto).
    * apply subList_weaken2; assumption.
Qed.

Lemma subList_In {A : Set} {xs ys : list A} {x} : In x xs -> subList xs ys -> In x ys.
Proof.
  revert xs.
  fix IH 1.
  destruct xs.
  - inversion 1.
  - destruct 1.
    + inversion 1; subst.
      assumption.
    + inversion 1; subst.
      apply (IH xs).
      * assumption.
      * eapply subList_weaken1; eassumption.
Qed.

Fixpoint subList_trans {A : Set} {xs ys zs : list A} : subList xs ys -> subList ys zs -> subList xs zs.
Proof.
  destruct xs; intros H1 H2.
  + constructor.
  + inversion H1; subst.
    constructor.
    * eapply subList_In; eassumption.
    * eapply subList_trans; eassumption.
Qed.

Definition equivList_cons {A : Set} {xs ys : list A} {a}  : equivList xs ys -> equivList (a :: xs) (a :: ys).
Proof.
  destruct xs; intros [H1 H2].
  - split.
    + repeat constructor.
    + inversion H2.
      * repeat constructor.
      * match goal with
        | [H : In _ nil |- _] => now inversion H
        end.
  - split.
    + constructor.
      * repeat constructor.
      * apply subList_weaken2.
        exact H1.
    + constructor.
      * repeat constructor.
      * apply (subList_weaken2 H2).
Qed.

Instance equivList_Equivalence {A : Set} : Equivalence (@equivList A).
Proof.
  split.
  - unfold Reflexive.
    fix IH 1. 
    intros [|].
    + repeat constructor.
    + intros.
      apply equivList_cons.
      apply IH.
  - inversion 1; constructor; assumption.
  - inversion 1; inversion 1; constructor;
    eapply subList_trans; eassumption.
Qed.

Definition eq_Z := Z.eqb.

Lemma eq_Z_correct x y : boolSpec (eq_Z x y) (x = y).
Proof.
  case_eq (eq_Z x y); intros Heq.
  + exact (proj1 (Z.eqb_eq  _ _) Heq).
  + exact (proj1 (Z.eqb_neq _ _) Heq).
Qed.

Definition lt_Z := Z.ltb.

Lemma lt_Z_correct x y : boolSpec (lt_Z x y) (x < y)%Z.
Proof.
  case_eq (lt_Z x y); intros Heq.
  + exact (proj1 (Z.ltb_lt  _ _) Heq).
  + exact (proj1 (Z.ltb_nlt _ _) Heq).
Qed.

Definition le_Z := Z.leb.

Lemma le_Z_correct x y : boolSpec (le_Z x y) (x <= y)%Z.
Proof.
  case_eq (le_Z x y); intros Heq.
  + exact (proj1 (Z.leb_le  _ _) Heq).
  + exact (proj1 (Z.leb_nle _ _) Heq).
Qed.
