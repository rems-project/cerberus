Require Import Common.
Require Import Context.

Require Context_defns.
Module D := Context_defns.

Lemma eq_context_correct {A B : Set} {eq_A} {eq_B} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  (forall x y : B, boolSpec (eq_B x y) (x = y)) ->
  forall x y, boolSpec (eq_context eq_A eq_B x y) (x = y).
Proof.
  intros eq_A_correct.
  intros eq_B_correct.
  apply (eq_list_correct (eq_pair_correct eq_A_correct eq_B_correct)).
Qed.

Definition lookup_functional {A B : Set} :
  forall {C} {a : A} {b1 b2 : B},
    D.lookup C a b1 ->
    D.lookup C a b2 ->
    b1 = b2.
Proof.
  induction C;
  inversion 1;
  inversion 1; subst.
  - reflexivity.
  - congruence.
  - congruence.
  - match goal with
    | L1 : D.lookup ?C1 _ _, L2 : D.lookup ?C2 _ _ |- _ =>
        is_var C1; is_var C2;
        assert (C1 = C) by congruence;
        assert (C2 = C) by congruence;
        eapply IHC; eassumption
    end.
Qed.
Arguments lookup_functional : default implicits.

Definition lookup_correct {A B : Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall (E : context A B) a, optionSpec (lookup eq_A E a) (D.lookup E a)).
Proof.
  intros eq_correct.
  fix IH 1.
  intros; destruct E; unfold_goal; simpl.
  + intros ?; inversion 1.
  + destruct p as [x b]; simpl.
    set (eq_correct x a).
    case_eq (eq_A x a); boolSpec_simpl; simpl.
    - my_auto.
    - fold (lookup eq_A E a).
      set (IH E a).
      case_eq (lookup eq_A E a).
      * intros ? Heq.
        rewrite Heq in *; my_auto.
      * intros Heq.
        rewrite Heq in *.
        intros ?; inversion 1; firstorder.
Qed.

Definition lookup_unique {A B : Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall (C : context A B) a,
    optionUnique (lookup eq_A C a) (D.lookup C a).
Proof.
  intros eq_A_correct.
  fix IH 1.
  intros C a; destruct C;
  unfold_goal; simpl.
  - my_auto.
  - inversion 1; subst.
    + set (eq_A_correct a a); boolSpec_destruct; my_auto.
    + set (eq_A_correct x a); boolSpec_destruct.
      * my_auto.
      * eapply IH; eassumption.
Qed.

Lemma disjoint_cons_left_lookup {A B1 B2: Set} {a} {b} {C1 : context A B1} {C2 : context A B2} :
  D.disjoint (add C1 a b) C2 -> forall b', neg (D.lookup C2 a b').
Proof.
  intros Hdisjoint.
  assert (D.lookup (add C1 a b) a b) as Hlookup by constructor.
  exact (fun _ => Hdisjoint _ _ _ Hlookup).
Qed.

Lemma disjoint_cons_left_lookup_inv {A B1 B2: Set} {a} {b} {C1 : context A B1} {C2 : context A B2} :
  D.disjoint C1 C2 -> (forall b, neg (D.lookup C2 a b)) -> D.disjoint (add C1 a b) C2.
Proof.
  intros Hdisjoint Hnlookup.
  intros ? ? ?.
  inversion 1; subst.
  - apply Hnlookup.
  - eapply Hdisjoint.
    eassumption.
Qed.


Lemma disjoint_weaken {A B1 B2: Set} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall {p}
         {C1 : context A B1}
         {C2 : context A B2},
    D.disjoint (p :: C1) C2 ->
    D.disjoint       C1  C2.
Proof.
  intros eq_A_correct [? ?] ? ? Hdisjoint a' ? ? ?.
  set (eq_A_correct a a'); boolSpec_destruct; my_auto;
  eapply (Hdisjoint a');
  econstructor (eassumption).
Qed.  

Lemma disjoint_cons_left {A B1 B2: Set} p {C1 C1' : context A B1} {C2 : context A B2} :
  D.disjoint (p :: C1 ) C2 ->
  D.disjoint       C1'  C2 ->
  D.disjoint (p :: C1') C2.
Proof.
  intros; destruct p.
  eapply disjoint_cons_left_lookup_inv.
  - assumption.
  - eapply disjoint_cons_left_lookup; eassumption.
Qed.

Lemma disjoint_app {A B1 B2: Set} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall {C1 C1' : context A B1}
         {C2     : context A B2},
    D.disjoint  C1         C2 ->
    D.disjoint        C1'  C2 ->
    D.disjoint (C1 ++ C1') C2.
Proof.
  intros eq_A_correct C1 C1' C2 H1 H1'.
  induction C1.
  - my_auto.
  - assert (D.disjoint C1 C2) as H by (eapply disjoint_weaken; eassumption).
    eapply disjoint_cons_left.
    + eassumption.
    + intuition.
Qed.

Definition context_ind {A B: Set} (P : context A B -> Type) :
  (P nil) ->
  (forall a b C, P C -> P (add C a b)) ->
  (forall C, P C).
Proof.
  intros Hnil Hcons.
  induction C as [|[? ?]].
  + exact Hnil.
  + eapply Hcons; assumption.
Qed.

Lemma remove_var_complete {A B: Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall a (C : context A B) a' b', 
    neg (a = a') ->
    D.lookup C a' b' ->
    D.lookup (remove_var eq_A a C) a' b'.
Proof.
  intros eq_A_correct.
  induction C as [|[? ?] C IH]; simpl.
  - inversion 2.
  - inversion 2;
    match goal with
    | [|- context[eq_A ?a1 ?a2]] => set (eq_A_correct a1 a2); boolSpec_destruct
    end; my_auto.
Qed.

Lemma remove_var_sound {A B: Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall a (C : context A B) a' b',
    neg (a = a') ->
    D.lookup (remove_var eq_A a C) a' b' ->
    D.lookup C a' b'.
Proof.
  intros eq_A_correct ? ? ? ? ?.
  induction C as [|[? ?] C IH]; simpl.
  - inversion 1.
  - match goal with
    | [|- context[eq_A ?a1 ?a2]] => set (eq_A_correct a1 a2); boolSpec_destruct; my_auto
    end.
    inversion 1; my_auto.
Qed.

Lemma remove_var_lookup {A B: Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall a (C : context A B) b, neg (D.lookup (remove_var eq_A a C) a b).
Proof.
  intros eq_A_correct.
  induction C as [|[? ?] C IH]; simpl.
  - inversion 1.
  - match goal with
    | [|- context[eq_A ?a1 ?a2]] => set (eq_A_correct a1 a2); boolSpec_destruct; my_auto
    end.
    inversion 1; my_auto; firstorder.
Qed.

Lemma linearize_sound {A B: Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall (C : context A B) a' b',
    D.lookup (linearize eq_A C) a' b' ->
    D.lookup C a' b'.
Proof.
  intros eq_A_correct.
  induction C as [|[? ?]]; simpl.
  - inversion 1.
  - inversion 1; subst.
    + constructor.
    + constructor 2.
      * assumption.
      * apply IHC.
        eapply remove_var_sound; eassumption.
Qed.

Lemma linearize_complete {A B: Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall (C : context A B) a' b',
    D.lookup C a' b' ->
    D.lookup (linearize eq_A C) a' b'.
Proof.
  intros eq_A_correct.
  induction C as [|[? ?]]; simpl.
  - inversion 1.
  - inversion 1; subst.
    + constructor.
    + constructor 2.
      * assumption.
      * eapply remove_var_complete; my_auto.
Qed.  

Lemma linear_remove_var {A B: Set} {eq_A : A -> A -> bool} a (C : context A B) :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  D.linear C -> D.linear (remove_var eq_A a C).
Proof.
  intros eq_A_correct.
  induction C as [|[? ?]]; simpl.
  - my_auto.
  - match goal with
    | [|- context[eq_A ?a1 ?a2] ] => set (eq_A_correct a1 a2); boolSpec_destruct
    end.
    + inversion 1; my_auto.
    + inversion 1; subst.
      constructor.
      * intros ? ?.
        match goal with
        | [H : forall _, neg (D.lookup C _ _) |- _] =>
            eapply H;
            eapply remove_var_sound;
            eassumption
        end.
      * my_auto.
Qed.

Lemma linearize_linear {A B: Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->  
  forall (C : context A B), D.linear (linearize eq_A C).
Proof.
  intros eq_A_correct.
  induction C as [|[? ?]]; simpl.
  - constructor.
  - econstructor.
    + apply remove_var_lookup; assumption.
    + apply linear_remove_var; assumption.
Qed.

Definition all_linear_correct {A B: Set} {eq_A : A -> A -> bool} {p : A -> B -> bool} {P : A -> B -> Type} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x y, boolSpec (p    x y) (P x y)) ->
  forall C, D.linear C -> boolSpec (all_linear eq_A p C) (forall a b, D.lookup C a b -> P a b).
Proof.
  intros eq_A_correct p_correct.
  induction C as [| [a b] C IH];
  unfold_goal; simpl; unfold andb.
  - my_auto.
  - match goal with
    | [|- context[p ?a1 ?a2] ] => set (p_correct a1 a2) as HP; boolSpec_destruct
    end.
    + inversion 1 as [| ? ? ? ? Hlinear]; subst.
      match goal with
      | [|- context[all_linear eq_A p ?C] ] =>
          set (IH Hlinear); boolSpec_destruct
      end.
      inversion 1; my_auto.
      intros Hlookup.
      apply (IH Hlinear); intros.
      apply Hlookup.
      constructor 2.
      * intros ?; subst; firstorder.
      * assumption.
    + intros Hlinear Hlookup.
      apply HP.
      apply Hlookup.
      constructor.
Qed.

Lemma all_correct {A B: Set} {eq_A : A -> A -> bool} {p : A -> B -> bool} {P : A -> B -> Type} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x y, boolSpec (p    x y) (P x y)) ->
  forall C, boolSpec (all eq_A p C) (forall a b, D.lookup C a b -> P a b).
Proof.
  intros eq_A_correct p_correct C.
  do 2 unfold_goal.
  set (all_linear_correct eq_A_correct p_correct _ (linearize_linear eq_A_correct C)) as H; boolSpec_destruct; intros.
  - apply H.
    apply linearize_complete; assumption.
  - intros Hlookup.
    apply H; intros.
    apply Hlookup.
    eapply linearize_sound; eassumption.
Qed.

Lemma sub_p_correct_aux {A B : Set} {eq_A} {p} {equiv_B} {P : A -> Type} {E : B -> B -> Type}:
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x, boolSpec (p x) (P x)) ->
  (forall x y, boolSpec (equiv_B x y) (E x y)) ->
  forall (C1 C2 : context A B) a b,
    boolSpec ((fun a b =>
                 if p a
                   then match lookup eq_A C2 a with
                        | Some b' => equiv_B b b'
                        | None    => false
                        end
                   else true) a b) (P a -> {b' : B & D.lookup C2 a b' * E b b'}).
Proof.
  intros eq_A_correct p_correct equiv_B_correct C1 C2 a b.
  unfold_goal.
  set (p_correct a) as Hp; boolSpec_destruct; [|my_auto].
  set (lookup_correct eq_A_correct C2 a) as Hlookup; optionSpec_destruct_hyp b'.
  - set (equiv_B_correct b b') as Hequiv; boolSpec_destruct.
    + eauto.
    + intros H'.
      destruct (H' Hp) as [? [H'' ?]].
      set (lookup_functional Hlookup H'').
      congruence.
  - intros H'.
    destruct (H' Hp) as [? [H'' ?]].
    exact (Hlookup _ H'').
Qed.

Lemma sub_p_correct {A B: Set} {eq_A : A -> A -> bool} {p : A -> bool} {equiv_B : B -> B -> bool} {P} {E} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x, boolSpec (p x) (P x)) ->
  (forall x y, boolSpec (equiv_B x y) (E x y)) ->
  forall (C1 C2 : context A B), boolSpec (sub_p eq_A p equiv_B C1 C2) (D.subP P E C1 C2).
Proof.
  intros eq_A_correct p_correct equiv_B_correct C1 C2.
  do 2 unfold_goal.
  set (all_correct eq_A_correct (sub_p_correct_aux eq_A_correct p_correct equiv_B_correct C1 C2) C1);
  boolSpec_destruct; unfold_goal; intuition.
Qed.

Lemma subP_sub {A B} E (C1 C2 : context A B):
  D.subP (fun _ => True) E C1 C2 -> D.sub E C1 C2.
Proof. unfold D.sub; intuition. Qed.

Lemma sub_subP {A B} E (C1 C2 : context A B):
  D.sub E C1 C2 -> D.subP (fun _ => True) E C1 C2.
Proof. unfold D.subP; intuition. Qed.

Lemma sub_correct {A B: Set} {eq_A : A -> A -> bool} {equiv_B : B -> B -> bool} {E} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x y, boolSpec (equiv_B x y) (E x y)) ->
  forall (C1 C2 : context A B), boolSpec (sub eq_A equiv_B C1 C2) (D.sub E C1 C2).
Proof.
  intros eq_A_correct equiv_B_correct C1 C2.
  assert (forall x : A, boolSpec ((fun _ => true) x) ((fun _ => True) x)) as p_correct by my_auto.
  set (sub_p_correct eq_A_correct p_correct equiv_B_correct C1 C2); unfold sub; boolSpec_destruct; simpl; unfold neg in *;
  [generalize (subP_sub E C1 C2)|generalize (sub_subP E C1 C2)];
  intuition.
Qed.

Lemma equiv_p_correct {A B: Set} {eq_A : A -> A -> bool} {p : A -> bool} {equiv_B : B -> B -> bool} {P} {E} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x, boolSpec (p x) (P x)) ->
  (forall x y, boolSpec (equiv_B x y) (E x y)) ->
  forall (C1 C2 : context A B), boolSpec (equiv_p eq_A p equiv_B C1 C2) (D.equivP P E C1 C2).
Proof.
  intros eq_A_correct p_correct equiv_B_correct C1 C2.
  do 2 unfold_goal.
  set (sub_p_correct eq_A_correct p_correct equiv_B_correct C1 C2); boolSpec_destruct.
  - set (sub_p_correct eq_A_correct p_correct equiv_B_correct C2 C1); boolSpec_destruct.
    + my_auto.
    + my_auto.
  - my_auto.
Qed.
  

Lemma equiv_correct {A B: Set} {eq_A : A -> A -> bool} {equiv_B : B -> B -> bool} {E} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x y, boolSpec (equiv_B x y) (E x y)) ->
  forall (C1 C2 : context A B), boolSpec (equiv eq_A equiv_B C1 C2) (D.equiv E C1 C2).
Proof.
  intros eq_A_correct equiv_B_correct C1 C2.
  do 2 unfold_goal.
  set (sub_correct eq_A_correct equiv_B_correct C1 C2); boolSpec_destruct.
  - set (sub_correct eq_A_correct equiv_B_correct C2 C1); boolSpec_destruct.
    + my_auto.
    + my_auto.
  - my_auto.
Qed.
