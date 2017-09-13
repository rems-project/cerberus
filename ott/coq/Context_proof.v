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

Lemma mem_correct {A B} {eq_A} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall a (C : context A B), boolSpec (mem eq_A a C) (D.mem a C).
Proof.
  intros eq_A_correct a C.
  unfold mem.
  pose proof (lookup_correct eq_A_correct C a).
  optionSpec_destruct; firstorder.
Qed.

Lemma fresh_correct {A B} {eq_A} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall a (C : context A B), boolSpec (fresh eq_A a C) (D.fresh a C).
Proof.
  intros eq_A_correct a C.
  unfold fresh.
  pose proof (mem_correct eq_A_correct a C) as H.
  boolSpec_destruct; firstorder.
Qed.

Lemma fresh_bindings_correct {A B1 B2 : Set} {eq_A} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall (bs : list (A * B1)) (C : context A B2),
  boolSpec (fresh_bindings eq_A bs C) (D.freshBindings bs C).
Proof.
  intros eq_A_correct bs C.
  exact (all_list_correct (fun b => fresh_correct eq_A_correct (fst b) C) bs).
Qed.

Lemma disjoint_cons_left_lookup {A B1 B2: Set} {a} {b} {C1 : context A B1} {C2 : context A B2} :
  D.disjoint (add a b C1) C2 -> D.fresh a C2.
Proof.
  intros Hdisjoint.
  assert (D.lookup (add a b C1) a b) as Hlookup by constructor.
  exact (Hdisjoint a (ex_intro _ b (D.Lookup_hd a b C1))).
Qed.

Lemma disjoint_cons_left_lookup_inv {A B1 B2 : Set} {a} {b} {C1 : context A B1} {C2 : context A B2} :
  D.disjoint C1 C2 -> D.fresh a C2 -> D.disjoint (add a b C1) C2.
Proof.
  intros Hdisjoint Hfresh.
  unfold D.disjoint.
  unfold D.mem.
  intros ? [? H] [? ?].
  inversion H; subst.
  apply Hfresh.
  eexists; eassumption.
  eapply Hdisjoint; eexists; eassumption.
Qed.

Lemma disjoint_weaken {A B1 B2: Set} {eq_A} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  forall {p}
         {C1 : context A B1}
         {C2 : context A B2},
    D.disjoint (p :: C1) C2 ->
    D.disjoint       C1  C2.
Proof.
  intros eq_A_correct [? ?] ? ? Hdisjoint a' [? ?] [? ?].
  set (eq_A_correct a a'); boolSpec_destruct; my_auto; (
    eapply (Hdisjoint a'); [
        eexists; finish eassumption
      | repeat econstructor; eassumption
    ]
  ).
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

Lemma disjoint_freshBindings {A B1 B2 : Set} {C2 : context A B2} :
  forall {bs : list (A * B1)}
         (HdisjointBindings : D.disjointBindings bs)
         (Hfresh : D.freshBindings bs C2)
         {C1 : context A B1}
         (Hdisjoint : D.disjoint C1 C2),
    D.disjoint (add_bindings bs C1) C2.
Proof.
  induction bs as [| [? ?]]; intros.
  - assumption.
  - eapply IHbs.
    + inversion_clear HdisjointBindings; assumption.
    + inversion_clear Hfresh; assumption.
    + eapply disjoint_cons_left_lookup_inv.
      * assumption.
      * inversion_clear Hfresh; assumption.
Qed.

Definition context_ind {A B: Set} (P : context A B -> Type) :
  (P nil) ->
  (forall a b C, P C -> P (add a b C)) ->
  (forall C, P C).
Proof.
  intros Hnil Hcons.
  induction C as [|[? ?]].
  + exact Hnil.
  + eapply Hcons; assumption.
Qed.

Lemma remove_var_complete {A B: Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall {a} {C : context A B} {a'} {b'}, 
    a <> a' ->
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
  forall {a} {C : context A B} {a'} {b'},
    a <> a' ->
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
  forall a (C : context A B) b, ~ D.lookup (remove_var eq_A a C) a b.
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
  forall {C : context A B} {a'} {b'},
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
  forall {C : context A B} {a'} {b'},
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

Lemma linear_remove_var {A B: Set} {eq_A : A -> A -> bool} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall a {C : context A B},
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
        | H : forall _, ~ D.lookup C _ _ |- _ =>
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

Definition all_linear_correct {A B: Set} {eq_A : A -> A -> bool} {p : A -> B -> bool} {P : A -> B -> Prop} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x y, boolSpec (p    x y) (P x y)) ->
  forall {C}, D.linear C -> boolSpec (all_linear p C) (forall a b, D.lookup C a b -> P a b).
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
      | [|- context[all_linear p ?C] ] =>
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

Lemma all_correct {A B: Set} {eq_A : A -> A -> bool} {p : A -> B -> bool} {P : A -> B -> Prop} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x y, boolSpec (p    x y) (P x y)) ->
  forall C, boolSpec (all eq_A p C) (forall a b, D.lookup C a b -> P a b).
Proof.
  intros eq_A_correct p_correct C.
  do 2 unfold_goal.
  set (all_linear_correct eq_A_correct p_correct (linearize_linear eq_A_correct C)) as H; boolSpec_destruct; intros.
  - apply H.
    apply linearize_complete; assumption.
  - intros Hlookup.
    apply H; intros.
    apply Hlookup.
    eapply linearize_sound; eassumption.
Qed.

Lemma sub_p_correct_aux {A B1 B2 : Set} {eq_A} {p} {equiv_B} {P : A -> Prop} {E : A -> B1 -> B2 -> Prop}:
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x, boolSpec (p x) (P x)) ->
  (forall a x y, boolSpec (equiv_B a x y) (E a x y)) ->
  forall (C1 : context A B1) (C2 : context A B2) a b1,
    boolSpec ((fun a b1 =>
                 if p a
                   then match lookup eq_A C2 a with
                        | Some b2 => equiv_B a b1 b2
                        | None    => false
                        end
                   else true) a b1) (P a -> exists b2 : B2, D.lookup C2 a b2 /\ E a b1 b2).
Proof.
  intros eq_A_correct p_correct equiv_B_correct C1 C2 a b1.
  unfold_goal.
  pose proof (p_correct a) as Hp; boolSpec_destruct; [|my_auto].
  pose proof (lookup_correct eq_A_correct C2 a) as Hlookup; optionSpec_destruct_hyp b2.
  - pose proof (equiv_B_correct a b1 b2) as Hequiv; boolSpec_destruct.
    + eauto.
    + intros H'.
      destruct (H' Hp) as [? [H'' ?]].
      set (lookup_functional Hlookup H'').
      congruence.
  - intros H'.
    destruct (H' Hp) as [? [H'' ?]].
    exact (Hlookup _ H'').
Qed.

Lemma sub_p_correct {A B1 B2: Set} {eq_A : A -> A -> bool} {p : A -> bool} {equiv_B : A -> B1 -> B2 -> bool} {P} {E} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x, boolSpec (p x) (P x)) ->
  (forall a x y, boolSpec (equiv_B a x y) (E a x y)) ->
  forall (C1 : context A B1) (C2 : context A B2), boolSpec (sub_p eq_A p equiv_B C1 C2) (D.subP P E C1 C2).
Proof.
  intros eq_A_correct p_correct equiv_B_correct C1 C2.
  do 2 unfold_goal.
  set (all_correct eq_A_correct (sub_p_correct_aux eq_A_correct p_correct equiv_B_correct C1 C2) C1);
  boolSpec_destruct; unfold_goal; intuition.
Qed.

Lemma subP_sub {A B1 B2} E (C1 : context A B1) (C2 : context A B2):
  D.subP (fun _ => True) E C1 C2 -> D.sub E C1 C2.
Proof. unfold D.sub; intuition. Qed.

Lemma sub_subP {A B1 B2} E (C1 : context A B1) (C2 : context A B2):
  D.sub E C1 C2 -> D.subP (fun _ => True) E C1 C2.
Proof. unfold D.subP; intuition. Qed.

Lemma sub_correct {A B1 B2: Set} {eq_A : A -> A -> bool} {equiv_B : A -> B1 -> B2 -> bool} {E} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall a x y, boolSpec (equiv_B a x y) (E a x y)) ->
  forall (C1 : context A B1) (C2 : context A B2), boolSpec (sub eq_A equiv_B C1 C2) (D.sub E C1 C2).
Proof.
  intros eq_A_correct equiv_B_correct C1 C2.
  assert (forall x : A, boolSpec ((fun _ => true) x) ((fun _ => True) x)) as p_correct by my_auto.
  set (sub_p_correct eq_A_correct p_correct equiv_B_correct C1 C2); unfold sub; boolSpec_destruct; simpl;
  [generalize (subP_sub E C1 C2)|generalize (sub_subP E C1 C2)];
  intuition.
Qed.

Lemma equiv_p_correct {A B1 B2: Set} {eq_A : A -> A -> bool} {p : A -> bool} {equiv_B : A -> B1 -> B2 -> bool} {P} {E} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall x, boolSpec (p x) (P x)) ->
  (forall a x y, boolSpec (equiv_B a x y) (E a x y)) ->
  forall (C1 : context A B1) (C2 : context A B2), boolSpec (equiv_p eq_A p equiv_B C1 C2) (D.equivP P E C1 C2).
Proof.
  intros eq_A_correct p_correct equiv_B_correct C1 C2.
  do 2 unfold_goal.
  set (sub_p_correct eq_A_correct p_correct equiv_B_correct C1 C2); boolSpec_destruct.
  - set (sub_p_correct eq_A_correct p_correct (fun a x y => equiv_B_correct a y x) C2 C1); boolSpec_destruct; my_auto.
  - my_auto.
Qed.
  
Lemma equiv_correct {A B1 B2: Set} {eq_A : A -> A -> bool} {equiv_B : A -> B1 -> B2 -> bool} {E} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  (forall a x y, boolSpec (equiv_B a x y) (E a x y)) ->
  forall (C1 : context A B1) (C2 : context A B2), boolSpec (equiv eq_A equiv_B C1 C2) (D.equiv E C1 C2).
Proof.
  intros eq_A_correct equiv_B_correct C1 C2.
  do 2 unfold_goal.
  set (sub_correct eq_A_correct equiv_B_correct C1 C2); boolSpec_destruct.
  - set (sub_correct eq_A_correct (fun a x y => equiv_B_correct a y x) C2 C1); boolSpec_destruct; my_auto.
  - my_auto.
Qed.

Lemma equivP_refl {A B : Set} {P : A -> Prop} {E : A -> B -> B -> Prop} (C : context A B) :
  (forall a b, P a -> E a b b) ->
  D.equivP P E C C.
Proof. split; intros a Hp b Hlookup; exists b; firstorder. Qed.

Lemma equivP_symm {A B1 B2 : Set} {P : A -> Prop} {E : A -> B1 -> B2 -> Prop} {C1 : context A B1} {C2 : context A B2} :
  D.equivP P E C1 C2 ->
  D.equivP P (fun a x y => E a y x) C2 C1.
Proof.
  split; intros a Hp b Hlookup;
  [apply proj2 in H | apply proj1 in H];
  destruct (H a Hp b Hlookup) as [b' ?];
  exists b'; intuition.
Qed.

Definition disjoint_correct {A B1 B2} {eq_A} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall (C1 : context A B1) (C2 : context A B2),
    boolSpec (disjoint eq_A C1 C2) (D.disjoint C1 C2).
Proof.
  intros eq_A_correct C1 C2.
  induction C1; unfold_goal; simpl.
  - intros ? [? H1]; inversion H1.
  - do 2 context_destruct.
    case_fun (lookup_correct eq_A_correct C2 a).
    + intros Hdisjoint; eapply Hdisjoint; eexists; finish eassumption.
    + boolSpec_destruct.
      * intros ? [? H1]; inversion H1; subst; firstorder.
      * intros Hdisjoint.
        apply IHC1.
        intros a' [? H1] [? H2].
        pose proof (eq_A_correct a a').
        boolSpec_destruct; my_auto; [
            firstorder
          | eapply Hdisjoint; eexists; [econstructor 2|]; eassumption
        ].
Qed.

Lemma fresh_in_bindings_correct {A B : Set} {eq_A} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall a (xs : list (A * B)), boolSpec (fresh_in_bindings eq_A a xs) (D.freshInBindings a xs).
Proof.
  intros eq_A_correct a xs.
  do 2 unfold_goal.
  pose proof (all_list_correct (fun (x : A * B) => negb_correct (eq_A_correct a (fst x))) xs) as H.
  boolSpec_destruct.
  - induction xs as [| [? ?]].
    + constructor.
    + inversion_clear H.
      constructor.
      * assumption.
      * apply IHxs; assumption.
  - induction xs as [| [? ?]].
    + intros _; apply H; constructor.
    + inversion_clear 1.
      apply IHxs.
      * intros ?; apply H; constructor; assumption.
      * assumption.
Qed.

Lemma disjoint_bindings_correct {A B : Set} {eq_A} :
  (forall x y, boolSpec (eq_A x y) (x = y)) ->
  forall (xs : list (A * B)), boolSpec (disjoint_bindings eq_A xs) (D.disjointBindings xs).
Proof.
  intros eq_A_correct xs.
  induction xs as [|[? ?]]; simpl;
  unfold boolSpec; unfold andb;
  repeat match goal with
  | |- fresh_in_bindings _ ?a ?xs = _ -> _ => case_fun (fresh_in_bindings_correct eq_A_correct a xs)
  | |- disjoint_bindings _ _ = _ -> _ => case_fun IHxs
  | _ => context_destruct
  end; my_auto.    
Qed.  

Lemma fresh_equiv {A B1 B2 : Set} {C1 : context A B1} {C2 : context A B2} :
    D.equiv (fun _ _ _ => True) C1 C2 ->
    forall {a},
      D.fresh a C1 ->
      D.fresh a C2.
Proof.
  intros Hequiv ? Hfresh1 [? Hlookup2].
  destruct ((proj2 Hequiv) _ _ Hlookup2) as [? [Hlookup1 _]].
  eapply Hfresh1; eexists; eassumption.
Qed.

Lemma freshBindings_equiv {A B1 B2 B : Set} {C1 : context A B1} {C2 : context A B2} :
  D.equiv (fun _ _ _ => True) C1 C2 ->
  forall {bs : list (A * B)},
    D.freshBindings bs C1 ->
    D.freshBindings bs C2.
Proof.
  intros Hequiv bs HfreshBindings1.
  induction bs.
  - constructor.
  - inversion_clear HfreshBindings1.
    constructor.
    * eapply fresh_equiv; eassumption.
    * apply IHbs; assumption.
Qed.

Lemma equiv_weaken {A B1 B2 : Set} (P Q : B1 -> B2 -> Prop) :
  (forall {b1 b2}, P b1 b2 -> Q b1 b2) ->
  forall {C1 : context A B1} {C2 : context A B2},
    D.equiv (fun _ => P) C1 C2 ->
    D.equiv (fun _ => Q) C1 C2.
Proof. firstorder. Qed.

Lemma mapP_linear_correct {A B1 B2 : Set} {P : A -> B1 -> Prop} {E : A -> B1 ->  B2 -> Prop} {eq_A} {p : A -> B1 -> option B2} :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  (forall a b1,
     match p a b1 with
     | Some b2 => P a b1 /\ E a b1 b2
     | None    => ~ P a b1 \/ P a b1 /\ forall b2, ~ E a b1 b2
     end) ->
  forall {C1 : context A B1},
    D.linear C1 ->
    match mapP_linear p C1 with
    | Some C2 => (forall a b1, D.lookup C1 a b1 -> P a b1) /\ D.equiv E C1 C2
    | None    => exists a b1, D.lookup C1 a b1 /\ (~ P a b1 \/ P a b1 /\ forall b2, ~ E a b1 b2)
    end.
Proof.
  intros eq_A_correct p_correct.
  induction C1 as [|[a b1] C1]; intros Hlinear; simpl.
  - now my_auto.
  - pose proof (p_correct a b1).
    destruct (p a b1) as [b2|].
    + destruct (mapP_linear p C1) as [C2|].
      * split.
          intros a' b1' Hlookup1.
          pose proof (eq_A_correct a a'); boolSpec_destruct; [subst|].
            inversion Hlookup1; now my_auto.

            inversion Hlookup1; subst; [congruence|].
            destruct IHC1 as [Hsub _].
            inversion_clear Hlinear; assumption.
            apply Hsub; assumption.

            split.
              intros a' b1' Hlookup1.
              pose proof (eq_A_correct a a'); boolSpec_destruct; [subst|].
                inversion Hlookup1; [|congruence]; subst.
                exists b2; now my_auto.

                inversion Hlookup1; [congruence|]; subst.  
                destruct IHC1 as [? [Hsub _]].
                inversion_clear Hlinear; assumption.
                destruct (Hsub a' b1') as [b2' ?]; [assumption|].
                exists b2'; now my_auto.

          intros a' b2' Hlookup1.
          inversion Hlookup1; subst.
            eexists; now my_auto.

            destruct IHC1 as [_ [_ Hsub]].
            inversion_clear Hlinear; assumption.
            destruct (Hsub a' b2') as [b1' ?]; [assumption|].
            exists b1'; now my_auto.
      * destruct IHC1 as [a' [b1' [Hlookup1 ?]]].
        inversion_clear Hlinear; assumption.
        pose proof (eq_A_correct a a'); boolSpec_destruct; [subst|].
          inversion Hlinear; subst.
          now firstorder.

          exists a'.
          exists b1'.
          now my_auto.
    + exists a.
      exists b1.
      intuition; now my_auto.
Qed.

Lemma mapP_correct {A B1 B2 : Set} {P : A -> B1 -> Prop} {E : A -> B1 ->  B2 -> Prop} {eq_A} (p : A -> B1 -> option B2) :
  (forall x y : A, boolSpec (eq_A x y) (x = y)) ->
  (forall a b1,
     match p a b1 with
     | Some b2 => P a b1 /\ E a b1 b2
     | None    => ~ P a b1 \/ P a b1 /\ forall b2, ~ E a b1 b2
     end) ->
  forall (C1 : context A B1),
    match mapP eq_A p C1 with
    | Some C2 => (forall a b1, D.lookup C1 a b1 -> P a b1) /\ D.equiv E C1 C2
    | None    => exists a b1, D.lookup C1 a b1 /\ (~ P a b1 \/ P a b1 /\ forall b2, ~ E a b1 b2)
    end.
Proof.
  intros eq_A_correct p_correct C1.
  unfold mapP.
  pose proof (mapP_linear_correct eq_A_correct p_correct (linearize_linear eq_A_correct C1)) as Hcorrect.
  destruct (mapP_linear p (linearize eq_A C1)).
  - split.
    + intros ? ? Hlookup1.
      apply (proj1 Hcorrect).
      exact (linearize_complete eq_A_correct Hlookup1).
    + split.
      * intros ? ? Hlookup1.
        apply (proj1 (proj2 Hcorrect)). 
        exact (linearize_complete eq_A_correct Hlookup1).
      * intros ? ? Hlookup2.
        destruct (proj2 (proj2 Hcorrect) _ _ Hlookup2) as [? [Hlookup1 ?]].
        apply (linearize_sound eq_A_correct) in Hlookup1.
        now firstorder.
  - destruct Hcorrect as [? [? [Hlookup1 ?]]].
    apply (linearize_sound eq_A_correct) in Hlookup1.
    now firstorder.
Qed.
