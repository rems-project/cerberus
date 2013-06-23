Require Import Common.

Definition context (A B : Set) := list (A * B).
Arguments context : default implicits.

Definition eq_context {A B} eq_A eq_B : context A B -> context A B -> bool :=
  eq_list (eq_pair eq_A eq_B).

Definition add {A B} (C : context A B) a b :=
  (a, b) :: C.

Definition lookup {A B : Set} (eq_A : A -> A -> bool) :=
  fix lookup (E : context A B) (a : A) : option B :=
    match E with
      | nil          => None
      | cons (x,b) E => if eq_A x a then Some b
                                    else lookup E a
    end.

Fixpoint remove_var {A B: Set} (eq_A : A -> A -> bool) a C : context A B :=
  match C with
  | nil             => nil
  | cons (a', b') C => if eq_A a a' 
                         then remove_var eq_A a C
                         else (a', b') :: remove_var eq_A a C
  end.

Fixpoint linearize {A B: Set} (eq_A : A -> A -> bool) C : context A B :=
  match C with
  | nil         => nil
  | (a, b) :: C => (a, b) :: remove_var eq_A a (linearize eq_A C)
  end.

Fixpoint all_linear {A B: Set} (eq_A : A -> A -> bool) (p : A -> B -> bool) C : bool :=
  match C with
  | nil         => true
  | (a, b) :: C => p a b && all_linear eq_A p C
  end.

Definition all {A B: Set} (eq_A : A -> A -> bool) (p : A -> B -> bool) C : bool :=
  all_linear eq_A p (linearize eq_A C).

Definition sub_p {A B: Set} (eq_A : A -> A -> bool) (p : A -> bool) (equiv_B : B -> B -> bool) (C1 C2 : context A B) :=
  all eq_A (fun a b =>
              if p a
                then match lookup eq_A C2 a with
                     | Some b' => equiv_B b b'
                     | None    => false
                     end
                else true) C1.

Definition sub {A B: Set} (eq_A : A -> A -> bool) (equiv_B : B -> B -> bool) :=
  sub_p eq_A (fun _ => true) equiv_B.

Definition equiv_p {A B: Set} (eq_A : A -> A -> bool) (p : A -> bool) (equiv_B : B -> B -> bool) (C1 C2 : context A B) :=
  sub_p eq_A p equiv_B C1 C2 && sub_p eq_A p equiv_B C2 C1.

Definition equiv {A B: Set} (eq_A : A -> A -> bool) (equiv_B : B -> B -> bool)  (C1 C2 : context A B) :=
  sub eq_A equiv_B C1 C2 && sub eq_A equiv_B C2 C1.
