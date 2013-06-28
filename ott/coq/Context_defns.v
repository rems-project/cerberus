Require Import Common.
Require Import Context.

Inductive lookup {A B : Set} : context A B -> A -> B -> Type :=
  | Lookup_hd     a b C :                           lookup ((a,b) :: C) a b
  | Lookup_tl x y a b C : x <> a -> lookup C a b -> lookup ((x,y) :: C) a b.

Definition disjoint {A B1 B2 : Set} C1 C2 : Type :=
  forall (a : A) (b1 : B1) (b2 : B2), lookup C1 a b1 -> lookup C2 a b2 -> False.

Definition subP {A B: Set} (P : A -> Type) (E : B -> B -> Type) (C1 C2 : context A B) :=
  forall id, P id -> forall b1, lookup C1 id b1 -> {b2 : B & lookup C2 id b2 * E b1 b2}.

Definition sub {A B: Set} (E : B -> B -> Type) (C1 C2 : context A B) :=
  forall id, forall b1, lookup C1 id b1 -> {b2 : B & lookup C2 id b2 * E b1 b2}.

Definition equivP {A B: Set} (P : A -> Type) (E : B -> B -> Type) (C1 C2 : context A B) :=
  subP P E C1 C2 * subP P E C2 C1.

Definition equiv {A B: Set} (E : B -> B -> Type) (C1 C2 : context A B) :=
  sub E C1 C2 * sub E C2 C1.

Inductive linear {A B: Set} : context A B -> Type :=
  | Linear_nil        : linear nil
  | Linear_cons a b C : (forall b, neg (lookup C a b)) -> linear C -> linear (add C a b).
