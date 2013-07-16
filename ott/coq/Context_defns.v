Require Import Common.
Require Import Context.

Inductive lookup {A B : Set} : context A B -> A -> B -> Type :=
  | Lookup_hd     a b C :                           lookup ((a,b) :: C) a b
  | Lookup_tl x y a b C : x <> a -> lookup C a b -> lookup ((x,y) :: C) a b.

Definition mem {A B} a (C : context A B) := {b : B & lookup C a b}.

Definition fresh {A B} a (C : context A B) := neg (mem a C).

Definition freshBindings {A B1 B2 : Set} (bs : list (A * B1)) (C : context A B2) := allList (fun b => fresh (fst b) C) bs.

Definition disjoint {A B1 B2 : Set} (C1 : context A B1) (C2 : context A B2) : Type :=
  forall (a : A), mem a C1 -> mem a C2 -> False.

Definition subP {A B1 B2: Set} (P : A -> Type) (E : B1 -> B2 -> Type) (C1 : context A B1) (C2 : context A B2) :=
  forall id, P id -> forall b1, lookup C1 id b1 -> {b2 : B2 & lookup C2 id b2 * E b1 b2}.

Definition sub {A B1 B2: Set} (E : B1 -> B2 -> Type) (C1 : context A B1) (C2 : context A B2) :=
  forall id, forall b1, lookup C1 id b1 -> {b2 : B2 & lookup C2 id b2 * E b1 b2}.

Definition equivP {A B1 B2: Set} (P : A -> Type) (E : B1 -> B2 -> Type) (C1 : context A B1) (C2 : context A B2) :=
  subP P E C1 C2 * subP P (fun x y => E y x) C2 C1.

Definition equiv {A B1 B2: Set} (E : B1 -> B2 -> Type) (C1 : context A B1) (C2 : context A B2) :=
  sub E C1 C2 * sub (fun x y => E y x) C2 C1.

Inductive linear {A B: Set} : context A B -> Type :=
  | Linear_nil        : linear nil
  | Linear_cons a b C : (forall b, neg (lookup C a b)) -> linear C -> linear (add a b C).

Inductive freshInBindings {A B : Set} : A -> list (A * B) -> Prop :=
 | FreshInBindings_nil a' :
     freshInBindings a' nil
 | FreshInBindings_cons a' a b bs :
     neg (a' = a) ->
     freshInBindings a' bs ->
     freshInBindings a' ((a, b) :: bs).

Inductive disjointBindings {A B : Set} : list (A * B) -> Prop :=
 | DisjointBindings_nil :
     disjointBindings nil
 | DisjointBindings_cons a b xs :
     freshInBindings a xs ->
     disjointBindings xs ->
     disjointBindings ((a, b) :: xs).
