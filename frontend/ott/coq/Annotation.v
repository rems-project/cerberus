Require Import AilSyntax.
Require Import GenTypes.

Record annotation {T1 T2 : Set} := make_annotation {
  add_type : genTypeCategory -> T1 -> T2;
  get_type : T2 -> genTypeCategory;
  id_add_get : forall gt x, get_type (add_type gt x) = gt
}.
Arguments annotation : default implicits.

Definition type_of {A1 A2 : Set} (A : annotation A1 A2) (e : expression A2) :=
  let '(AnnotatedExpression a _) := e in
  get_type A a.

Definition concrete_annotation {A} : annotation A genTypeCategory := {|
  add_type   := fun gtc _ => gtc;
  get_type   := id;
  id_add_get := fun _ _ => eq_refl
|}.
