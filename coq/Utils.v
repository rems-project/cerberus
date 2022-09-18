Require Import Coq.Lists.List.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Numbers.BinNums.
From Coq.Strings Require Import Byte.

From ExtLib.Structures Require Import Monad Monads.

Import ListNotations.
Import MonadNotation.

Local Open Scope list_scope.
Local Open Scope monad_scope.

Fixpoint list_init {A:Type} (n:nat) (f:nat -> A): list A
  :=
  match n with
  | O => []
  | S n => (f n) :: list_init n f
  end.

(** Inlike OCaml version if lists have different sizes, we just terminate
    after consuming the shortest one, without signaling error *)
Fixpoint fold_left2 {A B C:Type} (f: A -> B -> C -> A) (accu:A) (l1:list B) (l2:list C): A :=
  match l1, l2 with
  | a1::l1, a2::l2 => fold_left2 f (f accu a1 a2) l1 l2
  | _, _ => accu
  end.

Definition mem {A:Type} `{forall (x y:A), Decidable (x = y)} (a:A): (list A) -> bool
  := List.existsb (fun e => decide (e = a)).

Definition mapi {A B: Type} (f: nat -> A -> B) (l:list A) : list B :=
  let fix map_ n (l:list A) :=
    match l with
    | [] => []
    | a :: t => (f n a) :: (map_ (S n) t)
    end
  in map_ O l.

(* c.f.
   List.fold_left
     : forall A B : Type, (A -> B -> A) -> list B -> A -> A
 *)
Fixpoint monadic_fold_left
  {A B : Type}
  {m : Type -> Type}
  {M : Monad m}
  (f : A -> B -> m A) (l : list B) (a : A)
  : m A
  := match l with
     | List.nil => ret a
     | List.cons b l =>
         a' <- f a b ;;
         monadic_fold_left f l a'
     end.

Fixpoint monadic_fold_left2
  {A B C:Type}
  {m : Type -> Type}
  {M : Monad m}
  (f: A -> B -> C -> m A)
  (accu:A)
  (l1:list B)
  (l2:list C)
  : m A
  :=
  match l1, l2 with
  | a1::l1, a2::l2 =>
      accu' <- f accu a1 a2 ;;
      monadic_fold_left2 f accu' l1 l2
  | _, _ => ret accu
  end.

Definition maybeEqualBy
  {A: Type}
  (f: A -> A -> bool)
  (a: option A)
  (b: option A)
  : bool
  :=
  match a,b with
  | None, None => true
  | Some a, Some b => f a b
  | _, _ => false
  end.

(* TODO *)
Definition byte_of_Z: Z -> byte.
Proof. admit. Admitted.

(* TODO: Z.extract_num *)
Definition extract_num: Z -> Z -> Z -> Z.
Proof. admit. Admitted.
