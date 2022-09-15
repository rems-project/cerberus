Require Import Coq.Lists.List.
From ExtLib.Structures Require Import Monad Monads.

Import ListNotations.
Import MonadNotation.

Local Open Scope list_scope.
Local Open Scope monad_scope.

Definition list_init {A:Type}: nat -> (nat -> A) -> list A.
Proof. Admitted. (* TODO *)

Definition fold_left2 {A B C:Type} : (A -> B -> C -> A) -> A -> list B -> list C -> A.
Proof. Admitted. (* TODO *)

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

Definition monadic_fold_left2
  {A B C:Type}
  {m : Type -> Type}
  {M : Monad m}
  : (A -> B -> C -> m A) -> A -> list B -> list C -> m A.
Proof. Admitted. (* TODO *)
