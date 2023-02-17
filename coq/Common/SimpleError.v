(** simple string error *)

Require Import Coq.Strings.String.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadExc.
Require Import ExtLib.Data.Monads.EitherMonad.

Notation serr := (sum string).

Local Instance Exception_serr : MonadExc string (serr) :=
  { raise := fun _ v => inl v
  ; catch := fun _ c h => match c with
                       | inl v => h v
                       | inr x => inr x
                       end
  }.

Definition option2serr {A: Type} (msg:string) (o:option A): (serr A)
  := match o with
     | Some v => ret v
     | None => raise msg
     end.

Definition sassert (b:bool) (msg:string) : serr unit
  := if b then ret tt else raise msg.
