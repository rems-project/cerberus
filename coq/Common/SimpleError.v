(** simple string error *)

Require Import Coq.Strings.String.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadExc.
Require Import ExtLib.Data.Monads.EitherMonad.

Require Import Coq.Relations.Relation_Definitions.

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

(* 'serr' type comparision using given predicate.
     This version is strict and requires error messages
     to be the same *)
Definition serr_eq {A:Type}: relation(A) -> relation (serr A)
  := fun pred a b =>
       match a,b with
       | inr av, inr bv => pred av bv
       | inl ae, inl be => ae = be
       | _, _ => False
       end.
