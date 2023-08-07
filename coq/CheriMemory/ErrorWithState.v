Require Import Coq.Strings.String.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadExc.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.EitherMonad.

Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

Section withState.

  Variable St : Type.
  Variable ErrT: Type.

  Notation err := (sum ErrT).
  
  Definition errS A := St -> (St*(ErrT+A)).

  Global Instance Monad_errS: Monad errS :=
    { ret  := fun _ x => fun s => (s, inr x)
      ; bind := fun _ _ m f => fun s => match m s with
                                  | (s', inl v) => (s', inl v)
                                  | (s', inr x) => f x s'
                                  end
    }.

  Global Instance Exception_errS : MonadExc ErrT errS :=
    { raise := fun _ v => fun s => (s, inl v)
      ; catch := fun _ c h => fun s => match c s with
                                 | (s', inl v) => h v s'
                                 | (s', inr x) => (s', inr x)
                                 end
    }.

  Global Instance State_errS: MonadState St errS :=
    {
      get := fun s => (s, inr s)
    ; put := fun t s => (t, inr tt)
    }.

  (* Unwrapping/running monad *)
  
  (* Returns value *)
  Definition evalErrS {A:Type} (c : errS A) (initial : St) : err A :=
  match c initial with
  | (_, inl msg) => raise msg
  | (s, inr v) => ret v
  end.

  (* Returns state *)
  Definition execErrS {A:Type} (c : errS A) (initial : St) : err St :=
  match c initial with
  | (_, inl msg) => raise msg
  | (s, inr v) => ret s
  end.

  (* -- lifting [err] -- *)

  Definition err2errS {A: Type}: (err A) -> (errS A)
    := fun e => match e with
             | inl msg => raise msg
             | inr v => ret v
             end.

  (* -- lifting [option] -- *)
  
  Definition option2errS {A: Type} (msg:ErrT) (o:option A): (errS A)
    := match o with
       | Some v => ret v
       | None => raise msg
       end.

  (* -- state update -- *)
  Definition update f := st <- get ;; put (f st).

End withState.


Arguments option2errS {St} {ErrT} {A} (_) (_).
Arguments err2errS {St} {ErrT} {A} (_).
Arguments evalErrS {St} {ErrT} {A} (_) (_).
Arguments execErrS {St} {ErrT} {A} (_) (_).
Arguments update {St} {ErrT} (_).
