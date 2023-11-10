From ExtLib.Structures Require Import Monad Monads MonadExc MonadState Traversable.
From ExtLib.Data.Monads Require Import EitherMonad OptionMonad.
Require Import Common.SimpleError.

(* This (seemingly) prevents slow `Qed` problem.
   Usage: replace `cbn in H` with `cbn_hyp H`.

   See aslo:
     - discussion: https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Coq.20hangs.20on.20Qed
     - FAQ: https://github.com/coq/coq/wiki/Troubleshooting#what-can-i-do-when-qed-is-slow
 *)
Ltac cbn_hyp H :=
  let T := type of H in let T' := eval cbn in T in replace T with T' in H by (cbn;reflexivity).

Ltac inl_inr :=
  match goal with
  | [H1: inl _ = inr _ |- _] => inversion H1
  | [H1: inr _ = inl _ |- _] => inversion H1

  | [H1: inl _ = Monad.ret _ |- _] => inversion H1
  | [H1: Monad.ret _ = inl _ |- _] => inversion H1

  | [H1: raise _ = inr _ |- _] => inversion H1
  | [H1: inr _ = raise _ |- _] => inversion H1

  | [ |- inl ?x = inl ?x ] => reflexivity
  | [ |- inr ?x = inr ?x ] => reflexivity

  | [H1: ?a = inr _,
        H2: ?a = inl _ |- _] => rewrite H1 in H2;
                              inversion H2

  end.

Ltac inl_inr_inv :=
  match goal with
  | [H1: inl _ = inl _ |- _] => inversion H1; clear H1
  | [H1: inr _ = inr _ |- _] => inversion H1; clear H1

  | [H1: inr _ = Monad.ret _ |- _] => inversion H1; clear H1
  | [H1: Monad.ret _ = inr _ |- _] => inversion H1; clear H1
  | [H1: raise _ = inl _ |- _] => inversion H1; clear H1
  | [H1: inl _ = raise _ |- _] => inversion H1; clear H1
  end.

Ltac destruct_serr_eq :=
  match goal with
  | [|- serr_eq _ ?a ?b] =>
      let AH := fresh "Hserr" in
      let BH := fresh "Hserr" in
      destruct a eqn:AH, b eqn:BH
  end.

Ltac autospecialize H :=
  match type of H with
  | ?P -> _ => let T' := fresh "T" in
             assert (T' : P); [clear H | specialize (H T'); try clear T']
  end.

Ltac full_autospecialize H :=
  autospecialize H; [| try full_autospecialize H].
