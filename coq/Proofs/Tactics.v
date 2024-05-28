Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Bool.Bool.

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

Lemma ret_inr
  {T E:Type}
  {x0 x1:T}:
  @ret (sum E) (Monad_either E) T x0 = @inr E T x1 -> @inr E T x0 = @inr E T x1.
Proof.
  Transparent ret.
  intros H.
  unfold ret, Monad_either in H.
  apply H.
  Opaque ret.
Qed.

Lemma raise_inl
  {T E:Type}
  {e0 e1:E}:
  @raise E (sum E) (Exception_either E) T e0 = @inl E T e1 -> @inl E T e0 = @inl E T e1.
Proof.
  Transparent raise.
  intros H.
  unfold raise, Exception_either in H.
  apply H.
  Opaque raise.
Qed.

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
  | [H1: inr _ = @Monad.ret _ (Monad_either _) _ ?x |- _] =>
      symmetry in H1;
      apply ret_inr in H1;
      subst x
  | [H1: @Monad.ret _ (Monad_either _) _ _ = inr _ |- _] =>
      apply ret_inr in H1;
      inversion H1;
      clear H1

  | [H1: @raise _ (sum _) (Exception_either _) _ _ =
           @inl _ _ _ |- _] =>
      apply raise_inl in H1;
      inversion H1;
      clear H1
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

Ltac some_none :=
  let H' := fresh in
  match goal with
  | [H1: ?x = None, H2: ?x <> None |- _] => congruence
  | [H1: ?x = Some _, H2: ?x = None |- _ ] => congruence
  | [H: Some _ = None |- _ ] => inversion H
  | [H: None = Some _ |- _ ] => inversion H
  | [ |- Some _ <> None ] => intros H'; inversion H'
  | [ |- None <> None ] => congruence
  | [ |- Some ?a <> Some ?a ] => congruence
  | [ |- Some _ <> None ] => intros H'; inversion H'
  | [ |- None <> Some _ ] => intros H'; inversion H'
  | [ |- None = None ] => reflexivity
  | [ |- Some ?a = Some ?a] => reflexivity
  end.

Ltac some_inv :=
  match goal with
  | [H: Some ?a = Some ?b |- _ ] => inversion H; clear H
  end.

Ltac bool_inv :=
  match goal with
  | [H: true = false |- _] => inversion H
  | [H: false = true |- _] => inversion H
  | [H: false = false |- _] => clear H
  | [H: true = true |- _] => clear H
  end.

Ltac bool_to_prop_hyp :=
  repeat match goal with
    | [H: orb _ _ = false |- _] => apply orb_false_elim in H; destruct H
    | [H: orb _ _ = true |- _] =>  apply orb_prop in H; destruct H
    | [H: andb _ _ = true |- _] => apply andb_prop in H; destruct H
    | [H: andb _ _ = false |- _] => apply andb_false_iff in H; destruct H
    | [H: Z.eqb _ _ = true |-_] => apply Z.eqb_eq in H
    | [H: Z.eqb _ _ = false |-_] => apply Z.eqb_neq in H
    | [H: Z.geb _ _ = true |- _ ] => apply Z.geb_ge in H
    | [H: Z.geb _ _ = false |- _ ] => rewrite Z.geb_leb in H; apply Z.leb_gt in H
    | [H: Z.ltb _ _ = true |- _ ] => apply Z.ltb_lt in H
    | [H: Z.ltb _ _ = false |- _ ] => apply Z.ltb_ge in H
    | [H: Z.leb _ _ = true |- _ ] => apply Z.leb_le in H
    | [H: Z.gtb _ _ = _ |- _ ] => rewrite Z.gtb_ltb in H
    | [H: Nat.ltb _ _ = false |- _ ] => apply Nat.ltb_ge in H
    | [H: Nat.eqb _ _ = false |- _] => apply Nat.eqb_neq in H
    end.
