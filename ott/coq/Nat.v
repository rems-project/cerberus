Require Import Common.
Require Import Program.
Require Import Omega.
(* Equations
Require Import Equations.
*)

Instance nat_DecEq : DecidableEq nat.
Proof. dec_eq. Defined.

Fixpoint nat_le_fun (x y : nat) : bool :=
  match x, y with
  | 0  , _   => true
  | S _, 0   => false
  | S x, S y => nat_le_fun x y
  end.

Fixpoint nat_le_fun_correct x y : boolSpec (nat_le_fun x y) (x <= y).
Proof.
  case x as [|x].
  - exact (Le.le_0_n  _).
  - case y as [|y].
    + exact (Le.le_Sn_0 _).
    + simpl; set (nat_le_fun_correct x y) as IH;
             set (nat_le_fun         x y) as Hxy.
      case_eq Hxy; subst Hxy; intros Heq; rewrite Heq in *.
      * exact (Le.le_n_S _ _ IH).
      * exact (IH ∘ Le.le_S_n x y).
Defined.

(* Equations
nat_le_decide (x y : nat) : decidable (x <= y) :=
nat_le_decide O     y     := inl (Le.le_0_n  _);
nat_le_decide (S _) O     := inr (Le.le_Sn_0 _);
nat_le_decide (S x) (S y) := if nat_le_decide x y
                                then inl (Le.le_n_S _ _ _)
                                else inr (_ ∘ Le.le_S_n x y : _ -> False).
*)

Instance nat_le_dec : DecidableRelation le := {
 decide x y := boolSpec_Decision (nat_le_fun_correct x y)
}.
