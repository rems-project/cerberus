(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* A set, with the axiom of decidability of the equality,               *)
(* is enumerable if it exists a list of its elements.                   *)

(* the following notions are defined :                                  *)
(*      - U_enumerable : set with a list of its elements                *)
(*      - U_canon : list with unique occurrence of its elements         *)
(*              constructors : U_canon_nil, U_canon_cons.               *)
(*      - U_sum : sommation of the images of a list.                    *)

Require Export Sets.
Require Export List.

Section ENUMERATION.

Variable U : Set.

Hypothesis U_separable : forall x y : U, {x = y} + {x <> y}.

Definition U_list := list U.

Definition U_enumerable (E : U_set U) :=
  {ul : U_list | forall x : U, E x -> In x ul}.

Inductive U_canon : U_list -> Prop :=
  | U_canon_nil : U_canon nil
  | U_canon_cons :
      forall (x : U) (ul : U_list),
      U_canon ul -> ~ In x ul -> U_canon (x :: ul).

Lemma U_in_dec : forall (x : U) (ul : U_list), {In x ul} + {~ In x ul}.
Proof.
        simple induction ul; intros.
        right; red in |- *; intros; inversion H.

        case (U_separable x a); intros.
        left; rewrite e; simpl in |- *; auto.

        case H; intros.
        left; simpl in |- *; auto.

        right; red in |- *; intros; inversion H0.
        elim n; auto.

        elim n0; auto.
Qed.

Variable f : U -> nat.

Fixpoint U_sum (ul : U_list) : nat :=
  match ul with
  | nil => 0
  | x :: ul' => f x + U_sum ul'
  end.

Lemma U_enumerable_sum : forall E : U_set U, U_enumerable E -> nat.
Proof.
        intros; elim H; intros.
        apply (U_sum x).
Defined.

End ENUMERATION.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/Vminus/GraphBasics" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
