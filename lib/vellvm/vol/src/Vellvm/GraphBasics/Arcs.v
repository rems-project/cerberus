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



(* An arc is a directed couple of vertices.                             *)

(* The following notions are defined :                                  *)
(*      - Arc : set of arcs                                             *)
(*              constructor : A_ends.                                   *)
(*      - A_tail, A_head, A_loop.                                       *)
(*      - A_in_neighborhood, A_out_neighborhood.                        *)

(* Definitions and properties are inherited.                            *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Vertices.

Section ARC.

Inductive Arc : Set :=
    A_ends : Vertex -> Vertex -> Arc.

Lemma A_eq_dec : forall a b : Arc, {a = b} + {a <> b}.
Proof.
        simple destruct a; simple destruct b; intros.
        case (V_eq_dec v v1); intros.
        case (V_eq_dec v0 v2); intros.
        left; rewrite e; rewrite e0; trivial.

        right; injection; auto.

        right; injection; auto.
Qed.

Definition A_tail (a : Arc) := match a with
                               | A_ends x y => x
                               end.

Definition A_head (a : Arc) := match a with
                               | A_ends x y => y
                               end.

Definition A_loop (x : Vertex) := A_ends x x.

Definition A_list := list Arc.

Definition A_nil := nil (A:=Arc).

Definition A_in_dec := U_in_dec Arc A_eq_dec.

Definition A_canon := U_canon Arc.

Definition A_sum := U_sum Arc.

Definition A_set := U_set Arc.

Definition A_set_eq := U_set_eq Arc.

Definition A_set_diff := U_set_diff Arc.

Definition A_eq_set := U_eq_set Arc.

Definition A_set_eq_commut := U_set_eq_commut Arc.

Definition A_set_diff_commut := U_set_diff_commut Arc.

Definition A_empty := Empty Arc.

Definition A_empty_nothing := Empty_nothing Arc.

Definition A_single := Single Arc.

Definition A_in_single := In_single Arc.

Definition A_single_equal := Single_equal Arc.

Definition A_single_equal_single := Single_equal_single Arc.

Definition A_included := Included Arc.

Definition A_included_single := Included_single Arc.

Definition A_enumerable := U_enumerable Arc.

Definition A_enumerable_sum := U_enumerable_sum Arc.

Definition A_union := Union Arc.

Definition A_in_left := In_left Arc.

Definition A_in_right := In_right Arc.

Definition A_union_eq := Union_eq Arc.

Definition A_union_neutral := Union_neutral Arc.

Definition A_union_commut := Union_commut Arc.

Definition A_union_assoc := Union_assoc Arc.

Definition A_not_union := Not_union Arc.

Definition A_union_dec := Union_dec Arc.

Definition A_included_union := Included_union Arc.

Definition A_union_absorb := Union_absorb Arc.

Definition A_inter := Inter Arc.

Definition A_in_inter := In_inter Arc.

Definition A_inter_eq := Inter_eq Arc.

Definition A_inter_empty := Inter_empty Arc.

Definition A_inter_neutral := Inter_neutral Arc.

Definition A_inter_commut := Inter_commut Arc.

Definition A_inter_assoc := Inter_assoc Arc.

Definition A_not_inter := Not_inter Arc.

Definition A_included_inter := Included_inter Arc.

Definition A_inter_absorb := Inter_absorb Arc.

Definition A_differ := Differ Arc.

Definition A_differ_E_E := Differ_E_E Arc.

Definition A_differ_empty := Differ_empty Arc.

Definition A_union_differ_inter := Union_differ_inter Arc.

Definition A_distributivity_inter_union := Distributivity_inter_union Arc.

Definition A_distributivity_union_inter := Distributivity_union_inter Arc.

Definition A_union_inversion := Union_inversion Arc.

Definition A_union_inversion2 := Union_inversion2 Arc.

Definition A_single_disjoint := Single_disjoint Arc.

Definition A_single_single_disjoint := Single_single_disjoint Arc.

Fixpoint A_in_neighborhood (x : Vertex) (la : A_list) {struct la} : V_list :=
  match la with
  | nil => V_nil
  | A_ends x' y' :: la' =>
      if V_eq_dec x y'
      then x' :: A_in_neighborhood x la'
      else A_in_neighborhood x la'
  end.

Fixpoint A_out_neighborhood (x : Vertex) (la : A_list) {struct la} :
 V_list :=
  match la with
  | nil => V_nil
  | A_ends x' y' :: la' =>
      if V_eq_dec x x'
      then y' :: A_out_neighborhood x la'
      else A_out_neighborhood x la'
  end.

Lemma A_not_in_union :
 forall (a a' : A_set) (x : Vertex),
 (forall y : Vertex, ~ A_union a' a (A_ends x y)) ->
 forall y : Vertex, ~ a (A_ends x y).
Proof.
        intros; red in |- *; intros.
        elim (H y); apply A_in_right; trivial.
Qed.

End ARC.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
