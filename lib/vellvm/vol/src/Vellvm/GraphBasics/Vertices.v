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



(* The set of vertices -Vertex- is defined as an indexed set;           *)
(* so it is separable.                                                  *)

(* The following notions are defined :                                  *)
(*      - Vertex : set of vertices,                                     *)
(*              constructor : index.                                    *)

(* Definitions and properties are inherited from the previous sections. *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Enumerated.
Require Import Metatheory.

Section VERTEX.

Inductive Vertex : Set :=
    index : atom -> Vertex.

Lemma V_eq_dec : forall x y : Vertex, {x = y} + {x <> y}.
Proof.
        simple destruct x; simple destruct y; intros.
        case (eq_atom_dec a a0); intros.
        left; rewrite e; trivial.

        right; injection; trivial.
Qed.

Definition V_list := list Vertex.

Definition V_nil := nil (A:=Vertex).

Definition V_in_dec := U_in_dec Vertex V_eq_dec.

Definition V_canon := U_canon Vertex.

Definition V_sum := U_sum Vertex.

Definition V_set := U_set Vertex.

Definition V_set_eq := U_set_eq Vertex.

Definition V_set_diff := U_set_diff Vertex.

Definition V_eq_set := U_eq_set Vertex.

Definition V_set_eq_commut := U_set_eq_commut Vertex.

Definition V_set_diff_commut := U_set_diff_commut Vertex.

Definition V_empty := Empty Vertex.

Definition V_empty_nothing := Empty_nothing Vertex.

Definition V_single := Single Vertex.

Definition V_in_single := In_single Vertex.

Definition V_single_equal := Single_equal Vertex.

Definition V_single_equal_single := Single_equal_single Vertex.

Definition V_included := Included Vertex.

Definition V_included_single := Included_single Vertex.

Definition V_enumerable := U_enumerable Vertex.

Definition V_enumerable_sum := U_enumerable_sum Vertex.

Definition V_union := Union Vertex.

Definition V_in_left := In_left Vertex.

Definition V_in_right := In_right Vertex.

Definition V_union_eq := Union_eq Vertex.

Definition V_union_neutral := Union_neutral Vertex.

Definition V_union_commut := Union_commut Vertex.

Definition V_union_assoc := Union_assoc Vertex.

Definition V_not_union := Not_union Vertex.

Definition V_union_dec := Union_dec Vertex.

Definition V_included_union := Included_union Vertex.

Definition V_union_absorb := Union_absorb Vertex.

Definition V_inter := Inter Vertex.

Definition V_in_inter := In_inter Vertex.

Definition V_inter_eq := Inter_eq Vertex.

Definition V_inter_neutral := Inter_neutral Vertex.

Definition V_inter_empty := Inter_empty Vertex.

Definition V_inter_commut := Inter_commut Vertex.

Definition V_inter_assoc := Inter_assoc Vertex.

Definition V_not_inter := Not_inter Vertex.

Definition V_included_inter := Included_inter Vertex.

Definition V_inter_absorb := Inter_absorb Vertex.

Definition V_differ := Differ Vertex.

Definition V_differ_E_E := Differ_E_E Vertex.

Definition V_differ_empty := Differ_empty Vertex.

Definition V_union_differ_inter := Union_differ_inter Vertex.

Definition V_distributivity_inter_union := Distributivity_inter_union Vertex.

Definition V_distributivity_union_inter := Distributivity_union_inter Vertex.

Definition V_union_inversion := Union_inversion Vertex.

Definition V_union_inversion2 := Union_inversion2 Vertex.

Definition V_single_disjoint := Single_disjoint Vertex.

Definition V_single_single_disjoint := Single_single_disjoint Vertex.

Definition V_union_single_single := Union_single_single Vertex.

Lemma V_union_single_dec :
 forall (x y : Vertex) (v : V_set),
 ~ v x -> V_union (V_single x) v y -> {x = y} + {v y}.
Proof.
        intros; case (V_eq_dec x y); intros.
        left; trivial.

        right; inversion H0.
        elim n; inversion H1; trivial.

        trivial.
Qed.

End VERTEX.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/Vminus/GraphBasics" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
