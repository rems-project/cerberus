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



(* A directed graph -Digraph- is a type dependant of a set of           *)
(* vertices and a set of arcs. An inhabitant of such a type is a        *)
(* construction, inductively defined, of this graph. Some Digraphs      *)
(* are not inhabited.                                                   *)

(* The following notions are defined :                                  *)
(*      - (Digraph v a) : set of directed graph with vertices in v      *)
(*                              and arcs in a,                          *)
(*              constructors : D_empty, D_vertex, D_arc, D_eq;          *)
(*      - DV_list : list of vertices of a Digraph;                      *)
(*      - DA_list : list of arcs of a Digraph;                          *)
(*      - D_oreder : number of vertices;                                *)
(*      - D_size : number of arcs.                                      *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Arcs.

Section DIGRAPH.

Inductive Digraph : V_set -> A_set -> Set :=
  | D_empty : Digraph V_empty A_empty
  | D_vertex :
      forall (v : V_set) (a : A_set) (d : Digraph v a) (x : Vertex),
      ~ v x -> Digraph (V_union (V_single x) v) a
  | D_arc :
      forall (v : V_set) (a : A_set) (d : Digraph v a) (x y : Vertex),
      v x ->
      v y ->
      ~ a (A_ends x y) -> Digraph v (A_union (A_single (A_ends x y)) a)
  | D_eq :
      forall (v v' : V_set) (a a' : A_set),
      v = v' -> a = a' -> Digraph v a -> Digraph v' a'.

Fixpoint DV_list (v : V_set) (a : A_set) (d : Digraph v a) {struct d} :
 V_list :=
  match d with
  | D_empty => V_nil
  | D_vertex v' a' d' x _ => x :: DV_list v' a' d'
  | D_arc v' a' d' x y _ _ _ => DV_list v' a' d'
  | D_eq v v' a a' _ _ d => DV_list v a d
  end.

Fixpoint DA_list (v : V_set) (a : A_set) (d : Digraph v a) {struct d} :
 A_list :=
  match d with
  | D_empty => A_nil
  | D_vertex v' a' d' x _ => DA_list v' a' d'
  | D_arc v' a' d' x y _ _ _ => A_ends x y :: DA_list v' a' d'
  | D_eq v v' a a' _ _ d => DA_list v a d
  end.

Definition D_order (v : V_set) (a : A_set) (d : Digraph v a) :=
  length (DV_list v a d).

Definition D_size (v : V_set) (a : A_set) (d : Digraph v a) :=
  length (DA_list v a d).

Lemma D_v_dec :
 forall (v : V_set) (a : A_set) (d : Digraph v a) (x : Vertex),
 {v x} + {~ v x}.
Proof.
        intros v a d; elim d; intros.
        right; apply V_empty_nothing.

        case (H x0); intros.
        left; apply V_in_right; trivial.

        case (V_eq_dec x x0); intros.
        left; apply V_in_left; rewrite e; apply V_in_single.

        right; red in |- *; intros; inversion H0.
        elim n1; inversion H1; trivial.

        elim n0; trivial.

        auto.

        case (H x); intros.
        left; elim e; trivial.

        right; elim e; trivial.
Qed.

Lemma D_a_dec :
 forall (v : V_set) (a : A_set) (d : Digraph v a) (x : Arc), {a x} + {~ a x}.
Proof.
        intros v a d; elim d; intros.
        right; apply A_empty_nothing.

        auto.

        case (H x0); intros.
        left; apply A_in_right; trivial.

        case (A_eq_dec (A_ends x y) x0); intros.
        left; apply A_in_left; rewrite e; apply A_in_single.

        right; red in |- *; intros; inversion H0.
        elim n1; inversion H1; trivial.

        elim n0; trivial.

        case (H x); intros.
        left; elim e0; trivial.

        right; elim e0; trivial.
Qed.

End DIGRAPH.

Section UNION_DIGRAPHS.

Lemma D_union :
 forall (v1 v2 : V_set) (a1 a2 : A_set),
 Digraph v1 a1 -> Digraph v2 a2 -> Digraph (V_union v1 v2) (A_union a1 a2).
Proof.
        intros; elim H; intros.
        apply D_eq with (v := v2) (a := a2).
        symmetry  in |- *; apply V_union_neutral.

        symmetry  in |- *; apply A_union_neutral.

        trivial.

        case (D_v_dec v2 a2 H0 x); intros.
        apply D_eq with (v := V_union v v2) (a := A_union a a2).
        rewrite V_union_assoc; rewrite (V_union_absorb (V_single x)); trivial.
        apply V_included_single; apply V_in_right; trivial.

        trivial.

        trivial.

        apply
         D_eq
          with (v := V_union (V_single x) (V_union v v2)) (a := A_union a a2).
        symmetry  in |- *; apply V_union_assoc.

        trivial.

        apply D_vertex.
        trivial.

        apply V_not_union; trivial.

        case (D_a_dec v2 a2 H0 (A_ends x y)); intros.
        apply D_eq with (v := V_union v v2) (a := A_union a a2).
        trivial.

        rewrite A_union_assoc;
         rewrite (A_union_absorb (A_single (A_ends x y))); 
         trivial.
        apply A_included_single; apply A_in_right; trivial.

        trivial.

        apply
         D_eq
          with
            (v := V_union v v2)
            (a := A_union (A_single (A_ends x y)) (A_union a a2)).
        trivial.

        symmetry  in |- *; apply A_union_assoc.

        apply D_arc.
        trivial.

        apply V_in_left; trivial.

        apply V_in_left; trivial.

        apply A_not_union; trivial.

        apply D_eq with (v := V_union v v2) (a := A_union a a2).
        elim e; trivial.

        elim e0; trivial.

        trivial.
Qed.

End UNION_DIGRAPHS.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
