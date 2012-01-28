open Datatypes
open Enumerated
open MetatheoryAtom
open Sets

type coq_Vertex =
  AtomImpl.atom
  (* singleton inductive, whose constructor was index *)

(** val coq_Vertex_rect : (AtomImpl.atom -> 'a1) -> coq_Vertex -> 'a1 **)

let coq_Vertex_rect f v =
  f v

(** val coq_Vertex_rec : (AtomImpl.atom -> 'a1) -> coq_Vertex -> 'a1 **)

let coq_Vertex_rec f v =
  f v

(** val coq_V_eq_dec : coq_Vertex -> coq_Vertex -> bool **)

let coq_V_eq_dec x y =
  AtomImpl.eq_atom_dec x y

type coq_V_list = coq_Vertex list

(** val coq_V_nil : coq_Vertex list **)

let coq_V_nil =
  []

(** val coq_V_in_dec : coq_Vertex -> coq_Vertex coq_U_list -> bool **)

let coq_V_in_dec =
  coq_U_in_dec coq_V_eq_dec

(** val coq_V_sum : (coq_Vertex -> nat) -> coq_Vertex coq_U_list -> nat **)

let coq_V_sum =
  coq_U_sum

type coq_V_set = coq_Vertex coq_U_set

type coq_V_enumerable = coq_Vertex coq_U_enumerable

(** val coq_V_enumerable_sum :
    (coq_Vertex -> nat) -> coq_Vertex coq_U_enumerable -> nat **)

let coq_V_enumerable_sum f x =
  coq_U_enumerable_sum f x

(** val coq_V_union_dec : coq_Vertex -> bool -> bool -> bool **)

let coq_V_union_dec x x0 x1 =
  coq_Union_dec x x0 x1

(** val coq_V_union_single_dec : coq_Vertex -> coq_Vertex -> bool **)

let coq_V_union_single_dec x y =
  coq_V_eq_dec x y

