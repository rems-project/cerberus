open Datatypes
open Enumerated
open MetatheoryAtom
open Sets

type coq_Vertex =
  AtomImpl.atom
  (* singleton inductive, whose constructor was index *)

val coq_Vertex_rect : (AtomImpl.atom -> 'a1) -> coq_Vertex -> 'a1

val coq_Vertex_rec : (AtomImpl.atom -> 'a1) -> coq_Vertex -> 'a1

val coq_V_eq_dec : coq_Vertex -> coq_Vertex -> bool

type coq_V_list = coq_Vertex list

val coq_V_nil : coq_Vertex list

val coq_V_in_dec : coq_Vertex -> coq_Vertex coq_U_list -> bool

val coq_V_sum : (coq_Vertex -> nat) -> coq_Vertex coq_U_list -> nat

type coq_V_set = coq_Vertex coq_U_set

type coq_V_enumerable = coq_Vertex coq_U_enumerable

val coq_V_enumerable_sum :
  (coq_Vertex -> nat) -> coq_Vertex coq_U_enumerable -> nat

val coq_V_union_dec : coq_Vertex -> bool -> bool -> bool

val coq_V_union_single_dec : coq_Vertex -> coq_Vertex -> bool

