open Arcs
open Datatypes
open Vertices

type __ = Obj.t

type coq_Digraph =
  | D_empty
  | D_vertex of coq_Digraph * coq_Vertex
  | D_arc of coq_Digraph * coq_Vertex * coq_Vertex
  | D_eq of coq_Digraph

val coq_Digraph_rec :
  'a1 -> (__ -> __ -> coq_Digraph -> 'a1 -> coq_Vertex -> __ -> 'a1) -> (__
  -> __ -> coq_Digraph -> 'a1 -> coq_Vertex -> coq_Vertex -> __ -> __ -> __
  -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> coq_Digraph -> 'a1 -> 'a1)
  -> coq_Digraph -> 'a1

val coq_DV_list : coq_Digraph -> coq_V_list

val coq_DA_list : coq_Digraph -> coq_A_list

val coq_D_order : coq_Digraph -> nat

val coq_D_size : coq_Digraph -> nat

val coq_D_v_dec : coq_Digraph -> coq_Vertex -> bool

val coq_D_a_dec : coq_Digraph -> coq_Arc -> bool

val coq_D_union : coq_Digraph -> coq_Digraph -> coq_Digraph

