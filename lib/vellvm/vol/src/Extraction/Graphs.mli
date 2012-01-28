open Arcs
open Datatypes
open Digraphs
open Edges
open Vertices

type __ = Obj.t

type coq_Graph =
  | G_empty
  | G_vertex of coq_Graph * coq_Vertex
  | G_edge of coq_Graph * coq_Vertex * coq_Vertex
  | G_eq of coq_Graph

val coq_Graph_rec :
  'a1 -> (__ -> __ -> coq_Graph -> 'a1 -> coq_Vertex -> __ -> 'a1) -> (__ ->
  __ -> coq_Graph -> 'a1 -> coq_Vertex -> coq_Vertex -> __ -> __ -> __ -> __
  -> __ -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> coq_Graph -> 'a1 ->
  'a1) -> coq_Graph -> 'a1

val coq_GV_list : coq_Graph -> coq_V_list

val coq_GA_list : coq_Graph -> coq_A_list

val coq_GE_list : coq_Graph -> coq_E_list

val coq_G_order : coq_Graph -> nat

val coq_G_size : coq_Graph -> nat

val coq_G_v_dec : coq_Graph -> coq_Vertex -> bool

val coq_G_a_dec : coq_Graph -> coq_Arc -> bool

val graph_isa_digraph : coq_Graph -> coq_Digraph

val coq_G_union : coq_Graph -> coq_Graph -> coq_Graph

val coq_G_minus_vertex : coq_Graph -> coq_Vertex -> coq_Graph

val coq_G_minus_edge : coq_Graph -> coq_Vertex -> coq_Vertex -> coq_Graph

