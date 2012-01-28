open Acyclic
open Connected
open Graphs
open Vertices

type __ = Obj.t

type coq_Tree =
  | T_root of coq_Vertex
  | T_leaf of coq_Tree * coq_Vertex * coq_Vertex
  | T_eq of coq_Tree

val coq_Tree_rec :
  (coq_Vertex -> 'a1) -> (__ -> __ -> coq_Tree -> 'a1 -> coq_Vertex ->
  coq_Vertex -> __ -> __ -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ ->
  coq_Tree -> 'a1 -> 'a1) -> coq_Tree -> 'a1

val coq_Tree_isa_graph : coq_Tree -> coq_Graph

val coq_Tree_isa_connected : coq_Tree -> coq_Connected

val coq_Tree_isa_acyclic : coq_Tree -> coq_Acyclic

val coq_Acyclic_connected_isa_tree : coq_Acyclic -> coq_Connected -> coq_Tree

