open Graphs
open Vertices

type __ = Obj.t

type coq_Acyclic =
  | AC_empty
  | AC_vertex of coq_Acyclic * coq_Vertex
  | AC_leaf of coq_Acyclic * coq_Vertex * coq_Vertex
  | AC_eq of coq_Acyclic

val coq_Acyclic_rec :
  'a1 -> (__ -> __ -> coq_Acyclic -> 'a1 -> coq_Vertex -> __ -> 'a1) -> (__
  -> __ -> coq_Acyclic -> 'a1 -> coq_Vertex -> coq_Vertex -> __ -> __ -> 'a1)
  -> (__ -> __ -> __ -> __ -> __ -> __ -> coq_Acyclic -> 'a1 -> 'a1) ->
  coq_Acyclic -> 'a1

val coq_Acyclic_Isa_Graph : coq_Acyclic -> coq_Graph

