open Vertices

val coq_E_set_eq_dec :
  coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_Vertex -> bool

type coq_Edge =
  | E_ends of coq_Vertex * coq_Vertex

val coq_Edge_rect : (coq_Vertex -> coq_Vertex -> 'a1) -> coq_Edge -> 'a1

val coq_Edge_rec : (coq_Vertex -> coq_Vertex -> 'a1) -> coq_Edge -> 'a1

type coq_E_list = coq_Edge list

val coq_E_nil : coq_Edge list

val coq_E_eq_dec : coq_Edge -> coq_Edge -> bool

