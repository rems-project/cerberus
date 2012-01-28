open Graphs
open Vertices

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Acyclic =
  | AC_empty
  | AC_vertex of coq_Acyclic * coq_Vertex
  | AC_leaf of coq_Acyclic * coq_Vertex * coq_Vertex
  | AC_eq of coq_Acyclic

(** val coq_Acyclic_rec :
    'a1 -> (__ -> __ -> coq_Acyclic -> 'a1 -> coq_Vertex -> __ -> 'a1) -> (__
    -> __ -> coq_Acyclic -> 'a1 -> coq_Vertex -> coq_Vertex -> __ -> __ ->
    'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> coq_Acyclic -> 'a1 -> 'a1)
    -> coq_Acyclic -> 'a1 **)

let rec coq_Acyclic_rec f f0 f1 f2 = function
  | AC_empty -> f
  | AC_vertex (ac, x) -> f0 __ __ ac (coq_Acyclic_rec f f0 f1 f2 ac) x __
  | AC_leaf (ac, x, y) ->
      f1 __ __ ac (coq_Acyclic_rec f f0 f1 f2 ac) x y __ __
  | AC_eq a0 -> f2 __ __ __ __ __ __ a0 (coq_Acyclic_rec f f0 f1 f2 a0)

(** val coq_Acyclic_Isa_Graph : coq_Acyclic -> coq_Graph **)

let rec coq_Acyclic_Isa_Graph = function
  | AC_empty -> G_empty
  | AC_vertex (ac, x) -> G_vertex ((coq_Acyclic_Isa_Graph ac), x)
  | AC_leaf (ac, x, y) -> G_edge ((G_vertex ((coq_Acyclic_Isa_Graph ac), y)),
      x, y)
  | AC_eq a0 -> G_eq (coq_Acyclic_Isa_Graph a0)

