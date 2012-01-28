open Acyclic
open Connected
open Graphs
open Vertices

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Tree =
  | T_root of coq_Vertex
  | T_leaf of coq_Tree * coq_Vertex * coq_Vertex
  | T_eq of coq_Tree

(** val coq_Tree_rec :
    (coq_Vertex -> 'a1) -> (__ -> __ -> coq_Tree -> 'a1 -> coq_Vertex ->
    coq_Vertex -> __ -> __ -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ ->
    coq_Tree -> 'a1 -> 'a1) -> coq_Tree -> 'a1 **)

let rec coq_Tree_rec f f0 f1 = function
  | T_root r -> f r
  | T_leaf (t0, f2, n) -> f0 __ __ t0 (coq_Tree_rec f f0 f1 t0) f2 n __ __
  | T_eq t0 -> f1 __ __ __ __ __ __ t0 (coq_Tree_rec f f0 f1 t0)

(** val coq_Tree_isa_graph : coq_Tree -> coq_Graph **)

let rec coq_Tree_isa_graph = function
  | T_root r -> G_eq (G_vertex (G_empty, r))
  | T_leaf (t0, f, n) -> G_edge ((G_vertex ((coq_Tree_isa_graph t0), f)), n,
      f)
  | T_eq t0 -> G_eq (coq_Tree_isa_graph t0)

(** val coq_Tree_isa_connected : coq_Tree -> coq_Connected **)

let rec coq_Tree_isa_connected = function
  | T_root r -> C_isolated r
  | T_leaf (t0, f, n) -> C_leaf ((coq_Tree_isa_connected t0), n, f)
  | T_eq t0 -> C_eq (coq_Tree_isa_connected t0)

(** val coq_Tree_isa_acyclic : coq_Tree -> coq_Acyclic **)

let rec coq_Tree_isa_acyclic = function
  | T_root r -> AC_eq (AC_vertex (AC_empty, r))
  | T_leaf (t0, f, n) -> AC_leaf ((coq_Tree_isa_acyclic t0), n, f)
  | T_eq t0 -> AC_eq (coq_Tree_isa_acyclic t0)

(** val coq_Acyclic_connected_isa_tree :
    coq_Acyclic -> coq_Connected -> coq_Tree **)

let rec coq_Acyclic_connected_isa_tree a h =
  match a with
    | AC_empty -> assert false (* absurd case *)
    | AC_vertex (ac, x) -> T_eq (T_root x)
    | AC_leaf (ac, x, y) -> T_leaf
        ((coq_Acyclic_connected_isa_tree ac (coq_C_minus_pendant h x y)), y,
        x)
    | AC_eq a0 -> T_eq (coq_Acyclic_connected_isa_tree a0 (C_eq h))

