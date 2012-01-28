open Arcs
open Datatypes
open Vertices

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Digraph =
  | D_empty
  | D_vertex of coq_Digraph * coq_Vertex
  | D_arc of coq_Digraph * coq_Vertex * coq_Vertex
  | D_eq of coq_Digraph

(** val coq_Digraph_rec :
    'a1 -> (__ -> __ -> coq_Digraph -> 'a1 -> coq_Vertex -> __ -> 'a1) -> (__
    -> __ -> coq_Digraph -> 'a1 -> coq_Vertex -> coq_Vertex -> __ -> __ -> __
    -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> coq_Digraph -> 'a1 ->
    'a1) -> coq_Digraph -> 'a1 **)

let rec coq_Digraph_rec f f0 f1 f2 = function
  | D_empty -> f
  | D_vertex (d0, x) -> f0 __ __ d0 (coq_Digraph_rec f f0 f1 f2 d0) x __
  | D_arc (d0, x, y) ->
      f1 __ __ d0 (coq_Digraph_rec f f0 f1 f2 d0) x y __ __ __
  | D_eq d0 -> f2 __ __ __ __ __ __ d0 (coq_Digraph_rec f f0 f1 f2 d0)

(** val coq_DV_list : coq_Digraph -> coq_V_list **)

let rec coq_DV_list = function
  | D_empty -> coq_V_nil
  | D_vertex (d', x) -> x::(coq_DV_list d')
  | D_arc (d', x, y) -> coq_DV_list d'
  | D_eq d0 -> coq_DV_list d0

(** val coq_DA_list : coq_Digraph -> coq_A_list **)

let rec coq_DA_list = function
  | D_empty -> coq_A_nil
  | D_vertex (d', x) -> coq_DA_list d'
  | D_arc (d', x, y) -> (A_ends (x, y))::(coq_DA_list d')
  | D_eq d0 -> coq_DA_list d0

(** val coq_D_order : coq_Digraph -> nat **)

let coq_D_order d =
  length (coq_DV_list d)

(** val coq_D_size : coq_Digraph -> nat **)

let coq_D_size d =
  length (coq_DA_list d)

(** val coq_D_v_dec : coq_Digraph -> coq_Vertex -> bool **)

let rec coq_D_v_dec d x =
  match d with
    | D_empty -> false
    | D_vertex (d0, x0) ->
        if coq_D_v_dec d0 x then true else coq_V_eq_dec x0 x
    | D_arc (d0, x0, y) -> coq_D_v_dec d0 x
    | D_eq d0 -> coq_D_v_dec d0 x

(** val coq_D_a_dec : coq_Digraph -> coq_Arc -> bool **)

let rec coq_D_a_dec d x =
  match d with
    | D_empty -> false
    | D_vertex (d0, x0) -> coq_D_a_dec d0 x
    | D_arc (d0, x0, y) ->
        if coq_D_a_dec d0 x then true else coq_A_eq_dec (A_ends (x0, y)) x
    | D_eq d0 -> coq_D_a_dec d0 x

(** val coq_D_union : coq_Digraph -> coq_Digraph -> coq_Digraph **)

let rec coq_D_union h h0 =
  match h with
    | D_empty -> D_eq h0
    | D_vertex (d, x) ->
        if coq_D_v_dec h0 x
        then D_eq (coq_D_union d h0)
        else D_eq (D_vertex ((coq_D_union d h0), x))
    | D_arc (d, x, y) ->
        if coq_D_a_dec h0 (A_ends (x, y))
        then D_eq (coq_D_union d h0)
        else D_eq (D_arc ((coq_D_union d h0), x, y))
    | D_eq d -> D_eq (coq_D_union d h0)

