open Arcs
open Datatypes
open Digraphs
open Edges
open Vertices

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Graph =
  | G_empty
  | G_vertex of coq_Graph * coq_Vertex
  | G_edge of coq_Graph * coq_Vertex * coq_Vertex
  | G_eq of coq_Graph

(** val coq_Graph_rec :
    'a1 -> (__ -> __ -> coq_Graph -> 'a1 -> coq_Vertex -> __ -> 'a1) -> (__
    -> __ -> coq_Graph -> 'a1 -> coq_Vertex -> coq_Vertex -> __ -> __ -> __
    -> __ -> __ -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> coq_Graph ->
    'a1 -> 'a1) -> coq_Graph -> 'a1 **)

let rec coq_Graph_rec f f0 f1 f2 = function
  | G_empty -> f
  | G_vertex (d, x) -> f0 __ __ d (coq_Graph_rec f f0 f1 f2 d) x __
  | G_edge (d, x, y) ->
      f1 __ __ d (coq_Graph_rec f f0 f1 f2 d) x y __ __ __ __ __
  | G_eq g0 -> f2 __ __ __ __ __ __ g0 (coq_Graph_rec f f0 f1 f2 g0)

(** val coq_GV_list : coq_Graph -> coq_V_list **)

let rec coq_GV_list = function
  | G_empty -> coq_V_nil
  | G_vertex (g', x) -> x::(coq_GV_list g')
  | G_edge (g', x, y) -> coq_GV_list g'
  | G_eq g' -> coq_GV_list g'

(** val coq_GA_list : coq_Graph -> coq_A_list **)

let rec coq_GA_list = function
  | G_empty -> coq_A_nil
  | G_vertex (g', x) -> coq_GA_list g'
  | G_edge (g', x, y) -> (A_ends (x, y))::((A_ends (y, x))::(coq_GA_list g'))
  | G_eq g' -> coq_GA_list g'

(** val coq_GE_list : coq_Graph -> coq_E_list **)

let rec coq_GE_list = function
  | G_empty -> coq_E_nil
  | G_vertex (g', x) -> coq_GE_list g'
  | G_edge (g', x, y) -> (E_ends (x, y))::(coq_GE_list g')
  | G_eq g' -> coq_GE_list g'

(** val coq_G_order : coq_Graph -> nat **)

let coq_G_order g =
  length (coq_GV_list g)

(** val coq_G_size : coq_Graph -> nat **)

let coq_G_size g =
  length (coq_GE_list g)

(** val coq_G_v_dec : coq_Graph -> coq_Vertex -> bool **)

let rec coq_G_v_dec g x =
  match g with
    | G_empty -> false
    | G_vertex (d, x0) -> if coq_G_v_dec d x then true else coq_V_eq_dec x0 x
    | G_edge (d, x0, y) -> coq_G_v_dec d x
    | G_eq g0 -> coq_G_v_dec g0 x

(** val coq_G_a_dec : coq_Graph -> coq_Arc -> bool **)

let rec coq_G_a_dec g x =
  match g with
    | G_empty -> false
    | G_vertex (d, x0) -> coq_G_a_dec d x
    | G_edge (d, x0, y) ->
        if coq_G_a_dec d x
        then true
        else if coq_A_eq_dec (A_ends (x0, y)) x
             then true
             else coq_A_eq_dec (A_ends (y, x0)) x
    | G_eq g0 -> coq_G_a_dec g0 x

(** val graph_isa_digraph : coq_Graph -> coq_Digraph **)

let rec graph_isa_digraph = function
  | G_empty -> D_empty
  | G_vertex (d, x) -> D_vertex ((graph_isa_digraph d), x)
  | G_edge (d, x, y) -> D_eq (D_arc ((D_arc ((graph_isa_digraph d), y, x)),
      x, y))
  | G_eq g0 -> D_eq (graph_isa_digraph g0)

(** val coq_G_union : coq_Graph -> coq_Graph -> coq_Graph **)

let rec coq_G_union h h0 =
  match h with
    | G_empty -> G_eq h0
    | G_vertex (d, x) ->
        if coq_G_v_dec h0 x
        then G_eq (coq_G_union d h0)
        else G_eq (G_vertex ((coq_G_union d h0), x))
    | G_edge (d, x, y) ->
        if coq_G_a_dec h0 (A_ends (x, y))
        then G_eq (coq_G_union d h0)
        else G_eq (G_edge ((coq_G_union d h0), x, y))
    | G_eq g -> G_eq (coq_G_union g h0)

(** val coq_G_minus_vertex : coq_Graph -> coq_Vertex -> coq_Graph **)

let rec coq_G_minus_vertex g x =
  match g with
    | G_empty -> assert false (* absurd case *)
    | G_vertex (d, x0) ->
        if coq_V_union_single_dec x0 x
        then G_eq d
        else G_eq (G_vertex ((coq_G_minus_vertex d x), x0))
    | G_edge (d, x0, y) -> G_edge ((coq_G_minus_vertex d x), x0, y)
    | G_eq g0 -> G_eq (coq_G_minus_vertex g0 x)

(** val coq_G_minus_edge :
    coq_Graph -> coq_Vertex -> coq_Vertex -> coq_Graph **)

let rec coq_G_minus_edge g x0 y =
  match g with
    | G_empty -> assert false (* absurd case *)
    | G_vertex (d, x) -> G_vertex ((coq_G_minus_edge d x0 y), x)
    | G_edge (d, x, y0) ->
        if coq_E_set_eq_dec x x0 y0 y
        then G_eq d
        else G_eq (G_edge ((coq_G_minus_edge d x0 y), x, y0))
    | G_eq g0 -> G_eq (coq_G_minus_edge g0 x0 y)

