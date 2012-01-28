open Arcs
open Datatypes
open Edges
open Graphs
open Paths
open Specif
open Vertices

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Connected =
  | C_isolated of coq_Vertex
  | C_leaf of coq_Connected * coq_Vertex * coq_Vertex
  | C_edge of coq_Connected * coq_Vertex * coq_Vertex
  | C_eq of coq_Connected

(** val coq_Connected_rec :
    (coq_Vertex -> 'a1) -> (__ -> __ -> coq_Connected -> 'a1 -> coq_Vertex ->
    coq_Vertex -> __ -> __ -> 'a1) -> (__ -> __ -> coq_Connected -> 'a1 ->
    coq_Vertex -> coq_Vertex -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (__ ->
    __ -> __ -> __ -> __ -> __ -> coq_Connected -> 'a1 -> 'a1) ->
    coq_Connected -> 'a1 **)

let rec coq_Connected_rec f f0 f1 f2 = function
  | C_isolated x -> f x
  | C_leaf (co, x, y) ->
      f0 __ __ co (coq_Connected_rec f f0 f1 f2 co) x y __ __
  | C_edge (co, x, y) ->
      f1 __ __ co (coq_Connected_rec f f0 f1 f2 co) x y __ __ __ __ __
  | C_eq c0 -> f2 __ __ __ __ __ __ c0 (coq_Connected_rec f f0 f1 f2 c0)

(** val coq_Connected_Isa_Graph : coq_Connected -> coq_Graph **)

let rec coq_Connected_Isa_Graph = function
  | C_isolated x -> G_eq (G_vertex (G_empty, x))
  | C_leaf (co, x, y) -> G_edge ((G_vertex ((coq_Connected_Isa_Graph co),
      y)), x, y)
  | C_edge (co, x, y) -> G_edge ((coq_Connected_Isa_Graph co), x, y)
  | C_eq c0 -> G_eq (coq_Connected_Isa_Graph c0)

(** val coq_C_v_dec : coq_Connected -> coq_Vertex -> bool **)

let coq_C_v_dec c x =
  coq_G_v_dec (coq_Connected_Isa_Graph c) x

(** val coq_C_a_dec : coq_Connected -> coq_Arc -> bool **)

let coq_C_a_dec c x =
  coq_G_a_dec (coq_Connected_Isa_Graph c) x

(** val coq_Connected_walk :
    coq_Connected -> coq_Vertex -> coq_Vertex -> (coq_V_list, (coq_E_list,
    coq_Walk) sigT) sigT **)

let rec coq_Connected_walk c x0 y =
  match c with
    | C_isolated x -> Coq_existT (coq_V_nil, (Coq_existT (coq_E_nil, (W_null
        y))))
    | C_leaf (co, x, y0) ->
        if coq_V_union_single_dec y0 x0
        then if coq_V_union_single_dec y0 y
             then Coq_existT (coq_V_nil, (Coq_existT (coq_E_nil, (W_null
                    y0))))
             else let Coq_existT (x1, x2) = coq_Connected_walk co x y in
                  Coq_existT ((x::x1),
                  (let Coq_existT (x3, x4) = x2 in
                  Coq_existT (((E_ends (y0, x))::x3), (W_step (y0, x, y, x1,
                  x3, (coq_Walk_subgraph x y x1 x3 x4))))))
        else if coq_V_union_single_dec y0 y
             then let Coq_existT (x1, x2) = coq_Connected_walk co x0 x in
                  Coq_existT ((app x1 (y::coq_V_nil)),
                  (let Coq_existT (x3, x4) = x2 in
                  Coq_existT ((app x3 ((E_ends (x, y))::coq_E_nil)),
                  (coq_Walk_append x0 x y x1 (y::coq_V_nil) x3 ((E_ends (x,
                    y))::coq_E_nil) (coq_Walk_subgraph x0 x x1 x3 x4) (W_step
                    (x, y, y, coq_V_nil, coq_E_nil, (W_null y)))))))
             else let Coq_existT (x1, x2) = coq_Connected_walk co x0 y in
                  Coq_existT (x1,
                  (let Coq_existT (x3, x4) = x2 in
                  Coq_existT (x3, (coq_Walk_subgraph x0 y x1 x3 x4))))
    | C_edge (co, x, y0) ->
        let Coq_existT (x1, x2) = coq_Connected_walk co x0 y in
        Coq_existT (x1,
        (let Coq_existT (x3, x4) = x2 in
        Coq_existT (x3, (coq_Walk_subgraph x0 y x1 x3 x4))))
    | C_eq c0 ->
        let Coq_existT (x, x1) = coq_Connected_walk c0 x0 y in
        Coq_existT (x,
        (let Coq_existT (x2, x3) = x1 in
        Coq_existT (x2, (coq_Walk_eq x0 y x x2 x3))))

(** val coq_Connected_path :
    coq_Connected -> coq_Vertex -> coq_Vertex -> (coq_V_list, (coq_E_list,
    coq_Path) sigT) sigT **)

let coq_Connected_path g x y =
  let Coq_existT (x0, x1) = coq_Connected_walk g x y in
  let Coq_existT (x2, x3) = x1 in coq_Walk_to_path x y x0 x2 x3

(** val coq_C_minus_pendant :
    coq_Connected -> coq_Vertex -> coq_Vertex -> coq_Connected **)

let rec coq_C_minus_pendant c x0 y =
  match c with
    | C_isolated x -> assert false (* absurd case *)
    | C_leaf (co, x, y0) ->
        if coq_V_union_single_dec y0 y
        then C_eq co
        else if coq_V_union_single_dec y0 x0
             then C_eq (C_isolated y0)
             else C_eq (C_leaf ((coq_C_minus_pendant co x0 y), x, y0))
    | C_edge (co, x, y0) -> C_eq (C_edge ((coq_C_minus_pendant co x0 y), x,
        y0))
    | C_eq c0 -> coq_C_minus_pendant c0 x0 y

