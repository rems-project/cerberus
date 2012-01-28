open Datatypes
open Edges
open Graphs
open List0
open Specif
open Vertices

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Walk =
  | W_null of coq_Vertex
  | W_step of coq_Vertex * coq_Vertex * coq_Vertex * 
     coq_V_list * coq_E_list * coq_Walk

(** val coq_Walk_rect :
    (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
    coq_V_list -> coq_E_list -> coq_Walk -> 'a1 -> __ -> __ -> 'a1) ->
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk -> 'a1 **)

let rec coq_Walk_rect f f0 v v0 v1 e = function
  | W_null x -> f x __
  | W_step (x, y, z, vl, el, w0) ->
      f0 x y z vl el w0 (coq_Walk_rect f f0 y z vl el w0) __ __

(** val coq_Walk_rec :
    (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
    coq_V_list -> coq_E_list -> coq_Walk -> 'a1 -> __ -> __ -> 'a1) ->
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk -> 'a1 **)

let rec coq_Walk_rec f f0 v v0 v1 e = function
  | W_null x -> f x __
  | W_step (x, y, z, vl, el, w0) ->
      f0 x y z vl el w0 (coq_Walk_rec f f0 y z vl el w0) __ __

type coq_Trail =
  | T_null of coq_Vertex
  | T_step of coq_Vertex * coq_Vertex * coq_Vertex * 
     coq_V_list * coq_E_list * coq_Trail

(** val coq_Trail_rect :
    (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
    coq_V_list -> coq_E_list -> coq_Trail -> 'a1 -> __ -> __ -> __ -> 'a1) ->
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail -> 'a1 **)

let rec coq_Trail_rect f f0 v v0 v1 e = function
  | T_null x -> f x __
  | T_step (x, y, z, vl, el, t0) ->
      f0 x y z vl el t0 (coq_Trail_rect f f0 y z vl el t0) __ __ __

(** val coq_Trail_rec :
    (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
    coq_V_list -> coq_E_list -> coq_Trail -> 'a1 -> __ -> __ -> __ -> 'a1) ->
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail -> 'a1 **)

let rec coq_Trail_rec f f0 v v0 v1 e = function
  | T_null x -> f x __
  | T_step (x, y, z, vl, el, t0) ->
      f0 x y z vl el t0 (coq_Trail_rec f f0 y z vl el t0) __ __ __

type coq_Path =
  | P_null of coq_Vertex
  | P_step of coq_Vertex * coq_Vertex * coq_Vertex * 
     coq_V_list * coq_E_list * coq_Path

(** val coq_Path_rect :
    (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
    coq_V_list -> coq_E_list -> coq_Path -> 'a1 -> __ -> __ -> __ -> __ -> __
    -> __ -> 'a1) -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
    coq_Path -> 'a1 **)

let rec coq_Path_rect f f0 v v0 v1 e = function
  | P_null x -> f x __
  | P_step (x, y, z, vl, el, p0) ->
      f0 x y z vl el p0 (coq_Path_rect f f0 y z vl el p0) __ __ __ __ __ __

(** val coq_Path_rec :
    (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
    coq_V_list -> coq_E_list -> coq_Path -> 'a1 -> __ -> __ -> __ -> __ -> __
    -> __ -> 'a1) -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
    coq_Path -> 'a1 **)

let rec coq_Path_rec f f0 v v0 v1 e = function
  | P_null x -> f x __
  | P_step (x, y, z, vl, el, p0) ->
      f0 x y z vl el p0 (coq_Path_rec f f0 y z vl el p0) __ __ __ __ __ __

(** val coq_P_backstep :
    coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
    coq_Path -> (coq_E_list, coq_Path) sigT **)

let coq_P_backstep x y z vl el = function
  | P_null x0 -> assert false (* absurd case *)
  | P_step (x0, y0, z0, vl0, el0, h0) -> Coq_existT (el0, h0)

(** val coq_Trail_isa_walk :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail ->
    coq_Walk **)

let rec coq_Trail_isa_walk v v0 v1 e = function
  | T_null x -> W_null x
  | T_step (x, y, z, vl, el, t0) -> W_step (x, y, z, vl, el,
      (coq_Trail_isa_walk y z vl el t0))

(** val coq_Path_isa_trail :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
    coq_Trail **)

let rec coq_Path_isa_trail v v0 v1 e = function
  | P_null x -> T_null x
  | P_step (x, y, z, vl, el, p0) -> T_step (x, y, z, vl, el,
      (coq_Path_isa_trail y z vl el p0))

(** val coq_V_extract : coq_Vertex -> coq_V_list -> coq_V_list **)

let rec coq_V_extract x = function
  | [] -> coq_V_nil
  | y::vl' -> if coq_V_in_dec x vl' then coq_V_extract x vl' else vl'

(** val coq_P_extract :
    coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
    coq_Path -> (coq_E_list, coq_Path) sigT **)

let rec coq_P_extract x y z vl el x0 =
  match vl with
    | [] -> Coq_existT (el, x0)
    | y0::l ->
        let Coq_existT (x1, x2) = coq_P_backstep y y0 z l el x0 in
        if coq_V_in_dec x (y0::l)
        then coq_P_extract x y0 z l x1 x2
        else Coq_existT (el, x0)

(** val coq_Walk_to_path :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk ->
    (coq_V_list, (coq_E_list, coq_Path) sigT) sigT **)

let rec coq_Walk_to_path v v0 v1 e = function
  | W_null x -> Coq_existT (coq_V_nil, (Coq_existT (coq_E_nil, (P_null x))))
  | W_step (x, y, z, vl, el, w0) ->
      let Coq_existT (x0, x1) = coq_Walk_to_path y z vl el w0 in
      let Coq_existT (x2, x3) = x1 in
      if coq_V_in_dec x (y::x0)
      then let Coq_existT (x4, x5) = coq_P_extract x y z x0 x2 x3 in
           Coq_existT ((coq_V_extract x (y::x0)), (Coq_existT (x4, x5)))
      else if coq_V_in_dec y x0
           then Coq_existT ((y::coq_V_nil), (Coq_existT (((E_ends (x,
                  y))::coq_E_nil), (P_step (x, y, z, coq_V_nil, coq_E_nil,
                  (P_null y))))))
           else Coq_existT ((y::x0), (Coq_existT (((E_ends (x, y))::x2),
                  (P_step (x, y, z, x0, x2, x3)))))

(** val coq_Walk_eq :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk ->
    coq_Walk **)

let rec coq_Walk_eq v v0 v1 e = function
  | W_null x -> W_null x
  | W_step (x, y, z, vl, el, w0) -> W_step (x, y, z, vl, el,
      (coq_Walk_eq y z vl el w0))

(** val coq_Trail_eq :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail ->
    coq_Trail **)

let rec coq_Trail_eq v v0 v1 e = function
  | T_null x -> T_null x
  | T_step (x, y, z, vl, el, t0) -> T_step (x, y, z, vl, el,
      (coq_Trail_eq y z vl el t0))

(** val coq_Path_eq :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
    coq_Path **)

let rec coq_Path_eq v v0 v1 e = function
  | P_null x -> P_null x
  | P_step (x, y, z, vl, el, p0) -> P_step (x, y, z, vl, el,
      (coq_Path_eq y z vl el p0))

(** val coq_Walk_subgraph :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk ->
    coq_Walk **)

let rec coq_Walk_subgraph v v0 v1 e = function
  | W_null x -> W_null x
  | W_step (x, y, z, vl, el, w0) -> W_step (x, y, z, vl, el,
      (coq_Walk_subgraph y z vl el w0))

(** val coq_Trail_subgraph :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail ->
    coq_Trail **)

let rec coq_Trail_subgraph v v0 v1 e = function
  | T_null x -> T_null x
  | T_step (x, y, z, vl, el, t0) -> T_step (x, y, z, vl, el,
      (coq_Trail_subgraph y z vl el t0))

(** val coq_Path_subgraph :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
    coq_Path **)

let rec coq_Path_subgraph v v0 v1 e = function
  | P_null x -> P_null x
  | P_step (x, y, z, vl, el, p0) -> P_step (x, y, z, vl, el,
      (coq_Path_subgraph y z vl el p0))

(** val coq_Path_supergraph_vertex :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
    coq_Path **)

let rec coq_Path_supergraph_vertex v v0 v1 e = function
  | P_null x -> P_null x
  | P_step (x, y, z, vl, el, p0) -> P_step (x, y, z, vl, el,
      (coq_Path_supergraph_vertex y z vl el p0))

(** val coq_Path_supergraph_cons_vertex :
    coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
    coq_Path -> coq_Path **)

let rec coq_Path_supergraph_cons_vertex x y z vl el = function
  | P_null x0 -> P_null x0
  | P_step (x0, y0, z0, vl0, el0, p0) -> P_step (x0, y0, z0, vl0, el0,
      (coq_Path_supergraph_cons_vertex y0 z0 z vl0 el0 p0))

(** val coq_Path_supergraph_arc :
    coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
    coq_Graph -> coq_Path **)

let rec coq_Path_supergraph_arc v v0 v1 e p h =
  match p with
    | P_null x -> P_null x
    | P_step (x, y, z, vl, el, p0) -> P_step (x, y, z, vl, el,
        (coq_Path_supergraph_arc y z vl el p0 h))

(** val coq_Path_supergraph_cons_arc :
    coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list ->
    coq_E_list -> coq_Path -> coq_Path **)

let rec coq_Path_supergraph_cons_arc x y x' y' vl el = function
  | P_null x0 -> P_null x0
  | P_step (x0, y0, z, vl0, el0, p0) -> P_step (x0, y0, z, vl0, el0,
      (coq_Path_supergraph_cons_arc y0 z x' y' vl0 el0 p0))

(** val coq_Walk_append :
    coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_V_list ->
    coq_E_list -> coq_E_list -> coq_Walk -> coq_Walk -> coq_Walk **)

let rec coq_Walk_append x y z vl vl' el el' hw h =
  match hw with
    | W_null x0 -> h
    | W_step (x0, y0, z0, vl0, el0, w) -> W_step (x0, y0, z, 
        (app vl0 vl'), (app el0 el'),
        (coq_Walk_append y0 z0 z vl0 vl' el0 el' w h))

(** val cdr : coq_V_list -> coq_V_list **)

let cdr = function
  | [] -> coq_V_nil
  | x::vl' -> vl'

(** val coq_E_reverse : coq_E_list -> coq_E_list **)

let rec coq_E_reverse = function
  | [] -> coq_E_nil
  | e::el' ->
      let E_ends (x, y) = e in
      app (coq_E_reverse el') ((E_ends (y, x))::coq_E_nil)

(** val coq_Walk_reverse :
    coq_Graph -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
    coq_Walk -> coq_Walk **)

let rec coq_Walk_reverse g x y vl el = function
  | W_null x0 -> W_null x0
  | W_step (x0, y0, z, vl0, el0, w) ->
      coq_Walk_append z y0 x0 (cdr (app (rev vl0) (y0::[]))) (x0::[])
        (coq_E_reverse el0) ((E_ends (y0, x0))::coq_E_nil)
        (coq_Walk_reverse g y0 z vl0 el0 w) (W_step (y0, x0, x0, [],
        coq_E_nil, (W_null x0)))

