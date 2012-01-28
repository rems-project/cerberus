open Vertices

(** val coq_E_set_eq_dec :
    coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_Vertex -> bool **)

let coq_E_set_eq_dec x x' y y' =
  if coq_V_eq_dec x x'
  then coq_V_eq_dec y y'
  else if coq_V_eq_dec x y' then coq_V_eq_dec y x' else false

type coq_Edge =
  | E_ends of coq_Vertex * coq_Vertex

(** val coq_Edge_rect :
    (coq_Vertex -> coq_Vertex -> 'a1) -> coq_Edge -> 'a1 **)

let coq_Edge_rect f = function
  | E_ends (x, x0) -> f x x0

(** val coq_Edge_rec :
    (coq_Vertex -> coq_Vertex -> 'a1) -> coq_Edge -> 'a1 **)

let coq_Edge_rec f = function
  | E_ends (x, x0) -> f x x0

type coq_E_list = coq_Edge list

(** val coq_E_nil : coq_Edge list **)

let coq_E_nil =
  []

(** val coq_E_eq_dec : coq_Edge -> coq_Edge -> bool **)

let coq_E_eq_dec u v =
  let E_ends (a, b) = u in
  let E_ends (c, d) = v in
  if coq_V_eq_dec a c
  then coq_V_eq_dec b d
  else if coq_V_eq_dec a d then coq_V_eq_dec b c else false

