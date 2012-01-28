open Datatypes
open Enumerated
open Sets
open Vertices

type coq_Arc =
  | A_ends of coq_Vertex * coq_Vertex

(** val coq_Arc_rect :
    (coq_Vertex -> coq_Vertex -> 'a1) -> coq_Arc -> 'a1 **)

let coq_Arc_rect f = function
  | A_ends (x, x0) -> f x x0

(** val coq_Arc_rec : (coq_Vertex -> coq_Vertex -> 'a1) -> coq_Arc -> 'a1 **)

let coq_Arc_rec f = function
  | A_ends (x, x0) -> f x x0

(** val coq_A_eq_dec : coq_Arc -> coq_Arc -> bool **)

let coq_A_eq_dec a b =
  let A_ends (v, v0) = a in
  let A_ends (v1, v2) = b in
  if coq_V_eq_dec v v1 then coq_V_eq_dec v0 v2 else false

(** val coq_A_tail : coq_Arc -> coq_Vertex **)

let coq_A_tail = function
  | A_ends (x, y) -> x

(** val coq_A_head : coq_Arc -> coq_Vertex **)

let coq_A_head = function
  | A_ends (x, y) -> y

(** val coq_A_loop : coq_Vertex -> coq_Arc **)

let coq_A_loop x =
  A_ends (x, x)

type coq_A_list = coq_Arc list

(** val coq_A_nil : coq_Arc list **)

let coq_A_nil =
  []

(** val coq_A_in_dec : coq_Arc -> coq_Arc coq_U_list -> bool **)

let coq_A_in_dec =
  coq_U_in_dec coq_A_eq_dec

(** val coq_A_sum : (coq_Arc -> nat) -> coq_Arc coq_U_list -> nat **)

let coq_A_sum =
  coq_U_sum

type coq_A_set = coq_Arc coq_U_set

type coq_A_enumerable = coq_Arc coq_U_enumerable

(** val coq_A_enumerable_sum :
    (coq_Arc -> nat) -> coq_Arc coq_U_enumerable -> nat **)

let coq_A_enumerable_sum f x =
  coq_U_enumerable_sum f x

(** val coq_A_union_dec : coq_Arc -> bool -> bool -> bool **)

let coq_A_union_dec x x0 x1 =
  coq_Union_dec x x0 x1

(** val coq_A_in_neighborhood : coq_Vertex -> coq_A_list -> coq_V_list **)

let rec coq_A_in_neighborhood x = function
  | [] -> coq_V_nil
  | a::la' ->
      let A_ends (x', y') = a in
      if coq_V_eq_dec x y'
      then x'::(coq_A_in_neighborhood x la')
      else coq_A_in_neighborhood x la'

(** val coq_A_out_neighborhood : coq_Vertex -> coq_A_list -> coq_V_list **)

let rec coq_A_out_neighborhood x = function
  | [] -> coq_V_nil
  | a::la' ->
      let A_ends (x', y') = a in
      if coq_V_eq_dec x x'
      then y'::(coq_A_out_neighborhood x la')
      else coq_A_out_neighborhood x la'

