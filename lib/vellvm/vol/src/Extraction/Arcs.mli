open Datatypes
open Enumerated
open Sets
open Vertices

type coq_Arc =
  | A_ends of coq_Vertex * coq_Vertex

val coq_Arc_rect : (coq_Vertex -> coq_Vertex -> 'a1) -> coq_Arc -> 'a1

val coq_Arc_rec : (coq_Vertex -> coq_Vertex -> 'a1) -> coq_Arc -> 'a1

val coq_A_eq_dec : coq_Arc -> coq_Arc -> bool

val coq_A_tail : coq_Arc -> coq_Vertex

val coq_A_head : coq_Arc -> coq_Vertex

val coq_A_loop : coq_Vertex -> coq_Arc

type coq_A_list = coq_Arc list

val coq_A_nil : coq_Arc list

val coq_A_in_dec : coq_Arc -> coq_Arc coq_U_list -> bool

val coq_A_sum : (coq_Arc -> nat) -> coq_Arc coq_U_list -> nat

type coq_A_set = coq_Arc coq_U_set

type coq_A_enumerable = coq_Arc coq_U_enumerable

val coq_A_enumerable_sum :
  (coq_Arc -> nat) -> coq_Arc coq_U_enumerable -> nat

val coq_A_union_dec : coq_Arc -> bool -> bool -> bool

val coq_A_in_neighborhood : coq_Vertex -> coq_A_list -> coq_V_list

val coq_A_out_neighborhood : coq_Vertex -> coq_A_list -> coq_V_list

