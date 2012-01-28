open Arcs
open Datatypes
open Edges
open Graphs
open Paths
open Specif
open Vertices

type __ = Obj.t

type coq_Connected =
  | C_isolated of coq_Vertex
  | C_leaf of coq_Connected * coq_Vertex * coq_Vertex
  | C_edge of coq_Connected * coq_Vertex * coq_Vertex
  | C_eq of coq_Connected

val coq_Connected_rec :
  (coq_Vertex -> 'a1) -> (__ -> __ -> coq_Connected -> 'a1 -> coq_Vertex ->
  coq_Vertex -> __ -> __ -> 'a1) -> (__ -> __ -> coq_Connected -> 'a1 ->
  coq_Vertex -> coq_Vertex -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (__ -> __
  -> __ -> __ -> __ -> __ -> coq_Connected -> 'a1 -> 'a1) -> coq_Connected ->
  'a1

val coq_Connected_Isa_Graph : coq_Connected -> coq_Graph

val coq_C_v_dec : coq_Connected -> coq_Vertex -> bool

val coq_C_a_dec : coq_Connected -> coq_Arc -> bool

val coq_Connected_walk :
  coq_Connected -> coq_Vertex -> coq_Vertex -> (coq_V_list, (coq_E_list,
  coq_Walk) sigT) sigT

val coq_Connected_path :
  coq_Connected -> coq_Vertex -> coq_Vertex -> (coq_V_list, (coq_E_list,
  coq_Path) sigT) sigT

val coq_C_minus_pendant :
  coq_Connected -> coq_Vertex -> coq_Vertex -> coq_Connected

