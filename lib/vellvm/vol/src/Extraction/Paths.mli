open Datatypes
open Edges
open Graphs
open List0
open Specif
open Vertices

type __ = Obj.t

type coq_Walk =
  | W_null of coq_Vertex
  | W_step of coq_Vertex * coq_Vertex * coq_Vertex * 
     coq_V_list * coq_E_list * coq_Walk

val coq_Walk_rect :
  (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
  coq_V_list -> coq_E_list -> coq_Walk -> 'a1 -> __ -> __ -> 'a1) ->
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk -> 'a1

val coq_Walk_rec :
  (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
  coq_V_list -> coq_E_list -> coq_Walk -> 'a1 -> __ -> __ -> 'a1) ->
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk -> 'a1

type coq_Trail =
  | T_null of coq_Vertex
  | T_step of coq_Vertex * coq_Vertex * coq_Vertex * 
     coq_V_list * coq_E_list * coq_Trail

val coq_Trail_rect :
  (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
  coq_V_list -> coq_E_list -> coq_Trail -> 'a1 -> __ -> __ -> __ -> 'a1) ->
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail -> 'a1

val coq_Trail_rec :
  (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
  coq_V_list -> coq_E_list -> coq_Trail -> 'a1 -> __ -> __ -> __ -> 'a1) ->
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail -> 'a1

type coq_Path =
  | P_null of coq_Vertex
  | P_step of coq_Vertex * coq_Vertex * coq_Vertex * 
     coq_V_list * coq_E_list * coq_Path

val coq_Path_rect :
  (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
  coq_V_list -> coq_E_list -> coq_Path -> 'a1 -> __ -> __ -> __ -> __ -> __
  -> __ -> 'a1) -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
  coq_Path -> 'a1

val coq_Path_rec :
  (coq_Vertex -> __ -> 'a1) -> (coq_Vertex -> coq_Vertex -> coq_Vertex ->
  coq_V_list -> coq_E_list -> coq_Path -> 'a1 -> __ -> __ -> __ -> __ -> __
  -> __ -> 'a1) -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
  coq_Path -> 'a1

val coq_P_backstep :
  coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
  coq_Path -> (coq_E_list, coq_Path) sigT

val coq_Trail_isa_walk :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail ->
  coq_Walk

val coq_Path_isa_trail :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
  coq_Trail

val coq_V_extract : coq_Vertex -> coq_V_list -> coq_V_list

val coq_P_extract :
  coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
  coq_Path -> (coq_E_list, coq_Path) sigT

val coq_Walk_to_path :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk ->
  (coq_V_list, (coq_E_list, coq_Path) sigT) sigT

val coq_Walk_eq :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk ->
  coq_Walk

val coq_Trail_eq :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail ->
  coq_Trail

val coq_Path_eq :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
  coq_Path

val coq_Walk_subgraph :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Walk ->
  coq_Walk

val coq_Trail_subgraph :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Trail ->
  coq_Trail

val coq_Path_subgraph :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
  coq_Path

val coq_Path_supergraph_vertex :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
  coq_Path

val coq_Path_supergraph_cons_vertex :
  coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
  coq_Path -> coq_Path

val coq_Path_supergraph_arc :
  coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list -> coq_Path ->
  coq_Graph -> coq_Path

val coq_Path_supergraph_cons_arc :
  coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list ->
  coq_E_list -> coq_Path -> coq_Path

val coq_Walk_append :
  coq_Vertex -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_V_list ->
  coq_E_list -> coq_E_list -> coq_Walk -> coq_Walk -> coq_Walk

val cdr : coq_V_list -> coq_V_list

val coq_E_reverse : coq_E_list -> coq_E_list

val coq_Walk_reverse :
  coq_Graph -> coq_Vertex -> coq_Vertex -> coq_V_list -> coq_E_list ->
  coq_Walk -> coq_Walk

