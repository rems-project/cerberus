type vertex_id = int
type edge_id = int

type ('v, 'e) graph

val empty: ('v, 'e) graph
val is_empty: ('v, 'e) graph -> bool

val add_vertex: 'v -> ('v, 'e) graph -> vertex_id * ('v, 'e) graph
(* it throws an exception if vertices are not in the graph *)
val add_edge: vertex_id -> vertex_id -> 'e -> ('v, 'e) graph -> edge_id * ('v, 'e) graph

val update_vertex: vertex_id -> ('v -> 'v) -> ('v, 'e) graph -> ('v, 'e) graph
val update_edge: edge_id -> ('e -> 'e) -> ('v, 'e) graph -> ('v, 'e) graph

val remove_vertex: vertex_id -> ('v, 'e) graph -> ('v, 'e) graph
val remove_edge: edge_id -> ('v, 'e) graph -> ('v, 'e) graph

val remove_isolated_vertices: ('v, 'e) graph -> ('v, 'e) graph

val vertices: ('v, 'e) graph -> vertex_id list
val edges: ('v, 'e) graph -> edge_id list

val roots: ('v, 'e) graph -> vertex_id Pset.set
val is_root: vertex_id -> ('v, 'e) graph -> bool

val vertex: vertex_id -> ('v, 'e) graph -> 'v option
val edge: edge_id -> ('v, 'e) graph -> (vertex_id * 'e * vertex_id) option

val succ: vertex_id -> ('v, 'e) graph -> (edge_id * vertex_id) list
val pred: vertex_id -> ('v, 'e) graph -> (edge_id * vertex_id) list

val iter_vertex: (vertex_id -> 'v -> unit) -> ('v, 'e) graph -> unit
val iter_edge: (edge_id -> vertex_id * 'e * vertex_id -> unit) ->
               ('v, 'e) graph -> unit

val fold_vertex: (vertex_id -> 'v -> 'a -> 'a) -> ('v, 'e) graph -> 'a -> 'a
val fold_edge: (edge_id -> vertex_id * 'e * vertex_id -> 'a -> 'a) ->
               ('v, 'e) graph -> 'a -> 'a

val fold: (edge_id -> vertex_id * 'e * vertex_id -> 'a -> 'a) ->
          ('v, 'e) graph -> 'a -> 'a

val map: (vertex_id -> 'v1 -> 'v2) -> (edge_id -> 'e1 -> 'e2) -> ('v1, 'e1) graph -> ('v2, 'e2) graph

val print: out_channel ->
           (vertex_id -> 'v -> string) ->
           (edge_id -> 'e -> string) ->
           ('v, 'e) graph -> unit

(* returns none if graph contains a cycle *)
val topological_sort: ('v, 'e) graph -> vertex_id list option

val transitive_closure: ('v, 'e) graph -> ('v, 'e option) graph

val reachable: vertex_id -> ('v, 'e) graph -> vertex_id Pset.set

(* strongly connected components *)
val scc: ('v, 'e) graph -> vertex_id list list

(* weak topological ordering *)
val wto: ('v, 'e) graph -> vertex_id -> vertex_id Nested_list.nlist