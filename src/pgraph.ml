module Int = struct
  type t = int
  let compare = compare
end

module IMap = Map.Make(Int)

type vertex = int

type edge = int

type ('a, 'b) t =
  { vtx_map: 'a IMap.t;
    edge_map: (int * int * 'b) IMap.t;
    succ: (edge * vertex) list IMap.t;
    pred: (edge * vertex) list IMap.t;
    vtx_counter: int;
    edge_counter: int;
  }

let empty =
  { vtx_map = IMap.empty;
    edge_map = IMap.empty;
    succ = IMap.empty;
    pred = IMap.empty;
    vtx_counter = 0;
    edge_counter = 0;
  }

let is_empty g =
  IMap.is_empty g.vtx_map

let add_in_list e v1 v2 m =
  match IMap.find_opt v1 m with
  | Some vs -> IMap.add v1 ((e, v2)::vs) m
  | None -> IMap.add v1 [(e, v2)] m

let add_vertex attr g =
  let g' = { g with vtx_map = IMap.add g.vtx_counter attr g.vtx_map;
                    vtx_counter = g.vtx_counter + 1;
           }
  in (g.vtx_counter, g')

let add_edge v1 v2 attr g =
  match IMap.find_opt v1 g.vtx_map, IMap.find_opt v2 g.vtx_map with
  | Some _, Some _ ->
    let g' = { g with edge_map = IMap.add g.edge_counter (v1, v2, attr) g.edge_map;
                      edge_counter = g.edge_counter + 1;
                      succ = add_in_list g.edge_counter v1 v2 g.succ;
                      pred = add_in_list g.edge_counter v2 v1 g.pred;
             }
    in
    (g.edge_counter, g')
  | None, _ ->
    failwith @@ "vertex " ^ string_of_int v1 ^ " not in graph"
  | _, None ->
    failwith @@ "vertex " ^ string_of_int v2 ^ " not in graph"

let remove_vertex v g =
  let filter = fun (_, v') -> v <> v' in
  { g with vtx_map = IMap.remove v g.vtx_map;
           edge_map = IMap.filter (fun _ (v1, v2, _) -> v <> v1 && v <> v2)
               g.edge_map;
           succ = IMap.map (fun vs -> List.filter filter vs) g.succ;
           pred = IMap.map (fun vs -> List.filter filter vs) g.pred;
  }

let remove_edge e g =
  let remove_in_list k m =
    IMap.update k (function
        | None -> None
        | Some evs ->
          match List.remove_assq e evs with
          | [] -> None
          | evs -> Some evs) m
  in
  match IMap.find_opt e g.edge_map with
  | None -> g
  | Some (v1, v2, _) ->
    { g with edge_map = IMap.remove e g.edge_map;
             succ = remove_in_list v1 g.succ;
             pred = remove_in_list v2 g.pred;
    }

let vertex_attr v g =
  IMap.find_opt v g.vtx_map

let edge_from e g =
  match IMap.find_opt e g.edge_map with
  | Some (v, _, _) -> Some v
  | None -> None

let edge_to e g =
  match IMap.find_opt e g.edge_map with
  | Some (_, v, _) -> Some v
  | None -> None

let edge_attr e g =
  match IMap.find_opt e g.edge_map with
  | Some (_, _, attr) -> Some attr
  | None -> None

let succ v g =
  match IMap.find_opt v g.succ with
  | Some vs -> vs
  | None -> []

let pred v g =
  match IMap.find_opt v g.pred with
  | Some vs -> vs
  | None -> []

let iter_vertex f g =
  IMap.iter f g.vtx_map

let iter_vertex_subset f g s =
  IMap.iter (fun k v -> if Pset.mem k s then f k v else ()) g.vtx_map

let iter_vertex_list f g l =
  List.iter (fun k ->
      match IMap.find_opt k g.vtx_map with
      | Some v -> f k v
      | None -> ()) l

let iter_edge f g =
  IMap.iter f g.edge_map

let fold_vertex f g =
  IMap.fold f g.vtx_map

let fold_edge f g =
  IMap.fold f g.edge_map

let fold = fold_edge

let print oc string_of_vtx string_of_edge g =
  let open Printf in
  fprintf oc "digraph G {\n";
  iter_vertex (fun v attr ->
      fprintf oc "  v%d [label=\"%s\"]\n" v (string_of_vtx v attr)
    ) g;
  iter_edge (fun e (v1, v2, attr) ->
      fprintf oc "  v%d -> v%d [label=\"%s\"]\n" v1 v2 (string_of_edge e attr)
    ) g;
  fprintf oc "}\n"

let transpose g =
  { g with succ = g.pred;
           pred = g.succ;
           edge_map = IMap.map (fun (v1, v2, attr) -> (v2, v1, attr)) g.edge_map;
  }

let vertices g =
  Pset.from_list compare @@ List.map fst @@ IMap.bindings g.vtx_map

let roots g =
  let no_roots = Pset.from_list compare @@ List.map fst @@ IMap.bindings g.pred in
  Pset.diff (vertices g) no_roots

(* topological sort *)

(* Kahn's algorithm *)
let topological_sort g =
  let rec aux l s g =
    if Pset.is_empty s then
      if IMap.is_empty g.edge_map then
        Some (List.rev l)
      else
        None (* cycle *)
    else
      let n = Pset.choose s in
      let s = Pset.remove n s in
      let (g, s) = match IMap.find_opt n g.succ with
        | None -> (g, s)
        | Some evs ->
          List.fold_left (fun (g, s) (e, m) ->
              let g = remove_edge e g in
              if pred m g = [] then (g, Pset.add m s) else (g, s)
            ) (g, s) evs
      in
      aux (n::l) s g
  in aux [] (roots g) g

(* transitive closure *)

(* Floyd–Warshall algorithm *)
let transitive_closure g =
  let module M = Map.Make(struct
      type t = int * int
      let compare = compare
    end) in
  let diag_matrix =
    IMap.fold (fun v _ m ->
        M.add (v, v) 1 m
      ) g.vtx_map M.empty
  in
  let edge_matrix =
    IMap.fold (fun v1 evs2 m ->
        List.fold_left (fun m (_, v2) ->
            M.add (v1, v2) 1 m
          ) m evs2
      ) g.succ diag_matrix
  in
  let dist_matrix =
    IMap.fold (fun k _ m ->
      IMap.fold (fun i _ m ->
          IMap.fold (fun j _ m ->
              match M.find_opt (i, j) m,
                    M.find_opt (i, k) m,
                    M.find_opt (k, j) m
              with
              | None, Some d1, Some d2 ->
                M.add (i, j) (d1 + d2) m
              | Some r, Some d1, Some d2 when r > d1 + d2 ->
                M.add (i, j) (d1 + d2) m
              | _, _, _ ->
                m
            ) g.vtx_map m
          ) g.vtx_map m
        ) g.vtx_map edge_matrix
  in
  let g = { g with edge_map =
                     IMap.map (fun (v1, v2, a) -> (v1, v2, Some a)) g.edge_map
          } in
  M.fold (fun (v1, v2) _ g ->
      let succsv1 = List.map snd @@ succ v1 g in
      if List.mem v2 succsv1 then g
      else snd @@ add_edge v1 v2 None g
    ) dist_matrix g

(* reachable *)

let reachable v g =
  Pset.from_list compare @@ List.map snd @@ succ v @@ transitive_closure g

(* strongly connected components *)

(* Kosaraju's algorithm *)

let scc g =
  let rec visit (m, l) u =
    match IMap.find_opt u m with
    | None ->
      assert false
    | Some `Unvisited ->
      List.fold_left visit (IMap.add u `Visited m, u::l)
      @@ List.map snd @@ succ u g
    | Some `Visited ->
      (m, l)
  in
  let rec assign (s, c) u r =
    if Pset.mem u s then (s, c) else
      let s = Pset.add u s in
      let c =
        IMap.update r (function
            | None -> Some [u]
            | Some us -> Some (u::us)
          ) c
      in
      match IMap.find_opt u g.pred with
      | None ->
        (s, c)
      | Some vs ->
        List.fold_left (fun (s, c) v -> assign (s, c) v r) (s, c)
        @@ List.map snd vs
  in
  (* 1. For each vertex u of the graph, mark u as unvisited. Let L be empty. *)
  let m = IMap.map (fun _ -> `Unvisited) @@ g.vtx_map in
  (* 2. For each vertex u of the graph do Visit(u) *)
  let (_, l) = IMap.fold (fun v _ (m, l) -> visit (m, l) v) g.vtx_map (m, []) in
  (* 3. For each element u of L in order, do Assign(u,u) *)
  let (_, c) =
    List.fold_left (fun acc v -> assign acc v v)
      (Pset.empty compare, IMap.empty) @@ List.rev l
  in List.map snd @@ IMap.bindings c


(* connected sub? Components *)



