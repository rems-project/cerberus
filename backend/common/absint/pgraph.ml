module IMap = Map.Make(struct
    type t = int
    let compare = compare
  end)

type vertex_id = int

type edge_id = int

type ('a, 'b) graph =
  { vtx_map: 'a IMap.t;
    edge_map: (int * 'b * int) IMap.t;
    succ: (edge_id * vertex_id) list IMap.t;
    pred: (edge_id * vertex_id) list IMap.t;
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
    let g' = { g with edge_map = IMap.add g.edge_counter (v1, attr, v2) g.edge_map;
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

let update_vertex v f g =
  let opt_map = function None -> None | Some x -> Some (f x) in
  { g with vtx_map = IMap.update v opt_map g.vtx_map }

let update_edge e f g =
  let opt_map = function None -> None | Some (v1, x, v2) -> Some (v1, f x, v2) in
  { g with edge_map = IMap.update e opt_map g.edge_map }

let remove_vertex v g =
  let filter = fun (_, v') -> v <> v' in
  { g with vtx_map = IMap.remove v g.vtx_map;
           edge_map = IMap.filter (fun _ (v1, _, v2) -> v <> v1 && v <> v2)
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
  | Some (v1,_,v2) ->
    { g with edge_map = IMap.remove e g.edge_map;
             succ = remove_in_list v1 g.succ;
             pred = remove_in_list v2 g.pred;
    }

let vertex v g =
  IMap.find_opt v g.vtx_map

let edge e g =
  IMap.find_opt e g.edge_map

let succ v g =
  match IMap.find_opt v g.succ with
  | Some vs -> vs
  | None -> []

let pred v g =
  match IMap.find_opt v g.pred with
  | Some vs -> vs
  | None -> []

let remove_isolated_vertices g =
  IMap.fold (fun v _ g ->
      match succ v g, pred v g with
      | [], [] -> remove_vertex v g
      | _, _ -> g
    ) g.vtx_map g

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

let map fv fe g =
  { g with vtx_map = IMap.mapi fv g.vtx_map;
           edge_map = IMap.mapi (fun e (v1, attr, v2) ->
               (v1, fe e attr, v2)) g.edge_map; }


let print oc string_of_vtx string_of_edge g =
  let open Printf in
  fprintf oc "digraph G {\n";
  iter_vertex (fun v attr ->
      fprintf oc "  v%d [label=\"%s\"]\n" v (string_of_vtx v attr)
    ) g;
  iter_edge (fun e (v1, attr, v2) ->
      fprintf oc "  v%d -> v%d [label=\"%s\"]\n" v1 v2 (string_of_edge e attr)
    ) g;
  fprintf oc "}\n"

let transpose g =
  { g with succ = g.pred;
           pred = g.succ;
           edge_map = IMap.map (fun (v1, v2, attr) -> (v2, v1, attr)) g.edge_map;
  }

let vertices g =
  List.map fst @@ IMap.bindings g.vtx_map

let edges g =
  List.map fst @@ IMap.bindings g.edge_map

let roots g =
  let no_roots = Pset.from_list compare @@ List.map fst @@ IMap.bindings g.pred in
  Pset.diff (Pset.from_list compare @@ vertices g) no_roots

let is_root v g =
  Pset.mem v (roots g)

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
                     IMap.map (fun (v1, a, v2) -> (v1, Some a, v2)) g.edge_map
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

(* weak topological ordering *)
(* Francois Bourdoncle 1993 *)

let wto g root =
  let open Nested_list in
  let num = ref 0 in
  let dfa = Hashtbl.create 20 in
  let stack = Stack.create () in
  let rec component v =
    let part = List.fold_left (fun part (_, v_succ) ->
        match Hashtbl.find_opt dfa v_succ with
        | Some (Some n) when n = 0 ->
          snd @@ visit part v_succ
        | _ ->
          part
      ) [] @@ succ v g
    in (Atom v) :: part
  and visit part v =
    Stack.push v stack;
    num := !num + 1;
    Hashtbl.add dfa v (Some !num);
    let head = ref (Some !num) in
    let loop = ref false in
    let part =
      List.fold_left (fun part (_, v_succ) ->
          let (min, part) =
            match Hashtbl.find_opt dfa v_succ with
            | Some (Some n) when n = 0 ->
              visit part v_succ
            | Some n_opt ->
              (n_opt, part)
            | None ->
              assert false
          in
          match min, !head with
          | Some m, Some h when m <= h ->
            head := min;
            loop := true;
            part
          | _ ->
            part
        ) part @@ succ v g
    in
    match Hashtbl.find_opt dfa v with
    | Some n_opt when !head = n_opt ->
      Hashtbl.add dfa v None;
      let elem = ref (Stack.pop stack) in
      if !loop then begin
        while !elem <> v do
          Hashtbl.add dfa !elem (Some 0);
          elem := Stack.pop stack
        done;
        (!head, (List (component v)) :: part)
      end else begin
        (!head, (Atom v) :: part)
      end
    | _ ->
      (!head, part)
  in
  IMap.iter (fun v _ -> Hashtbl.add dfa v (Some 0)) g.vtx_map;
  snd @@ visit [] root
