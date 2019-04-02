open Pgraph
open Nested_list

let debug msg = Debug_ocaml.print_debug 5 [] (fun _ -> msg)

module type FIXPOINT = sig
  type absstate

  type t =
    { bottom: vertex_id -> absstate;
      init: vertex_id -> absstate;
      is_bottom: vertex_id -> absstate -> bool;
      is_leq: vertex_id -> absstate -> absstate -> bool;
      join: vertex_id -> absstate -> absstate -> absstate;
      join_list: vertex_id -> absstate list -> absstate;
      widening: vertex_id -> absstate -> absstate -> absstate;
      apply: edge_id -> absstate -> absstate;
    }

  val run: t -> ('a, 'b) Pgraph.graph ->
           Pgraph.vertex_id ->
           (absstate, unit) Pgraph.graph
end

module Make(S: sig type t end): (FIXPOINT with type absstate = S.t) = struct
  type absstate = S.t

  type t =
    { bottom: vertex_id -> S.t;
      init: vertex_id -> S.t;
      is_bottom: vertex_id -> S.t -> bool;
      is_leq: vertex_id -> S.t -> S.t -> bool;
      join: vertex_id -> S.t -> S.t -> S.t;
      join_list: vertex_id -> S.t list -> S.t;
      widening: vertex_id -> S.t -> S.t -> S.t;
      apply: edge_id -> S.t -> S.t;
    }

  (* state attached to vertices *)
  type vertex_attr =
    { abstract: S.t;
      is_empty: bool; (* empty state *)
    }

  (* whether or not is coming from a bot state *)
  type edge_attr = bool

  (* strategy node state *)
  type strategy_node =
    { vertex: vertex_id;
      edges: (edge_id * vertex_id) list;
      widen: bool;
    }

  type strategy = strategy_node Nested_list.nlist

  (* internal state *)
  type state =
    { graph: (vertex_attr, edge_attr) graph;
      opers: t;
      vinit: vertex_id;
      widening_start: int;
      widening_descend: int;
      workset: vertex_id Pset.set;
    }

  module StateMonad = Monad.Make(struct type t = state end)
  open StateMonad

  (* check b do f () if true otherwise returns false *)
  let checkM bM f =
    bM >>= fun b -> if b then f () else return false

  let update_workset v0 =
    update @@ fun st ->
    let workset =
      List.fold_left (fun s (_, v) ->
          Pset.add v s
        ) st.workset @@ Pgraph.succ v0 st.graph
    in
    debug @@ "New work set: " ^ String.concat ", "
    @@ List.map string_of_int @@ Pset.elements workset;
    { st with workset; }

  let remove_workset v =
    update @@ fun st ->
    { st with workset = Pset.remove v st.workset }

  let get_workset () =
    get >>= fun st -> return st.workset

  let mem_workset v =
    get >>= fun st ->
    return @@ Pset.mem v st.workset

  let cardinal_workset () =
    get >>= fun st ->
    return @@ Pset.cardinal st.workset

  let widening_start () =
    get >>= fun st ->
    return st.widening_start

  let widening_descend () =
    get >>= fun st ->
    return st.widening_descend

  let attr_of_vertex v =
    get >>= fun st ->
    match Pgraph.vertex v st.graph with
    | Some attr -> return attr
    | None -> assert false

  let attr_of_edge e =
    get >>= fun st ->
    match Pgraph.edge e st.graph with
    | Some (_, attr, _) -> return attr
    | None -> assert false

  let abstract_of_vertex v =
    attr_of_vertex v >>= fun attr ->
    return attr.abstract

  let apply v abs =
    get >>= fun st ->
    return @@ st.opers.apply v abs

  let is_empty v =
    attr_of_vertex v >>= fun attr ->
    return attr.is_empty

  let is_bottom v abs =
    get >>= fun st ->
    return @@ st.opers.is_bottom v abs

  let update_vertex v abstract =
    update @@ fun st ->
    let attr = { abstract; is_empty = st.opers.is_bottom v abstract } in
    { st with graph = Pgraph.update_vertex v (fun _ -> attr) st.graph }

  let update_edge e is_empty =
    update @@ fun st ->
    { st with graph = Pgraph.update_edge e (fun _ -> is_empty) st.graph }

  let init_post_list v =
    get >>= fun st ->
    if st.vinit = v then
      return [st.opers.init v]
    else
      return []

  let join_post_list v lpost =
    get >>= fun st ->
    if lpost = [] then
      return @@ st.opers.bottom v
    else
      return @@ st.opers.join_list v lpost

  let widening v old_abs =
    debug ("Widening vertex");
    abstract_of_vertex v >>= fun new_abs ->
    get >>= fun st ->
    update_vertex v @@
    st.opers.widening v old_abs new_abs

  let is_leq v abs1 abs2 =
    get >>= fun st ->
    return @@ st.opers.is_leq v abs1 abs2

  let is_growing v old_attr =
    attr_of_vertex v >>= fun attr ->
    is_leq v attr.abstract old_attr.abstract >>= fun b ->
    return @@ not b

  let is_reducing v old_attr =
    attr_of_vertex v >>= fun attr ->
    is_leq v old_attr.abstract attr.abstract >>= fun b ->
    return @@ not b

  let propagate_vertex ~descend n =
    remove_workset n.vertex >>
    init_post_list n.vertex >>= fun lpost ->
    List.fold_left (fun lpostM (e, v) ->
        debug ("Propagating edge" ^ string_of_int e ^ " to v" ^ string_of_int v);
        lpostM >>= fun lpost ->
        attr_of_edge e >>= fun aempty ->
        is_empty v >>= fun is_empty ->
        if not (descend && aempty) && not is_empty then
          abstract_of_vertex v >>= fun abs ->
          apply e abs >>= fun post ->
          is_bottom v abs >>= function
          | true ->
            update_edge e true >>
            return lpost
          | false ->
            update_edge e false >>
            return @@ post :: lpost
        else
          update_edge e true >>
          return lpost
      ) (return lpost) n.edges >>= fun lpost ->
    join_post_list n.vertex lpost >>= update_vertex n.vertex

  let process_vertex ~widen n =
    let should_widen n =
      is_empty n.vertex >>= fun is_empty ->
      return (widen && n.widen && not is_empty)
    in
    debug ("Processing vertex: " ^ string_of_int n.vertex);
    attr_of_vertex n.vertex >>= fun old_attr ->
    propagate_vertex ~descend:false n >>
    checkM (is_growing n.vertex old_attr) begin fun () ->
      update_workset n.vertex >>
      whenM (should_widen n)
            (fun () -> widening n.vertex old_attr.abstract) >>
      return true
    end

  let descend_strategy stgy =
    let process n =
      checkM (mem_workset n.vertex) begin fun () ->
        attr_of_vertex n.vertex >>= fun old_attr ->
        propagate_vertex ~descend:true n >>
        whenM (is_reducing n.vertex old_attr)
              (fun () -> update_workset n.vertex) >>
        return true
      end
    in
    let rec loop (reducing, counter) =
      let counter = counter + 1 in
      Nested_list.fold (fun n accM ->
          accM >>= fun acc ->
          process n >>= fun reducing ->
          return (acc || reducing)
        ) stgy (return reducing)
      >>= fun reducing ->
      cardinal_workset () >>= fun card ->
      widening_descend () >>= fun wd ->
      let reducing = reducing && card > 0 in
      if reducing && counter < wd then
        loop (reducing,counter)
      else
        return ()
    in loop (false, 0)

  let descend stgy =
    widening_descend () >>= fun wd ->
    checkM (return (wd > 0)) begin fun () ->
      get_workset () >>= fun old_ws ->
      Nested_list.fold (fun n wsM ->
          wsM >>= fun ws ->
          attr_of_vertex n.vertex >>= fun attr ->
          if not attr.is_empty then
            return @@ Pset.add n.vertex ws
          else
            return ws
        ) stgy (return @@ Pset.empty compare) >>= fun ws ->
      update (fun st -> { st with workset = ws }) >>
      descend_strategy stgy >>
      cardinal_workset () >>= fun card ->
      update (fun st -> { st with workset = old_ws }) >>
      return (card > 0)
    end

  let rec process_strategy ~depth stgy =
    assert (depth >= 2);
    let aux ~widen = function
      | Atom n ->
        checkM (mem_workset n.vertex) (fun () -> process_vertex ~widen n)
      | List stgy ->
        process_strategy ~depth:(depth+1) stgy
    in
    let rec iterate (growing, looping) ~widen = function
      | [] ->
        return (growing, looping)
      | x::xs ->
        aux ~widen x >>= fun res ->
        iterate (growing || res, looping || res) ~widen xs
    in
    let rec loop (growing, counter) =
      let counter = counter + 1 in
      widening_start () >>= fun ws ->
      let widen = (counter >= ws) in
      iterate (growing, false) ~widen stgy >>= fun (growing, looping) ->
      begin if not looping && depth >= 3 then
        Nested_list.fold (fun n repeatM ->
            ifM repeatM
              (fun _ -> return true)
              (fun () -> mem_workset n.vertex)
            ) stgy (return false)
        else
          return false
      end >>= function
      | true -> loop (growing, counter)
      | false -> return growing
    in loop (false, 0)

  let process stgy =
    let aux = function
      | Atom n ->
        checkM (mem_workset n.vertex) (fun () -> process_vertex ~widen:false n)
        >>= fun grow -> return (grow, false)
      | List stgy ->
        process_strategy ~depth:2 stgy >>= fun grow ->
        checkM (return grow) (fun () -> descend stgy) >>= fun red ->
        return (grow, red)
    in
    let rec loop (ggrow, gred) = function
      | [] ->
        return (ggrow, gred)
      | x :: xs ->
        aux x >>= fun (grow, red) ->
        loop (ggrow || grow, gred || red) xs
    in loop (false, false) stgy

  (* creates the internal repr and initialize the working sets *)
  (* initialise state *)
  let init_state l g v0 =
    let add_attr v _ =
      let (is_empty, abstract) =
        if v = v0 then (false, l.init v)
        else (true, l.bottom v)
      in { is_empty; abstract; }
    in
    (* add attributes to the edges *)
    let graph = Pgraph.map add_attr (fun _ _ -> true) g in
    { graph; vinit = v0;
      opers = l;
      widening_start = 0;
      widening_descend = 1;
      workset = Pset.empty compare;
      }

  let init_strategy g v0 =
    let wto = Pgraph.wto g v0 in
    debug @@ "Strategy: " ^ Nested_list.string_of_nested_list string_of_int wto;
    let init_vertex widen vertex =
      { vertex; edges = Pgraph.pred vertex g; widen }
    in
    (* TODO: maybe flatten to a desired depth *)
    Nested_list.map_aux init_vertex wto

  let run l g v0 =
    let state = init_state l g v0 in
    let strategy = init_strategy g v0 in
    let (_, st) = run (update_workset v0 >> process strategy) state in
    Pgraph.map (fun _ attr -> attr.abstract) (fun _ _ -> ()) st.graph
end
