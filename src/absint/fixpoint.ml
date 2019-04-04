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
      (* INVARIANT: apply must be strict: apply v bot = bot *)
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
    { abstract: S.t; (* abstract state *)
      is_bot: bool; (* quick way to bot, since functions are strict *)
    }

  (* whether or not is coming from a bot state *)
  type edge_attr = bool

  (* strategy point state *)
  type point =
    { vertex: vertex_id;
      edges: (edge_id * vertex_id) list;
      widen: bool;
    }

  type strategy = point Nested_list.nlist

  (* internal state *)
  type state =
    { graph: (vertex_attr, edge_attr) graph;
      opers: t;
      vinit: vertex_id;
      widening_start: int;          (* iterations until start widening *)
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

  (* Quick version since functions are strict *)
  let is_bottom_vertex v =
    attr_of_vertex v >>= fun attr ->
    return attr.is_bot

  let is_bottom v abs =
    get >>= fun st ->
    return @@ st.opers.is_bottom v abs

  let update_vertex v abstract =
    update @@ fun st ->
    let attr = { abstract; is_bot = st.opers.is_bottom v abstract } in
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
    debug ("Widening v" ^ string_of_int v);
    abstract_of_vertex v >>= fun new_abs ->
    get >>= fun st ->
    update_vertex v @@
    st.opers.widening v old_abs new_abs

  let is_leq v abs1 abs2 =
    get >>= fun st ->
    return @@ st.opers.is_leq v abs1 abs2

  (* It is (strictly) growing if it is not the case that new <= old *)
  let is_growing v old_attr =
    attr_of_vertex v >>= fun attr ->
    is_leq v attr.abstract old_attr.abstract >>= fun b ->
    return @@ not b

  (* It is (strictly) reducing if it is not the case that old <= new *)
  let is_reducing v old_attr =
    attr_of_vertex v >>= fun attr ->
    is_leq v old_attr.abstract attr.abstract >>= fun b ->
    return @@ not b

  (* Propagate joined abstract states from incoming points *)
  let propagate ~descend n =
    remove_workset n.vertex >>
    init_post_list n.vertex >>= fun lpost0 ->
    List.fold_left (fun lpostM (e, v) ->
        debug ("Propagating edge" ^ string_of_int e ^ " to v" ^ string_of_int v);
        lpostM >>= fun lpost ->
        attr_of_edge e >>= fun coming_from_bot ->
        is_bottom_vertex v >>= fun is_bot ->
        if not (descend && coming_from_bot) && not is_bot then
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
      ) (return lpost0) n.edges >>= fun lpost ->
    join_post_list n.vertex lpost >>= update_vertex n.vertex

  let descend_strategy stgy =
    let process n =
      checkM (mem_workset n.vertex) begin fun () ->
        attr_of_vertex n.vertex >>= fun old_attr ->
        propagate ~descend:true n >>
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
          if not attr.is_bot then
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

  (* Run strategy point. *)
  let run_point ~widen p =
    debug ("Processing v: " ^ string_of_int p.vertex);
    attr_of_vertex p.vertex >>= fun old_attr ->
    propagate ~descend:false p >>
    checkM (is_growing p.vertex old_attr) begin fun () ->
      update_workset p.vertex >>= fun () ->
      whenM (return (widen && p.widen && not old_attr.is_bot))
            (fun () -> widening p.vertex old_attr.abstract) >>
      return true
    end

  (* Run strategy point list. *)
  let rec run_list ~depth stgy =
    assert (depth >= 2);
    let aux ~widen = function
      | Atom n ->
        checkM (mem_workset n.vertex) (fun () -> run_point ~widen n)
      | List stgy ->
        run_list ~depth:(depth+1) stgy
    in
    let rec iterate growing ~widen = function
      | [] ->
        return growing
      | x::xs ->
        aux ~widen x >>= fun res ->
        iterate (growing || res) ~widen xs
    in
    (* iterate until stabilization *)
    let rec loop (acc_growing, counter) =
      let counter = counter + 1 in
      widening_start () >>= fun ws ->
      let widen = (counter >= ws) in
      iterate false ~widen stgy >>= fun growing ->
      begin if growing (*&& depth >= 3*) then
        Nested_list.fold (fun n repeatM ->
            ifM repeatM
              (fun _ -> return true)
              (fun () -> mem_workset n.vertex)
            ) stgy (return false)
        else
          return false
      end >>= function
      | true ->
        loop (acc_growing || growing, counter)
      | false ->
        return (acc_growing || growing)
    in loop (false, 0)

  (* Run top strategy *)
  (* NOTE: No need to stabilize. *)
  let run_top_strategy stgy =
    let aux = function
      | Atom p ->
        checkM (mem_workset p.vertex) (fun () -> run_point ~widen:false p)
        >>= fun growing -> return (growing, false)
      | List stgy ->
        run_list ~depth:2 stgy >>= fun growing ->
        checkM (return growing) (fun () -> descend stgy) >>= fun reducing ->
        return (growing, reducing)
    in
    let rec loop (ggrow, gred) = function
      | [] ->
        return (ggrow, gred)
      | x :: xs ->
        aux x >>= fun (grow, red) ->
        loop (ggrow || grow, gred || red) xs
    in loop (false, false) stgy

  (* Creates the internal state *)
  let init_state l g v0 =
    let add_attr v _ =
      if v = v0 then { is_bot = false; abstract = l.init v }
      else { is_bot = true; abstract = l.bottom v }
    in
    let graph = Pgraph.map add_attr (fun _ _ -> true) g in
    { graph; vinit = v0;
      opers = l;
      widening_start = 0;
      widening_descend = 1;
      workset = Pset.empty compare;
    }

  (* Calculate an efficient chaotic iteration strategy
   * Francois Bourdoncle (1993) *)
  let init_strategy g v0 =
    let wto = Pgraph.wto g v0 in
    debug @@ "Strategy: " ^ Nested_list.string_of_nested_list string_of_int wto;
    let init_vertex widen vertex =
      { vertex; edges = Pgraph.pred vertex g; widen }
    in
    (* TODO: maybe flatten to a desired depth *)
    Nested_list.map_aux init_vertex wto

  let run l g v0 =
    let st   = init_state l g v0 in
    let stgy = init_strategy g v0 in
    let (_, st) = run (update_workset v0 >> run_top_strategy stgy) st in
    Pgraph.map (fun _ attr -> attr.abstract) (fun _ _ -> ()) st.graph
end
