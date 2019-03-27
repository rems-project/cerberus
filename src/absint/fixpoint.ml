(* Bertrand Jeannet, INRIA. This file is released under LGPL license. *)

(** Fixpoint analysis of an equation system: types *)

(** {2 Introduction}

    This module provides a generic engine for computing
    iteratively the solution of a fixpoint equation on a lattice.

    The equation system is represented with an hypergraph, in
    which vertices corresponds to unknown and oriented hyperedges
    to functions. It is assumed that hyperedges have unique
    destination vertex, and that associated functions are strict
    in each of their arguments: a bottom value in one of the
    argument implies that the result is empty.

    The equation system is parameterized by a manager, which
    provides the operations of the abstract lattices, and the
    transfer functions involved in the equation system.

    This interface is polymorphic and makes use of the following
    type variables:

    - ['vertex] is the type of vertex identifiers in the hypergraphs
    - ['hedge] is the type of hyperedges identifiers in the hypergraphs
    - ['abstract] is the type of abstract values (or dataflow properties)
    - ['arc] is the type of the information associated to hyperedges (optional features).

*)

(* TODO: temporarary *)

let set_of_sette s =
  List.fold_left (fun x y -> Pset.add y x) (Pset.empty compare) (PSette.elements s)

let sette_of_set cmp s =
  List.fold_left (fun x y -> PSette.add y x) (PSette.empty cmp) (Pset.elements s)

open Format

(*  ********************************************************************** *)
(** {2 Public datatypes} *)
(*  ********************************************************************** *)

(*  ====================================================================== *)
(** {3 Manager} *)
(*  ====================================================================== *)

type ('vertex,'hedge,'abstract,'arc) manager = {
  (** Lattice operation *)
  mutable bottom : 'vertex -> 'abstract;
  mutable canonical : 'vertex -> 'abstract -> unit;
  mutable is_bottom : 'vertex -> 'abstract -> bool;
  mutable is_leq : 'vertex -> 'abstract -> 'abstract -> bool;
  mutable join :  'vertex -> 'abstract -> 'abstract -> 'abstract;
  mutable join_list : 'vertex -> 'abstract list -> 'abstract;
  mutable widening : 'vertex -> 'abstract -> 'abstract -> 'abstract;
  mutable odiff :  ('vertex -> 'abstract -> 'abstract -> 'abstract) option;

  (** Initialisation of equations *)
  mutable abstract_init : 'vertex -> 'abstract;
  mutable arc_init : 'hedge -> 'arc;

  (** Interpreting hyperedges *)
  mutable apply : 'hedge -> 'abstract array -> 'arc * 'abstract;

  (** Printing functions *)
  mutable print_vertex : Format.formatter -> 'vertex -> unit;
  mutable print_hedge : Format.formatter -> 'hedge -> unit;
  mutable print_abstract: Format.formatter -> 'abstract -> unit;
  mutable print_arc: Format.formatter -> 'arc -> unit;

  (** Fixpoint Options *)
  mutable accumulate : bool;

  (** Printing Options *)
  mutable print_fmt : Format.formatter;
  mutable print_analysis : bool;
  mutable print_component : bool;
  mutable print_step : bool;
  mutable print_state : bool;
  mutable print_postpre : bool;
  mutable print_workingsets : bool;

  (** DOT Options *)
  mutable dot_fmt : Format.formatter option;
  mutable dot_vertex : Format.formatter -> 'vertex -> unit;
  mutable dot_hedge : Format.formatter -> 'hedge -> unit;
  mutable dot_attrvertex : Format.formatter -> 'vertex -> unit;
  mutable dot_attrhedge : Format.formatter -> 'hedge -> unit;
}

(*  ====================================================================== *)
(** {3 Dynamically explored equation system} *)
(*  ====================================================================== *)

type ('vertex,'hedge) equation =
  'vertex -> ('hedge, 'vertex array * 'vertex) Pmap.map

(*  ====================================================================== *)
(** {3 Iteration strategies} *)
(*  ====================================================================== *)

type strategy_iteration = {
  mutable widening_start : int;
  mutable widening_descend : int;
  mutable ascending_nb : int;
  mutable descending_nb : int;
  mutable descending_stable : bool;
}

type ('vertex,'hedge) strategy_vertex = {
  mutable vertex : 'vertex;
  mutable hedges : 'hedge list;
  mutable widen : bool;
}
type ('vertex,'hedge) strategy =
    (strategy_iteration, ('vertex,'hedge) strategy_vertex) Ilist.t

let print_strategy_iteration fmt it =
  fprintf fmt "(%i,%i,%i,%i,%b)"
    it.widening_start it.widening_descend
    it.ascending_nb it.descending_nb it.descending_stable

let print_strategy_vertex
  (man:('vertex,'hedge,'abstract,'arc) manager)
  fmt
  (v:('vertex,'hedge) strategy_vertex)
  =
  fprintf fmt "@[<h>(%b,%a,%a)@]"
    v.widen
    man.print_vertex v.vertex
    (Print.list ~first:"@[<h>[" ~sep:"," ~last:"]@]"
  man.print_hedge)
    v.hedges

let print_strategy
  (man:('vertex,'hedge,'abstract,'arc) manager)
  fmt
  (s:('vertex,'hedge) strategy)
  =
  Ilist.print
    ~first:"[ @[<hv>"
    ~last:"@] ]"
    print_strategy_iteration
    (print_strategy_vertex man) fmt s

let make_strategy_iteration
    ?(widening_start=0)
    ?(widening_descend=1)
    ()
    = {
      widening_start = widening_start;
      widening_descend = widening_descend;
      ascending_nb = 0;
      descending_nb = 0;
      descending_stable = false;
    }

let make_strategy_vertex
    ?priority
    (graph:('vertex,'hedge,'a,'b,'c) PSHGraph.t)
    (widen:bool)
    (vertex:'vertex)
    :
    ('vertex,'hedge) strategy_vertex
    =
  let spredhedges =
    set_of_sette @@ PSHGraph.predhedge graph vertex in
  let hedges =
    Pset.fold (fun hedge res ->
        let takeit = match priority with
          | None -> true
          | Some(PSHGraph.Filter filter) -> filter hedge
          | Some(PSHGraph.Priority p) -> (p hedge)>=0
        in
        if takeit then hedge::res else res
      ) spredhedges []
  in
  let strategy_vertex = {
    vertex = vertex;
    hedges = hedges;
    widen = widen
  }
  in
  strategy_vertex

let make_strategy_default
    ?(depth=2)
    ?(widening_start=0)
    ?(widening_descend=1)
    ?priority
    ~(vertex_dummy:'vertex)
    ~(hedge_dummy:'hedge)
    (graph:('vertex,'hedge,'a,'b,'c) PSHGraph.t)
    (sinit:'vertex Pset.set)
    :
    ('vertex,'hedge) strategy
    =
  let scfc =
    PSHGraph.scfc_multi
      vertex_dummy hedge_dummy
      ?priority graph (sette_of_set graph.PSHGraph.compare.comparev sinit)
  in
  let scfc =
    Ilist.map
      (make_strategy_iteration ~widening_start ~widening_descend)
      (begin fun flag _ vertex ->
  make_strategy_vertex ?priority graph flag vertex
      end)
      scfc
  in
  Ilist.flatten ~depth scfc

(*  ====================================================================== *)
(** {3 Output} *)
(*  ====================================================================== *)

(** statistics at the end of the analysis *)
type stat_iteration = {
  mutable nb: int;
  mutable stable: bool;
}
type stat = {
  mutable time : float;
  mutable ascending : (stat_iteration,unit) Ilist.t;
  mutable descending : (stat_iteration,unit) Ilist.t;
}

(** result of the analysis *)
type ('vertex,'hedge,'abstract,'arc) output =
  ('vertex,'hedge,'abstract, 'arc, stat) PSHGraph.t

let ilist_map_condense f (it,ll) =
  let rec parcours res = function
    | [] -> res
    | Ilist.Atome(_)::ll -> parcours res ll
    | Ilist.List(it2,ll2)::ll ->
  let nit2 = f it2 in
  let nll2 = parcours [] ll2 in
  parcours ((Ilist.List(nit2, nll2))::res) ll
  in
  Ilist.rev ((f it),(parcours [] ll))

let stat_iteration_merge (it,ll) =
  let res = { nb = 0; stable = true } in
  let rec parcours = function
    | [] -> ()
    | (Ilist.Atome _)::ll -> parcours ll
    | (Ilist.List(it,ll2)::ll) ->
  res.nb <- max res.nb it.nb;
  res.stable <- res.stable && it.stable;
  parcours ll2; parcours ll
  in
  parcours ll;
  res

let print_stat_iteration fmt it =
  fprintf fmt "(%i,%b)" it.nb it.stable
let print_stat_iteration_ilist fmt ilist =
  Ilist.print
    print_stat_iteration (fun fmt _ -> ()) fmt ilist

let print_stat fmt stat =
  fprintf fmt "{ @[<hov>time=%f;@ ascending=%a;@ descending=%a;@] }"
    stat.time
    print_stat_iteration_ilist stat.ascending
    print_stat_iteration_ilist stat.descending

let print_output
    (man:('vertex,'hedge,'abstract,'arc) manager)
    fmt
    (g:('vertex,'hedge,'abstract,'arc, stat) PSHGraph.t)
    =
  PSHGraph.print
    man.print_vertex
    man.print_hedge
    man.print_abstract
    man.print_arc
    print_stat
    fmt
    g

(*  ********************************************************************** *)
(** {2 Internal datatypes} *)
(*  ********************************************************************** *)

type 'abstract attr = {
  mutable reach : 'abstract;
  mutable diff : 'abstract;
  mutable empty : bool;
}

type 'arc arc = {
  mutable arc : 'arc;
  mutable aempty : bool;
}

type ('vertex,'hedge) infodyn = {
  mutable iaddhedge : ('hedge,'vertex array * 'vertex) PHashhe.t;
  iequation : ('vertex,'hedge) equation
}

type ('vertex,'hedge) info = {
  iinit : 'vertex Pset.set;
  itime : float ref;
  mutable iascending : (stat_iteration,unit) Ilist.t;
  mutable idescending : (stat_iteration,unit) Ilist.t;
  mutable iworkvertex : ('vertex,unit) PHashhe.t;
  mutable iworkhedge : ('hedge,unit) PHashhe.t;
  iinfodyn : ('vertex,'hedge) infodyn option;
}

type ('vertex,'hedge,'abstract,'arc) graph =
  ('vertex, 'hedge, 'abstract attr, 'arc arc, ('vertex,'hedge) info) PSHGraph.t

(*  ====================================================================== *)
(** {3 Printing functions} *)
(*  ====================================================================== *)

let print_attr
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (attr:'abstract attr)
  =
  fprintf fmt "{ @[<hov>reach=%a;@ empty=%b@] }"
    man.print_abstract attr.reach
    attr.empty

let print_arc
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (arc:'arc arc)
  =
  fprintf fmt "{ @[<hov>arc=%a;@ aempty=%b@] }"
    man.print_arc arc.arc
    arc.aempty

let print_info
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (info:('vertex,'hedge) info)
  =
  fprintf fmt "{ @[<hov>itime=%f;@ iascending=%a;@ idescending=%a;@ iworkvertex=%a;@ iworkhedge=%a@] }"
    !(info.itime)
    print_stat_iteration_ilist info.iascending
    print_stat_iteration_ilist info.idescending
    (PHashhe.print man.print_vertex (fun _ _ -> ())) info.iworkvertex
    (PHashhe.print man.print_hedge (fun _ _ -> ())) info.iworkhedge

let print_workingsets
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    :
    unit
    =
  let hashprint print fmt x =
      PHashhe.print
  ~first:"[@[<hov>" ~last:"@]]"
  ~firstbind:"" ~sepbind:"" ~lastbind:""
  print (fun _ _ -> ())
  fmt x
  in
  let info = PSHGraph.info graph in
  fprintf fmt "@[<v>workvertex = %a@ workhedge = %a"
    (hashprint man.print_vertex) info.iworkvertex
    (hashprint man.print_hedge) info.iworkhedge
  ;
  begin match info.iinfodyn with
  | Some(dyn) ->
      fprintf fmt "@ addhedge = %a"
  (hashprint man.print_hedge) dyn.iaddhedge
  | None -> ()
  end;
  fprintf fmt "@]"

let print_graph
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (g:('vertex,'hedge,'abstract,'arc) graph)
    =
  PSHGraph.print
    man.print_vertex
    man.print_hedge
    (print_attr man)
    (print_arc man)
    (print_info man)
    fmt
    g

(*  ====================================================================== *)
(** {3 DOT functions} *)
(*  ====================================================================== *)

let set2_of_strategy
    comparev
    (strategy:('vertex,'hedge) strategy)
    :
    'vertex Pset.set * 'vertex Pset.set
    =
  let empty = Pset.empty comparev in
  Ilist.fold_left
    (begin fun (res,resw) _ _ v ->
      if v.widen then
  res,(Pset.add v.vertex resw)
      else
  (Pset.add v.vertex res),resw
    end)
    (empty,empty) strategy

let dot_graph
    ?(style="size=\"7.5,10\";center=true;ranksep=0.16;nodesep=0.02;")
    ?(titlestyle="fontsize=18")
    ?(vertexstyle="shape=box,fontsize=18,height=0.02,width=0.01")
    ?(hedgestyle="shape=plaintext,fontsize=18,height=0.0,width=0.01")
    ?strategy
    ?vertex
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    ~(title:string)
    =
  let comparev = graph.PSHGraph.compare.PSHGraph.comparev in
  match man.dot_fmt with
  | None -> ()
  | Some dot_fmt ->
      let (set,setw) = match strategy with
  | None -> let e = Pset.empty comparev in (e,e)
  | Some strategy -> set2_of_strategy comparev strategy
      in
      let info = PSHGraph.info graph in
      let fvertexstyle = begin fun v ->
  let vertexstyle =
    if begin match vertex with
    | None -> false
    | Some vertex -> (graph.PSHGraph.compare.PSHGraph.comparev v vertex) = 0
    end
    then
      vertexstyle^",style=filled,fillcolor=coral1"
    else if Pset.mem v setw then
      vertexstyle^",style=filled,fillcolor=red1"
    else if Pset.mem v set then
      vertexstyle^",style=filled,fillcolor=orange1"
    else
      vertexstyle
  in
  let vertexstyle =
    if PHashhe.mem info.iworkvertex v then
      vertexstyle^",fontcolor=blue3"
    else
      vertexstyle
  in
  vertexstyle
      end
      in
      let fhedgestyle = begin fun h ->
  let hedgestyle =
    if PHashhe.mem info.iworkhedge h then
      hedgestyle^",fontcolor=blue3"
    else
      hedgestyle
  in
  hedgestyle
      end
      in
      PSHGraph.print_dot
  ~titlestyle
  ~style
  ~fvertexstyle
  ~fhedgestyle
  ~title
  (fun fmt vertex ->
    fprintf fmt "\"%s\""
      (String.escaped
        (Print.sprintf "%a" man.dot_vertex vertex)))
  (fun fmt hedge ->
    fprintf fmt "\"%s\""
      (String.escaped
        (Print.sprintf "%a" man.dot_hedge hedge)))
  (fun fmt vertex attr ->
    fprintf fmt "%s"
      (String.escaped
        (Print.sprintf ~margin:40 "%a@.%a"
    man.dot_attrvertex vertex
    man.print_abstract attr.reach)))
  (fun fmt hedge arc ->
    fprintf fmt "%s"
      (String.escaped
        (Print.sprintf ~margin:40 "%a@.%a"
    man.dot_attrhedge hedge
    man.print_arc arc.arc)))
  dot_fmt
  graph

(* Bertrand Jeannet, INRIA. This file is released under LGPL license. *)

(** Fixpoint analysis of an equation system *)

(*  ********************************************************************** *)
(** {2 Utilities} *)
(*  ********************************************************************** *)

(** Does the array of vertices belong to the graph, all with non
    bottom values ? *)
let is_tvertex
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    (tvertex:'vertex array)
    :
    bool
    =
  try
    Array.iter
      (begin fun vertex ->
  let attr = PSHGraph.attrvertex graph vertex in
  if attr.empty then raise Exit;
      end)
      tvertex
    ;
    true
  with Exit | Not_found ->
    false

(** Return the array of abstract values associated to the vertices
*)
let treach_of_tvertex
    ~(descend:bool)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    (tvertex:'vertex array)
    :
    'abstract array
    =
  if not descend && (Array.length tvertex)=1 then
    let attr = PSHGraph.attrvertex graph tvertex.(0) in
    [| attr.diff |]
  else
    Array.map
      (begin fun vertex ->
  let attr = PSHGraph.attrvertex graph vertex in
  attr.reach
      end)
      tvertex

(** Update working sets assuming that the abstract value
    associated to the vertex has been modified. If [hedge=true], then
    also consider the working set associated to hyperhedges. *)
let update_workingsets
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    ~(hedge:bool)
    (vertex:'vertex)
    :
    unit
    =
  let info = PSHGraph.info graph in
  begin match info.iinfodyn with
  | None ->
      let seth = PSHGraph.succhedge graph vertex in
      Pset.iter (fun (h:'hedge) ->
          if hedge then PHashhe.replace info.iworkhedge h ();
          let succ = PSHGraph.succvertex graph h in
          assert ((Array.length succ)=1);
          PHashhe.replace info.iworkvertex succ.(0) ();
        ) (set_of_sette seth);
  | Some(dyn) ->
      let maph = dyn.iequation vertex in
      Pmap.iter
        (fun h ((tpredvertex,succvertex) as tpredsucc) ->
           if (PSHGraph.is_hedge graph h) then begin
             if hedge then PHashhe.replace info.iworkhedge h ();
             PHashhe.replace info.iworkvertex succvertex ();
           end else begin
             PHashhe.replace dyn.iaddhedge h tpredsucc;
           end
        ) maph
  end

(*  ********************************************************************** *)
(** {2 Initialisation of fixpoint computation} *)
(*  ********************************************************************** *)

(** [init manager input sinit] creates the internal graph
    structure (from the equation graph [input]) and initialize the
    working sets (from the set of initial points [sinit]) (stored
    in the info field of the internal graph). *)
let init
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (input:('vertex,'hedge,'a,'b,'c) PSHGraph.t)
    (sinit:'vertex Pset.set)
    :
    ('vertex,'hedge,'abstract,'arc) graph
    =
  let make_attr vertex _ : 'abstract attr
      =
    let (empty,def) =
      if Pset.mem vertex sinit
      then (false,manager.abstract_init vertex)
      else (true,manager.bottom vertex)
    in {
      reach = def;
      diff = def;
      empty = empty;
    }
  in
  let make_arc hedge _ : 'arc arc
      =
    { arc = manager.arc_init hedge; aempty = true }
  in
  let make_info _ : ('vertex,'hedge) info
      =
    {
      iinit = sinit;
      itime = ref 0.0;
      iascending = ({nb=0; stable=false}, []);
      idescending = ({nb=0; stable=false}, []);
      iworkvertex = PHashhe.create_compare input.PSHGraph.compare.PSHGraph.hashv 7;
      iworkhedge = PHashhe.create_compare input.PSHGraph.compare.PSHGraph.hashh 7;
      iinfodyn = None;
    }
  in
  let graph =
    PSHGraph.copy make_attr make_arc make_info input
  in
  Pset.iter
    (update_workingsets graph ~hedge:manager.accumulate)
    sinit
  ;
  graph

(*  ********************************************************************** *)
(** {2 Process a vertex} *)
(*  ********************************************************************** *)

(*  ====================================================================== *)
(** {3 Accumulate} *)
(*  ====================================================================== *)

(** Compute the least upper bound of the current value of the
    vertex/variable with the values propagated by the incoming
    hyperedges belonging to the working set. Returns [true] if the
    value is strictly increasing. *)

let av_print_intro manager vertex =
  fprintf manager.print_fmt "processing (acc) vertex %a:@   @[<v>"
    manager.print_vertex vertex

let av_print_oldreach manager oldreach =
  fprintf manager.print_fmt "contrib of oldreach = %a@ "
    manager.print_abstract oldreach
let av_print_contrib manager hedge post =
  fprintf manager.print_fmt "contrib of hedge %a = %a@ "
    manager.print_hedge hedge manager.print_abstract post

let av_print_result manager graph vertex attr growing =
  fprintf manager.print_fmt "reach=%a" manager.print_abstract attr.reach;
  if manager.accumulate && manager.odiff<>None then
    fprintf manager.print_fmt "@ diff=%a" manager.print_abstract attr.diff;
  if not growing then fprintf manager.print_fmt "@ no change";
  fprintf manager.print_fmt "@]@ ";
  if manager.dot_fmt<>None then
    dot_graph manager graph
      ~vertex
      ~title:(
  Print.sprintf "processed (acc) %a"
    manager.dot_vertex vertex
      )
  ;
  ()

let accumulate_vertex
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    (svertex:('vertex,'hedge) strategy_vertex)
    (attr:'abstract attr)
    :
    bool
    =
  let info = PSHGraph.info graph in
  let vertex = svertex.vertex in
  let lhedges = svertex.hedges in
  let oldreach = attr.reach in
  if manager.print_state then av_print_intro manager vertex;

  PHashhe.remove info.iworkvertex vertex;
  let lpost = ref [] in
  let allpost = ref true in
  if manager.print_postpre then av_print_oldreach manager oldreach;
  List.iter
    (begin fun hedge ->
      if not manager.accumulate || PHashhe.mem info.iworkhedge hedge then begin
  PHashhe.remove info.iworkhedge hedge;
  let tpredvertex = PSHGraph.predvertex graph hedge in
  if is_tvertex graph tpredvertex then begin
    let attrhedge = PSHGraph.attrhedge graph hedge in
    let treach = treach_of_tvertex ~descend:false graph tpredvertex in
    let (arc,post) = manager.apply hedge treach in
    attrhedge.arc <- arc;
    if manager.print_postpre then av_print_contrib manager hedge post;
    if not (attrhedge.aempty && manager.is_bottom vertex post) then begin
      lpost := post :: !lpost;
      attrhedge.aempty <- false;
      attr.empty <- false;
    end
    else allpost := false;
  end
  else allpost := false;
      end
      else allpost := false;
    end)
    lhedges
  ;
  let lpost2 =
    if not !allpost || svertex.widen || Pset.mem vertex info.iinit then
      oldreach :: !lpost
    else
      !lpost
  in
  attr.reach <- manager.join_list vertex lpost2;
  manager.canonical vertex attr.reach;
  let growing =
    match manager.odiff with
    | Some(diff) when manager.accumulate ->
  let nabs = match !lpost with
    | [post] -> post
    | _ -> attr.reach
  in
  attr.diff <- diff vertex nabs oldreach;
  not (manager.is_bottom vertex attr.diff)
    | _ ->
  attr.diff <- attr.reach;
  not (manager.is_leq vertex attr.reach oldreach)
  in
  if manager.print_state then av_print_result manager graph vertex attr growing;
  growing

(*  ====================================================================== *)
(** {3 Propagate} *)
(*  ====================================================================== *)

(** Compute the least upper bound of the values propagated by all
    the incoming hyperedges. Returns [true] if the value is
    strictly increasing. If [descend=true], the value is supposed
    to be decreasing and returns true if it is strictly
    decreasing. *)

let pv_print_intro manager vertex =
  fprintf manager.print_fmt "processing (prop) vertex %a:@   @[<v>"
    manager.print_vertex vertex
let pv_print_result manager graph vertex attr update =
  fprintf manager.print_fmt "reach=%a" manager.print_abstract attr.reach;
  if not update then fprintf manager.print_fmt "@ no change";
  fprintf manager.print_fmt "@]@ ";
  if manager.dot_fmt<>None then
    dot_graph manager graph
      ~vertex
      ~title:(
  Print.sprintf "processed (prop) %a"
    manager.dot_vertex vertex
      )
  ;
  ()

let propagate_vertex
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    ~(descend:bool)
    (svertex:('vertex,'hedge) strategy_vertex)
    (attr:'abstract attr)
    :
    bool
    =
  let info = PSHGraph.info graph in
  let vertex = svertex.vertex in
  let lhedges = svertex.hedges in
  let oldreach = attr.reach in
  if manager.print_state then pv_print_intro manager vertex;

  PHashhe.remove info.iworkvertex vertex;

  let (lpost:'abstract list ref) = ref [] in
  if Pset.mem vertex info.iinit then
      lpost := (manager.abstract_init vertex) :: !lpost
  ;
  List.iter
    (begin fun hedge ->
      let tpredvertex = PSHGraph.predvertex graph hedge in
      let attrhedge = PSHGraph.attrhedge graph hedge in
      let takeit =
  (if descend then not attrhedge.aempty else true)
  && is_tvertex graph tpredvertex
      in
      if takeit then begin
  PHashhe.remove info.iworkhedge hedge;
  let treach = treach_of_tvertex ~descend graph tpredvertex in
  let (arc,post) = manager.apply hedge treach in
  attrhedge.arc <- arc;
  if manager.print_postpre then av_print_contrib manager hedge post;
  if not (manager.is_bottom vertex post) then begin
    lpost := post :: !lpost;
    attrhedge.aempty <- false
  end
  else
    attrhedge.aempty <- true;
      end
      else
  attrhedge.aempty <- true;
    end)
    lhedges
  ;
  attr.reach <-
    if !lpost=[]
    then manager.bottom vertex
    else  manager.join_list vertex !lpost;
  manager.canonical vertex attr.reach;
  attr.diff <- attr.reach;
  attr.empty <- manager.is_bottom vertex attr.reach;
  let update =
    if descend
    then not (manager.is_leq vertex oldreach attr.reach)
    else not (manager.is_leq vertex attr.reach oldreach)
  in
  if manager.print_state then pv_print_result manager graph vertex attr update;
  update

(*  ====================================================================== *)
(** {3 Accumulate and update} *)
(*  ====================================================================== *)

let p_print_result manager graph vertex attr =
  fprintf manager.print_fmt "  widening = %a@ "
    manager.print_abstract attr.reach;
  if manager.accumulate && manager.odiff<>None then
    fprintf manager.print_fmt "  diff=%a@ " manager.print_abstract attr.diff;
  if manager.dot_fmt<>None then
    dot_graph manager graph ~vertex ~title:"after widening"

let process_vertex
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    ~(widening:bool)
    (svertex:('vertex,'hedge) strategy_vertex)
    :
    bool
    =
  let vertex = svertex.vertex in
  let attr = PSHGraph.attrvertex graph vertex in
  let oldreach = attr.reach in
  let oldempty = attr.empty in
  let growing =
    (if manager.accumulate || svertex.widen && widening then
      accumulate_vertex
    else
      propagate_vertex ~descend:false
    )
      manager graph svertex attr
  in
  if growing then begin
    update_workingsets ~hedge:manager.accumulate graph vertex;
  end;
  if manager.print_workingsets then fprintf manager.print_fmt "  %a@ " (print_workingsets manager) graph;
  if growing && svertex.widen then begin
    if widening && not oldempty then begin
      attr.reach <- manager.widening vertex oldreach attr.reach;
      manager.canonical vertex attr.reach;
      attr.diff <- begin match manager.odiff with
      | Some(diff) when manager.accumulate ->
    diff vertex attr.reach oldreach;
      | _ ->
    attr.reach;
      end;
      if manager.print_state then p_print_result manager graph vertex attr;
    end;
    assert (not (manager.is_leq vertex attr.reach oldreach));
  end;
  growing

(*  ********************************************************************** *)
(** {2 Process a descending strategy of depth 2 (a strongly
    connected component} *)
(*  ********************************************************************** *)

let d_print_intro manager graph strategy =
  fprintf manager.print_fmt "Descending (linearized) strategy@   %a@   @[<v>"
    (print_strategy manager) strategy
  ;
  if manager.dot_fmt<>None then begin
    dot_graph manager graph ~strategy ~title:"Descending (linearized) strategy"
  end

let d_print_step manager graph strategy counter =
  fprintf manager.print_fmt "Sum up of the descending step (%i iterations)@ "
    !counter;
  Ilist.iter
    (begin fun _ _ svertex ->
      let vertex = svertex.vertex in
      let attrvertex = PSHGraph.attrvertex graph vertex in
      fprintf manager.print_fmt "  acc(%a)=%a@ "
  manager.print_vertex vertex
  manager.print_abstract attrvertex.reach
    end)
    strategy
  ;
  if manager.dot_fmt<>None then
    dot_graph manager graph ~strategy ~title:(Print.sprintf "Sum up of the descending step (%i iterations)" !counter)

let d_print_result manager graph strategy =
  fprintf manager.print_fmt "End descending strategy";
  if true then begin
    Ilist.iter
      (begin fun _ _ svertex ->
  let vertex = svertex.vertex in
  let attrvertex = PSHGraph.attrvertex graph vertex in
  fprintf manager.print_fmt "@   acc(%a) =%a"
    manager.print_vertex vertex
    manager.print_abstract attrvertex.reach
      end)
      strategy
  end;
  fprintf manager.print_fmt "@]@ ";
  if manager.dot_fmt<>None then begin
    dot_graph manager graph
      ~strategy
      ~title:"End Descending strategy"
  end

let descend_strategy
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    strategy
    :
    bool
    =
  let info = PSHGraph.info graph in
  let process_svertex svertex : bool =
    if PHashhe.mem info.iworkvertex svertex.vertex
    then begin
      let attr = PSHGraph.attrvertex graph svertex.vertex in
      let reducing =
  propagate_vertex ~descend:true manager graph svertex attr
      in
      if reducing then begin
  update_workingsets ~hedge:false graph svertex.vertex;
      end;
      if manager.print_workingsets then fprintf manager.print_fmt "  %a@ " (print_workingsets manager) graph;
      reducing
    end
    else
      false
  in

  if manager.print_component then d_print_intro manager graph strategy;
  let (it,_) = strategy in
  let reducing = ref true in
  let counter = ref 0 in
  while !reducing && !counter < it.widening_descend do
    reducing := false;
    incr counter;
    (* Linear iteration on vertices of a strongly connected component *)
    Ilist.iter
      (begin fun _ _ svertex ->
  let reducing2 = process_svertex svertex in
  reducing := !reducing || reducing2
      end)
      strategy
    ;
    reducing := !reducing && (PHashhe.length info.iworkvertex) > 0;
    if !reducing && manager.print_step then d_print_step manager graph strategy counter;
  done;
  if manager.print_component then d_print_result manager graph strategy;
  it.descending_nb <- !counter;
  it.descending_stable <- not !reducing;
  !reducing

(*  ********************************************************************** *)
(** {2 Descending sequence} *)
(*  ********************************************************************** *)

let descend
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    (strategy:('vertex,'hedge) strategy)
    :
    bool
    =
  let (it,_) = strategy in
  if it.widening_descend>0 then begin
    let info = PSHGraph.info graph in
    let oldworkvertex = PHashhe.copy info.iworkvertex in
    let oldworkhedge = PHashhe.copy info.iworkhedge in
    PHashhe.clear info.iworkvertex;
    PHashhe.clear info.iworkhedge;
    Ilist.iter
      (begin fun _ _ svertex ->
  let vertex = svertex.vertex in
  let attrvertex = PSHGraph.attrvertex graph vertex in
  if not attrvertex.empty then
    PHashhe.replace info.iworkvertex vertex ()
      end)
      strategy
    ;
    if manager.print_workingsets then fprintf manager.print_fmt "  %a@ " (print_workingsets manager) graph;
    ignore (descend_strategy manager graph strategy);
    let reducing = (PHashhe.length info.iworkvertex) > 0 in
    info.iworkvertex <- oldworkvertex;
    info.iworkhedge <- oldworkhedge;
    reducing
  end else begin
    it.descending_nb <- 0;
    it.descending_stable <- false;
    false;
  end

(*  ********************************************************************** *)
(** {2 Process a (recursive) strategy of depth 2 or more} *)
(*  ********************************************************************** *)

let s_print_intro ~depth manager graph strategy =
  fprintf manager.print_fmt "Processing strategy at depth=%i@   %a@   @[<v>"
    depth (print_strategy manager) strategy;
  if manager.dot_fmt<>None then begin
    dot_graph manager graph
      ~strategy
      ~title:(Print.sprintf "Processing strategy at depth %i" depth)
  end

let tops_print_intro manager graph strategy =
  fprintf manager.print_fmt "Processing toplevel strategy@   %a@   @[<v>"
    (print_strategy manager) strategy;
  if manager.dot_fmt<>None then begin
    dot_graph manager graph
      ~strategy
      ~title:"Processing toplevel strategy"
  end

let s_print_step manager graph strategy nsteps growing =
  fprintf manager.print_fmt "Sum up of the looping step (%i iterations) (growing=%b)@ " !nsteps !growing;
  Ilist.iter
    (begin fun _ _ strategy_vertex ->
      let vertex = strategy_vertex.vertex in
      let attrvertex = PSHGraph.attrvertex graph vertex in
      fprintf manager.print_fmt "  acc (%a)=%a@ "
  manager.print_vertex vertex
  manager.print_abstract attrvertex.reach
      ;
      if manager.accumulate && manager.odiff<>None then
  fprintf manager.print_fmt "@   diff(%a)=%a"
    manager.print_vertex vertex
    manager.print_abstract attrvertex.diff
    end)
    strategy
  ;
  if manager.print_workingsets then
    fprintf manager.print_fmt "  %a@ " (print_workingsets manager) graph;

  if manager.dot_fmt<>None then begin
    dot_graph manager graph ~strategy
      ~title:(Print.sprintf "Sum up of the looping step (%i iterations)" !nsteps)
  end

let s_print_result ~depth manager graph strategy =
  fprintf manager.print_fmt "End processing strategy at depth %i" depth;
  if true then begin
    Ilist.iter
      (begin fun _ _ svertex ->
  let vertex = svertex.vertex in
  let attrvertex = PSHGraph.attrvertex graph vertex in
  fprintf manager.print_fmt "@   acc (%a)=%a"
    manager.print_vertex vertex
    manager.print_abstract attrvertex.reach
  ;
  if manager.accumulate && manager.odiff<>None then
    fprintf manager.print_fmt "@   diff(%a)=%a"
      manager.print_vertex vertex
      manager.print_abstract attrvertex.diff
      end)
      strategy
  end;
  fprintf manager.print_fmt "@]@ ";
  if manager.dot_fmt<>None then begin
    dot_graph manager graph
      ~strategy
      ~title:(Print.sprintf "End Processing strategy at depth %i" depth)
  end

let tops_print_result manager graph strategy =
  fprintf manager.print_fmt "End processing toplevel strategy";
  if true then begin
    Ilist.iter
      (begin fun _ _ svertex ->
  let vertex = svertex.vertex in
  let attrvertex = PSHGraph.attrvertex graph vertex in
  fprintf manager.print_fmt "@   acc (%a)=%a"
    manager.print_vertex vertex
    manager.print_abstract attrvertex.reach
  ;
  if manager.accumulate && manager.odiff<>None then
    fprintf manager.print_fmt "@   diff(%a)=%a"
      manager.print_vertex vertex
      manager.print_abstract attrvertex.diff
      end)
      strategy
  end;
  fprintf manager.print_fmt "@]@ ";
  if manager.dot_fmt<>None then begin
    dot_graph manager graph
      ~strategy
      ~title:"End Processing toplevel strategy"
  end

(* Returns true if some vertex has increased. *)
let rec process_strategy
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    ~(depth:int)
    (strategy:('vertex,'hedge) strategy)
    :
    bool
    =
  assert(depth>=2);
  let info = PSHGraph.info graph in
  let (it,sstrategy) = strategy in
  let growing = ref false in
  let loop = ref true in
  let counter = ref 0 in

  let rec parcours widening = function
    | [] -> ()
    | elt::rest ->
  let res =
    begin match elt with
    | Ilist.Atome(strategy_vertex) ->
        if PHashhe.mem info.iworkvertex strategy_vertex.vertex then
    process_vertex manager graph ~widening strategy_vertex
        else
    false
    | Ilist.List(strategy) ->
        process_strategy manager graph ~depth:(depth+1) strategy
    end
  in
  growing := !growing || res;
  loop := !loop || res;
  parcours widening rest;
  in

  if manager.print_component then s_print_intro ~depth manager graph strategy;
  while !loop do
    loop := false;
    incr counter;
    let widening = (!counter >= it.widening_start) in
    parcours widening sstrategy;
    if not !loop && depth>=3 then begin
      (* if Bourdoncle technique, check working sets *)
      try
  Ilist.iter
    (begin fun _ _ strategy_vertex ->
      if PHashhe.mem
        info.iworkvertex strategy_vertex.vertex
      then begin
        loop := true; raise Exit
      end
    end)
    strategy
      with
      Exit -> ()
    end
    ;
    if !loop && manager.print_step then s_print_step manager graph strategy counter loop;
  done;
  if manager.print_component then s_print_result ~depth manager graph strategy;
  it.ascending_nb <- it.ascending_nb + !counter;

  !growing

(*  ********************************************************************** *)
(** {2 Process the toplevel strategy} *)
(*  ********************************************************************** *)

(* Returns [(growing,reducing)] *)
let process_toplevel_strategy
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) graph)
    (strategy:('vertex,'hedge) strategy)
    :
    bool * bool
    =
  let info = PSHGraph.info graph in
  let (it,sstrategy) = strategy in
  let ggrowing = ref false in
  let greducing = ref false in
  let rec parcours = function
    | [] -> ()
    | elt::rest ->
  begin match elt with
  | Ilist.Atome(strategy_vertex) ->
      if PHashhe.mem info.iworkvertex strategy_vertex.vertex then
        let growing =
    process_vertex manager graph ~widening:false strategy_vertex
        in
        ggrowing := !ggrowing || growing
  | Ilist.List(strategy) ->
      let growing =
        process_strategy manager graph ~depth:2 strategy
      in
      ggrowing := !ggrowing || growing;
      let reducing =
        if growing then
    (* Descending *)
    descend manager graph strategy
        else
    false
      in
      greducing := !greducing || reducing
  end;
  parcours rest;
  in
  if manager.print_component then tops_print_intro manager graph strategy;
  if manager.print_workingsets then fprintf manager.print_fmt "%a@ " (print_workingsets manager) graph;

  parcours sstrategy;

  if manager.print_component then tops_print_result manager graph strategy;
  it.ascending_nb <- 1;
  it.descending_nb <- min 1 it.widening_descend;
  it.descending_stable <- not !greducing;

  info.iascending <-
    ilist_map_condense
    (fun it -> { nb = it.ascending_nb; stable = true; })
    strategy;
  info.idescending <-
    ilist_map_condense
    (fun it -> { nb = it.descending_nb; stable = it.descending_stable; })
    (Ilist.flatten ~depth:2 strategy)
  ;

  (!ggrowing,!greducing)


(*  ********************************************************************** *)
(** {2 Standard analysis} *)
(*  ********************************************************************** *)

let output_of_graph graph =
    PSHGraph.copy
      (fun vertex attrvertex -> attrvertex.reach)
      (fun hedge attrhedge -> attrhedge.arc)
      (fun info -> {
  time = !(info.itime);
  ascending = info.iascending;
  descending = info.idescending;
      })
      graph

let analysis
    (manager:('vertex,'hedge,'abstract,'arc) manager)
    (input:('vertex,'hedge,'a,'b,'c) PSHGraph.t)
    (sinit:'vertex Pset.set)
    (strategy:('vertex,'hedge) strategy)
    :
    ('vertex,'hedge,'abstract,'arc) output
    =
  if manager.print_analysis then begin
    fprintf manager.print_fmt "*** Analysis...@.";
  end;
  let graph = init manager input sinit in
  let info = PSHGraph.info graph in
  Time.wrap_duration_add info.itime (begin fun () ->
    let (_,reducing) = process_toplevel_strategy manager graph strategy in
    let info = PSHGraph.info graph in
    if manager.print_analysis then
      fprintf manager.print_fmt "... in@.    %a ascending iterations@.    %a descending iterations@.    stabilization:%b@.***@."
  print_stat_iteration_ilist info.iascending
  print_stat_iteration_ilist info.idescending
  (not reducing)
    ;
  end)
  ;
  if manager.print_analysis && manager.dot_fmt<>None then begin
    dot_graph manager graph
      ~title:"Result"
  end
  ;
  output_of_graph graph

(* Bertrand Jeannet, INRIA. This file is released under LGPL license. *)

(** Fixpoint analysis of an equation system *)

(*  ********************************************************************** *)
(** {2 Datatypes} *)
(*  ********************************************************************** *)

(*
type ('vertex,'hedge,'abstract,'arc) manager =
  ('vertex,'hedge,'abstract,'arc) FixpointType. manager = {
    mutable bottom : 'vertex -> 'abstract;
    mutable canonical : 'vertex -> 'abstract -> unit;
    mutable is_bottom : 'vertex -> 'abstract -> bool;
    mutable is_leq : 'vertex -> 'abstract -> 'abstract -> bool;
    mutable join :  'vertex -> 'abstract -> 'abstract -> 'abstract;
    mutable join_list : 'vertex -> 'abstract list -> 'abstract;
    mutable widening : 'vertex -> 'abstract -> 'abstract -> 'abstract;
    mutable odiff :  ('vertex -> 'abstract -> 'abstract -> 'abstract) option;
    mutable abstract_init : 'vertex -> 'abstract;
    mutable arc_init : 'hedge -> 'arc;
    mutable apply : 'hedge -> 'abstract array -> 'arc * 'abstract;
    mutable print_vertex : Format.formatter -> 'vertex -> unit;
    mutable print_hedge : Format.formatter -> 'hedge -> unit;
    mutable print_abstract: Format.formatter -> 'abstract -> unit;
    mutable print_arc: Format.formatter -> 'arc -> unit;
    mutable accumulate : bool;
    mutable print_fmt : Format.formatter;
    mutable print_analysis : bool;
    mutable print_component : bool;
    mutable print_step : bool;
    mutable print_state : bool;
    mutable print_postpre : bool;
    mutable print_workingsets : bool;
    mutable dot_fmt : Format.formatter option;
    mutable dot_vertex : Format.formatter -> 'vertex -> unit;
    mutable dot_hedge : Format.formatter -> 'hedge -> unit;
    mutable dot_attrvertex : Format.formatter -> 'vertex -> unit;
    mutable dot_attrhedge : Format.formatter -> 'hedge -> unit;
  }

type strategy_iteration = FixpointType.strategy_iteration = {
  mutable widening_start : int;
  mutable widening_descend : int;
  mutable ascending_nb : int;
  mutable descending_nb : int;
  mutable descending_stable : bool;
}
type ('vertex,'hedge) strategy_vertex =
  ('vertex,'hedge) FixpointType.strategy_vertex = {
    mutable vertex : 'vertex;
    mutable hedges : 'hedge list;
    mutable widen : bool;
  }
type ('vertex,'hedge) strategy =
  (strategy_iteration, ('vertex,'hedge) strategy_vertex) Ilist.t
  (* = ('vertex,'hedge) FixpointType.strategy *)

type ('vertex,'hedge) equation =
  'vertex -> ('hedge, 'vertex array * 'vertex) PMappe.t
  (* = ('vertex,'hedge) FixpointType.equation *)

type stat_iteration = FixpointType.stat_iteration = {
  mutable nb: int;
  mutable stable: bool;
}
type stat = FixpointType.stat = {
  mutable time : float;
  mutable ascending : (stat_iteration,unit) Ilist.t;
  mutable descending : (stat_iteration,unit) Ilist.t;
}
  (** statistics at the end of the analysis *)

type ('vertex,'hedge,'abstract,'arc) output =
  ('vertex,'hedge,'abstract,'arc, stat) PSHGraph.t
*)
  (** result of the analysis *)

(*  ********************************************************************** *)
(** {2 Functions} *)
(*  ********************************************************************** *)

let make_strategy_default = make_strategy_default
let analysis_std = analysis
(*let analysis_guided = FixpointGuided.analysis*)
(*let analysis_dyn = FixpointDyn.analysis

let equation_of_graph = FixpointDyn.equation_of_graph

let graph_of_equation = FixpointDyn.graph_of_equation*)

(*  ********************************************************************** *)
(** {2 Printing functions} *)
(*  ********************************************************************** *)

let print_strategy_vertex = print_strategy_vertex
let print_strategy = print_strategy
let print_stat = print_stat
let print_output = print_output