open Cfg

type absstate =
  | Bot | Top
  | S of (*Symbol.sym Core.generic_value*) int SMap.t

let is_leq s1 s2 =
  match s1, s2 with
  | Bot, _ -> true
  | _, Bot -> false
  | _, Top -> true
  | Top, _ -> false
  | S m1, S m2 ->
    (* TODO: this is not correct *)
    SMap.fold (fun k v1 acc ->
        match SMap.find_opt k m2 with
        | Some v2 -> acc && v1 <= v2 (* TODO *)
        | None -> false
      ) m1 true

let join s1 s2 =
  match s1, s2 with
  | Bot, s -> s
  | s, Bot -> s
  | _, Top
  | Top, _ -> print_endline "joined to top"; Top
  | S m1, S m2 ->
    (* TODO: this is not correct *)
    S (SMap.fold SMap.add m1 m2)


let show_absstate = function
  | Top -> "top"
  | Bot -> "bot"
  | S m ->
    SMap.fold (fun k v acc ->
        acc ^ Sym.show k ^ ": " ^ (*String_core.string_of_value*) string_of_int v ^ "\n"
      ) m ""

let test = ref 0

let apply psh he st_arr =
  print_endline "APPLYING";
  let tr = PSHGraph.attrhedge psh he in
  let abs = st_arr.(0) in
  print_endline @@ Cfg.show_transfer tr;
  match tr with
  | Tskip -> abs
  | Tcond c ->
    print_endline "TODO: cond";
    abs
  | Tcall _ ->
    print_endline "TODO: call";
    abs
  | Tassign (pat, te) ->
    (* TODO: evaluate te *)
    (* HACK: pat *)
    let open Core in
    match pat with
    | Pattern (_, CaseBase (None, _)) -> abs
    | Pattern (_, CaseBase (Some sym, _)) ->
      incr test;
      begin match abs with
        | Bot -> S (SMap.add sym !test SMap.empty)
        | S m -> S (SMap.add sym !test m)
        | _ -> print_endline "returned top in apply"; Top
      end
    | _ -> print_endline "TODO"; abs


(*
  (*| Tskip -> print_endline "skip"; ((), Top) (*st_arr.(0)) *) *)
  | _ -> incr test; ((), S !test)
   *)

let make_fpmanager psh =
  let open Fixpoint in
  { bottom = (fun vtx -> print_endline "checking bot"; print_endline ("vtx: " ^ string_of_int vtx); Bot);
    canonical = (fun vtx abs -> ());
    is_bottom = (fun vtx abs ->
        print_endline "is bottom";
        abs = Bot);
    is_leq = (fun vtx abs1 abs2 ->
        print_endline "is_leq"; 
        match abs1, abs2 with
        | Bot, _ -> true
        | S n, S m -> n <= m
        | _, _ -> false);
    join = (fun vst abs1 abs2 -> join abs1 abs2);
    join_list = (fun vtx abs_s -> List.fold_left join Bot abs_s);
    widening = (fun vtx abs1 abs2 -> assert false);
    odiff = None;
    abstract_init = (fun vtx -> Bot);
    arc_init = (fun edge -> ());
    apply = (fun he st_arr -> ((), apply psh he st_arr));
    print_vertex = (fun _ _ -> ());
    print_hedge = (fun _ _ -> ());
    print_abstract = (fun _ _ -> ());
    print_arc = (fun _ _ -> ());
    accumulate = false;
    print_fmt = Format.err_formatter;
    print_analysis = false;
    print_component = false;
    print_step = false;
    print_state = false;
    print_postpre = false;
    print_workingsets = false;
    dot_fmt = None;
    dot_vertex = (fun _ _ -> ());
    dot_hedge = (fun _ _ -> ());
    dot_attrvertex = (fun _ _ -> ());
    dot_attrhedge = (fun _ _ -> ());
  }

type info =
  { mutable counter: int;
  }

let add_vertex (graph) (torg) (transfer) (dest) : unit =
  Array.iter
    (begin fun var ->
      if not (PSHGraph.is_vertex graph var) then PSHGraph.add_vertex graph var ()
    end)
    torg;
  if not (PSHGraph.is_vertex graph dest) then PSHGraph.add_vertex graph dest ();
  let info = PSHGraph.info graph in
  PSHGraph.add_hedge graph info.counter transfer ~pred:torg ~succ:[|dest|];
  info.counter <- info.counter + 1

let gcompare = {
  PSHGraph.hashv = {
    Hashhe.hash = (fun x -> abs x);
    Hashhe.equal = (=);
  };
  PSHGraph.hashh = {
    Hashhe.hash = (fun x -> abs x);
    Hashhe.equal = (==)
  };
  PSHGraph.comparev = Cfg.Graph.compare_vertex;
  PSHGraph.compareh = compare
}

let convert_graph g =
  let psh = PSHGraph.create gcompare 20 { counter = 0 } in
  Cfg.Graph.iter_edges g (fun v1 v2 d ->
      add_vertex psh [|v1|] d v2
    );
  let open Format in
  PSHGraph.print_dot
    (fun fmt v -> pp_print_text fmt @@ Cfg.Graph.string_of_vertex v)
    (fun fmt e -> pp_print_text fmt @@ string_of_int e)
    (fun fmt v _ -> pp_print_text fmt @@ Cfg.Graph.string_of_vertex v)
    (fun fmt _ tf -> pp_print_text fmt @@ Cfg.show_transfer tf)
    (Format.formatter_of_out_channel (open_out "c.dot"))
    psh;
  psh

let solve core =
  let cfg = Cfg.mk_main ~sequentialise:true core in
  let psh = convert_graph cfg in
  let fpman = make_fpmanager psh in
  let init = PSette.singleton (Cfg.Graph.compare_vertex) 1 in
  let fp_strategy = Fixpoint.make_strategy_default ~vertex_dummy:(-1) ~hedge_dummy:(-1) psh init in
  let fp = Fixpoint.analysis_std fpman psh init fp_strategy in
  let open Format in
  PSHGraph.print_dot
    (fun fmt v -> pp_print_text fmt @@ Cfg.Graph.string_of_vertex v)
    (fun fmt e -> pp_print_text fmt @@ string_of_int e)
    (fun fmt _ s -> pp_print_text fmt @@ show_absstate s)
    (fun fmt _ tf -> ())
    Format.err_formatter
    fp
