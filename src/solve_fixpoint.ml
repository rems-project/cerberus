open Cfg
open Core

module N = Nat_big_num

type info =
  { mutable counter: int;
  }



(* TODO: we fix box (intervals) at the moment *)
let man = Box.manager_alloc ()

type absterm =
  | ATunit
  | ATtrue
  | ATfalse
  | ATctype of Core_ctype.ctype0 (* C type as value *)
  | ATtuple of absterm list
        (*
  | ATint of Ocaml_mem.integer_value
  | ATsym of Symbol.sym
           *)
  | ATexpr of Apron.Texpr1.t
  | ATunspec
  | ATtop

type env =
  { env_scalar: Box.t Apron.Abstract1.t; (* pointer, integers and floats *)
    env_term: absterm SMap.t;
  }

let show_abs env =
    Apron.Abstract1.print Format.str_formatter env;
    Format.flush_str_formatter ()

type absstate = env option

let is_leq s1 s2 =
  print_endline "is_leq";
  match s1, s2 with
  | _, None -> true
  | None, _ -> false
  | Some env1, Some env2 ->
    (* TODO/NOTE: this is wrong, it ignores non scalar terms *)
    (*
    print_endline "leq";
    print_string "1: ";
    print_endline @@ show_abs env1.env_scalar;
    print_string "2: ";
    print_endline @@ show_abs env2.env_scalar;
       *)
    let abs_env =
      match Apron.Environment.compare (Apron.Abstract1.env env1.env_scalar)
              (Apron.Abstract1.env env2.env_scalar) with
      | -2 -> assert false
      | -1 -> Apron.Abstract1.env env2.env_scalar
      | 0
      | 1 -> Apron.Abstract1.env env1.env_scalar
      | _ -> assert false
    in
    let env_scalar1
      = Apron.Abstract1.change_environment man env1.env_scalar abs_env true in
    let env_scalar2
      = Apron.Abstract1.change_environment man env2.env_scalar abs_env true in
    Apron.Abstract1.is_leq man env_scalar1 env_scalar2

let join s1 s2 =
  print_endline "join";
  match s1, s2 with
  | _, None | None, _ -> None
  | Some env1, Some env2 ->
    (* TODO/NOTE: this is wrong, it ignores non scalar terms *)
    let abs_env =
      match Apron.Environment.compare (Apron.Abstract1.env env1.env_scalar)
              (Apron.Abstract1.env env2.env_scalar) with
      | -2 -> assert false
      | -1 -> Apron.Abstract1.env env2.env_scalar
      | 0
      | 1 -> Apron.Abstract1.env env1.env_scalar
      | _ -> assert false
    in
    let env_scalar1
      = Apron.Abstract1.change_environment man env1.env_scalar abs_env true in
    let env_scalar2
      = Apron.Abstract1.change_environment man env2.env_scalar abs_env true in
    let env =
      { env_scalar = Apron.Abstract1.join man env_scalar1 env_scalar2;
        env_term = env1.env_term;
      }
    in Some env

let bot () =
  let env0 = Apron.Environment.make [||] [||] in
  let env =
    { env_scalar = Apron.Abstract1.bottom man env0;
      env_term = SMap.empty;
    }
  in Some env

let top =
  None

let show_absstate = function
  | None -> "top"
  | Some env ->
    (* TODO/NOTE: ignoring non scalar terms *)
    show_abs env.env_scalar

let absterm_of_action env = function
  | Create _ ->
    assert false
  | Store0 (_, _, p_pe, v_pe, _) ->
    assert false
  | Kill _ ->
    (* TODO *)
    ATunit
  | _ -> assert false

let rec absterm_of_texpr env = function
  | TEsym x ->
    let var = Apron.Var.of_string (Sym.show x) in
    ATexpr (Apron.Texpr1.var env var)
  | TEval v ->
    begin match v with
      | Vobject (OVinteger i)
      | Vloaded (LVspecified (OVinteger i)) ->
        let n = Ocaml_mem.case_integer_value i
          (fun n -> Apron.Coeff.s_of_int (N.to_int n))
          (fun _ -> assert false)
        in
        ATexpr (Apron.Texpr1.cst env n)
      | _ ->
        assert false
    end
  | TEcall (Sym (Symbol.Symbol (_, _, Some "catch_exceptional_condition")), [_; te])
  | TEcall (Sym (Symbol.Symbol (_, _, Some "conv_int")), [_; te])
  | TEcall (Sym (Symbol.Symbol (_, _, Some "conv_loaded_int")), [_; te])
    ->
    absterm_of_texpr env te
  | TEcall (Sym sym, _) ->
    print_endline @@ Sym.show sym;
    assert false
  | TEcall _ ->
    assert false
  | TEundef _ ->
    assert false
  | TEctor (ctor, tes) ->
    begin match ctor, tes with
      | Ctuple, _ ->
        ATtuple (List.map (absterm_of_texpr env) tes)
      | Cspecified, [te] ->
        absterm_of_texpr env te
      | _ ->
        assert false
    end
  | TEop (bop, te1, te2) ->
    let t1 = absterm_of_texpr env te1 in
    let t2 = absterm_of_texpr env te2 in
    begin match t1, t2 with
    | ATexpr e1, ATexpr e2 ->
      let bop = match bop with
        | OpAdd -> Apron.Texpr1.Add
        | OpSub -> Apron.Texpr1.Sub
        | OpMul -> Apron.Texpr1.Mul
        | OpDiv -> Apron.Texpr1.Div
        | OpRem_t -> Apron.Texpr1.Mod
        | OpRem_f -> Apron.Texpr1.Mod (* TODO *)
        | _ -> assert false
      in
      ATexpr (Apron.Texpr1.binop bop e1 e2 Apron.Texpr1.Int Apron.Texpr1.Rnd)
    end
  | TEaction (Paction (_, Action (_, _, act))) ->
    absterm_of_action env act
  | _ ->
    assert false

let rec match_pattern pat te =
  match pat, te with
  | Pattern (_, CaseBase (None, _)), _
  | Pattern (_, CaseBase (Some _, _)), _ ->
    true
  | Pattern (_, CaseCtor (Cspecified, [pat])), te ->
    match_pattern pat te
  | Pattern (_, CaseCtor (Ctuple, pats)), TEctor (Ctuple, tes) ->
    if List.length pats = List.length tes then
      List.for_all (fun (pat, te) -> match_pattern pat te)
        @@ List.combine pats tes
    else
      false
  | _ -> false

let apply psh he st_arr =
  print_endline "APPLYING";
  let tr = PSHGraph.attrhedge psh he in
  let abs = st_arr.(0) in
  print_endline @@ Cfg.show_transfer tr;
  match tr with
  | Tskip -> abs
  | Tcond c ->
    let rec aux = function
      | Cmatch (pat, te) -> match_pattern pat te
      | Cnot c -> not @@ aux c
      | _ ->
        print_endline "TODO: cond";
        assert false
    in
    if aux c then
      abs
    else
      bot ()
  | Tcall _ ->
    print_endline "TODO: call";
    abs
  | Tassign (pat, te) ->
    (* TODO: evaluate te *)
    (* HACK: pat *)
    let rec aux env = function
      | Pattern (_, CaseBase (None, _)), _ -> env
      | Pattern (_, CaseBase (Some sym, _)), e ->
        let env0 = Apron.Abstract1.env env.env_scalar in
        begin match e with
          | ATexpr e ->
            (* TODO: this is poor *)
            (* TODO: I dont' know how to deal with the apron env *)
            let var = Apron.Var.of_string (Sym.show sym) in
            print_endline @@ "adding var: " ^ Sym.show sym;
            print_endline @@ show_abs env.env_scalar;
            let env1 = Apron.Environment.add env0 [| var |] [||] in
            (* TODO: add dest *)
            let env_scalar =
              Apron.Abstract1.change_environment man env.env_scalar env1
                true in
            let env_scalar =
              Apron.Abstract1.assign_texpr man env_scalar var e None
            in { env with env_scalar }
          | _ ->
            assert false
        end
      | Pattern (_, CaseCtor (Cspecified, [pat])), e ->
        aux env (pat, e)
      | Pattern (_, CaseCtor (Ctuple, pats)), ATtuple es ->
        List.fold_left aux env @@ List.combine pats es
      | _, _ -> print_endline "TODO"; env
    in
    begin match abs with
      | None ->
        print_endline "returned top in apply"; None
      | Some env ->
        let env0 = Apron.Abstract1.env env.env_scalar in
        begin match te with
          | TEundef _ -> top
          | _ ->
            let e = absterm_of_texpr env0 te in
            Some (aux env (pat, e))
        end
    end

let make_fpmanager psh =
  let open Fixpoint in
  (* let info = PSHGraph.info psh in
  let env_map = create_env_map psh in *)
  { bottom = (fun vtx ->
        bot ());
    canonical = (fun vtx abs -> ());
    is_bottom = (fun vtx abs ->
        match abs with
        | Some env ->
          Apron.Abstract1.is_bottom man env.env_scalar
        | None ->
          false
      );
    is_leq = (fun vtx -> is_leq);
    join = (fun vst -> join);
    join_list = (fun vtx abs_s -> List.fold_left join (bot ()) abs_s);
    widening = (fun vtx abs1 abs2 -> assert false);
    odiff = None;
    abstract_init = (fun vtx ->
      let env0 = Apron.Environment.make [||] [||] in
      let env =
        { env_scalar = Apron.Abstract1.top man env0;
          env_term = SMap.empty;
        }
      in Some env
      );
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
  try (
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
  ) with
    | Apron.Manager.Error e ->
      print_endline e.Apron.Manager.msg;
      assert false
