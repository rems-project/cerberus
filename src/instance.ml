open Util
open Instance_api

type conf =
  { pipeline: Pipeline.configuration;
    io: Pipeline.io_helpers;
    instance: Instance_api.conf;
  }

let dummy_io =
  let open Pipeline in
  let skip = fun _ -> Exception.except_return ()
  in {
    pass_message=   skip;
    set_progress=   skip;
    run_pp=         (fun _ -> skip);
    print_endline=  skip;
    print_debug=    (fun _ -> skip);
    warn=           skip;
  }

let setup conf =
  let pipeline_conf =
    { Pipeline.debug_level=        conf.cerb_debug_level;
      Pipeline.pprints=            [];
      Pipeline.astprints=          [];
      Pipeline.ppflags=            [];
      Pipeline.typecheck_core=     false;
      Pipeline.rewrite_core=       conf.rewrite_core;
      Pipeline.sequentialise_core= conf.sequentialise_core;
      Pipeline.cpp_cmd=            conf.cpp_cmd;

    }
  in { pipeline= pipeline_conf;
       io= dummy_io;
       instance= conf;
      }

(* It would be nice if Smt2 could use polymorphic variant *)
let to_smt2_mode = function
  | Random -> Smt2.Random
  | Exhaustive -> Smt2.Exhaustive

(* TODO: this hack is due to cerb_conf be undefined when running Cerberus *)
let hack ~conf mode =
  let open Global_ocaml in
  let cerb_path =
      try
        Sys.getenv "CERB_PATH"
      with Not_found ->
        error "expecting the environment variable CERB_PATH set to point\
               to the location cerberus."
  in
  let pipe_conf = conf.pipeline in
  cerb_conf := fun () ->
    { cpp_cmd=            pipe_conf.Pipeline.cpp_cmd;
      pps=                [];
      ppflags=            [];
      exec_mode_opt=      Some (to_smt2_mode mode);
      ocaml=              false;
      ocaml_corestd=      false;
      progress=           false;
      rewrite=            pipe_conf.Pipeline.rewrite_core;
      sequentialise=      pipe_conf.Pipeline.sequentialise_core;
      concurrency=        false;
      preEx=              false;
      error_verbosity=    Global_ocaml.QuoteStd;
      batch=              `Batch;
      experimental_unseq= false;
      typecheck_core=     pipe_conf.Pipeline.typecheck_core;
      defacto=            false;
      fs_dump=            false;
      default_impl=       false;
      action_graph=       false;
      n1507=              if true (* TODO: put a switch in the web *) (* error_verbosity = QuoteStd *) then
                            Some (Yojson.Basic.from_file (cerb_path ^ "/tools/n1570.json"))
                          else None;
    }

let respond filename name f = function
  | Exception.Result r ->
    f r
  | Exception.Exception err ->
    Failure (Str.replace_first (Str.regexp_string filename) name @@ Pp_errors.to_string err)

(* elaboration *)

let elaborate ~conf ~filename =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack ~conf Random;
  Switches.set conf.instance.switches;
  Debug.print 7 @@ List.fold_left (fun acc sw -> acc ^ " " ^ sw) "Switches: " conf.instance.switches;
  Debug.print 7 ("Elaborating: " ^ filename);
  try
    Pipeline.load_core_stdlib () >>= fun core_stdlib ->
    Pipeline.load_core_impl core_stdlib conf.instance.core_impl >>= fun core_impl ->
    Pipeline.c_frontend (conf.pipeline, conf.io) (core_stdlib, core_impl) filename
    >>= function
    | (Some cabs, Some ail, sym_suppl, core) ->
      Pipeline.core_passes (conf.pipeline, conf.io) ~filename core
      >>= fun (_, core') ->
      return (cabs, ail, sym_suppl, core')
    | _ ->
      failwith "fatal failure core pass"
  with
  | e ->
    Debug.warn ("Exception raised during elaboration. " ^ Printexc.to_string e);
    raise e

let string_of_doc d =
  let buf = Buffer.create 1024 in
  Colour.do_colour := false;
  PPrint.ToBuffer.pretty 1.0 80 buf d;
  Buffer.contents buf

let pp_core core =
  let locs = ref [] in
  let module PP = Pp_core.Make (struct
      let show_std = true
      let show_include = false
      let handle_location c_loc core_range =
        match Location_ocaml.to_cartesian c_loc with
        | Some c_range ->
          locs := (c_range, core_range)::!locs
        | None -> ()
      let handle_uid _ _ = ()
    end) in
  let core' = string_of_doc @@ PP.pp_file core in
  (core', !locs)

let result_of_elaboration (cabs, ail, _, core) =
  let elim_paragraph_sym = Str.global_replace (Str.regexp_string "§") "" in
  let mk_elab d = Some (elim_paragraph_sym @@ string_of_doc d) in
  let (core, locs) = pp_core core in
  Elaboration
    { pp= {
        cabs= None;
        ail=  mk_elab @@ Pp_ail.pp_program false false ail;
        core= Some (elim_paragraph_sym core)
      };
      ast= {
        cabs= mk_elab @@ Pp_cabs.pp_translation_unit false false cabs;
        ail=  mk_elab @@ Pp_ail_ast.pp_program false false ail;
        core = None;
      };
      locs= locs;
      result= "success";
    }

(* execution *)

let execute ~conf ~filename (mode: exec_mode) =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack ~conf mode;
  Debug.print 7 ("Executing in "^string_of_exec_mode mode^" mode: " ^ filename);
  try
    elaborate ~conf ~filename
    >>= fun (cabs, ail, sym_suppl, core) ->
    Pipeline.interp_backend dummy_io sym_suppl (Core_run_aux.convert_file core)
      [] `Batch false false (to_smt2_mode mode)
    >>= function
    | Either.Left res ->
      return (String.concat "\n" res)
    | Either.Right res ->
      return (string_of_int res)
  with
  | e ->
    Debug.warn ("Exception raised during execution: " ^ Printexc.to_string e);
    raise e

(* WARN: fresh new ids *)
let last_node_id : int ref = ref 0
let new_id () = incr last_node_id; !last_node_id

let encode s = Marshal.to_string s [Marshal.Closures]
let decode s = Marshal.from_string s 0

let get_state_details st =
  let string_of_env st =
    let env = st.Driver.core_run_state.env in
    let f e = Pmap.fold (fun (s:Symbol.sym) (v:Core.value) acc ->
        Pp_symbol.to_string_pretty s ^ "= " ^ String_core.string_of_value v ^ "\n" ^ acc
      ) e "" in
    List.fold_left (fun acc e -> acc ^ f e) "" env
  in
  let outp = String.concat "" @@ Dlist.toList (st.Driver.core_state.Core_run.io.Core_run.stdout) in
  match st.Driver.core_state.Core_run.thread_states with
  | (_, (_, ts))::_ ->
    let arena = Pp_utils.to_plain_pretty_string @@ Pp_core.Basic.pp_expr ts.arena in
    let Core.Expr (arena_annots, _) = ts.arena in
    let maybe_uid = Annot.get_uid arena_annots in
    let loc = Option.case id (fun _ -> ts.Core_run.current_loc) @@ Annot.get_loc arena_annots in
    (loc, maybe_uid, arena, string_of_env st, outp)
  | _ ->
    (Location_ocaml.unknown, None, "", "", outp)

let create_node dr_info st next_state =
  let mk_info info =
    { step_kind = info.Driver.step_kind;
      step_debug = Option.case (fun i -> i.Core_run.debug_str) (fun _ -> "no debug string") info.Driver.core_run_info;
      step_file = Option.case (fun i -> i.Core_run.from_file) (fun _ -> None) info.Driver.core_run_info;
      step_error_loc = info.Driver.error_loc
    }
  in
  let node_id = new_id () in
  let node_info = mk_info dr_info in
  let memory = Ocaml_mem.serialise_mem_state st.Driver.layout_state in
  let (c_loc, core_uid, arena, env, outp) = get_state_details st in
  { node_id; node_info; memory; c_loc; core_uid; arena; env; next_state; outp }

let rec multiple_steps step_state (((Nondeterminism.ND m): (Driver.driver_result, Driver.driver_info, Driver.driver_error, _, _) Nondeterminism.ndM), st) =
  let module CS = (val Ocaml_mem.cs_module) in
  let (>>=) = CS.bind in
  let create_branch dr_info st (ns, es, previousNode) =
    let n = create_node dr_info st None in
    let ns' = n :: ns in
    let es' = Edge (previousNode, n.node_id) :: es in
    (ns', es', n.node_id)
  in
  let create_leafs st ms (ns, es, previousNode) =
    let (is, ns') = List.fold_left (fun (is, ns) (dr_info, m) ->
        let n = create_node dr_info st (Some (encode (m, st))) in
        (n.node_id::is, n::ns)
      ) ([], ns) ms in
    let es' = (List.map (fun n -> Edge (previousNode, n)) is) @ es in
    (ns', es', previousNode)
  in
  let check st f = function
    | `UNSAT -> CS.return (Some "unsat", create_branch (Driver.mk_info_kind "unsat") st step_state)
    | `SAT -> CS.return @@ f ()
  in
  let runCS st f = CS.runEff (CS.check_sat >>= check st f) in
  let withCS str cs st f =
    CS.runEff (CS.with_constraints str cs (CS.check_sat >>= check st f))
  in
  try
    let open Nondeterminism in
    let one_step: (_, Driver.driver_info, _, _, _) Nondeterminism.nd_action * _ -> _ = function
      | (NDactive a, st') ->
        runCS st' begin fun () ->
          let str_v = String_core.string_of_value a.Driver.dres_core_value in
          let res =
            "Defined {value: \"" ^ str_v ^ "\", stdout: \""
            ^ String.escaped a.Driver.dres_stdout
            ^ "\", blocked: \""
            ^ if a.Driver.dres_blocked then "true\"}" else "false\"}"
          in
          (Some res, create_branch (Driver.mk_info_kind str_v) st' step_state)
        end
      | (NDkilled r, st') ->
        let loc, reason = match r with
          | Undef0 (loc, ubs) ->
            Some loc, "Undefined: " ^ Lem_show.stringFromList Undefined.ub_short_string ubs
          | Error0 (loc, str) ->
            Some loc, "Error: " ^ str ^ ""
          | Other dr_err ->
            let string_of_driver_error = function
              | Driver.DErr_core_run err ->
                None, Pp_errors.string_of_core_run_cause err
              | Driver.DErr_memory err ->
                let open Mem_common in
                let string_of_access_error = function
                  | NullPtr -> "null pointer"
                  | FunctionPtr -> "function pointer"
                  | DeadPtr -> "dead pointer"
                  | OutOfBoundPtr -> "out of bound pointer"
                  | NoProvPtr -> "invalid provenance"
                in
                let string_of_free_error = function
                  | Free_static_allocation -> "static allocated region"
                  | Free_dead_allocation -> "dead allocation"
                  | Free_out_of_bound -> "out of bound"
                in
                begin match err with
                  | MerrOutsideLifetime str ->
                    None, "memory outside lifetime: " ^ str
                  | MerrOther str ->
                    None, "other memory error: " ^ str
                  | MerrPtrdiff ->
                    None, "invalid pointer diff"
                  | MerrAccess (loc, LoadAccess, err) ->
                    Some loc, "invalid memory load: " ^ string_of_access_error err
                  | MerrAccess (loc, StoreAccess, err) ->
                    Some loc, "invalid memory store: " ^ string_of_access_error err
                  | MerrInternal str ->
                    None, "internal error: " ^ str
                  | MerrPtrFromInt ->
                    None, "invalid cast pointer from integer"
                  | MerrWriteOnReadOnly _ ->
                    None, "writing read only memory"
                  | MerrUndefinedFree (loc, err) ->
                    Some loc, "freeing " ^ string_of_free_error err
                  | MerrUndefinedRealloc ->
                    None, "undefined behaviour in realloc"
                  | MerrIntFromPtr ->
                    None, "invalid cast integer from pointer"
                  | MerrWIP str ->
                    None, "wip: " ^ str
              end
            | Driver.DErr_concurrency str ->
                None, "Concurrency error: " ^ str
            | Driver.DErr_other str ->
                None, str
          in
          let loc, str = string_of_driver_error dr_err in
          loc, "killed: " ^ str
        in
        let info =
          let open Driver in
          { step_kind= reason;
            core_run_info= None;
            error_loc= loc;
          }
        in (Some reason, create_branch info st' step_state)
      | (NDbranch (str, cs, m1, m2), st') ->
        withCS str cs st' begin fun () ->
          create_branch str st' step_state
          |> create_leafs st' [(Driver.mk_info_kind "opt1", m1); (Driver.mk_info_kind "opt2", m2)]
          |> fun res -> (None, res)
        end
      | (NDguard (str, cs, m), st') ->
        withCS str cs st' begin fun () ->
          create_leafs st' [(str, m)] step_state
          |> fun res -> (None, res)
        end
        |> fun s -> Debug.print 0 "finish guard"; s
      | (NDnd (str, ms), st') ->
        (None, create_leafs st' ms step_state)
      | (NDstep (_, ms), st') ->
        (None, create_leafs st' ms step_state)
    in begin match m st with
      | (NDstep (_, [(lab, m')]), st') ->
        let step_state' = create_branch lab st' step_state in
        multiple_steps step_state' (m', st')
      | act -> one_step act
    end
  with
  | e -> Debug.warn ("Exception raised during execution: " ^ Printexc.to_string e);
    raise e

let create_expr_range_list core =
  let table = Hashtbl.create 100 in
  let module PP = Pp_core.Make (struct
      let show_std = true
      let show_include = false
      let handle_location _ _ = ()
      let handle_uid = Hashtbl.add table
    end) in
  ignore (string_of_doc @@ PP.pp_file core);
  Hashtbl.fold (fun k v acc -> (k, v)::acc) table []

let step ~conf ~filename (active_node_opt: Instance_api.active_node option) =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  match active_node_opt with
  | None -> (* no active node *)
    hack ~conf Random;
    elaborate ~conf ~filename >>= fun (_, _, sym_suppl, core) ->
    let core'    = Core_aux.set_uid @@ Core_run_aux.convert_file core in
    let ranges   = create_expr_range_list core' in
    let st0      = Driver.initial_driver_state sym_suppl core' in
    let (m, st)  = (Driver.drive false false sym_suppl core' [], st0) in
    last_node_id := 0;
    let node_info= { step_kind= "init"; step_debug = "init"; step_file = None; step_error_loc = None } in
    let memory = Ocaml_mem.serialise_mem_state st.Driver.layout_state in
    let (c_loc, core_uid, arena, env, outp) = get_state_details st in
    let next_state = Some (encode (m, st)) in
    let n = { node_id= 0; node_info; memory; c_loc; core_uid; arena; env; next_state; outp } in
    let tagDefs  = encode @@ Tags.tagDefs () in
    return @@ Interactive (tagDefs, ranges, ([n], []))
  | Some n ->
    let tagsMap : (Symbol.sym, Tags.tag_definition) Pmap.map = decode n.tagDefs in
    Tags.set_tagDefs tagsMap;
    hack ~conf Random;
    Switches.set conf.instance.switches;
    last_node_id := n.last_id;
    decode n.marshalled_state
    |> multiple_steps ([], [], n.active_id)
    |> fun (res, (ns, es, _)) -> return @@ Step (res, n.active_id, (ns, es))

let instance debug_level =
  Debug.level := debug_level;
  Debug.print 7 ("Using model: " ^ Prelude.string_of_mem_switch ());
  let do_action  : Instance_api.request -> Instance_api.result = function
    | `Elaborate (conf, filename, name) ->
      elaborate ~conf:(setup conf) ~filename
      |> respond filename name result_of_elaboration
    | `Execute (conf, filename, name, mode) ->
      execute ~conf:(setup conf) ~filename mode
      |> respond filename name (fun s -> Execution s)
    | `Step (conf, filename, name, active) ->
      step ~conf:(setup conf) ~filename active
      |> respond filename name id
  in
  let redirect () =
    (* NOTE: redirect stdout to stderr copying stdout file descriptor
     * just in case any module in Cerberus tries to print something *)
    let stdout' = Unix.dup Unix.stdout in
    Unix.dup2 Unix.stderr Unix.stdout;
    stdout'
  in
  let recover oc =
    flush stdout;
    Unix.dup2 oc Unix.stdout
  in
  let send result =
    Marshal.to_channel stdout result [Marshal.Closures];
  in
  let stdout = redirect () in
  try
    let result = do_action @@ Marshal.from_channel stdin in
    recover stdout; send result;
    Debug.print 7 "Instance has successfully finished."
  with
  | Failure msg ->
    Debug.error ("Exception raised in instance: " ^ msg);
    recover stdout; send (Failure msg)
  | e ->
    Debug.error ("Exception raised in instance: " ^ Printexc.to_string e);
    recover stdout;
    send (Failure (Printexc.to_string e))

(* Arguments *)

open Cmdliner

let debug_level =
  let doc = "Set the debug message level for the instance to $(docv) \
             (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let () =
  let instance = Term.(pure instance $ debug_level) in
  let doc  = "Cerberus instance with a fixed memory model." in
  let info = Term.info "Cerberus instance" ~doc in
  match Term.eval (instance, info) with
  | `Error _ -> exit 1;
  | `Ok _
  | `Version
  | `Help -> exit 0
