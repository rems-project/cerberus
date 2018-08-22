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
let hack conf mode =
  let open Global_ocaml in
  let conf =
    { cpp_cmd=            conf.Pipeline.cpp_cmd;
      pps=                [];
      ppflags=            [];
      exec_mode_opt=      Some (to_smt2_mode mode);
      ocaml=              false;
      ocaml_corestd=      false;
      progress=           false;
      rewrite=            conf.Pipeline.rewrite_core;
      sequentialise=      conf.Pipeline.sequentialise_core;
      concurrency=        false;
      preEx=              false;
      error_verbosity=    Global_ocaml.QuoteStd;
      batch=              true;
      experimental_unseq= false;
      typecheck_core=     conf.Pipeline.typecheck_core;
      defacto=            false;
      default_impl=       false;
      action_graph=       false;
      n1507=              if true (* TODO: put a switch in the web *) (* error_verbosity = QuoteStd *) then
                            Some (Yojson.Basic.from_file (Pipeline.cerb_path ^ "/tools/n1570.json"))
                          else None;
    }
  in cerb_conf := fun () -> conf

let respond f = function
  | Exception.Result r -> f r
  | Exception.Exception err -> Failure (Pp_errors.to_string err)

(* elaboration *)

let elaborate ~conf ~filename =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack conf.pipeline Random;
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
  hack conf.pipeline mode;
  Debug.print 7 ("Executing in "^string_of_exec_mode mode^" mode: " ^ filename);
  try
    elaborate ~conf ~filename
    >>= fun (cabs, ail, sym_suppl, core) ->
    Pipeline.interp_backend dummy_io sym_suppl (Core_run_aux.convert_file core)
      [] true false false (to_smt2_mode mode)
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

let rec multiple_steps step_state (Nondeterminism.ND m, st) =
  let module CS = (val Ocaml_mem.cs_module) in
  let (>>=) = CS.bind in
  let get_location st =
    match st.Driver.core_state.Core_run.thread_states with
    | (_, (_, ts))::_ -> Some (ts.Core_run.current_loc, ts.Core_run.current_uid)
    | _ -> None
  in
  let create_branch lab (st: Driver.driver_state) (ns, es, previousNode) =
    let nodeId  = new_id () in
    let mem     = Ocaml_mem.serialise_mem_state st.Driver.layout_state in
    let newNode = Branch (nodeId, lab, mem, get_location st) in
    let ns' = newNode :: ns in
    let es' = Edge (previousNode, nodeId) :: es in
    (ns', es', nodeId)
  in
  let create_leafs st ms (ns, es, previousNode) =
    let (is, ns') = List.fold_left (fun (is, ns) (l, m) ->
        let i = new_id () in
        let n = Leaf (i, l, encode (m, st)) in
        (i::is, n::ns)
      ) ([], ns) ms in
    let es' = (List.map (fun n -> Edge (previousNode, n)) is) @ es in
    (ns', es', previousNode)
  in
  let check st f = function
    | `UNSAT -> CS.return (Some "unsat", create_branch "unsat" st step_state)
    | `SAT -> CS.return @@ f ()
  in
  let runCS st f = CS.runEff (CS.check_sat >>= check st f) in
  let withCS str cs st f =
    CS.runEff (CS.with_constraints str cs (CS.check_sat >>= check st f))
  in
  try
    let open Nondeterminism in
    let one_step = function
      | (NDactive a, st') ->
        Debug.print 0 "active";
        runCS st' begin fun () ->
          let str_v = String_core.string_of_value a.Driver.dres_core_value in
          let res =
            "Defined {value: \"" ^ str_v ^ "\", stdout: \""
            ^ String.escaped a.Driver.dres_stdout
            ^ "\", blocked: \""
            ^ if a.Driver.dres_blocked then "true\"}" else "false\"}"
          in
          (Some res, create_branch str_v st' step_state)
        end
      | (NDkilled r, st') ->
        (Some "killed", create_branch "killed" st' step_state)
      | (NDbranch (str, cs, m1, m2), st') ->
        withCS str cs st' begin fun () ->
          create_branch str st' step_state
          |> create_leafs st' [("opt1", m1); ("opt2", m2)]
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
      | (NDstep ms, st') ->
        (None, create_leafs st' ms step_state)
    in begin match m st with
      | (NDstep [(lab, m')], st') ->
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

let step ~conf ~filename active_node =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  match active_node with
  | None -> (* no active node *)
    hack conf.pipeline Random;
    elaborate ~conf ~filename >>= fun (_, _, sym_suppl, core) ->
    let core'    = Core_aux.set_uid @@ Core_run_aux.convert_file core in
    let ranges   = create_expr_range_list core' in
    let st0      = Driver.initial_driver_state sym_suppl core' in
    let (m, st)  = (Driver.drive false false sym_suppl core' [], st0) in
    let initId   = new_id () in
    let nodeId   = Leaf (initId, "Initial", encode (m, st)) in
    let tagDefs  = encode @@ Tags.tagDefs () in
    return @@ Interactive (tagDefs, ranges, ([nodeId], []))
  | Some (last_id, marshalled_state, node, tags) ->
    let tagsMap : (Symbol.sym, Tags.tag_definition) Pmap.map = decode tags in
    Tags.set_tagDefs tagsMap;
    hack conf.pipeline Random;
    last_node_id := last_id;
    decode marshalled_state
    |> multiple_steps ([], [], node)
    |> fun (res, (ns, es, _)) -> return @@ Step (res, node, (ns, es))

let instance debug_level =
  Debug.level := debug_level;
  Debug.print 7 ("Using model: " ^ Prelude.string_of_mem_switch ());
  let do_action = function
    | `Elaborate (conf, filename) ->
      elaborate ~conf:(setup conf) ~filename
      |> respond result_of_elaboration
    | `Execute (conf, filename, mode) ->
      execute ~conf:(setup conf) ~filename mode
      |> respond (fun s -> Execution s)
    | `Step (conf, filename, active) ->
      step ~conf:(setup conf) ~filename active
      |> respond id
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
  try
    let stdout = redirect () in
    let result = do_action @@ Marshal.from_channel stdin in
    recover stdout; send result;
    Debug.print 7 "Instance has successfully finished."
  with e ->
    Debug.error ("Exception raised in instance: " ^ Printexc.to_string e)

(* Arguments *)

open Cmdliner

let debug_level =
  let doc = "Set the debug message level for the instance to $(docv) \
             (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let () =
  let instance = Term.(pure instance $ debug_level) in
  let doc  = "Cerberus instance with fixed memory model." in
  let info = Term.info "Cerberus instance" ~doc in
  match Term.eval (instance, info) with
  | `Error _ -> exit 1;
  | `Ok _
  | `Version
  | `Help -> exit 0
