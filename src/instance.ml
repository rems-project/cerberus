open Util
open Instance_api

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
  let core_stdlib = Pipeline.load_core_stdlib () in
  let core_impl   = Pipeline.load_core_impl core_stdlib conf.core_impl in
  let pipeline_conf =
    { Pipeline.debug_level=        conf.cerb_debug_level;
      Pipeline.pprints=            [];
      Pipeline.astprints=          [];
      Pipeline.ppflags=            [];
      Pipeline.typecheck_core=     false;
      Pipeline.rewrite_core=       conf.rewrite_core;
      Pipeline.sequentialise_core= true;
      Pipeline.cpp_cmd=            conf.cpp_cmd;
      Pipeline.core_stdlib=        core_stdlib;
      Pipeline.core_impl=          core_impl;
    }
  in (pipeline_conf, dummy_io)

(* It would be nice if Smt2 could use polymorphic variant *)
let to_smt2_mode = function
  | Random -> Smt2.Random
  | Exhaustive -> Smt2.Exhaustive

(* TODO: this hack is due to cerb_conf be undefined when running Cerberus *)
let hack conf mode =
  let open Global_ocaml in
  cerb_conf := fun () -> {
    cpp_cmd=            conf.Pipeline.cpp_cmd;
    pps=                [];
    ppflags=            [];
    core_stdlib=        conf.Pipeline.core_stdlib;
    core_impl_opt=      Some conf.Pipeline.core_impl;
    core_parser=        (fun _ -> failwith "No core parser");
    exec_mode_opt=      Some (to_smt2_mode mode);
    ocaml=              false;
    ocaml_corestd=      false;
    progress=           false;
    rewrite=            conf.Pipeline.rewrite_core;
    sequentialise=      conf.Pipeline.sequentialise_core;
    concurrency=        false;
    preEx=              false;
    error_verbosity=    Global_ocaml.Basic;
    batch=              true;
    experimental_unseq= false;
    typecheck_core=     conf.Pipeline.typecheck_core;
    defacto=            false;
    default_impl=       false;
    action_graph=       false;
  }

let respond f = function
  | Exception.Result r -> f r
  | Exception.Exception err -> Failure (Pp_errors.to_string err)

(* elaboration *)

let elaborate ~conf ~filename =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack (fst conf) Random;
  Debug.print 7 ("Elaborating: " ^ filename);
  try
    Pipeline.c_frontend conf filename
    >>= function
    | (Some cabs, Some ail, sym_suppl, core) ->
      Pipeline.core_passes conf ~filename core
      >>= fun (core', _) ->
      return (cabs, ail, sym_suppl, core')
    | _ ->
      Exception.throw (Location_ocaml.unknown,
                       Errors.OTHER "fatal failure core pass")
  with
  | e ->
    Debug.warn ("Exception raised during elaboration. " ^ Printexc.to_string e);
    raise e

let result_of_elaboration (cabs, ail, _, core) =
  let string_of_doc d =
    let buf = Buffer.create 1024 in
    PPrint.ToBuffer.pretty 1.0 80 buf d;
    Buffer.contents buf
  in
  let elim_paragraph_sym = Str.global_replace (Str.regexp_string "§") "" in
  let mk_elab d = Some (elim_paragraph_sym @@ string_of_doc d) in
  let (core, locs) =
    let module Param_pp_core = Pp_core.Make (struct
        let show_std = true
        let show_location = true
        let show_proc_decl = false
      end) in
    Colour.do_colour := false;
    Param_pp_core.pp_file core
    |> string_of_doc
    |> Location_mark.extract
  in Elaboration
    { pp= {
        cabs= None;
        ail=  mk_elab @@ Pp_ail.pp_program ail;
        core= Some (elim_paragraph_sym core)
      };
      ast= {
        cabs= mk_elab @@ Pp_cabs.pp_translation_unit false false cabs;
        ail=  mk_elab @@ Pp_ail_ast.pp_program ail;
        core = None;
      };
      locs= locs;
      result= "success";
    }

(* execution *)

let execute ~conf ~filename (mode: exec_mode) =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack (fst conf) mode;
  Debug.print 7 ("Executing in "^string_of_exec_mode mode^" mode: " ^ filename);
  try
    elaborate ~conf ~filename
    >>= fun (cabs, ail, sym_suppl, core) ->
    Pipeline.interp_backend dummy_io sym_suppl core [] true false false
      (to_smt2_mode mode)
    >>= function
    | Either.Left res ->
      return (String.concat "\n" res)
    | Either.Right res ->
      return (string_of_int res)
  with
  | e ->
    Debug.warn ("Exception raised during execution." ^ Printexc.to_string e);
    raise e

(* WARN: fresh new ids *)
let last_node_id : int ref = ref 0
let new_id () = incr last_node_id; !last_node_id

let encode s = Marshal.to_string s [Marshal.Closures]
let decode s = Marshal.from_string s 0

let rec multiple_steps step_state (Nondeterminism.ND m, st) =
  let get_location _ = None in (* TODO *)
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
  try
    let open Nondeterminism in
    let one_step step_state = function
      | (NDactive a, st') ->
        let str_v = String_core.string_of_value a.Driver.dres_core_value in
        let res =
          "Defined {value: \"" ^ str_v ^ "\", stdout: \""
          ^ String.escaped a.Driver.dres_stdout
          ^ "\", blocked: \""
          ^ if a.Driver.dres_blocked then "true\"}" else "false\"}"
        in
        (Some res, create_branch str_v st' step_state)
      | (NDkilled r, st') ->
        (Some "killed", create_branch "killed" st' step_state)
      | (NDbranch (str, _, m1, m2), st') ->
        create_branch str st' step_state
        |> create_leafs st' [("opt1", m1); ("opt2", m2)]
        |> fun res -> (None, res)
      | (NDguard (str, _, m), st') ->
        create_leafs st' [(str, m)] step_state
        |> fun res -> (None, res)
      | (NDnd (str, (_,m)::ms), st') ->
        (* json_of_step (msg.steps, str, m, st') *)
        failwith "Ndnd"
      | (NDstep ms, st') ->
        create_leafs st' ms step_state
        |> fun res -> (None, res)
      | _ -> failwith ""
    in begin match m st with
      | (NDstep [(lab, m')], st') ->
        let step_state' = create_branch lab st' step_state in
        multiple_steps step_state' (m', st')
      | act -> one_step step_state act
    end
  with
  | e -> Debug.warn ("Exception raised during execution." ^ Printexc.to_string e);
    raise e

let step ~conf ~filename active_node =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  match active_node with
  | None -> (* no active node *)
    hack (fst conf) Random;
    elaborate ~conf ~filename >>= fun (_, _, sym_suppl, core) ->
    let core'    = Core_run_aux.convert_file core in
    let st0      = Driver.initial_driver_state sym_suppl core' in
    let (m, st)  = (Driver.drive false false sym_suppl core' [], st0) in
    let initId   = new_id () in
    let nodeId   = Leaf (initId, "Initial State", encode (m, st)) in
    return (None, ([nodeId], [], 0))
  | Some (last_id, marshalled_state, node) ->
    hack (fst conf) Random;
    last_node_id := last_id;
    decode marshalled_state
    |> multiple_steps ([], [], node)
    |> return

let result_of_step (res, (ns, es, _)) = Interaction (None, (ns, es))

let instance debug_level =
  Debug.level := debug_level;
  Debug.print 7 ("Model: " ^ Prelude.string_of_mem_switch ());
  let do_action = function
    | `Elaborate (conf, filename) ->
      elaborate ~conf:(setup conf) ~filename
      |> respond result_of_elaboration
    | `Execute (conf, filename, mode) ->
      execute ~conf:(setup conf) ~filename mode
      |> respond (fun s -> Execution s)
    | `Step (conf, filename, active) ->
      step ~conf:(setup conf) ~filename active
      |> respond result_of_step
  in
  let result = do_action @@ Marshal.from_channel stdin
  in Marshal.to_channel stdout result [Marshal.Closures]

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
