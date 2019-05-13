open Util
open Instance_api
open Pipeline

let time label f =
  let t = Unix.gettimeofday () in
  let res = f () in
  let delta = string_of_float @@ Unix.gettimeofday () -. t in
  Debug.print 5 @@ label ^ ": execution time: " ^ delta ^ " seconds";
  res

type conf =
  { pipeline: configuration;
    io: io_helpers;
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
    { debug_level=        conf.cerb_debug_level;
      pprints=            [];
      astprints=          [];
      ppflags=            [];
      typecheck_core=     false;
      rewrite_core=       conf.rewrite_core;
      sequentialise_core= conf.sequentialise_core;
      cpp_cmd=            (if conf.link_libc
                           then conf.cpp_cmd ^ " -DCERB_WITH_LIB"
                           else conf.cpp_cmd);
      cpp_stderr=         false;
    }
  in { pipeline= pipeline_conf;
       io= dummy_io;
       instance= conf;
      }

let add_bmc_macro ~bmc_model conf =
  let macro_model =
    match bmc_model with
      | `C11 -> " -D__memory_model_c11__"
      | `RC11 -> " -D__memory_model_rc11__"
      | `RC11_Hardcoded -> " -D__memory_model_rc11__"
      | `Linux -> " -D__memory_model_linux__"
      | `Custom _ -> " -D__memory_model_custom__"
      | _ -> ""
  in
  let cpp_cmd = conf.pipeline.cpp_cmd ^ " -D__bmc_cerb__" ^ macro_model in
  { conf with pipeline = { conf.pipeline with cpp_cmd } }

(* It would be nice if Smt2 could use polymorphic variant *)
let to_smt2_mode = function
  | Random -> Smt2.Random
  | Exhaustive -> Smt2.Exhaustive

(* TODO: this hack is due to cerb_conf be undefined when running Cerberus *)
let hack ~conf mode =
  let open Global_ocaml in
  let conf =
   {  exec_mode_opt=    Some (to_smt2_mode mode);
      concurrency=      false;
      error_verbosity=  Global_ocaml.QuoteStd;
      defacto=          false;
      n1570=            Some conf.instance.n1570;
    }
  in cerb_conf := fun () -> conf

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
    load_core_stdlib () >>= fun core_stdlib ->
    load_core_impl core_stdlib conf.instance.core_impl >>= fun core_impl ->
    c_frontend (conf.pipeline, conf.io) (core_stdlib, core_impl) filename
    >>= function
    | (Some cabs, Some ail, core) ->
      core_passes (conf.pipeline, conf.io) ~filename core
      >>= fun core' ->
      return (core_stdlib, core_impl, cabs, ail, core')
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

let result_of_elaboration (_, _, cabs, ail, core) =
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


let write_tmp_file content =
  try
    let tmp = Filename.temp_file "herd" ".cat" in
    let oc  = open_out tmp in
    output_string oc content;
    close_out oc;
    Debug.print 8 ("Contents written at: " ^ tmp);
    tmp
  with _ ->
    Debug.warn "Error when writing the contents in disk.";
    failwith "write_tmp_file"

let bmc ~filename ~name ~conf ~bmc_model:bmc_model ~filename () =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  Debug.print 7 ("Running BMC...");
  try
    elaborate ~conf ~filename
    >>= fun (core_std, core_lib, cabs, ail, core) ->
    Tags.set_tagDefs core.tagDefs;
    let (cat_file_opt, mem_model) =
      match bmc_model with
      | `C11 ->
        Debug.print 7 ("BMC model: C11");
        (Some "bmc/c11.cat", Bmc_globals.MemoryMode_C)
      | `RC11_Hardcoded ->
        Debug.print 7 ("BMC model: RC11 (hardcoded)");
        (None, Bmc_globals.MemoryMode_C)
      | `RC11 ->
        Debug.print 7 ("BMC model: RC11");
        (Some "bmc/rc11.cat", Bmc_globals.MemoryMode_C)
      | `Linux ->
        Debug.print 7 ("BMC model: Linux");
        (Some "bmc/linux.cat", Bmc_globals.MemoryMode_Linux)
      | `Custom content ->
        Debug.print 7 ("BMC model: Custom");
        let filename = write_tmp_file content in
        (Some filename, Bmc_globals.MemoryMode_C)
    in
    Bmc_globals.set 3 true true "main" 0 true false cat_file_opt mem_model;
    return @@ match Bmc.bmc core (Some ail) with
    | `Satisfiable (out, dots) -> `Satisfiable (Str.replace_first (Str.regexp_string filename) name out, dots)
    | `Unknown out -> `Unknown (Str.replace_first (Str.regexp_string filename) name out)
    | `Unsatisfiable (out, dots) -> `Unsatisfiable (Str.replace_first (Str.regexp_string filename) name out, dots)
  with
  | e ->
    Debug.warn ("Exception raised during execution: " ^ Printexc.to_string e);
    raise e

(* execution *)
let execute ~conf ~filename (mode: exec_mode) =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack ~conf mode;
  Debug.print 7 ("Executing in "^string_of_exec_mode mode^" mode: " ^ filename);
  try
    elaborate ~conf ~filename
    >>= fun (core_std, core_lib, cabs, ail, core) ->
    begin if conf.instance.link_libc then
      let libc = Pipeline.read_core_object (core_std, core_lib) @@ Global_ocaml.cerb_path ^ "/libc/libc.co" in
      Core_linking.link [core; libc]
    else
      return core
    end >>= fun core ->
    Tags.set_tagDefs core.tagDefs;
    let open Exhaustive_driver in
    let driver_conf = {concurrency=false; experimental_unseq=false; exec_mode=(to_smt2_mode mode); fs_dump=false; trace=false; } in
    interp_backend dummy_io core ~args:[] ~batch:`Batch ~fs:None ~driver_conf
    >>= function
    | Either.Left res ->
      return (String.concat "\n" res)
    | Either.Right res ->
      return (string_of_int res)
  with
  | e ->
    Debug.warn ("Exception raised during execution: " ^ Printexc.to_string e);
    raise e

let set_uid file =
  let fresh =
    let n = ref 0 in
    fun () -> incr n; string_of_int !n
  in
  let open Core in
  let rec set_pe (Pexpr (annots, bty, pe_)) =
    let pe_' = match pe_ with
      | PEsym s -> PEsym s
      | PEimpl impl -> PEimpl impl
      | PEval v -> PEval v
      | PEconstrained cs ->
        PEconstrained (List.mapi (fun i (m, pe) -> (m, set_pe pe)) cs)
      | PEundef (loc, undef) -> PEundef (loc, undef)
      | PEerror (err, pe) -> PEerror (err, set_pe pe)
      | PEctor (ctor, pes) -> PEctor (ctor, List.map set_pe pes)
      | PEcase (pe, cases) -> PEcase (set_pe pe,
                                      List.mapi (fun i (pat, pe) -> (pat, set_pe pe)) cases)
      | PEarray_shift (pe, cty, pes) -> PEarray_shift (set_pe pe, cty, set_pe pes)
      | PEmember_shift (pe, sym, cid) -> PEmember_shift (set_pe pe, sym, cid)
      | PEnot pe -> PEnot (set_pe pe)
      | PEop (bop, pe1, pe2) -> PEop (bop, set_pe pe1, set_pe pe2)
      | PEstruct (sym, fields) ->
          PEstruct (sym, List.mapi (fun i (cid, pe) -> (cid, set_pe pe)) fields)
      | PEunion (sym, cid, pe) -> PEunion (sym, cid, set_pe pe)
      | PEcfunction pe -> PEcfunction (set_pe pe)
      | PEmemberof (tag_sym, memb_ident, pe) -> PEmemberof (tag_sym, memb_ident, set_pe pe)
      | PEcall (name, pes) -> PEcall (name, List.map set_pe pes)
      | PElet (pat, pe1, pe2) -> PElet (pat, set_pe pe1, set_pe pe2)
      | PEif (pe1, pe2, pe3) -> PEif (set_pe pe1, set_pe pe2, set_pe pe3)
      | PEis_scalar pe -> PEis_scalar (set_pe pe)
      | PEis_integer pe -> PEis_integer (set_pe pe)
      | PEis_signed pe -> PEis_signed (set_pe pe)
      | PEis_unsigned pe -> PEis_unsigned (set_pe pe)
      | PEbmc_assume pe -> PEbmc_assume (set_pe pe)
      | PEare_compatible (pe1, pe2) -> PEare_compatible (set_pe pe1, set_pe pe2)
    in Pexpr (Annot.Auid (fresh ()) :: annots, bty, pe_')
  in
  let rec set_e (Expr (annots, e_)) =
    let e_' = match e_ with
      | Epure pe -> Epure (set_pe pe)
      | Ememop (memop, pes) -> Ememop (memop, List.map set_pe pes)
      | Eaction pact -> Eaction pact
      | Ecase (pe, cases) ->
        Ecase (set_pe pe, List.mapi (fun i (pat, e) -> (pat, set_e e)) cases)
      | Elet (pat, pe, e) -> Elet (pat, set_pe pe, set_e e)
      | Eif (pe, e1, e2) -> Eif (set_pe pe, set_e e1, set_e e2)
      | Eskip -> Eskip
      | Eccall (x, pe1, pe2, args) -> Eccall (x, set_pe pe1, set_pe pe2, List.map set_pe args)
      | Eproc (x, name, args) -> Eproc (x, name, List.map set_pe args)
      | Eunseq es -> Eunseq (List.map set_e es)
      | Ewseq (pat, e1, e2) -> Ewseq (pat, set_e e1, set_e e2)
      | Esseq (pat, e1, e2) -> Esseq (pat, set_e e1, set_e e2)
      | Easeq (bty, act, pact) -> Easeq (bty, act, pact)
      | Eindet (n, e) -> Eindet (n, set_e e)
      | Ebound (n, e) -> Ebound (n, set_e e)
      | End es -> End (List.map set_e es)
      | Esave (lab_bty, args, e) ->
        Esave (lab_bty,
               List.mapi (fun i (s, (bty, pe)) -> (s, (bty, set_pe pe))) args,
               set_e e)
      | Erun (x, lab, pes) -> Erun (x, lab, List.map set_pe pes)
      | Epar es -> Epar (List.map set_e es)
      | Ewait thid -> Ewait thid
    in Expr (Annot.Auid (fresh ()) :: annots, e_')
  in
  let set_fun fname = function
    | Proc (loc, bty, args, e) ->
      Proc (loc, bty, args, set_e e)
    | f -> f
  in
  let set_globs (gname, glb) =
    (gname, match glb with
      | GlobalDef (bty, e) ->
        GlobalDef (bty, set_e e)
      | GlobalDecl bty ->
        GlobalDecl bty
    )
  in
  { main=    file.main;
    tagDefs= file.tagDefs;
    stdlib=  file.stdlib;
    impl=    file.impl;
    globs=   List.map set_globs file.globs;
    funs=    Pmap.mapi set_fun file.funs;
    extern=  file.extern;
    funinfo= file.funinfo;
  }

(* WARN: fresh new ids *)
let last_node_id : int ref = ref 0
let new_id () = incr last_node_id; !last_node_id

let encode s = Marshal.to_string s [Marshal.Closures]
let decode s = Marshal.from_string s 0

let get_state_details st =
  let string_of_env env =
    let f e = Pmap.fold (fun (s:Symbol.sym) (v:Core.value) acc ->
        Pp_symbol.to_string_pretty s ^ "= " ^ String_core.string_of_value v ^ "\n" ^ acc
      ) e "" in
    List.fold_left (fun acc e -> acc ^ f e) "" env
  in
  (* TODO: this is a bit naive *)
  let stdout = String.concat "" @@ Dlist.toList (st.Driver.core_state.Core_run.io.Core_run.stdout) in
  let stderr = String.concat "" @@ Dlist.toList (st.Driver.core_state.Core_run.io.Core_run.stderr) in
  match st.Driver.core_state.Core_run.thread_states with
  | (_, (_, ts))::_ ->
    let arena = Pp_utils.to_plain_pretty_string @@ Pp_core.Basic.pp_expr ts.arena in
    let Core.Expr (arena_annots, _) = ts.arena in
    let maybe_uid = Annot.get_uid arena_annots in
    let loc = Option.case id (fun _ -> ts.Core_run.current_loc) @@ Annot.get_loc arena_annots in
    (loc, maybe_uid, arena, string_of_env ts.env, stdout, stderr)
  | _ ->
    (Location_ocaml.unknown, None, "", "", stdout, stderr)

let get_file_hash core =
  match core.Core.main with
  | Some (Symbol.Symbol (hash, _, _)) -> hash
  | None -> failwith "get_file_hash"

(* NOTE: Web doesn't depend on Driver *)
let json_of_step_kind step =
  let open Driver in
  match step with
  | SK_action_request str ->
    `Assoc [("kind", `String "action request");
            ("debug", `String str)]
  | SK_memop_request ->
    `Assoc [("kind", `String "memop request")]
  | SK_tau str ->
    `Assoc [("kind", `String "tau");
            ("debug", `String str)]
  | SK_eval str ->
    `Assoc [("kind", `String "eval");
            ("debug", `String str)]
  | SK_done ->
    `Assoc [("kind", `String "done")]
  | SK_misc strs ->
    `Assoc [("kind", `String "action request");
            ("debug", `List (List.map (fun str -> `String str) strs))]

let create_node node_info st next_state =
  let node_id = new_id () in
  let memory = Ocaml_mem.serialise_mem_state (get_file_hash st.Driver.core_file) st.Driver.layout_state in
  let (c_loc, core_uid, arena, env, stdout, stderr) = get_state_details st in
  { node_id; node_info; memory; c_loc; core_uid; arena; env; next_state; stdout; stderr }

let multiple_steps step_state (m, st) =
  let module CS = (val Ocaml_mem.cs_module) in
  let (>>=) = CS.bind in
  let create_branch node_info st (ns, es, previousNode) =
    let n = create_node node_info st None in
    let ns' = n :: ns in
    let es' = Edge (previousNode, n.node_id) :: es in
    (ns', es', n.node_id)
  in
  let create_leafs st ms (ns, es, previousNode) =
    let (is, ns') = List.fold_left (fun (is, ns) (dr_info, m) ->
        let n = create_node (`Step (json_of_step_kind dr_info)) st (Some (encode (m, st))) in
        (n.node_id::is, n::ns)
      ) ([], ns) ms in
    let es' = (List.map (fun n -> Edge (previousNode, n)) is) @ es in
    (ns', es', previousNode)
  in
  let check step_state st f = function
    | `UNSAT -> CS.return (Some "unsat", create_branch `Unsat st step_state)
    | `SAT -> CS.return @@ f ()
  in
  let runCS step_state st f = CS.runEff (CS.check_sat >>= check step_state st f) in
  let withCS str cs st f =
    CS.runEff (CS.with_constraints str cs (CS.check_sat >>= check step_state st f))
  in
  try
    let open Nondeterminism in
    let one_step step_state : (_, Driver.step_kind, _, _, _) Nondeterminism.nd_action * _ -> _ = function
      | (NDactive a, st') ->
        runCS step_state st' begin fun () ->
          let str_v = String_core.string_of_value a.Driver.dres_core_value in
          let res =
            "Defined {value: \"" ^ str_v ^ "\", stdout: \""
            ^ String.escaped a.Driver.dres_stdout
            ^ "\", blocked: \""
            ^ if a.Driver.dres_blocked then "true\"}" else "false\"}"
          in
          (Some res, create_branch (`Done str_v) st' step_state)
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
          string_of_driver_error dr_err
        in (Some reason, create_branch (`Error (loc, reason)) st' step_state)
      | (NDbranch (str, cs, m1, m2), st') ->
        withCS str cs st' begin fun () ->
          create_branch `Branch st' step_state
          |> create_leafs st' [(SK_misc ["1"], m1); (SK_misc ["2"], m2)]
          |> fun res -> (None, res)
        end
      | (NDguard (str, cs, m), st') ->
        withCS str cs st' begin fun () ->
          create_leafs st' [(str, m)] step_state
          |> fun res -> (None, res)
        end
        |> fun s -> Debug.print 0 "finish guard"; s
      | (NDnd (_, ms), st') ->
        (None, create_leafs st' ms step_state)
      | (NDstep (_, ms), st') ->
        (None, create_leafs st' ms step_state)
    in
    let is_user_state st =
      (* NOTE: it checks that the first thread core expression in the
       * arena has an identifier, which means it's user code *)
      match st.Driver.core_state.Core_run.thread_states with
      | (_, (_, ts))::_ ->
        let Core.Expr (arena_annots, _) = ts.arena in
        begin match Annot.get_uid arena_annots with
          | None -> false
          | Some _ -> true
        end
      | _ -> false
    in
    let rec aux step_state (ND m) st =
      let is_user_state = is_user_state st in
      match m st with
      | (NDstep (_, [(step_kind, m')]), st') when is_user_state ->
        let step_state' = create_branch (`Step (json_of_step_kind step_kind)) st' step_state in
        aux step_state' m' st'
      | (NDstep (_, (_, m')::_), st') when not is_user_state ->
        (* if not user state, choose the first one and continue executing *)
        aux step_state m' st'
      | act ->
        one_step step_state act
    in aux step_state m st
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
    elaborate ~conf ~filename >>= fun (core_std, core_lib, _, _, core) ->
    let core     = set_uid core in
    let ranges   = create_expr_range_list core in
    begin if conf.instance.link_libc then
      let libc = Pipeline.read_core_object (core_std, core_lib) @@ Global_ocaml.cerb_path ^ "/libc/libc.co" in
      Core_linking.link [core; libc]
    else
      return core
    end >>= fun core ->
    Tags.set_tagDefs core.tagDefs;
    let core'    = Core_run_aux.convert_file core in
    let st0      = Driver.initial_driver_state core' Sibylfs.fs_initial_state (* TODO *) in
    let (m, st)  = (Driver.drive false false core' [], st0) in
    last_node_id := 0;
    let node_info= `Init in
    let memory = Ocaml_mem.serialise_mem_state (get_file_hash core) st.Driver.layout_state in
    let (c_loc, core_uid, arena, env, stdout, stderr) = get_state_details st in
    let next_state = Some (encode (m, st)) in
    let n = { node_id= 0; node_info; memory; c_loc; core_uid; arena; env; next_state; stdout; stderr } in
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
    | `BMC (conf, bmc_model, filename, name) ->
      try
        bmc ~filename ~name ~conf:(add_bmc_macro ~bmc_model @@ setup conf) ~bmc_model ~filename ()
        |> respond filename name (fun res -> BMC res)
      with Failure msg ->
        Failure (Str.replace_first (Str.regexp_string filename) name msg)
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
