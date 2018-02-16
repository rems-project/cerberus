open Lwt
open Cohttp_lwt_unix

open Core_json

(* Debugging *)

module Debug =
struct

  let level = ref 0

  let print n msg =
    if !level >= n then Printf.printf "[%d]: %s\n%!" n msg

  let warn msg  =
    if !level > 0 then Printf.printf "\x1b[33m[ WARN  ]: %s\n\x1b[0m%!" msg

  let error msg =
    Printf.printf "\x1b[31m[ ERROR ]: %s\n\x1b[0m%!" msg

  let warn_exception msg e =
    warn (msg ^ " " ^ Printexc.to_string e)

  let error_exception msg e =
    error (msg ^ " " ^ Printexc.to_string e)

end

(* Util *)

let timeout d f =
  let try_with () =
    Lwt.pick [
      Lwt_unix.timeout d;
      f >|= fun v -> Some v;
    ]
  in catch try_with (fun _ -> Lwt.return None)

let write_tmp_file content =
  try
    let tmp = Filename.temp_file "source" ".c" in
    let oc  = open_out tmp in
    output_string oc content;
    close_out oc;
    Debug.print 8 ("Contents written at: " ^ tmp);
    tmp
  with _ ->
    Debug.warn "Error when writing the contents in disk.";
    failwith "write_tmp_file"

let string_of_doc d =
  let buf = Buffer.create 1024 in
  PPrint.ToBuffer.pretty 1.0 150 buf d;
  Buffer.contents buf

let encode s = B64.encode (Marshal.to_string s [Marshal.Closures])
let decode s = Marshal.from_string (B64.decode s) 0

let option_case b f = function
  | None -> b
  | Some x -> f x

let option_string f s =
  if s = "" then None else Some (f s)

(* Initialise pipeline *)

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

let setup_cerb_conf cerb_debug_level cpp_cmd impl_filename =
  let open Pipeline in
  let core_stdlib = load_core_stdlib ()
  in {
    debug_level=         cerb_debug_level;
    pprints=             [];
    astprints=           [];
    ppflags=             [];
    typecheck_core=      false;
    rewrite_core=        true;
    sequentialise_core=  true;
    cpp_cmd=             cpp_cmd;
    core_stdlib=         core_stdlib;
    core_impl=           load_core_impl core_stdlib impl_filename;
  }

(* Incoming messages *)

type action =
  | NoAction
  | Elaborate
  | Random
  | Exhaustive
  | Step

type state = ((Driver.driver_result, Driver.driver_error,
               Ocaml_mem.integer_value Mem_common.mem_constraint,
               Driver.driver_state) Nondeterminism.ndM
             * Driver.driver_state)

type incoming_msg =
  { action:  action;
    source:  string;
    rewrite: bool;
    state:   state option;
    steps:   string list;  (* steps taken *)
  }

let parse_incoming_json msg =
  let empty = { action=  NoAction;
                source=  "";
                state=   None;
                rewrite= true;
                steps=   [];
              }
  in
  let action_from_string = function
    | "Elaborate"  -> Elaborate
    | "Random"     -> Random
    | "Exhaustive" -> Exhaustive
    | "Step"       -> Step
    | s -> failwith ("unknown action " ^ s)
  in
  let parse_string = function
    | `String s -> s
    | _ -> failwith "expecting a string"
  in
  let parse_bool = function
    | `Bool b -> b
    | _ -> failwith "expecting a bool"
  in
  let parse_list f = function
    | `List xs -> List.map f xs
    | _ -> failwith "expecting a list"
  in
  let parse_assoc msg (k, v) =
    match k with
    | "action"  -> { msg with action= action_from_string (parse_string v) }
    | "source"  -> { msg with source= parse_string v }
    | "rewrite" -> { msg with rewrite= parse_bool v }
    | "state"   -> { msg with state= option_string decode (parse_string v) }
    | "steps"   -> { msg with steps= parse_list parse_string v }
    | key ->
      Debug.warn ("unknown value " ^ key ^ " when parsing incoming message");
      msg (* ignore unknown key *)
  in
  let rec parse msg = function
    | `Assoc xs -> List.fold_left parse_assoc msg xs
    | `List xs -> List.fold_left parse msg xs
    | _ -> failwith "wrong message format"
  in
  parse empty msg

(* Outgoing messages *)

let json_of_elaboration (cabs, ail, _, core) =
  let elim_paragraph_sym = Str.global_replace (Str.regexp_string "§") "" in
  let json_of_doc d = `String (elim_paragraph_sym (string_of_doc d)) in
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
  in
  `Assoc [
    ("pp", `Assoc [
        ("cabs", `Null);
        ("ail",  json_of_doc (Pp_ail.pp_program ail));
        ("core", `String core)]);
    ("ast", `Assoc [
        ("cabs", json_of_doc (Pp_cabs.pp_translation_unit false false cabs));
        ("ail",  json_of_doc (Pp_ail_ast.pp_program ail));
        ("core", `Null)]);
    ("locs", locs);
  ]

let json_of_execution str =
  `Assoc [
    ("console", `String str);
  ]

let json_of_step (steps, str, m, st) =
  `Assoc [
    ("state",   `String (encode (m, st)));
    ("mem",     Ocaml_mem.serialise_mem_state st.Driver.layout_state);
    ("steps",   `List (List.map (fun s -> `String s) (str::steps)));
  ]

let json_of_fail msg =
  `Assoc [("stderr",  `String msg)]


(* Server default responses *)

let forbidden path =
  let body = Printf.sprintf
      "<html><body>\
       <h2>Forbidden</h2>\
       <p><b>%s</b> is forbidden</p>\
       <hr/>\
       </body></html>"
      path in
  Debug.warn ("Trying to access path: " ^ path);
  Server.respond_string ~status:`Forbidden ~body ()

let not_allowed meth path =
  let body = Printf.sprintf
      "<html><body>\
       <h2>Method Not Allowed</h2>\
       <p><b>%s</b> is not an allowed method on <b>%s</b>\
       <hr />\
       </body></html>"
      (Cohttp.Code.string_of_method meth) path
  in Server.respond_string ~status:`Method_not_allowed ~body ()

(* TESTING *)


let init_step (sym_supply: Symbol.sym UniqueId.supply) (file: 'a Core.file) args =
  Random.self_init ();
  
  (* changing the annotations type from unit to core_run_annotation *)
  let file = Core_run_aux.convert_file file in
  let initial_dr_st = Driver.initial_driver_state sym_supply file in
  
  (* computing the value (or values if exhaustive) *)
  (Driver.drive false false sym_supply file args, initial_dr_st)



(* Cerberus actions *)

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
    exec_mode_opt=      Some mode;
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


let respond_json json =
  let headers = Cohttp.Header.of_list [("content-type", "application/json")] in
  (Server.respond_string ~flush:true ~headers) `OK (Yojson.to_string json) ()

let failure s = respond_json (json_of_fail s)

let respond f = function
  | Exception.Result r ->
    respond_json (f r)
  | Exception.Exception err ->
    failure (Pp_errors.to_string err)

let elaborate ~conf ~filename =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  Debug.print 2 ("Elaborating: " ^ filename);
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
  | e -> Debug.warn_exception "Exception raised during elaboration." e; raise e

let execute ~conf ~filename (mode: Smt2.execution_mode) =
  let return = Exception.except_return in
  let (>>=)  = Exception.except_bind in
  hack (fst conf) mode;
  let string_of_mode = function
    | Smt2.Random -> "random"
    | Smt2.Exhaustive -> "exhaustive"
  in
  Debug.print 2 ("Executing in " ^ string_of_mode mode ^ " mode: " ^ filename);
  try
    elaborate ~conf ~filename
    >>= fun (cabs, ail, sym_suppl, core) ->
    Pipeline.interp_backend dummy_io sym_suppl core [] true false false mode
    >>= function
    | Either.Left res ->
      return (String.concat "\n" res)
    | Either.Right res ->
      return (string_of_int res)
  with
  | e -> Debug.warn_exception "Exception raised during execution." e; raise e


let execute_step (msg : incoming_msg) ~conf ~filename =
  hack (fst conf) Smt2.Random;
  let step_init () =
    let return = Exception.except_return in
    let (>>=)  = Exception.except_bind in
    elaborate ~conf ~filename
    >>= fun (_, _, sym_suppl, core) ->
    let core' = Core_run_aux.convert_file core in
    let st0   = Driver.initial_driver_state sym_suppl core' in
    return (Driver.drive false false sym_suppl core' [], st0)
  in
  try
    match msg.state with
    | None ->
      begin match step_init () with
        | Exception.Result (m, st) ->
          json_of_step (msg.steps, "init", m, st)
        | Exception.Exception err ->
          json_of_fail (Pp_errors.to_string err)
      end
    | Some (ND m, st) ->
      match m st with
      | (NDactive a, st') ->
        let str_v = String_core.string_of_value a.Driver.dres_core_value in
        let res =
          "Defined {value: \"" ^ str_v ^ "\", stdout: \""
          ^ String.escaped a.Driver.dres_stdout
          ^ "\", blocked: \""
          ^ if a.Driver.dres_blocked then "true\"}" else "false\"}"
        in
        json_of_execution res
      | (NDkilled r, st') ->
        json_of_execution ("killed")
      | (NDbranch (str, _, m1, m2), st') ->
        json_of_step (msg.steps, str, m2, st')
      | (NDguard (str, _, m), st') ->
        json_of_step (msg.steps, str, m, st')
      | (NDnd (str, (_,m)::ms), st') ->
        json_of_step (msg.steps, str, m, st')
      | (NDstep ((str,m)::ms), st') ->
        json_of_step (msg.steps, str, m, st')
      | _ -> failwith ""
  with
  | e -> Debug.warn_exception "Exception raised during execution." e; raise e


let update_conf (conf, io_helpers) msg =
  let new_conf = { conf with Pipeline.rewrite_core= msg.rewrite }
  in (new_conf, io_helpers)

let cerberus ~conf content =
  let msg      = parse_incoming_json (Yojson.Basic.from_string content) in
  let filename = write_tmp_file msg.source in
  let conf     = update_conf conf msg in
  match msg.action with
  | NoAction   ->
    failure "no action"
  | Elaborate  ->
    elaborate ~conf ~filename
    |> respond json_of_elaboration
  | Random     ->
    execute ~conf ~filename Smt2.Random
    |> respond json_of_execution
  | Exhaustive ->
    execute ~conf ~filename Smt2.Exhaustive
    |> respond json_of_execution
  | Step ->
    execute_step msg ~conf ~filename
    |> respond_json

(* GET and POST *)

let get ~docroot uri path =
  let is_regular filename =
    match Unix.((stat filename).st_kind) with
    | Unix.S_REG -> true
    | _ -> false
  in
  let get_local_file () =
    let filename = Server.resolve_local_file ~docroot ~uri in
    if is_regular filename then Server.respond_file filename ()
    else forbidden path
  in
  let try_with () =
    Debug.print 9 ("GET " ^ path);
    match path with
    | "/" -> Server.respond_file "public/index.html" ()
    | _   -> get_local_file ()
  in catch try_with begin fun e ->
    Debug.error_exception "GET" e;
    forbidden path
  end

let post ~docroot ~conf uri path content =
  let try_with () =
    Debug.print 9 ("POST " ^ path);
    Debug.print 8 ("POST data " ^ content);
    match path with
    | "/cerberus" -> cerberus ~conf content
    | _ ->
      (* Ignore POST, fallback to GET *)
      Debug.warn ("Unknown post action " ^ path);
      Debug.warn ("Fallback to GET");
      get ~docroot uri path
  in catch try_with begin fun e ->
    Debug.error_exception "POST" e;
    forbidden path
  end

(* Main *)

let request ~docroot ~conf conn req body =
  let uri  = Request.uri req in
  let meth = Request.meth req in
  let path = Uri.path uri in
  match meth with
  | `HEAD -> get ~docroot uri path >|= fun (res, _) -> (res, `Empty)
  | `GET  -> get ~docroot uri path
  | `POST -> Cohttp_lwt__Body.to_string body >>= post ~docroot ~conf uri path
  | _     -> not_allowed meth path

let setup cerb_debug_level debug_level impl cpp_cmd port docroot =
  try
    let conf = (setup_cerb_conf cerb_debug_level cpp_cmd impl, dummy_io) in
    Debug_ocaml.debug_level := cerb_debug_level;
    Debug.level := debug_level;
    Debug.print 1 ("Starting server with public folder: " ^ docroot
                   ^ " in port: " ^ string_of_int port);
    Server.make ~callback: (request ~docroot ~conf) ()
    |> Server.create ~mode:(`TCP (`Port port))
    |> Lwt_main.run
  with
  | e ->
    Debug.error_exception "Fatal error:" e;
    Debug.error ("Check port " ^ string_of_int port ^ " access right")

(* Arguments *)

open Cmdliner

let cerb_debug_level =
  let doc = "Set the debug message level for Cerberus to $(docv) \
             (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["cerb-debug"] ~docv:"N" ~doc)

let debug_level =
  let doc = "Set the debug message level for the server to $(docv) \
             (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let impl =
  let doc = "Set the C implementation file (to be found in CERB_COREPATH/impls \
             and excluding the .impl suffix)." in
  Arg.(value & opt string "gcc_4.9.0_x86_64-apple-darwin10.8.0"
       & info ["impl"] ~docv:"IMPL" ~doc)

let cpp_cmd =
  let default = "cc -E -C -traditional-cpp -nostdinc -undef -D__cerb__ -I "
                ^ Pipeline.cerb_path ^ "/include/c/libc -I "
                ^ Pipeline.cerb_path ^ "/include/c/posix" in
  let doc = "Command to call for the C preprocessing." in
  Arg.(value & opt string default & info ["cpp"] ~docv:"CMD" ~doc)

let docroot =
  let doc = "Set public (document root) files locations." in
  Arg.(value & pos 0 string "./public/" & info [] ~docv:"PUBLIC" ~doc)

let port =
  let doc = "Set TCP port." in
  Arg.(value & opt int 8080 & info ["p"; "port"] ~docv:"PORT" ~doc)

let () =
  let server = Term.(pure setup $ cerb_debug_level $ debug_level
                     $ impl $ cpp_cmd $ port $ docroot) in
  let info = Term.info "web" ~doc:"Web server frontend for Cerberus." in
  match Term.eval (server, info) with
  | `Error _ -> exit 1;
  | `Ok _
  | `Version
  | `Help -> exit 0
