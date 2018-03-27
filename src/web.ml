open Lwt
open Cohttp_lwt_unix

open Json

open Instance_manager

(* TODO: change this HACK TO INCLUDE Z3 *)
let () =
  Z3.enable_trace "";
  let _ = Lem_relation.isIrreflexive in
  let _ = Lem_show_extra.stringFromSet in
  let _ = Xstring.explode in
  ();;

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

let diff xs ys = List.filter (fun x -> not (List.mem x ys)) xs

let concatMap f xs = List.concat (List.map f xs)

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
  PPrint.ToBuffer.pretty 1.0 80 buf d;
  Buffer.contents buf

let encode s = B64.encode (Marshal.to_string s [Marshal.Closures])
let decode s = Marshal.from_string (B64.decode s) 0

(* Load Concrete and Symbolic instances of Cerberus *)

let load_instance fname =
  let fname = Dynlink.adapt_filename fname in
  if Sys.file_exists fname then
    try Dynlink.loadfile fname
    with
    | Dynlink.Error err ->
       Debug.error ("Loading memory model: " ^ Dynlink.error_message err)
  else Debug.error "File does not exists"

let () =
  Prelude.mem_switch := Prelude.MemConcrete;
  load_instance "./_build/src/memmodel.cma";
  Prelude.mem_switch := Prelude.MemSymbolic;
  load_instance "./_build/src/memmodel.cma";
  set_model "Concrete" ;;

(* Incoming messages *)

type action =
  | NoAction
  | Elaborate
  | RunRandom
  | RunExhaustive
  | Step

type state = (unit * unit)
type mem = unit

(* NOTE: the execution tree is a pair of node and edges lists
 * this encoding works better in the client side (js libraries)
 * than functional AST for trees *)

type node_id = int
type node =
  | Branch of node_id * string * mem * Location_ocaml.t option
  | Leaf of node_id * string * state
type edge =
  | Edge of node_id * node_id (* from -> to *)

(*
type node = string * state option (* label and maybe a state *)
type edge = node_id * node_id (* from -> to *)
   *)
type exec_tree = node list * edge list


(* get location of first thread *)

let get_location st = None
  (* TODO:
  match st.Driver.core_state.Core_run.thread_states with
  | (_, (_, ts))::_ -> Some ts.current_loc
  | _ -> None
*)

let json_of_exec_tree ((ns, es) : exec_tree) =
  let json_of_node = function
    | Branch (id, lab, mem, loc) ->
      `Assoc [("id", `Int id);
              ("label", `String lab);
              ("mem", `Null); (*TODO: Ocaml_mem.serialise_mem_state mem); *)
              ("loc", Json.of_option Json.of_location loc)]
    | Leaf (id, lab, st) ->
      `Assoc [("id", `Int id);
              ("label", `String lab);
              ("state", `String (encode st));
              ("loc", `Null); (*TODO: json_of_location (get_location (snd st)));*)
              ("group", `String "leaf")]
  in
  let json_of_edge = function
    | Edge (p, c) -> `Assoc [("from", `Int p);
                               ("to", `Int c)]
  in
  let nodes = `List (List.map json_of_node ns) in
  let edges = `List (List.map json_of_edge es) in
  `Assoc [("nodes", nodes); ("edges", edges)]

type incoming_msg =
  { action:  action;
    source:  string;
    model:   string;
    rewrite: bool;
    interactive: (state * node_id) option; (* active node *)
  }

let parse_incoming_json msg =
  let empty = { action=      NoAction;
                source=      "";
                model=       "Concrete";
                rewrite=     true;
                interactive= None;
              }
  in
  let parse_option f = function
    | `Null      -> None
    | `String "" -> None
    | x          -> Some (f x)
  in
  let action_from_string = function
    | "Elaborate"  -> Elaborate
    | "Random"     -> RunRandom
    | "Exhaustive" -> RunExhaustive
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
  let parse_interactive = function
    | `Assoc [("state", `String st); ("active", `Int i)] -> (decode st, i)
    | _ -> failwith "expecting state * integer"
  in
  let parse_assoc msg (k, v) =
    match k with
    | "action"  -> { msg with action= action_from_string (parse_string v) }
    | "source"  -> { msg with source= parse_string v }
    | "rewrite" -> { msg with rewrite= parse_bool v }
    | "model"   -> { msg with model= parse_string v }
    | "interactive" -> { msg with interactive=parse_option parse_interactive v }
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

let json_of_exec_tree t = failwith ""

let json_of_result = function
  | Elaboration r ->
    `Assoc [
      ("status", `String "elaboration");
      ("pp", `Assoc [
          ("cabs", Json.of_opt_string r.pp.cabs);
          ("ail",  Json.of_opt_string r.pp.ail);
          ("core", Json.of_opt_string r.pp.core);
        ]);
      ("ast", `Assoc [
          ("cabs", Json.of_opt_string r.ast.cabs);
          ("ail",  Json.of_opt_string r.ast.ail);
          ("core", Json.of_opt_string r.ast.core);
        ]);
      ("locs", r.locs);
      ("result", `String "");
      ("console", `String "");
    ]
  | Execution str ->
    `Assoc [
      ("status", `String "execution");
      ("result", `String str);
    ]
  | Interaction (res, t) ->
    `Assoc [
      ("status", `String "stepping");
      ("result", Json.of_opt_string res);
      ("interactive", `Assoc [
          ("steps", json_of_exec_tree t);
        ]);
    ]
  | Failure err ->
    `Assoc [
      ("status", `String "failure");
      ("console", `String "");
    ]

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

let respond_json json =
  let headers = Cohttp.Header.of_list [("content-type", "application/json")] in
  (Server.respond_string ~flush:true ~headers) `OK (Yojson.to_string json) ()

(* Cerberus actions *)

let cerberus content =
  let msg       = parse_incoming_json (Yojson.Basic.from_string content) in
  let filename  = write_tmp_file msg.source in
  let conf      = { Instance_manager.rewrite= msg.rewrite; } in
  let failure s = respond_json @@ json_of_result @@ Failure s in
  Instance_manager.set_model msg.model;
  match msg.action with
  | NoAction   ->
    failure "no action"
  | Elaborate  ->
    elaborate conf filename
    |> json_of_result
    |> respond_json
  | RunRandom     ->
    execute conf filename Random
    |> json_of_result
    |> respond_json
  | RunExhaustive ->
    execute conf filename Exhaustive
    |> json_of_result
    |> respond_json
  | _ -> failwith "unknown action"
  (*
  | Step ->
    execute_step msg ~conf ~filename
    |> respond_json
*)

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

let post ~docroot uri path content =
  let try_with () =
    Debug.print 9 ("POST " ^ path);
    Debug.print 8 ("POST data " ^ content);
    match path with
    | "/cerberus" -> cerberus content
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

let request ~docroot conn req body =
  let uri  = Request.uri req in
  let meth = Request.meth req in
  let path = Uri.path uri in
  match meth with
  | `HEAD -> get ~docroot uri path >|= fun (res, _) -> (res, `Empty)
  | `GET  -> get ~docroot uri path
  | `POST -> Cohttp_lwt__Body.to_string body >>= post ~docroot uri path
  | _     -> not_allowed meth path

let setup cerb_debug_level debug_level impl cpp_cmd port docroot =
  try
    Debug_ocaml.debug_level := cerb_debug_level;
    Debug.level := debug_level;
    Debug.print 1 ("Starting server with public folder: " ^ docroot
                   ^ " in port: " ^ string_of_int port);
    Server.make ~callback: (request ~docroot) ()
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

(* TODO:*)
let cerb_path = ""
let cpp_cmd =
  let default = "cc -E -C -traditional-cpp -nostdinc -undef -D__cerb__ -I "
                ^ cerb_path ^ "/include/c/libc -I "
                ^ cerb_path ^ "/include/c/posix" in
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

