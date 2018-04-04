open Lwt
open Cohttp_lwt_unix
open Instance_api
open Json
open Util

(* Misc *)

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

(* Incoming messages *)

type action =
  [ `Nop
  | `Elaborate
  | `Random
  | `Exhaustive
  | `Step ]

let string_of_action = function
  | `Nop        -> "Nop"
  | `Elaborate  -> "Elaborate"
  | `Random     -> "Random"
  | `Exhaustive -> "Exhaustive"
  | `Step       -> "Step"

type incoming_msg =
  { action:  action;
    source:  string;
    model:   string;
    rewrite: bool;
    interactive: active_node option;
  }

let parse_incoming_json msg =
  let empty = { action=      `Nop;
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
    | "Elaborate"  -> `Elaborate
    | "Random"     -> `Random
    | "Exhaustive" -> `Exhaustive
    | "Step"       -> `Step
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
    | `Assoc [("lastId",  `Int n);
              ("state",   `String state);
              ("active",  `Int i);
              ("tagDefs", `String tagDefs);
             ] -> (n, B64.decode state, i, B64.decode tagDefs)
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

let json_of_exec_tree ((ns, es) : exec_tree) =
  let get_location _ = `Null in
  let json_of_node = function
    | Branch (id, lab, mem, loc) ->
      `Assoc [("id", `Int id);
              ("label", `String lab);
              ("mem", mem); (* TODO *)
              ("loc", Json.of_option Json.of_location loc)]
    | Leaf (id, lab, st) ->
      `Assoc [("id", `Int id);
              ("label", `String lab);
              ("state", `String (B64.encode st));
              ("loc", (get_location st)); (* TODO *)
              ("group", `String "leaf")]
  in
  let json_of_edge = function
    | Edge (p, c) -> `Assoc [("from", `Int p);
                               ("to", `Int c)]
  in
  let nodes = `List (List.map json_of_node ns) in
  let edges = `List (List.map json_of_edge es) in
  `Assoc [("nodes", nodes); ("edges", edges)]


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
      ("console", `String "");
      ("result", `String "");
    ]
  | Execution str ->
    `Assoc [
      ("status", `String "execution");
      ("console", `String "");
      ("result", `String str);
    ]
  | Interaction (res, tags, t) ->
    `Assoc [
      ("status", `String "stepping");
      ("result", Json.of_opt_string res);
      ("tagDefs", Json.of_option (fun s -> `String (B64.encode s)) tags);
      ("interactive", `Assoc [
          ("steps", json_of_exec_tree t);
        ]);
    ]
  | Failure err ->
    `Assoc [
      ("status", `String "failure");
      ("console", `String err);
      ("result", `String "");
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

let cerberus ~conf content =
  let msg       = parse_incoming_json (Yojson.Basic.from_string content) in
  let filename  = write_tmp_file msg.source in
  let conf      = { conf with rewrite_core= msg.rewrite; } in
  let timeout   = float_of_int conf.timeout in
  let request req : result Lwt.t =
    let instance = "./cerb." ^ String.lowercase_ascii msg.model in
    let cmd = (instance, [| instance; "-d" ^ string_of_int !Debug.level |]) in
    let proc = Lwt_process.open_process ~timeout cmd in
    Lwt_io.write_value proc#stdin ~flags:[Marshal.Closures] req >>= fun () ->
    Lwt_io.close proc#stdin >>= fun () ->
    Lwt_io.read_value proc#stdout
  in
  let do_action = function
    | `Nop   -> return @@ Failure "no action"
    | `Elaborate  -> request @@ `Elaborate (conf, filename)
    | `Random -> request @@ `Execute (conf, filename, Random)
    | `Exhaustive -> request @@ `Execute (conf, filename, Exhaustive)
    | `Step -> request @@ `Step (conf, filename, msg.interactive)
  in
  Debug.print 7 ("Executing action " ^ string_of_action msg.action);
  do_action msg.action >>= respond_json % json_of_result

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

let setup cerb_debug_level debug_level timeout core_impl cpp_cmd port docroot =
  try
    Debug.level := debug_level;
    let conf = { rewrite_core = false; cpp_cmd; core_impl;
                 cerb_debug_level; timeout; tagDefs = "" } in
    Debug.print 1 ("Starting server with public folder: " ^ docroot
                   ^ " in port: " ^ string_of_int port);
    Server.make ~callback: (request ~docroot ~conf) ()
    |> Server.create ~mode:(`TCP (`Port port))
    |> Lwt_main.run
  with
  | e ->
    Debug.error_exception "Fatal error:" e;
    Debug.error ("Check port " ^ string_of_int port ^ " access right")

(* The path to where Cerberus is installed *)
let cerb_path =
    try
      Sys.getenv "CERB_PATH"
    with Not_found ->
      Debug.error "expecting the environment variable CERB_PATH \
                   set to point to the location cerberus.";
      exit 1

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
                ^ cerb_path ^ "/include/c/libc -I "
                ^ cerb_path ^ "/include/c/posix" in
  let doc = "Command to call for the C preprocessing." in
  Arg.(value & opt string default & info ["cpp"] ~docv:"CMD" ~doc)

let timeout =
  let doc = "Instance execution timeout in seconds." in
  Arg.(value & opt int 45 & info ["t"; "timeout"] ~docv:"TIMEOUT" ~doc)

let docroot =
  let doc = "Set public (document root) files locations." in
  Arg.(value & pos 0 string "./public/" & info [] ~docv:"PUBLIC" ~doc)

let port =
  let doc = "Set TCP port." in
  Arg.(value & opt int 8080 & info ["p"; "port"] ~docv:"PORT" ~doc)

let () =
  let server = Term.(pure setup $ cerb_debug_level $ debug_level $ timeout
                     $ impl $ cpp_cmd $ port $ docroot) in
  let info = Term.info "web" ~doc:"Web server frontend for Cerberus." in
  match Term.eval (server, info) with
  | `Error _ -> exit 1;
  | `Ok _
  | `Version
  | `Help -> exit 0
