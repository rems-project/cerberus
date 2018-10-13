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
    sequentialise: bool;
    interactive: active_node option;
    ui_switches: string list;
  }

let parse_incoming_msg content =
  let empty = { action=         `Nop;
                source=         "";
                model=          "Concrete";
                rewrite=        false;
                sequentialise=  false;
                interactive=    None;
                ui_switches=    []
              }
  in
  let empty_node_id = { last_id= 0;
                        tagDefs= "";
                        marshalled_state= "";
                        active_id= 0;
                      }
  in
  let action_from_string = function
    | "Elaborate"  -> `Elaborate
    | "Random"     -> `Random
    | "Exhaustive" -> `Exhaustive
    | "Step"       -> `Step
    | s -> failwith ("unknown action " ^ s)
  in
  let parse_bool = function
    | "true" -> true
    | "false" -> false
    | s ->
      Debug.warn ("Unknown boolean " ^ s); false
  in
  let get = function Some m -> m | None -> empty_node_id in
  let parse msg = function
    | ("action", [act])      -> { msg with action= action_from_string act; }
    | ("source", [src])      -> { msg with source= src; }
    | ("rewrite", [b])       -> { msg with rewrite= parse_bool b; }
    | ("sequentialise", [b]) -> { msg with sequentialise= parse_bool b; }
    | ("model", [model])     -> { msg with model= model; }
    | ("switches[]", [sw])   -> { msg with ui_switches= sw::msg.ui_switches }
    | ("interactive[lastId]", [v]) ->
      { msg with interactive= Some { (get msg.interactive) with last_id = int_of_string v } }
    | ("interactive[state]", [v]) ->
      { msg with interactive= Some { (get msg.interactive) with marshalled_state = B64.decode v } }
    | ("interactive[active]", [v]) ->
      { msg with interactive= Some { (get msg.interactive) with active_id = int_of_string v } }
    | ("interactive[tagDefs]", [v]) ->
      { msg with interactive= Some { (get msg.interactive) with tagDefs = B64.decode v } }
    | (k, _) ->
      Debug.warn ("unknown value " ^ k ^ " when parsing incoming message");
      msg (* ignore unknown key *)
  in List.fold_left parse empty content

(* Outgoing messages *)

let json_of_exec_tree ((ns, es) : exec_tree) =
  let json_of_info i =
    `Assoc [("kind", `String i.step_kind);
            ("debug", `String i.step_debug);
            ("file", Json.of_opt_string i.step_file);]
  in
  let json_of_node n =
    let json_of_loc (loc, uid) =
      `Assoc [("c", Location_ocaml.to_json loc);
              ("core", Json.of_opt_string uid) ]
    in
    `Assoc [("id", `Int n.node_id);
            ("info", json_of_info n.node_info);
            ("mem", n.memory);
            ("loc", json_of_loc (n.c_loc, n.core_uid));
            ("arena", `String n.arena);
            ("env", `String n.env);
            ("state",
             match n.next_state with
             | Some state -> `String (B64.encode state)
             | None -> `Null);
           ]
  in
  let json_of_edge = function
    | Edge (p, c) -> `Assoc [("from", `Int p);
                               ("to", `Int c)]
  in
  let nodes = `List (List.map json_of_node ns) in
  let edges = `List (List.map json_of_edge es) in
  `Assoc [("nodes", nodes); ("edges", edges)]

let json_of_range (p1, p2) =
  let json_of_point (x, y) =
    `Assoc [("line", `Int x); ("ch", `Int y)]
  in
  `Assoc [("begin", json_of_point p1); ("end", json_of_point p2)]

let json_of_locs locs = `List
  (List.fold_left (
    fun (jss, i) (cloc, coreloc) ->
      let js = `Assoc [
          ("c", json_of_range cloc);
          ("core", json_of_range coreloc);
          ("color", `Int i);
        ]
      in (js::jss, i+1)
  ) ([], 1) locs (*(sort locs)*)
  |> fst)

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
      ("locs", json_of_locs r.locs);
      ("console", `String "");
      ("result", `String "");
    ]
  | Execution str ->
    `Assoc [
      ("status", `String "execution");
      ("console", `String "");
      ("result", `String str);
    ]
  | Interactive (tags, ranges, t) ->
    `Assoc [
      ("steps", json_of_exec_tree t);
      ("status", `String "interactive");
      ("result", `String "");
      ("ranges", `Assoc (List.map (fun (uid, range) -> (uid, json_of_range range)) ranges));
      ("tagDefs", `String (B64.encode tags));
    ]
  | Step (res, activeId, t) ->
    `Assoc [
      ("steps", json_of_exec_tree t);
      ("activeId", `Int activeId);
      ("status", `String "stepping");
      ("result", Json.of_opt_string res);
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

let get_headers ?(gzipped=false) contentType =
  Cohttp.Header.of_list @@
  ("content-type", contentType) :: if gzipped then [("content-encoding", "gzip")] else []

let respond_json ?(gzipped=false) json =
  let headers = get_headers ~gzipped "application/json" in
  let response_string = Yojson.to_string json in
  Debug.print 10 "[ RESPONSE ]";
  Debug.print 10 response_string;
  let data = (if gzipped then Ezgzip.compress ~level:9 else id) response_string in
  (Server.respond_string ~flush:true ~headers) `OK data ()

let respond_file ~gzipped filename =
  let ext = Filename.extension filename in
  let contentType =
    if ext = ".js" then Some "application/javascript"
    else if ext = ".css" then Some "text/css"
    else None
  in match contentType with
  | Some contentType ->
    if gzipped && Sys.file_exists (filename ^ ".gz") then
      let headers = get_headers ~gzipped contentType in
      (Server.respond_file ~headers) (filename ^ ".gz") ()
    else
      let headers = get_headers contentType in
      (Server.respond_file ~headers) filename ()
  | None ->
    Server.respond_file filename ()

(* Cerberus actions *)

let log_request msg flow =
  match flow with
  | Conduit_lwt_unix.TCP tcp ->
    let open Unix in
    let tm = gmtime @@ time () in
    let oc = open_out_gen [Open_text;Open_append;Open_creat] 0o666
        "./public/dist/request.log"
    in Printf.fprintf oc "%s %d/%d/%d %d:%d:%d %s:%s \"%s\"\n"
      (Ipaddr.to_string tcp.ip)
      tm.tm_mday (tm.tm_mon+1) (tm.tm_year+1900)
      (tm.tm_hour+1) tm.tm_min tm.tm_sec
      (string_of_action msg.action)
      (msg.model)
      (String.escaped msg.source)
    ; close_out oc
  | _ -> ()

let cerberus ?(gzipped=false) ~conf ~flow content =
  let msg       = parse_incoming_msg content in
  let filename  = write_tmp_file msg.source in
  let conf      = { conf with rewrite_core= msg.rewrite;
                              sequentialise_core = msg.sequentialise;
                              switches = msg.ui_switches;
                  }
  in
  let timeout   = float_of_int conf.timeout in
  let request req : result Lwt.t =
    let instance = "./cerb." ^ String.lowercase_ascii msg.model in
    let cmd = (instance, [| instance; "-d" ^ string_of_int !Debug.level |]) in
    let proc = Lwt_process.open_process ~timeout cmd in
    Lwt_io.write_value proc#stdin ~flags:[Marshal.Closures] req >>= fun () ->
    Lwt_io.close proc#stdin >>= fun () ->
    Lwt_io.read_value proc#stdout
  in
  log_request msg flow;
  let do_action = function
    | `Nop   -> return @@ Failure "no action"
    | `Elaborate  -> request @@ `Elaborate (conf, filename)
    | `Random -> request @@ `Execute (conf, filename, Random)
    | `Exhaustive -> request @@ `Execute (conf, filename, Exhaustive)
    | `Step -> request @@ `Step (conf, filename, msg.interactive)
  in
  Debug.print 7 ("Executing action " ^ string_of_action msg.action);
  do_action msg.action >>= (respond_json ~gzipped) % json_of_result

(* GET and POST *)

let head ~docroot ?(gzipped=false) uri path =
  let is_regular filename =
    match Unix.((stat filename).st_kind) with
    | Unix.S_REG -> true
    | _ -> false
  in
  let check_local_file () =
    let filename = Server.resolve_local_file ~docroot ~uri in
    if is_regular filename && Sys.file_exists filename then
        Server.respond `OK  `Empty ()
    else forbidden path
  in
  let try_with () =
    Debug.print 10 ("HEAD " ^ path);
    match path with
    | "/" -> Server.respond `OK `Empty ()
    | _   -> check_local_file ()
  in catch try_with begin fun e ->
    Debug.error_exception "HEAD" e;
    forbidden path
  end


let get ~docroot ?(gzipped=false) uri path =
  let is_regular filename =
    match Unix.((stat filename).st_kind) with
    | Unix.S_REG -> true
    | _ -> false
  in
  let get_local_file () =
    let filename = Server.resolve_local_file ~docroot ~uri in
    if is_regular filename then
      respond_file ~gzipped filename
    else forbidden path
  in
  let try_with () =
    Debug.print 9 ("GET " ^ path);
    match path with
    | "/" -> Server.respond_file (docroot ^ "/index.html") ()
    | _   -> get_local_file ()
  in catch try_with begin fun e ->
    Debug.error_exception "GET" e;
    forbidden path
  end

let post ~docroot ?(gzipped=false) ~conf ~flow uri path content =
  let try_with () =
    Debug.print 9 ("POST " ^ path);
    match path with
    | "/cerberus" -> cerberus ~gzipped ~conf ~flow content
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

let request ~docroot ~conf (flow, _) req body =
  let uri  = Request.uri req in
  let meth = Request.meth req in
  let path = Uri.path uri in
  let try_with () =
    let gzipped = match Cohttp__.Header.get req.headers "accept-encoding" with
      | Some enc -> contains enc "gzip"
      | None -> false
    in
    if gzipped then Debug.print 10 "accepts gzip";
    match meth with
    | `HEAD -> head ~docroot ~gzipped uri path >|= fun (res, _) -> (res, `Empty)
    | `GET  -> get ~docroot ~gzipped uri path
    | `POST ->
      Cohttp_lwt.Body.to_string body >|= Uri.query_of_encoded >>=
      post ~docroot ~gzipped ~conf ~flow uri path
    | _     -> not_allowed meth path
  in catch try_with begin fun e ->
    Debug.error_exception "POST" e;
    forbidden path
  end


let setup cerb_debug_level debug_level timeout core_impl cpp_cmd port docroot =
  try
    Debug.level := debug_level;
    let conf = { rewrite_core = false;
                 sequentialise_core = false;
                 tagDefs = "";
                 switches = [];
                 cpp_cmd; core_impl; cerb_debug_level; timeout;
               }
    in
    (* NOTE: ad-hoc fix for server crash: https://github.com/mirage/ocaml-cohttp/issues/511 *)
    Lwt.async_exception_hook := ignore;
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
  Arg.(value & pos 0 string "./public/dist" & info [] ~docv:"PUBLIC" ~doc)

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
