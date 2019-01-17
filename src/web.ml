open Lwt
open Cohttp_lwt_unix
open Instance_api
open Util

(* Web server configuration *)

type webconf =
  { tls_cert: string;
    tls_key: string;
    tls_port: int;
    tcp_port: int;
    tcp_redirect: bool;
    docroot: string;
    timeout: int;
    log_file: string;
    index_file: string;
    request_file: string;
    cerb_path: string;
    core_impl: string;
    z3_path: string;
    cerb_debug_level: int;
    tmp_path: string;
  }

let webconf =
  ref (fun () -> failwith "webconf undefined")

let print_webconf () =
  let w = !webconf() in
  Printf.printf "[1]: Web server configuration:
    TLS certificate: %s
    TLS key: %s
    TLS port: %d
    TCP port: %d
    TCP redirect: %b
    Public folder: %s
    Executions timeout: %ds
    Log file: %s
    Index file: %s
    Request file: %s
    CERB_PATH: %s
    Core implementation file: %s
    Z3 path: %s
    TMP path: %s\n"
    w.tls_cert w.tls_key w.tls_port
    w.tcp_port w.tcp_redirect
    w.docroot
    w.timeout
    w.log_file
    w.index_file
    w.request_file
    w.cerb_path
    w.core_impl
    w.z3_path
    w.tmp_path;
  flush stdout

let set_webconf cfg_file timeout core_impl tcp_port docroot cerb_debug_level =
  let cerb_path =
    try Sys.getenv "CERB_PATH"
    with Not_found -> "."
  in
  let ld_path =
    try Sys.getenv "LD_LIBRARY_PATH"
    with Not_found -> "."
  in
  let time =
    let tm = Unix.gmtime @@ Unix.time () in
    Printf.sprintf "%04d_%02d_%02d-%02d_%02d_%02d"
      (tm.tm_year+1900) (tm.tm_mon+1) tm.tm_mday tm.tm_hour tm.tm_min tm.tm_sec
  in
  let set_log name =
    Printf.sprintf "%s_%s.log" name time
  in
  let default =
    { tls_cert= cerb_path ^ "/tools/server.cert";
      tls_key= cerb_path ^ "/tools/server.key";
      tls_port= 443;
      tcp_port= tcp_port;
      tcp_redirect= false;
      docroot= docroot;
      timeout= timeout;
      cerb_path= cerb_path;
      core_impl= core_impl;
      log_file= set_log "main";
      index_file= set_log "index";
      request_file= set_log "request";
      z3_path= ld_path;
      tmp_path= Filename.get_temp_dir_name ();
      cerb_debug_level= 0;
    }
  in
  let parse cfg = function
    | ("tls", `Assoc tls) ->
      let parse_tls cfg = function
        | ("cert", `String cert) -> { cfg with tls_cert = cert }
        | ("key", `String key) -> { cfg with tls_key = key }
        | ("port", `Int port) -> { cfg with tls_port = port }
        | (k, _) ->
          Debug.warn @@ "Unknown TLS configuration key: " ^ k;
          cfg
      in
      List.fold_left parse_tls cfg tls
    | ("tcp", `Assoc tcp) ->
      let parse_tcp cfg = function
        | ("port", `Int port) -> { cfg with tcp_port = port }
        | ("redirect", `Bool b) -> { cfg with tcp_redirect = b }
        | (k, _) ->
          Debug.warn @@ "Unknown TCP configuration key: " ^ k;
          cfg
      in
      List.fold_left parse_tcp cfg tcp
    | ("docroot", `String docroot) -> { cfg with docroot = docroot }
    | ("timeout", `Int max) -> { cfg with timeout = max }
    | ("log", `Assoc log) ->
      let parse_log cfg = function
        | ("all", `String file) -> { cfg with log_file = set_log file }
        | ("index", `String file) -> { cfg with index_file = set_log file }
        | ("request", `String file) -> { cfg with request_file = set_log file }
        | (k, _) ->
          Debug.warn @@ "Unknown log configuration key: " ^ k;
          cfg
      in
      List.fold_left parse_log cfg log
    | ("z3_path", `String path) -> { cfg with z3_path = path }
    | ("cerb_path", `String path) -> { cfg with cerb_path= path }
    | ("tmp_path", `String path) -> { cfg with tmp_path= path }
    | (k, _) ->
      Debug.warn @@ "Unknown configuration key: " ^ k;
      cfg
  in
  let c =
    try
      match Yojson.Basic.from_file cfg_file with
      | `Assoc cfgs ->
        List.fold_left parse default cfgs
      | _ ->
        Debug.warn "Configuration file has an incorrect format...";
        default
    with e ->
      Debug.error_exception "Error reading configuration file:" e;
      default
  in webconf := fun () -> c

(* Create configuration for every instance model *)
let create_conf w =
  let cpp_cmd () =
    "cc -E -C -nostdinc -undef -D__cerb__ -I " ^ w.docroot ^ " -I "
    ^ w.cerb_path ^ "/libc/include -I "
    ^ w.cerb_path ^ "/libc/include/posix"
  in
  { rewrite_core = false;
    sequentialise_core = false;
    tagDefs = "";
    switches = [];
    cpp_cmd = cpp_cmd ();
    core_impl = w.core_impl;
    timeout = w.timeout;
    cerb_debug_level = w.cerb_debug_level;
  }

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
  | `Step
  | `BMC ]

let string_of_action = function
  | `Nop        -> "Nop"
  | `Elaborate  -> "Elaborate"
  | `Random     -> "Random"
  | `Exhaustive -> "Exhaustive"
  | `Step       -> "Step"
  | `BMC        -> "BMC"

type incoming_msg =
  { action:  action;
    source:  string;
    name:    string;  (* name of the file in the UI *)
    model:   string;
    rewrite: bool;
    sequentialise: bool;
    interactive: active_node option;
    ui_switches: string list;
  }

let parse_incoming_msg content =
  let empty = { action=         `Nop;
                source=         "";
                name=           "<unknown>";
                model=          "concrete";
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
    | "elaborate"  -> `Elaborate
    | "random"     -> `Random
    | "exhaustive" -> `Exhaustive
    | "step"       -> `Step
    | "bmc"        -> `BMC
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
    | ("name", [name])       -> { msg with name= name; }
    | ("rewrite", [b])       -> { msg with rewrite= parse_bool b; }
    | ("sequentialise", [b]) -> { msg with sequentialise= parse_bool b; }
    | ("model", [model])     -> { msg with model= model; }
    | ("switches[]", [sw])   -> { msg with ui_switches= sw::msg.ui_switches }
    | ("interactive[lastId]", [v]) ->
      { msg with interactive=
        Some { (get msg.interactive) with last_id = int_of_string v } }
    | ("interactive[state]", [v]) ->
      { msg with interactive=
        Some { (get msg.interactive) with marshalled_state = B64.decode v } }
    | ("interactive[active]", [v]) ->
      { msg with interactive=
        Some { (get msg.interactive) with active_id = int_of_string v } }
    | ("interactive[tagDefs]", [v]) ->
      { msg with interactive=
        Some { (get msg.interactive) with tagDefs = B64.decode v } }
    | (k, _) ->
      Debug.warn ("unknown value " ^ k ^ " when parsing incoming message");
      msg (* ignore unknown key *)
  in List.fold_left parse empty content

(* Outgoing messages *)

let json_of_exec_tree ((ns, es) : exec_tree) =
  let json_of_info i =
    `Assoc [("kind", `String i.step_kind);
            ("debug", `String i.step_debug);
            ("file", Json.of_opt_string i.step_file);
            ("error_loc", Json.of_option Location_ocaml.to_json i.step_error_loc);]
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
            ("outp", `String n.outp);
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
      ("result", `String ""); (* TODO: eliminate result *)
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
      ("ranges",
       `Assoc (List.map (fun (uid, range) -> (uid, json_of_range range)) ranges));
      ("tagDefs", `String (B64.encode tags));
    ]
  | Step (res, activeId, t) ->
    `Assoc [
      ("steps", json_of_exec_tree t);
      ("activeId", `Int activeId);
      ("status", `String "stepping");
      ("result", Json.of_opt_string res);
    ]
  | BMC (`Unsatisfiable (res, dots) | `Satisfiable (res, dots)) ->
    `Assoc [
      ("status", `String "bmc");
      ("executions", `List (List.map (fun s -> `String s) dots));
      ("result", `String res)
    ]
  | BMC (`Unknown err) ->
    `Assoc [
      ("status", `String "failure");
      ("console", `String err);
      ("result", `String "");
    ]
  | Failure err ->
    `Assoc [
      ("status", `String "failure");
      ("console", `String err);
      ("result", `String "");
    ]

(* Request headers *)

type rheader =
  { accept_gzip: bool;
    if_none_match: string;
    user_agent: string;
    referer: string;
    host: string;
  }

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

let resolve_mime file =
  match Filename.extension file with
  | ".js"   -> "text/javascript; charset=utf-8"
  | ".css"  -> "text/css; charset=utf-8"
  | ".html" -> "text/html; charset=utf-8"
  | ".md"   -> "text/markdown; charset=utf-8"
  | ".json" -> "text/json; charset=utf-8"
  | ".png" -> "image/png"
  | ".gif" -> "image/gif"
  | ".jpg" -> "image/jpg"
  | ".ico" -> "image/x-icon"
  | _ -> "text/plain"

let respond_json ~time ~rheader json =
  let gzipped  = rheader.accept_gzip in
  let compress = (if gzipped then Ezgzip.compress ~level:9 else id) in
  let headers = Cohttp.Header.of_list
      [("Content-Type", "text/json; charset=utf-8");
       ("Content-Encoding", if gzipped then "gzip" else "identity");
       ("Cache-Control", "no-cache");
       ("Server-Timing",
        match time with Some t -> "dur=" ^ string_of_float t | None -> "");
       ("Server", "Cerberus/1.0")] in
  let data = compress @@ Yojson.to_string json in
  (Server.respond_string ~flush:true ~headers) `OK data ()

let date () =
  let open Unix in
  let week = function
    | 0 -> "Sun" | 1 -> "Mon" | 2 -> "Tue" | 3 -> "Wed" | 4 -> "Thu"
    | 5 -> "Fri" | 6 -> "Sat" | _ -> assert false
  in
  let month = function
    | 0 -> "Jan" | 1 -> "Feb" | 2 -> "Mar" | 3 -> "Apr" | 4 -> "May"
    | 5 -> "Jun" | 6 -> "Jul" | 7 -> "Aug" | 8 -> "Sep" | 9 -> "Oct"
    | 10 -> "Nov" | 11 -> "Dec" | _ -> assert false
  in
  let tm = gmtime @@ time () in
  Printf.sprintf "%s, %02d %s %04d %02d:%02d:%02d GMT"
    (week tm.tm_wday) tm.tm_mday (month tm.tm_mon) (tm.tm_year+1900)
    (tm.tm_hour+1) tm.tm_min tm.tm_sec

let respond_file ~rheader fname =
  let gzipped = rheader.accept_gzip && Sys.file_exists (fname ^ ".gz") in
  let mime  = resolve_mime fname in
  let fname = fname ^ (if gzipped then ".gz" else "") in
  let hash = Digest.to_hex @@ Digest.file fname in
  Debug.print 7 @@ "File: " ^ fname;
  Debug.print 7 @@ "Hash: " ^ hash;
  let try_with () =
    let count = 16384 (* 16 KB *) in
    Lwt_io.open_file
      ~buffer:(Lwt_bytes.create count)
      ~mode:Lwt_io.input fname
    >>= fun ic ->
    Lwt_io.length ic >>= fun len ->
    let encoding = Cohttp.Transfer.Fixed len in
    let stream = Lwt_stream.from @@ fun () ->
      Lwt.catch (fun () ->
          Lwt_io.read ~count ic >|= function
          | "" -> None
          | buf -> Some buf)
        (fun e ->
           Debug.error_exception ("Error resolving file " ^ fname) e;
           return_none)
    in
    Lwt.on_success (Lwt_stream.closed stream)
      (fun () -> ignore_result @@ Lwt_io.close ic);
    let body = Cohttp_lwt.Body.of_stream stream in
    let headers = Cohttp.Header.of_list
      [("Content-Type", mime);
       ("Content-Encoding", if gzipped then "gzip" else "identity");
       ("Cache-Control", "max-age=900");
       ("ETag", hash);
       ("Date", date ());
       ("Server", "Cerberus/1.0")]
    in
    let res = Cohttp.Response.make ~status:`OK ~encoding ~headers () in
    return (res, body)
  in
  if rheader.if_none_match = hash then begin
    Debug.warn "not-modified";
    Server.respond `Not_modified `Empty ()
  end
  else Lwt.catch try_with @@ function
    | Unix.Unix_error (Unix.ENOENT, _, _) ->
      Server.respond_not_found ()
    | e ->
      Debug.error_exception ("responding file : " ^ fname) e;
      forbidden fname

(* Cerberus actions *)

let now () =
  let tm = Unix.gmtime @@ Unix.time () in
  Printf.sprintf "%02d/%02d/%04d %02d:%02d:%02d"
    tm.tm_mday (tm.tm_mon+1) (tm.tm_year+1900)
    (tm.tm_hour+1) tm.tm_min tm.tm_sec

let log_index flow =
  match Conduit_lwt_unix.endp_of_flow flow with
  | `TLS (_, `TCP (ip, _))
  | `TCP (ip, _) ->
    let oc =
      open_out_gen [Open_text;Open_append;Open_creat] 0o666 (!webconf()).index_file
    in
    Printf.fprintf oc "%s %s\n" (Ipaddr.to_string ip) (now ());
    close_out oc
  | _ -> ()

let log_request msg flow =
  match Conduit_lwt_unix.endp_of_flow flow with
  | `TLS (_, `TCP (ip, _))
  | `TCP (ip, _) ->
    let oc = open_out_gen [Open_text;Open_append;Open_creat] 0o666
        (!webconf()).request_file
    in
    Printf.fprintf oc "%s %s %s:%s \"%s\"\n"
      (Ipaddr.to_string ip)
      (now ())
      (string_of_action msg.action)
      (msg.model)
      (String.escaped msg.source);
    close_out oc
  | _ -> ()


let cerberus ~rheader ~conf ~flow content =
  let start_time = Sys.time () in
  let msg       = parse_incoming_msg content in
  let filename  = write_tmp_file msg.source in
  let conf      = { conf with rewrite_core= msg.rewrite;
                              sequentialise_core = msg.sequentialise;
                              switches = msg.ui_switches;
                  }
  in
  let timeout   = float_of_int conf.timeout in
  let request req : result Lwt.t =
    let instance = "./cerb." ^ msg.model in
    let cmd = (instance, [| instance; "-d" ^ string_of_int !Debug.level|]) in
    let env = [|"PATH=/usr/bin";
                "CERB_PATH="^(!webconf()).cerb_path;
                "LD_LIBRARY_PATH="^(!webconf()).z3_path|]
    in
    let proc = Lwt_process.open_process ~env ~timeout cmd in
    Lwt_io.write_value proc#stdin ~flags:[Marshal.Closures] req >>= fun () ->
    Lwt_io.read_value proc#stdout >>= fun data ->
    proc#close >>= fun _ ->
    return data
  in
  log_request msg flow;
  let do_action = function
    | `Nop   -> return @@ Failure "no action"
    | `Elaborate  -> request @@ `Elaborate (conf, filename, msg.name)
    | `Random -> request @@ `Execute (conf, filename, msg.name, Random)
    | `Exhaustive -> request @@ `Execute (conf, filename, msg.name, Exhaustive)
    | `Step -> request @@ `Step (conf, filename, msg.name, msg.interactive)
    | `BMC -> request @@ `BMC (conf, filename, msg.name)
  in
  Debug.print 9 ("Time: " ^ now ());
  Debug.print 7 ("Executing action " ^ string_of_action msg.action);
  do_action msg.action >|= json_of_result >>=
  let time = Some ((Sys.time () -. start_time) *. 1000.) in
  respond_json ~time ~rheader

(* GET and POST *)

let head uri path =
  let is_regular filename =
    match Unix.((stat filename).st_kind) with
    | Unix.S_REG -> true
    | _ -> false
  in
  let check_local_file () =
    let docroot = (!webconf()).docroot in
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


let get ~rheader ~flow uri path =
  let is_regular filename =
    match Unix.((stat filename).st_kind) with
    | Unix.S_REG -> true
    | _ -> false
  in
  let docroot = (!webconf()).docroot in
  let get_local_file () =
    let filename = Server.resolve_local_file ~docroot ~uri in
    if is_regular filename then
      respond_file ~rheader filename
    else forbidden path
  in
  let try_with () =
    Debug.print 9 ("GET " ^ path);
    match path with
    | "" | "/" ->
      log_index flow;
      respond_file ~rheader (docroot ^ "/index.html")
    | _   -> get_local_file ()
  in catch try_with begin fun e ->
    Debug.error_exception "GET" e;
    forbidden path
  end

let post ~conf ~rheader ~flow uri path content =
  let try_with () =
    Debug.print 9 ("POST " ^ path);
    match path with
    | "/query" -> cerberus ~rheader ~conf ~flow content
    | _ ->
      (* Ignore POST, fallback to GET *)
      Debug.warn ("Unknown post action " ^ path);
      Debug.warn ("Fallback to GET");
      get ~rheader ~flow uri path
  in catch try_with begin fun e ->
    Debug.error_exception "POST" e;
    forbidden path
  end

(* Main *)

let parse_req_header header =
  let get k = match Cohttp.Header.get header k with Some v -> v | None -> "" in
  { accept_gzip= contains (get "accept-encoding") "gzip";
    if_none_match= get "if-none-match";
    referer= get "referer";
    user_agent= get "user-agent";
    host= get "host";
  }

let request ~conf (flow, conn) req body =
  let uri  = Request.uri req in
  let meth = Request.meth req in
  let path =
    try
      let cerb = "/cerberus" in
      let clen = String.length cerb in
      let path = Uri.path uri in
      if String.sub path 0 clen = cerb then
        String.sub path (clen - 1) (String.length path - clen)
      else
        path
    with Invalid_argument _ -> Uri.path uri
  in
  let rheader = parse_req_header req.headers in
  if rheader.host = "" || rheader.host = "cerberus.cl.cam.ac.uk" || rheader.host = "localhost" then
  begin
    let try_with () =
      let accept_gzip = match Cohttp__.Header.get req.headers "accept-encoding" with
        | Some enc -> contains enc "gzip"
        | None -> false
      in
      if accept_gzip then Debug.print 10 "accepts gzip";
      match meth with
      | `HEAD -> head uri path >|= fun (res, _) -> (res, `Empty)
      | `GET  -> get ~rheader ~flow uri path
      | `POST ->
        Cohttp_lwt.Body.to_string body >|= Uri.query_of_encoded >>=
        post ~conf ~rheader ~flow uri path
      | _     -> not_allowed meth path
    in catch try_with begin fun e ->
      Debug.error_exception "POST" e;
      forbidden path
    end
  end else begin
    let headers = Cohttp.Header.of_list [("Location", "https://cerberus.cl.cam.ac.uk" ^ path)] in
    (Server.respond ~headers) `Moved_permanently Cohttp_lwt__.Body.empty ()
  end

let redirect ~conf conn req body =
  let uri  = Request.uri req in
  let meth = Request.meth req in
  match meth, Uri.path uri with
  | `GET, "/" | `GET, "/index.html" | `GET, "/cerberus" | `GET, "/cerberus/index.html" ->
    let headers =
      Cohttp.Header.of_list [("Location", "https:" ^ Uri.to_string uri)] in
    (Server.respond ~headers) `Moved_permanently Cohttp_lwt__.Body.empty ()
  | _ -> request ~conf conn req body

let initialise () =
  try
    (* NOTE: ad-hoc fix for server crash:
     * https://github.com/mirage/ocaml-cohttp/issues/511 *)
    Lwt.async_exception_hook := ignore;
    let webconf = !webconf() in
    Filename.set_temp_dir_name webconf.tmp_path;
    let conf    = create_conf webconf in
    let http_server = Server.make
        ~callback: (if webconf.tcp_redirect then redirect ~conf
                    else request ~conf) () in
    let https_server = Server.make ~callback: (request ~conf) () in
    Lwt_main.run @@ Lwt.join
      [ Server.create ~mode:(`TCP (`Port webconf.tcp_port)) http_server
      ; Server.create ~mode:(`TLS_native (`Crt_file_path webconf.tls_cert,
                                   `Key_file_path webconf.tls_key,
                                   `No_password,
                                   `Port webconf.tls_port)) https_server]
  with
  | e ->
    Debug.error_exception "Fatal error:" e

let setup cfg_file cerb_debug_level debug_level timeout core_impl port docroot =
  Debug.level := debug_level;
  set_webconf cfg_file timeout core_impl port docroot cerb_debug_level;
  if debug_level > 0 then print_webconf ();
  initialise ()

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

let timeout =
  let doc = "Instance execution timeout in seconds." in
  Arg.(value & opt int 45 & info ["t"; "timeout"] ~docv:"TIMEOUT" ~doc)

let docroot =
  let doc = "Set public (document root) files locations." in
  Arg.(value & pos 0 string "./public/dist/" & info [] ~docv:"PUBLIC" ~doc)

let config =
  let doc = "Configuration file in JSON. \
             This file overwrites any other command line option." in
  Arg.(value & opt string "config.json" & info ["c"; "config"] ~docv:"CONFIG" ~doc)

let port =
  let doc = "Set TCP port." in
  Arg.(value & opt int 80 & info ["p"; "port"] ~docv:"PORT" ~doc)

let () =
  let server = Term.(pure setup $ config $ cerb_debug_level $ debug_level
                     $ timeout $ impl $ port $ docroot) in
  let info = Term.info "web" ~doc:"Web server frontend for Cerberus." in
  match Term.eval (server, info) with
  | `Error _ -> exit 1;
  | `Ok _
  | `Version
  | `Help -> exit 0
