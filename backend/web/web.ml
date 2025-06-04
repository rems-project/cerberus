open Lwt
open Cohttp_lwt_unix
open Instance_api
open Cerb_util

(* Web server configuration *)

type webconf =
  { tcp_port: int;
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


(* Preventing filesystem disclosure *)
let check_docroot str =
  let path = Fpath.v str in
  if Fpath.(normalize path = path && is_abs path) then
    str
  else begin
    Debug.error "the DOCROOT must be set to an absolute and normalised path.";
    Stdlib.exit 1
  end

let check_filepath str =
  let open Fpath in
  let root = v (!webconf()).docroot in
  is_rooted ~root (v str)

let print_webconf () =
  let w = !webconf() in
  Printf.printf "[1]: Web server configuration:
    TCP port: %d
    Public folder: %s
    Executions timeout: %ds
    Log file: %s
    Index file: %s
    Request file: %s
    CERB_PATH: %s
    Core implementation file: %s
    Z3 path: %s
    TMP path: %s\n"
    w.tcp_port
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
    { tcp_port= tcp_port;
      docroot= check_docroot docroot;
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
    | ("tcp", `Assoc tcp) ->
      let parse_tcp cfg = function
        | ("port", `Int port) -> { cfg with tcp_port = port }
        | (k, _) ->
          Debug.warn @@ "Unknown TCP configuration key: " ^ k;
          cfg
      in
      List.fold_left parse_tcp cfg tcp
    | ("docroot", `String docroot) -> { cfg with docroot = check_docroot docroot }
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
      "cc -std=c11 -E -C -Werror -nostdinc -undef -D__cerb__ -I " ^ w.docroot ^ " -I "
    ^ w.cerb_path ^ "/runtime/bmc -I "
    ^ w.cerb_path ^ "/runtime/libc/include -I "
    ^ w.cerb_path ^ "/runtime/libc/include/posix"
  in
  { rewrite_core = false;
    sequentialise_core = false;
    link_libc = false;
    tagDefs = "";
    switches = [];
    cpp_cmd = cpp_cmd ();
    core_impl = w.core_impl;
    timeout = w.timeout;
    cerb_debug_level = w.cerb_debug_level;
    n1570 = Lazy.force N1570.data;
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

let _string_of_doc d =
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
  | `BMC
  | `Shorten ]

(* implementation of the memory interface *)
type model =
  [ `Concrete
  | `Symbolic
  | `VIP ]

let string_of_model = function
  | `Concrete -> "concrete"
  | `Symbolic -> "symbolic"
  | `VIP      -> "vip"

let string_of_action = function
  | `Nop        -> "Nop"
  | `Elaborate  -> "Elaborate"
  | `Random     -> "Random"
  | `Exhaustive -> "Exhaustive"
  | `Step       -> "Step"
  | `BMC        -> "BMC"
  | `Shorten    -> "Shorten"

type incoming_msg =
  { action:  action;
    source:  string;
    name:    string;  (* name of the file in the UI *)
    model:   model;
    bmc_model: bmc_model;
    rewrite: bool;
    sequentialise: bool;
    libc: bool;
    interactive: active_node option;
    ui_switches: string list;
  }

let parse_incoming_msg content =
  let empty = { action=         `Nop;
                source=         "";
                name=           "<unknown>";
                model=          `Concrete;
                bmc_model=      `C11;
                rewrite=        false;
                sequentialise=  false;
                libc=           false;
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
    | "shorten"    -> `Shorten
    | s -> failwith ("unknown action " ^ s)
  in
  let bmc_mode_from_string = function
    | "bmc_c11"   -> Some `C11
    | "bmc_rc11"  -> Some `RC11
    | "bmc_rc11_hardcoded"  -> Some `RC11_Hardcoded
    | "bmc_linux" -> Some `Linux
    | "bmc_linux_no_rcu" -> Some `LinuxNoRCU
    | "bmc_custom" -> None
    | s -> failwith ("unknown BMC model " ^ s)
  in
  let parse_bool = function
    | "true" -> true
    | "false" -> false
    | s ->
      Debug.warn ("Unknown boolean " ^ s); false
  in
  let parse_model = function
    | "concrete" -> `Concrete
    | "symbolic" -> `Symbolic
    | "vip"      -> `VIP
    | str -> 
        Debug.warn ("Unknown model: '" ^ str ^ "' (defaulting to 'concrete')");
        `Concrete
  in
  let get = function Some m -> m | None -> empty_node_id in
  let parse msg = function
    | ("action", [act])      -> { msg with action= action_from_string act; }
    | ("source", [src])      -> { msg with source= src; }
    | ("name", [name])       -> { msg with name= name; }
    | ("rewrite", [b])       -> { msg with rewrite= parse_bool b; }
    | ("sequentialise", [b]) -> { msg with sequentialise= parse_bool b; }
    | ("libc", [b])          -> { msg with libc= parse_bool b; }
    | ("model", [model])     -> { msg with model= parse_model model; }
    | ("bmc_model", [model]) ->
      begin match bmc_mode_from_string model with
        | Some bmc_model -> { msg with bmc_model }
        | None -> msg
      end
    | ("bmc_herd_file", [herd]) -> { msg with bmc_model= `Custom herd }
    | ("switches[]", [sw])   -> { msg with ui_switches= sw::msg.ui_switches }
    | ("interactive[lastId]", [v]) ->
      { msg with interactive=
        Some { (get msg.interactive) with last_id = int_of_string v } }
    | ("interactive[state]", [v]) ->
      { msg with interactive=
        Some { (get msg.interactive) with marshalled_state = Base64.decode_exn v } }
    | ("interactive[active]", [v]) ->
      { msg with interactive=
        Some { (get msg.interactive) with active_id = int_of_string v } }
    | ("interactive[tagDefs]", [v]) ->
      { msg with interactive=
        Some { (get msg.interactive) with tagDefs = Base64.decode_exn v } }
    | (k, _) ->
      Debug.warn ("unknown value " ^ k ^ " when parsing incoming message");
      msg (* ignore unknown key *)
  in
  try
    List.fold_left parse empty content
  with
    | Invalid_argument str ->
        begin 
          Debug.warn ("Failed to decode Base64 msg ==> " ^ str);
          failwith "parse_incoming_msg"
        end

(* Outgoing messages *)

let json_of_exec_tree ((ns, es) : exec_tree) =
  let json_of_info = function
      | `Init ->
        `Assoc [("kind", `String "init")]
      | `Done res ->
        `Assoc [("kind", `String "done");
                ("result", `String res)]
      | `Error (loc_opt, reason) ->
        `Assoc [("kind", `String "error");
                ("reason", `String reason);
                ("loc", Cerb_json.of_option Cerb_location.to_json loc_opt)]
      | `Branch ->
        `Assoc [("kind", `String "branch")]
      | `Step args ->
        `Assoc [("kind", `String "step");
                ("step_kind", args)]
      | `Unsat ->
        `Assoc [("kind", `String "unsat")]
  in
  let json_of_node n =
    let json_of_loc (loc, uid) =
      `Assoc [("c", Cerb_location.to_json loc);
              ("core", Cerb_json.of_opt_string uid) ]
    in
    `Assoc [("id", `Int n.node_id);
            ("info", json_of_info n.node_info);
            ("mem", n.memory);
            ("loc", json_of_loc (n.c_loc, n.core_uid));
            ("arena", `String n.arena);
            ("env", `String n.env);
            ("stdout", `String n.stdout);
            ("stderr", `String n.stderr);
            ("state",
             match n.next_state with
             | Some state -> `String (Base64.encode_string state)
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
          ("cabs", Cerb_json.of_opt_string r.pp.cabs);
          ("ail",  Cerb_json.of_opt_string r.pp.ail);
          ("core", Cerb_json.of_opt_string r.pp.core);
        ]);
      ("ast", `Assoc [
          ("cabs", Cerb_json.of_opt_string r.ast.cabs);
          ("ail",  Cerb_json.of_opt_string r.ast.ail);
          ("core", Cerb_json.of_opt_string r.ast.core);
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
      ("tagDefs", `String (Base64.encode_string tags));
    ]
  | Step (res, activeId, t) ->
    `Assoc [
      ("steps", json_of_exec_tree t);
      ("activeId", `Int activeId);
      ("status", `String "stepping");
      ("result", Cerb_json.of_opt_string res);
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
  | Shorten url ->
    `Assoc [
      ("status", `String "shorten");
      ("url", `String url);
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
  let body =
      "<html><body>\
       <h2>Forbidden</h2>\
       <p>the requested path is forbidden</p>\
       <hr/>\
       </body></html>" in
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
  let body = compress @@ Yojson.to_string json in
  Server.respond_string ~flush:true ~headers ~status:`OK ~body ()

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
  (* I know this is already done before calls to this function.
     Tryin to prevent future misuses. *)
  if not (check_filepath fname) then begin
    forbidden fname
  end else begin
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
      Server.respond ~status:`Not_modified ~body:`Empty ()
    end
    else Lwt.catch try_with @@ function
      | Unix.Unix_error (Unix.ENOENT, _, _) ->
        Server.respond_not_found ()
      | e ->
        Debug.error_exception ("responding file : " ^ fname) e;
        forbidden fname
  end

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
      (string_of_model msg.model)
      (String.escaped msg.source);
    close_out oc
  | _ -> ()

let shorten source =
  if source = "" then
    return @@ Failure "Empty source!"
  else
    let docroot = (!webconf()).docroot in
    let digest = Digest.to_hex @@ Digest.string source in
    let digest_len = String.length digest in
    let path = docroot ^ "short/" in
    let write_file hash =
      let len = String.length source in
      if len > 1000000 then (* max: 1MB *)
        return @@ Failure "File is too large."
      else
        Lwt_io.open_file ~mode:Lwt_io.Output (path ^ hash) >>= fun oc ->
        Lwt_io.write_from_string oc source 0 (String.length source) >>= fun _ ->
        Lwt_io.close oc >>= fun () ->
        return @@ Shorten hash
    in
    let rec aux n =
      if n >= digest_len then begin
        Debug.warn @@ "Numerous file conflict: " ^ digest ^ ".";
        write_file digest
      end else
        let hash = String.sub digest 0 n in
        Lwt_unix.file_exists (path ^ hash) >>= function
        | true ->
          if Digest.to_hex @@ Digest.file (path ^ hash) = digest then
            return @@ Shorten hash (* same file *)
          else
            aux (n+1)
        | false ->
          write_file hash
    in aux 6

let cerberus ~rheader ~conf ~flow content =
  let start_time = Sys.time () in
  let msg       = parse_incoming_msg content in
  let filename  = write_tmp_file msg.source in
  let conf      = { conf with rewrite_core= msg.rewrite;
                              sequentialise_core = msg.sequentialise;
                              switches = msg.ui_switches;
                              link_libc = msg.libc;
                  }
  in
  let timeout   = float_of_int conf.timeout in
  let request (req: request) : result Lwt.t =
    let instance =
      (* the indirection string -> poly variant -> string is to 
         prevent the possibility of exploits since the string comes from the client *)
      "./webcerb." ^ begin match msg.model with
        | `Concrete -> "concrete"
        | `Symbolic -> "symbolic"
        | `VIP      -> "vip"
      end in
    let cmd = (instance, [| instance; "-d" ^ string_of_int !Debug.level|]) in
    let env = [|"PATH=/usr/bin";
                "CERB_PATH="^(!webconf()).cerb_path;
                "LD_LIBRARY_PATH=/usr/local/lib:"^(!webconf()).z3_path;
                "DYLD_LIBRARY_PATH=/usr/local/lib:"^(!webconf()).z3_path;
                "OPAM_SWITCH_PREFIX="^Sys.getenv "OPAM_SWITCH_PREFIX"|]
    in
    let proc = Lwt_process.open_process ~env ~timeout cmd in
    Lwt_io.write_value proc#stdin ~flags:[Marshal.Closures] req >>= fun () ->
    Lwt_io.read_value proc#stdout >>= fun data ->
    proc#close >>= fun _ ->
    proc#terminate;  (* NOTE: force process to terminate, the server was leaking before *)
    return data
  in
  log_request msg flow;
  let do_action = function
    | `Nop   -> return @@ Failure "no action"
    | `Elaborate  -> request @@ `Elaborate (conf, filename, msg.name)
    | `Random -> request @@ `Execute (conf, filename, msg.name, Random)
    | `Exhaustive -> request @@ `Execute (conf, filename, msg.name, Exhaustive)
    | `Step -> request @@ `Step (conf, filename, msg.name, msg.interactive)
    | `BMC -> request @@ `BMC (conf, msg.bmc_model,filename, msg.name)
    | `Shorten -> shorten msg.source
  in
  Debug.print 9 ("Time: " ^ now ());
  Debug.print 7 ("Executing action " ^ string_of_action msg.action);
  do_action msg.action >|= json_of_result >>= fun json ->
  let time = Some ((Sys.time () -. start_time) *. 1000.) in
  Sys.remove filename;
  respond_json ~time ~rheader (json : Cerb_json.json :> Yojson.t)

(* GET and POST *)

let head uri path =
  (* without this `resolve_local_file` doesn't catch .. followed by the / in hexa (%2f),
     resulting in a full filesytem disclosure vulnerability *)
  let uri = Uri.(of_string (pct_decode (to_string uri))) in
  let is_regular filename =
    match Unix.((stat filename).st_kind) with
    | Unix.S_REG -> true
    | _ -> false
  in
  let check_local_file () =
    let docroot = (!webconf()).docroot in
    let filename = Cohttp.Path.resolve_local_file ~docroot ~uri in
    if check_filepath filename && is_regular filename && Sys.file_exists filename then
        Server.respond ~status:`OK ~body:`Empty ()
    else forbidden path
  in
  let try_with () =
    Debug.print 10 ("HEAD " ^ path);
    match path with
    | "/" -> Server.respond ~status:`OK ~body:`Empty ()
    | _   -> check_local_file ()
  in catch try_with begin fun e ->
    Debug.error_exception "HEAD" e;
    forbidden path
  end


let get ~rheader ~flow uri path =
  (* without this `resolve_local_file` doesn't catch .. followed by the / in hexa (%2f),
     resulting in a full filesytem disclosure vulnerability *)
     let uri = Uri.(of_string (pct_decode (to_string uri))) in
  let is_regular filename =
    match Unix.((stat filename).st_kind) with
    | Unix.S_REG -> true
    | _ -> false
  in
  let docroot = (!webconf()).docroot in
  let get_local_file () =
    let filename = Cohttp.Path.resolve_local_file ~docroot ~uri in
    if check_filepath filename && is_regular filename then
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
  in catch try_with begin function
    | Lwt_io.Channel_closed msg ->
      Debug.warn @@ "Lwt channel closed: " ^ msg;
      respond_json ~time:None ~rheader
      @@ (json_of_result : _ -> Cerb_json.json :> _ -> Yojson.t)
      @@ Failure "Error: timeout!"
    | e ->
      Debug.error_exception "POST" e;
      forbidden path
  end

(* Main *)

let parse_req_header header =
  let get k = match Cohttp.Header.get header k with Some v -> v | None -> "" in
  { accept_gzip= starts_with ~prefix:"gzip" (get "accept-encoding");
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
  if rheader.host = "" || rheader.host = "cerberus.cl.cam.ac.uk" || rheader.host = "localhost"
     || (String.length rheader.host > 10 && String.sub rheader.host 0 9 = "localhost") then
  begin
    let try_with () =
      let accept_gzip = match Cohttp__.Header.get req.headers "accept-encoding" with
        | Some enc -> starts_with ~prefix:"gzip" enc
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
    Server.respond ~headers ~status:`Moved_permanently ~body:Cohttp_lwt__.Body.empty ()
  end

let _redirect ~conf conn req body =
  let uri  = Request.uri req in
  let meth = Request.meth req in
  match meth, Uri.path uri with
  | `GET, "/" | `GET, "/index.html" | `GET, "/cerberus" | `GET, "/cerberus/index.html" ->
    let headers = Cohttp.Header.of_list [("Location", "https:" ^ Uri.to_string uri)] in
    Server.respond ~headers ~status:`Moved_permanently ~body:Cohttp_lwt__.Body.empty ()
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
        ~callback: (request ~conf) () in
    Lwt_main.run @@ Lwt.join
      [ Server.create ~mode:(`TCP (`Port webconf.tcp_port)) http_server ]
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
  Arg.(value & pos 0 string (Sys.getenv "PWD") & info [] ~docv:"PUBLIC" ~doc)

let config =
  let doc = "Configuration file in JSON. \
             This file overwrites any other command line option." in
  Arg.(value & opt string "config.json" & info ["c"; "config"] ~docv:"CONFIG" ~doc)

let port =
  let doc = "Set TCP port." in
  Arg.(value & opt int 80 & info ["p"; "port"] ~docv:"PORT" ~doc)

let () =
  let server = Term.(const setup $ config $ cerb_debug_level $ debug_level
                     $ timeout $ impl $ port $ docroot) in
  let info = Cmd.info "web" ~doc:"Web server frontend for Cerberus." in
  Stdlib.exit @@ Cmd.eval (Cmd.v info server)
