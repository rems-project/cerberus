open Lwt
open Cohttp_lwt_unix

(* Debugging *)

module Debug =
struct
  let level = ref 0
  let print n msg =
    if !level >= n then Printf.printf "%d: %s\n%!" n msg
  let warn msg = Printf.printf "[WARN]: %s\n%!" msg
  let error msg = Printf.printf "[ERROR]: %s\n%!" msg
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
    tmp
  with _ -> failwith "write_tmp_file"

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

(* Result *)

let string_of_doc d =
  let buf = Buffer.create 1024 in
  PPrint.ToBuffer.pretty 1.0 150 buf d;
  Buffer.contents buf

let success ?(result="") (cabs, ail, core) =
  let headers = Cohttp.Header.of_list [("content-type", "application/json")] in
  let respond str = (Server.respond_string ~flush:true ~headers) `OK str () in
  let elim_paragraph_sym = Str.global_replace (Str.regexp_string "§") "" in
  let json_of_doc d = Json.Str (elim_paragraph_sym (string_of_doc d)) in
  Colour.do_colour := false;
  let pp_core = string_of_doc (Pp_core.All.pp_file core) in
  let (core_str, locs) = Location_mark.extract pp_core in
  Json.Map [
    ("cabs",    json_of_doc (Pp_cabs.pp_translation_unit false false cabs));
    ("ail",     json_of_doc (Pp_ail.pp_program ail));
    ("ail_ast", json_of_doc (Pp_ail_ast.pp_program ail));
    ("core",    Json.Str (elim_paragraph_sym core_str));
    ("locs",    locs);
    ("stdout",  Json.Str result);
    ("stderr",  Json.empty);
  ] |> Json.string_of |> respond

let failure msg =
  let headers = Cohttp.Header.of_list [("content-type", "application/json")] in
  let respond str = (Server.respond_string ~flush:true ~headers) `OK str () in
  Json.Map [
    ("cabs",    Json.empty);
    ("ail",     Json.empty);
    ("ail_ast", Json.empty);
    ("core",    Json.empty);
    ("locs",    Json.empty);
    ("stdout",  Json.empty);
    ("stderr",  Json.Str msg);
  ] |> Json.string_of |> respond

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

(* Cerberus actions *)

let elab_rewrite ~filename ~conf =
  match Pipeline.c_frontend conf filename with
  | Exception.Result (Some cabs, Some ail, _, core) ->
    success (cabs, ail, core)
  | _ ->
    forbidden "elab"

let elab ~filename ~conf =
  match Pipeline.c_frontend conf filename with
  | Exception.Result (Some cabs, Some ail, _, core) ->
    begin match Pipeline.core_passes conf ~filename core with
      | Exception.Result core' ->
        success (cabs, ail, core')
      | Exception.Exception (loc, err) ->
        print_endline (Pp_errors.short_message err);
        forbidden "fail"
    end
  | _ ->
    forbidden "elab_rewrite"

let execute ~filename ~conf =
  match Pipeline.c_frontend conf filename with
  | Exception.Result (Some cabs, Some ail, sym_suppl, core) ->
    begin match Pipeline.core_passes conf ~filename core with
      | Exception.Result core' ->
        begin match Pipeline.interp_backend dummy_io sym_suppl core []
                      true false false `Random with
          | Exception.Result r ->
            success ~result:(string_of_int r) (cabs, ail, core')
          | Exception.Exception (loc, err) ->
            print_endline (Pp_errors.short_message err);
            forbidden "fail"
        end
      | Exception.Exception (loc, err) ->
        print_endline (Pp_errors.short_message err);
        forbidden "fail"
    end
  | _ ->
    forbidden "elab_rewrite"

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
  in catch try_with (fun _ -> Debug.error "GET"; forbidden path)

let post ~docroot ~conf uri path content =
  let try_with () =
    Debug.print 9 ("POST " ^ path);
    let filename = write_tmp_file content in
    match path with
    | "/elab" -> elab ~filename ~conf
    | "/elab_rewrite" -> elab_rewrite ~filename ~conf
    | "/ramdom" -> execute ~filename ~conf
    | _ -> forbidden path
  in catch try_with (fun e -> Debug.error "POST"; forbidden path)

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
  let conf = (setup_cerb_conf cerb_debug_level cpp_cmd impl, dummy_io) in
  Debug_ocaml.debug_level := cerb_debug_level;
  Debug.level := debug_level;
  Server.make ~callback: (request ~docroot ~conf) ()
  |> Server.create ~mode:(`TCP (`Port port))
  |> Lwt_main.run

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
  Arg.(value & opt int 80 & info ["p"; "port"] ~docv:"PORT" ~doc)

let () =
  let server = Term.(pure setup $ cerb_debug_level $ debug_level
                     $ impl $ cpp_cmd $ port $ docroot) in
  let info = Term.info "web" ~doc:"Web server frontend for Cerberus." in
  match Term.eval (server, info) with
  | `Error _ -> exit 1;
  | `Ok _
  | `Version
  | `Help -> exit 0
