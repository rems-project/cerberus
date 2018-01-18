open Lwt
open Cohttp_lwt_unix

(* Util *)

let debug = ignore
(* let debug = prerr_endline *)

let timeout d f =
  let try_with () =
    Lwt.pick [
      Lwt_unix.timeout d;
      f >|= fun v -> Some v;
    ]
  in catch try_with (fun _ -> Lwt.return None)

(* Initialise pipeline *)

let dummy_io =
  let skip = fun _ -> Exception.except_return ()
  in {
    Pipeline.pass_message=   skip;
    Pipeline.set_progress=   skip;
    Pipeline.run_pp=         (fun _ -> skip);
    Pipeline.print_endline=  skip;
    Pipeline.print_debug=    (fun _ -> skip);
    Pipeline.warn=           skip;
  }

let dummy_conf =
  let cpp_cmd = "cc -E -C -traditional-cpp -nostdinc -undef -D__cerb__ -I "
                ^ Pipeline.cerb_path ^ "/include/c/libc -I "
                ^ Pipeline.cerb_path ^ "/include/c/posix" in
  (* TODO: hack *)
  let impl_filename = "gcc_4.9.0_x86_64-apple-darwin10.8.0" in
  let core_stdlib = Pipeline.load_core_stdlib () in {
  Pipeline.debug_level=         0;
  Pipeline.pprints=             [];
  Pipeline.astprints=           [];
  Pipeline.ppflags=             [];
  Pipeline.typecheck_core=      false;
  Pipeline.rewrite_core=        true;
  Pipeline.sequentialise_core=  true;
  Pipeline.cpp_cmd=             cpp_cmd;
  Pipeline.core_stdlib=         core_stdlib;
  Pipeline.core_impl=           Pipeline.load_core_impl core_stdlib impl_filename;
}

(* Result *)

let string_of_doc d =
  let buf = Buffer.create 1024 in
  PPrint.ToBuffer.pretty 1.0 150 buf d;
  Buffer.contents buf

let result (cabs, ail, core) =
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
    ("stdout",  Json.empty);
    ("stderr",  Json.empty);
  ] |> Json.string_of |> respond

(* Server default responses *)

let forbidden path =
  let body = Printf.sprintf
      "<html><body>\
       <h2>Forbidden</h2>\
       <p><b>%s</b> is forbidden</p>\
       <hr/>\
       </body></html>"
      path
  in Server.respond_string ~status:`Forbidden ~body ()

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

let elab () =
  match Pipeline.c_frontend (dummy_conf, dummy_io) "public/buffer.c" with
  | Exception.Result (Some cabs, Some ail, _, core) ->
    result (cabs, ail, core)
  | _ ->
    forbidden "elab"

let elab_rewrite () =
  let filename = "public/buffer.c" in
  let conf     = (dummy_conf, dummy_io) in
  match Pipeline.c_frontend conf filename with
  | Exception.Result (Some cabs, Some ail, _, core) ->
    begin match Pipeline.core_passes conf ~filename core with
      | Exception.Result core' ->
        result (cabs, ail, core')
      | Exception.Exception (loc, err) ->
        print_endline (Pp_errors.short_message err);
        (*try print_endline (Pp_errors.to_string msg)
        with
        | Failure str ->  print_endline str*)
        forbidden "FAIL"
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
    debug ("GET " ^ path);
    match path with
    | "/" -> Server.respond_file "public/index.html" ()
    | _   -> get_local_file ()
  in catch try_with (fun _ -> debug "GET: fatal error"; forbidden path)

let post ~docroot uri path conf content =
  let try_with () =
    debug ("POST " ^ path);
    match path with
    | "/elab" -> elab ()
    | "/elab_rewrite" -> elab_rewrite ()
    | _ -> forbidden path
  in catch try_with (fun e -> debug "POST: fatal error"; forbidden path)

(* Main *)

let main conf docroot conn req body =
  let uri  = Request.uri req in
  let meth = Request.meth req in
  let path = Uri.path uri in
  match meth with
  | `HEAD -> get ~docroot uri path >|= fun (res, _) -> (res, `Empty)
  | `GET  -> get ~docroot uri path
  | `POST -> Cohttp_lwt__Body.to_string body >>= post ~docroot uri path conf
  | _     -> not_allowed meth path

let _ =
  if Array.length Sys.argv != 3 then
    Printf.printf "usage: %s [public] [port]\n" Sys.argv.(0)
  else
    let port = int_of_string Sys.argv.(2) in
    Server.make ~callback:(main () Sys.argv.(1)) ()
    |> Server.create ~mode:(`TCP (`Port port))
    |> Lwt_main.run
