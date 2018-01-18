open Lwt
open Cohttp_lwt_unix

(* Util *)

let debug = ignore
(* let debug = perr_endline *)

let timeout d f =
  let try_with () =
    Lwt.pick [
      Lwt_unix.timeout d;
      f >|= fun v -> Some v;
    ]
  in catch try_with (fun _ -> Lwt.return None)

(* Server responses *)

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
    debug ("GET " ^ path);
    match path with
    | "/elab_rewrite" ->
      (*ignore (Pipeline.c_frontend conf "public/buffer.c");*) forbidden path
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
    (*let conf = Pipeline.setup () in *)
    Server.make ~callback:(main () Sys.argv.(1)) ()
    |> Server.create ~mode:(`TCP (`Port port))
    |> Lwt_main.run
