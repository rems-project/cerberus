(* Based on cohttp_server_async example *)

open Lwt
open Cohttp_lwt_unix

(* TODO: add a timeout *)
let exec_cerberus ?args:(args="") content =
  let source = Filename.temp_file "source" ".c" in
  let output = Filename.temp_file "output" ".core" in
  let cmd = Printf.sprintf
      "cerberus --exec --batch %s %s &> %s"
      source args output
  in
  let sfile = open_out source in
  output_string sfile content; close_out sfile;
  let res = Sys.command cmd in
  let headers = Cohttp.Header.of_list ["cerberus", string_of_int res] in
  (Server.respond_file ~headers) output ()

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

let valid_file fname =
  match Unix.((stat fname).st_kind) with
  | Unix.S_REG -> true
  | _ -> false

let get ~docroot uri path =
  let try_with () =
    match path with
    | "/" -> Server.respond_file "../public/index.html" ()
    | _ ->
      let fname = Server.resolve_local_file ~docroot ~uri in
      if valid_file fname then Server.respond_file fname ()
      else forbidden path
  in catch try_with (fun _ -> forbidden path)

let post ~docroot uri path content =
  let try_with () =
    match path with
    | "/exhaustive" -> exec_cerberus ~args:"--mode=exhaustive" content
    | "/random" -> exec_cerberus content
    | _ -> forbidden path
  in catch try_with (fun _ -> forbidden path)

let handler docroot conn req body =
  let uri = Request.uri req in
  let meth = Request.meth req in
  let path = Uri.path uri in
  match meth with
  | `HEAD -> get ~docroot uri path >|= fun (res, _) -> (res, `Empty)
  | `GET  -> get ~docroot uri path
  | `POST -> Cohttp_lwt_body.to_string body >>= post ~docroot uri path
  | _ -> not_allowed meth path

let usage () =
  Printf.printf "usage: %s [public] [port]" Sys.argv.(0)

let _ =
  if Array.length Sys.argv != 3 then usage ()
  else
    let port = int_of_string Sys.argv.(2) in
    Server.make ~callback:(handler Sys.argv.(1)) ()
    |> Server.create ~mode:(`TCP (`Port port))
    |> Lwt_main.run