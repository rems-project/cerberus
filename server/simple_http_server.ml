(* Based on cohttp_server_async example *)

open Lwt
open Cohttp_lwt_unix

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

let serve ~docroot uri path =
  let try_with () =
    match path with
    | "/" -> Server.respond_file "../public/index.html" ()
    (*| "/run" -> run cerberus *)
    | _ ->
      let fname = Server.resolve_local_file ~docroot ~uri in
      if valid_file fname then Server.respond_file fname ()
      else forbidden path
  in catch try_with (fun _ -> forbidden path)

let handler docroot _ req _ =
  let uri = Request.uri req in
  let meth = Request.meth req in
  let path = Uri.path uri in
  let respond (res, body) =
    match meth with
    | `HEAD -> return (res, `Empty)
    | _ -> return (res, body)
  in
  match meth with
  | (`GET | `HEAD) -> serve ~docroot uri path >>= respond
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