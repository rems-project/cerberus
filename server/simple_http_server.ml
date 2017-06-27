(* Based on cohttp_server_async example *)

open Lwt
open Cohttp
open Cohttp_lwt_unix
open Printf
open Unix

let html_of_not_found path =
  sprintf "<html><body>\
           <h2>Not Found</h2><p><b>%s</b> was not found on this server</p>\
           <hr />\
           </body></html>" path

let html_of_forbidden path =
  sprintf "<html><body>\
         <h2>Forbidden</h2>\
         <p><b>%s</b> is not a normal file</p>\
         <hr/>\
         </body></html>"
  path

let html_of_method_not_allowed meth allowed path =
  sprintf
    "<html><body>\
     <h2>Method Not Allowed</h2>\
     <p><b>%s</b> is not an allowed method on <b>%s</b>\
     </p><p>Allowed methods on <b>%s</b> are <b>%s</b></p>\
     <hr />\
     </body></html>"
    meth path path allowed

let serve ~docroot uri path =
  catch (fun () ->
      let file_name = Server.resolve_local_file ~docroot ~uri in
      match (stat file_name).st_kind with
      | S_REG -> Server.respond_file file_name ()
      | _ ->
        if file_name = "../public/" then
          Server.respond_file "../public/index.html" ()
        else
          Server.respond_string
               ~status:`Forbidden
               ~body:(html_of_forbidden path) ()
    )(function
      | Unix_error (ENOENT,_,_) ->
        Server.respond_string
           ~status:`Forbidden
           ~body:(html_of_not_found path) ()
      | e -> fail e
    )

let handler docroot _ req _ =
  let uri = Request.uri req in
  let meth = Request.meth req in
  let str_meth = Code.string_of_method meth in
  let path = Uri.path uri in
  printf "%s %s!" str_meth path;
  match meth with
  | (`GET | `HEAD) ->
    serve ~docroot uri path
    >>= fun (res, body) ->
    begin match meth with
      | `HEAD -> return (res, `Empty)
      | _ -> return (res, body)
    end
  | _ ->
    let allowed = "GET, HEAD" in
    Server.respond_string
      ~headers:(Header.of_list ["allow", allowed])
      ~status:`Method_not_allowed
      ~body:(html_of_method_not_allowed str_meth allowed path) ()

(* TODO: port and docroot should be set as arguments *)
let _ =
  Server.make ~callback:(handler "../public") ()
  |> Server.create ~mode:(`TCP (`Port 8000))
  |> Lwt_main.run