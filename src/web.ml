open Lwt
open Cohttp_lwt_unix
open Cohttp_lwt_body

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

(* Get method *)
let get ~docroot uri path =
  forbidden path

let main docroot conn req body =
  let uri = Request.uri req in
  let path = Uri.path uri in
  get ~docroot uri path

let _ =
  if Array.length Sys.argv != 3 then
    Printf.printf "usage: %s [public] [port]\n" Sys.argv.(0)
  else
    let port = int_of_string Sys.argv.(2) in
    Server.make ~callback:(main Sys.argv.(1)) ()
    |> Server.create ~mode:(`TCP (`Port port))
    |> Lwt_main.run
