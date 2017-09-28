(* Based on cohttp_server_async example *)

open Lwt
open Cohttp_lwt_unix

open Cohttp_lwt_body

type json =
  | JSONVal   of string
  | JSONArray of json list
  | JSONMap   of (string * json) list

let in_quotes s = "\"" ^ String.escaped s ^ "\""

let rec in_commas f = function
  | []    -> ""
  | [x]   -> f x
  | x::xs -> f x ^ ", " ^ in_commas f xs

let rec string_of_json = function
  | JSONVal   v  -> in_quotes v
  | JSONArray vs -> "[" ^ in_commas string_of_json vs ^ "]"
  | JSONMap   vs ->
    "{" ^ in_commas (fun (k,v) -> in_quotes k ^ ":" ^ string_of_json v) vs ^ "}"

let load_file f =
  let ic  = open_in f in
  let n   = in_channel_length ic in
  let res = Bytes.create n in
  really_input ic res 0 n;
  close_in ic;
  Bytes.to_string res

let run_cerberus args content =
  let source = Filename.temp_file "source" ".c" in
  let output = Filename.temp_file "output" ".core" in
  let sfile = open_out source in
  let cmd = Printf.sprintf "cerberus %s %s > %s 2>&1" args source output in
  output_string sfile content; close_out sfile;
  let res = Sys.command cmd in
  let headers = Cohttp.Header.of_list ["cerberus", string_of_int res] in
  (Server.respond_file ~headers) output ()

let pp_result tmpfile =
  let f = Filename.chop_extension (Filename.basename tmpfile) in
  JSONMap [
    ("cabs", JSONVal (load_file (f ^ ".cabs")));
    ("ail",  JSONVal (load_file (f ^ ".ail")));
    ("core", JSONVal (load_file (f ^ ".core")))
  ]

let pp_cerberus content =
  let source = Filename.temp_file "source" ".c" in
  let output = Filename.temp_file "output" ".res" in
  let sfile = open_out source in
  let cmd =
    Printf.sprintf
      "cerberus --pp=cabs,ail,core --pp_flags=annot,fout %s 2> %s"
      source output
  in
  output_string sfile content; close_out sfile;
  let res = Sys.command cmd in
  let headers = Cohttp.Header.of_list [("cerberus", string_of_int res); ("content-type", "application/json")] in
  if res = 0 then
    (Server.respond_string ~headers) `OK (string_of_json (pp_result source)) ()
  else
    (Server.respond_file ~headers) output ()


let create_graph content =
  ignore (run_cerberus "--exec --rewrite --mode=exhaustive --graph" content);
  (*let res = Sys.command "dot -Tsvg graph.dot -o graph.svg" in*)
  let headers = Cohttp.Header.of_list ["cerberus", "0"] in
  (Server.respond_file ~headers) "cerb.json" ()

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
    | "/exhaustive" -> run_cerberus "--exec --batch --mode=exhaustive" content
    | "/random" -> run_cerberus "--exec --batch" content
    | "/cabs" -> run_cerberus "--pp=cabs --pp_annotated" content
    | "/ail" -> run_cerberus "--pp=ail --pp_annotated" content
    | "/core" -> run_cerberus "--pp=core --pp_annotated" content
    | "/graph" -> create_graph content
    | "/elab"  -> pp_cerberus content
    | _ -> forbidden path
  in catch try_with (fun _ -> forbidden path)

let handler docroot conn req body =
  let _ =
    let oc = open_out_gen [Open_append; Open_creat; Open_text] 0o666 "log" in
    Printf.fprintf oc "%s\n"
      (Sexplib.Sexp.to_string (Request.sexp_of_t req));
    close_out oc
  in
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