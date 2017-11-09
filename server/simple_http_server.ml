(* Based on cohttp_server_async example *)

open Lwt
open Cohttp_lwt_unix

open Cohttp_lwt_body

(* Util *)

let load_file f =
  try
    let ic  = open_in f in
    let n   = in_channel_length ic in
    let res = Bytes.create n in
    really_input ic res 0 n;
    close_in ic;
    Bytes.to_string res
  with _ -> ""

let write_file f content =
  try
    let oc = open_out f in
    output_string oc content;
    close_out oc;
  with _ -> ()


(* JSON *)

type json =
  | JsonInt   of int
  | JsonStr   of string
  | JsonArray of json list
  | JsonMap   of (string * json) list

(* let json_of_int n = JsonVal (string_of_int n) *)

let json_of_file filename = JsonStr (load_file filename)

let in_quotes s =
  let escaped_no_unicode s =
    String.escaped s
      (* TODO: this is a horrible hack *)
    |> Str.global_replace (Str.regexp "\\\\[0-9]+") ""
  in
  "\"" ^ (escaped_no_unicode s) ^ "\""

let rec in_commas f = function
  | []    -> ""
  | [x]   -> f x
  | x::xs -> f x ^ ", " ^ in_commas f xs

let rec string_of_json = function
  | JsonInt   i  -> string_of_int i
  | JsonStr   s  -> in_quotes s
  | JsonArray vs -> "[" ^ in_commas string_of_json vs ^ "]"
  | JsonMap   vs ->
    "{" ^ in_commas (fun (k,v) -> in_quotes k ^ ":" ^ string_of_json v) vs ^ "}"

(* Location *)

type loc =
  { line: int;
    col:  int;
  }

let mk_loc (l, c) =
  { line= l;
    col=  c;
  }

type loc_range =
  { init:  loc;
    final: loc;
  }

let mk_loc_line_range (l0, l) =
  { init=  mk_loc (l0, 0);
    final= mk_loc (l,  0);
  }

let loc_range_cmp l1 l2 =
  if l1.init.line = l2.init.line then
    if l1.final.line = l2.final.line then
      if l1.init.col = l2.init.col then
        l1.final.col - l2.final.col
      else l1.init.col - l2.init.col
    else l1.final.line - l2.final.line
  else l1.init.line - l2.init.line

(* Parse location markers: {-#dd:dd-dd:dd:#-} *)
let parse_loc str =
  match List.map int_of_string (Str.split (Str.regexp "[{}#:-]+") str) with
  | [il; ic; fi; fc] ->
    { init=  mk_loc (il-1, ic-1);
      final= mk_loc (fi-1, fc-1);
    }
  | _ -> raise (Failure "get_c_locs: wrong format")

let json_of_loc l =
  JsonMap [("line", JsonInt l.line); ("ch", JsonInt l.col)]

let json_of_loc_range l =
  JsonMap [("begin", json_of_loc l.init); ("end", json_of_loc l.final)]

(* Retrieve locations in core *)

let count_lines str =
  let n = ref 0 in
  String.iter (fun c -> if c == '\n' then n := !n + 1) str; !n

(* Stack using lists *)
let push sp x = x::sp

let pop = function
  | x::sp -> (x, sp)
  | [] -> raise (Failure "popping an empty stack")

let parse_core_locs core =
  (* chunks - of core source
   * locs   - pair of c location and core location
   * sp     - stack of visited location marks
   * l0     - line of last visited location mark
   * l      - current line
   **)
  let rec loop (chunks, locs) sp l0 l = function
    | [] -> (String.concat "" (List.rev chunks), locs)
    | res::rest -> match res with
      (* if chunk, add to chunks *)
      | Str.Text chunk ->
        loop (chunk::chunks, locs) sp l0 (l+(count_lines chunk)) rest
      (* if location mark then ... *)
      | Str.Delim loc  ->
        (* if end mark then pop last location and save it in locs *)
        if String.compare loc "{-#ELOC#-}" = 0 then
          let ((c_loc, l0'), sp') = pop sp in
            loop (chunks, (c_loc, mk_loc_line_range (l0, l))::locs) sp' l0' l rest
        (* otherwise push to stack *)
        else
          let loc_no_unicode = Str.replace_first (Str.regexp_string "§") "" loc in
          loop (chunks, locs) (push sp (parse_loc loc_no_unicode, l0)) l l rest
  in
  Str.full_split (Str.regexp "{-#[^#§]*#-}") core
  |> loop ([], []) [] 0 0

let parse_cabs_locs cabs =
  let rec loop locs l = function
    | [] -> locs
    | res::rest ->
      if Str.string_match (Str.regexp "<.*>") res 0 then
        loop ((Str.matched_string res, l)::locs) (l+1) rest
      else loop locs (l+1) rest
  in
  Str.split (Str.regexp "[\n]+") cabs
  |> loop [] 1


let json_of_locs locs=
  List.fold_left (
    fun (jss, i) (cloc, coreloc) ->
      let js = JsonMap [
          ("c", json_of_loc_range cloc);
          ("core", json_of_loc_range coreloc);
          ("color", JsonInt i);
        ]
      in (js::jss, i+1)
  ) ([], 1) locs
  |> fst

let mk_result file out err =
  let f = Filename.chop_extension (Filename.basename file) in
  let (core, locs) = parse_core_locs (load_file (f ^ ".core")) in
  let sorted_locs  =
    List.sort (fun ls1 ls2 -> loc_range_cmp (fst ls1) (fst ls2)) locs
  in
  let elim_paragraph_sym = Str.global_replace (Str.regexp_string "§") "" in
  let result =
    JsonMap [
      ("cabs", json_of_file (f ^ ".cabs"));
      ("ail",  JsonStr (elim_paragraph_sym (load_file (f ^ ".ail"))));
      ("core", JsonStr (elim_paragraph_sym core));
      ("locs", JsonArray (json_of_locs sorted_locs));
      ("stdout", json_of_file out);
      ("stderr", json_of_file err);
    ] |> string_of_json
  in
  ignore (Sys.command "rm -f *.{cabs,ail,core}"); (* clean results *)
  print_endline err;
  print_endline (string_of_json (json_of_file err));
  result

(* Cerberus interaction *)

let elab_rewrite =
  Printf.sprintf
    "cerberus --pp=cabs,ail,core --rewrite --pp_flags=annot,fout %s > %s 2> %s"

let elab =
  Printf.sprintf
    "cerberus --pp=cabs,ail,core --pp_flags=annot,fout %s > %s 2> %s"

let run mode =
  Printf.sprintf
    "cerberus --exec --batch --mode=%s                    \
     --pp=cabs,ail,core --pp_flags=annot,fout %s > %s 2> %s"
  mode

let cerberus f content =
  let source  = Filename.temp_file "source" ".c" in
  let out     = Filename.temp_file "out" ".res" in
  let err     = Filename.temp_file "err" ".res" in
  let headers = Cohttp.Header.of_list [("content-type", "application/json")] in
  let respond str = (Server.respond_string ~headers) `OK str () in
  write_file source content;
  ignore (Sys.command (f source out err));
  respond (mk_result source out err)

(* TODO: not being used *)
let create_graph content =
  ignore (cerberus (run "--exec --rewrite --mode=exhaustive --graph") content);
  (*let res = Sys.command "dot -Tsvg graph.dot -o graph.svg" in*)
  let headers = Cohttp.Header.of_list ["cerberus", "0"] in
  (Server.respond_file ~headers) "cerb.json" ()

(* Server reponses *)

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
    | "/exhaustive" -> cerberus (run "exhaustive") content
    | "/random" -> cerberus (run "random") content
    | "/graph" -> create_graph content
    | "/elab_rewrite"  -> cerberus elab_rewrite content
    | "/elab"  -> cerberus elab content
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