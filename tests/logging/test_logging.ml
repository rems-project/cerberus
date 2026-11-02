let debug src msg = Logs.debug ~src (fun m -> m "%s" (msg ()))

let check condition msg = if not condition then failwith msg
let get = function Ok x -> x | Error msg -> failwith msg
let alpha_source = Logs.Src.create "Alpha.parse"
let beta_source = Logs.Src.create "Beta.parse"
let context_tag = Logs.Tag.def "context" Format.pp_print_string

let lines path =
  let ic = open_in path in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
    let rec loop acc =
      match input_line ic with
      | line -> loop (line :: acc)
      | exception End_of_file -> List.rev acc in
    loop [])

let with_file format f =
  let path = Filename.temp_file "cerberus-logging" ".log" in
  let reporter, close = get (Cerb_log.open_reporter (File path) format) in
  let previous = Logs.reporter () in
  Logs.set_reporter reporter;
  Fun.protect ~finally:(fun () -> Logs.set_reporter previous; close (); Sys.remove path)
    (fun () -> f path reporter close)

let test_json () = with_file Cerb_log.Json (fun filename _ close ->
  let text = "quote: \"; slash: \\; tab:\t; newline:\n; nul:\000; λ" in
  debug alpha_source (fun () -> text);
  Logs.debug ~src:alpha_source (fun m ->
    m ~tags:Logs.Tag.(add Cerb_log.location_tag "input.c:12" empty) "located");
  Logs.info ~src:beta_source (fun m ->
    m ~tags:Logs.Tag.(add context_tag "test input" empty) "bound");
  Logs.warn ~src:alpha_source (fun m -> m "warning");
  Logs.err ~src:alpha_source (fun m -> m "error");
  close (); close ();
  let open Yojson.Basic.Util in
  match List.map Yojson.Basic.from_string (lines filename) with
  | [debug; located; bound; warning; error] ->
      check (debug |> member "message" |> to_string = text) "JSON string round trip";
      check (debug |> member "verbosity" = `Null) "no numeric verbosity";
      check (debug |> member "schema_version" |> to_int = 1) "schema version";
      check (debug |> member "source" |> to_string = "Alpha.parse") "qualified source";
      check (debug |> member "module" |> to_string = "Alpha") "module metadata";
      check (debug |> member "function" |> to_string = "parse") "function metadata";
      check (located |> member "location" |> to_string = "input.c:12") "location metadata";
      check (bound |> member "tags" |> member "context" |> to_string = "test input")
        "custom tag";
      check (warning |> member "level" |> to_string = "warning") "warning severity";
      check (error |> member "level" |> to_string = "error") "error severity"
  | _ -> failwith "unexpected JSON event count")

let test_reporter () = with_file Cerb_log.Text (fun filename reporter close ->
  let over_count = ref 0 and k_count = ref 0 in
  let value = reporter.Logs.report Logs.default Logs.Info
      ~over:(fun () -> incr over_count) (fun () -> incr k_count; 42)
      (fun m -> m ~header:"header" "%s" "message") in
  check (value = 42 && !over_count = 1 && !k_count = 1) "reporter continuation contract";
  let alpha = alpha_source in
  let beta = beta_source in
  begin try debug alpha (fun () -> failwith "printer"); assert false
    with Failure msg when msg = "printer" -> () end;
  (* Message formatting may itself log another message. *)
  debug alpha (fun () -> debug beta (fun () -> "inner"); "outer");
  close ();
  (* Writes after close must consistently fail; close stays idempotent. *)
  for _ = 1 to 2 do
    match reporter.Logs.report alpha Logs.Debug
        ~over:(fun () -> ()) (fun () -> ()) (fun m -> m "closed") with
    | () -> failwith "write after close accepted"
    | exception Invalid_argument _ -> ()
  done;
  close ();
  let reporter2, close2 = get (Cerb_log.open_reporter (File filename) Text) in
  reporter2.Logs.report Logs.default Logs.Info ~over:(fun () -> ()) (fun () -> ())
    (fun m -> m "appended");
  close2 ();
  check (List.length (lines filename) = 4) "text output, exception recovery and append";
  check (List.hd (lines filename) = "[info] application [header]: message") "text format";
  check (Result.is_error (Cerb_log.open_reporter (File (filename ^ "/missing")) Text)) "open error")

let test_located_strings () = with_file Cerb_log.Json (fun filename _ close ->
  let loc = Cerb_location.other "input.c:7" in
  Cerb_log.configure (Some Logs.Warning) ["Bridge"];
  Cerb_log.debug_located_string "Bridge.located" loc (fun m -> m "message");
  close ();
  let open Yojson.Basic.Util in
  match List.map Yojson.Basic.from_string (lines filename) with
  | [record] ->
      check (record |> member "location" |> to_string = Cerb_location.location_to_string loc)
        "string bridge lost location metadata"
  | _ -> failwith "located string emission count")

let () =
  Logs.set_level ~all:true (Some Logs.Debug);
  test_json (); test_reporter (); test_located_strings ();
  print_endline "Reporter tests passed"
