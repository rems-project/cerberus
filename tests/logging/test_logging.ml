let debug src msg = Logs.debug ~src (fun m -> m "%s" (msg ()))

let check condition msg = if not condition then failwith msg
let get = function Ok x -> x | Error msg -> failwith msg
let alpha_source = Logs.Src.create "Alpha.parse"
let beta_source = Logs.Src.create "Beta.parse"
let never () = failwith "disabled message was evaluated"

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

let test_gates () =
  Logs.set_level ~all:true (Some Logs.Warning);
  debug alpha_source never;
  Cerb_log.info alpha_source never;
  Logs.debug ~src:alpha_source (fun _ -> failwith "native disabled message evaluated");
  Logs.Src.set_level alpha_source None;
  Cerb_log.warn alpha_source never;
  Cerb_log.err alpha_source never;
  Logs.set_level ~all:true (Some Logs.Debug)

let test_json () = with_file Cerb_log.Json (fun filename _ close ->
  let text = "quote: \"; slash: \\; tab:\t; newline:\n; nul:\000; λ" in
  debug alpha_source (fun () -> text);
  Logs.debug ~src:alpha_source (fun m ->
    m ~tags:Logs.Tag.(add Cerb_log.location_tag "input.c:12" empty) "located");
  Logs.info ~src:beta_source (fun m ->
    m ~tags:Logs.Tag.(add Cerb_log.translation_unit_tag "b.c" empty) "bound");
  Cerb_log.warn alpha_source (fun () -> "warning");
  Cerb_log.err alpha_source (fun () -> "error");
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
      check (bound |> member "translation_unit" |> to_string = "b.c") "explicit TU tag";
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
  (* A nested logger must not deadlock on the output mutex. *)
  debug alpha (fun () -> debug beta (fun () -> "inner"); "outer");
  close ();
  let reporter2, close2 = get (Cerb_log.open_reporter (File filename) Text) in
  reporter2.Logs.report Logs.default Logs.Info ~over:(fun () -> ()) (fun () -> ())
    (fun m -> m "appended");
  close2 ();
  check (List.length (lines filename) = 4) "text output, exception recovery and append";
  check (List.hd (lines filename) = "[info] application [header]: message") "text format";
  check (Result.is_error (Cerb_log.open_reporter (File (filename ^ "/missing")) Text)) "open error")

let test_threads () = with_file Cerb_log.Json (fun filename _ close ->
  let alpha = alpha_source in
  let worker id () =
    for i = 1 to 300 do
      debug alpha (fun () -> Printf.sprintf "%d:%d\n%s" id i (String.make 1024 'x'))
    done in
  let threads = List.init 8 (fun id -> Thread.create (worker id) ()) in
  List.iter Thread.join threads;
  close ();
  let messages = List.map (fun line -> Yojson.Basic.Util.(Yojson.Basic.from_string line |> member "message" |> to_string)) (lines filename) in
  check (List.length messages = 2400) "thread event count";
  check (List.length (List.sort_uniq String.compare messages) = 2400) "thread event integrity")

let test_formats () = with_file Cerb_log.Json (fun filename reporter close ->
  let log msgf = reporter.Logs.report Logs.default Logs.Debug
      ~over:(fun () -> ()) (fun () -> ()) msgf in
  log (fun m -> m "%s" "raw\nstring");
  log (fun m -> m "%8s" "padded");
  log (fun m -> m "%s:%04d" "mixed" 7);
  log (fun m -> m "%S" "quoted\nstring");
  log (fun m -> m "@[<h>%a@ %s@]" Format.pp_print_int 42 "printer");
  begin try log (fun m -> m "%a" (fun _ () -> failwith "format printer") ()); assert false
    with Failure msg when msg = "format printer" -> () end;
  log (fun m -> m "constant");
  close ();
  let messages = List.map (fun line ->
    Yojson.Basic.Util.(Yojson.Basic.from_string line |> member "message" |> to_string)) (lines filename) in
  check (messages = ["raw\nstring"; "  padded"; "mixed:0007"; "\"quoted\\nstring\"";
                     "42 printer"; "constant"]) "plain strings and general Format behavior")

let test_late_source () = with_file Cerb_log.Text (fun filename late close_late ->
  let source = Logs.Src.create "Late.parse" in
  let early, close_early = get (Cerb_log.open_reporter (File filename) Text) in
  Fun.protect ~finally:close_early (fun () ->
    let log reporter level = reporter.Logs.report source level
      ~over:(fun () -> ()) (fun () -> ()) (fun m -> m "%s" "message") in
    let levels = [Logs.App; Logs.Error; Logs.Warning; Logs.Info; Logs.Debug] in
    List.iter (log late) levels;
    List.iter (log early) levels;
    (* Registration order must not leave one reporter rebuilding prefixes on
       every call. Compare allocations, not machine-dependent elapsed time. *)
    let allocated reporter =
      let before = Gc.allocated_bytes () in
      for _ = 1 to 100 do log reporter Logs.Debug done;
      Gc.allocated_bytes () -. before in
    let late_bytes = allocated late in
    let early_bytes = allocated early in
    check (late_bytes = early_bytes) "late sources retain their text prefixes";
    close_late (); close_early ();
    let expected = List.map (fun level ->
      "[" ^ Logs.level_to_string (Some level) ^ "] Late.parse: message") levels in
    let first_ten = List.filteri (fun i _ -> i < 10) (lines filename) in
    check (first_ten = expected @ expected) "late source prefixes at every level"))

let () =
  test_gates (); test_json (); test_reporter (); test_threads (); test_formats ();
  test_late_source ();
  print_endline "logging tests passed"
