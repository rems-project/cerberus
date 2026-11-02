(* The same assertions run on real systhreads and, separately, OCaml 5
   domains. Always join every worker before propagating a failure or changing
   the shared logging policy. Systhreads must yield while waiting at barriers. *)
let run_workers ~spawn ~join ~relax count f =
  let ready = Atomic.make 0 and start = Atomic.make false in
  let failures = Array.make count None in
  let workers = Array.init count (fun id -> spawn (fun () ->
    Atomic.incr ready;
    while not (Atomic.get start) do relax () done;
    try f id with exn ->
      failures.(id) <- Some (exn, Printexc.get_raw_backtrace ()))) in
  while Atomic.get ready <> count do relax () done;
  Atomic.set start true;
  Array.iter join workers;
  Array.iter (function
    | None -> ()
    | Some (exn, trace) -> Printexc.raise_with_backtrace exn trace) failures

let run_threads count f =
  run_workers ~spawn:(fun f -> Thread.create f ()) ~join:Thread.join
    ~relax:Thread.yield count f

let check condition reason = if not condition then failwith reason
let never _ = failwith "disabled callback evaluated"
let configure selectors = Cerb_log.configure (Some Logs.Warning) selectors
let count_sources () = List.length (Logs.Src.list ())
let emit level raw message = match level with
  | Logs.Debug -> Cerb_log.debug_string raw message
  | Logs.Info -> Cerb_log.info raw (fun m -> message (m "%s"))
  | Logs.Warning -> Cerb_log.warn_string raw message
  | Logs.Error -> Cerb_log.err_string raw message
  | _ -> assert false

let concurrent_misses ~run_workers () =
  (* Distinct static names normalize to one enabled or disabled source. *)
  let enabled = [|"Concurrent.enabled"; "Concurrent.enabled.local"|] in
  let disabled = [|"Concurrent.disabled"; "Concurrent.disabled.local"|] in
  let before = count_sources () in
  let events = Atomic.make 0 in
  let previous = Logs.reporter () in
  Logs.set_reporter {Logs.report = fun src level ~over k msgf ->
    check (Logs.Src.name src = "Concurrent.enabled" && level = Logs.Debug)
      "wrong source published during concurrent admission";
    msgf (fun ?header:_ ?tags:_ fmt -> Format.kasprintf (fun _ ->
      Atomic.incr events; over (); k ()) fmt)};
  Fun.protect ~finally:(fun () -> Logs.set_reporter previous) (fun () ->
    for _ = 1 to 4 do
      configure ["Concurrent.enabled"];
      run_workers 8 (fun id ->
        for _ = 1 to 32 do
          Cerb_log.debug enabled.(id mod 2) (fun m -> m "event");
          Cerb_log.debug_string disabled.(id mod 2) never
        done);
      check (count_sources () = before + 1) "concurrent aliases registered duplicate sources";
      let names = List.filter (String.starts_with ~prefix:"Concurrent.") (Cerb_log.sources ()) in
      check (names = ["Concurrent.disabled"; "Concurrent.enabled"])
        "concurrent positive or negative names missing from discovery"
    done;
    check (Atomic.get events = 4 * 8 * 32) "concurrent admission lost events")

let concurrent_severities ~run_workers () =
  Cerb_log.configure (Some Logs.Warning) ["Missing.fn"];
  let names = [|"Concurrent_severity.target"; "Concurrent_severity.target.local";
                "Concurrent_severity.target.(fun)"; "Concurrent_severity.target.other"|] in
  let before = count_sources () in
  let events = Atomic.make 0 in
  let previous = Logs.reporter () in
  Logs.set_reporter {Logs.report = fun src level ~over k msgf ->
    check (Logs.Src.name src = "Concurrent_severity.target" &&
           Logs.Src.level src = Some Logs.Warning &&
           (level = Logs.Warning || level = Logs.Error))
      "wrong source or threshold published";
    msgf (fun ?header:_ ?tags:_ fmt -> Format.kasprintf (fun _ ->
      Atomic.incr events; over (); k ()) fmt)};
  Fun.protect ~finally:(fun () -> Logs.set_reporter previous) (fun () ->
    (* Reject Debug first, then race Warning/Error registration for these names. *)
    Array.iter (fun raw -> Cerb_log.debug_string raw never) names;
    check (count_sources () = before) "rejected first calls registered a source";
    run_workers 8 (fun id ->
      let raw = names.(id mod Array.length names) in
      let order = if id mod 2 = 0 then [Logs.Debug; Logs.Info; Logs.Warning; Logs.Error]
        else [Logs.Error; Logs.Warning; Logs.Info; Logs.Debug] in
      for _ = 1 to 32 do
        List.iter (fun level -> emit level raw
          (if level = Logs.Debug || level = Logs.Info then never else fun m -> m "event")) order
      done);
    check (count_sources () = before + 1) "concurrent severities duplicated a source";
    check (Atomic.get events = 8 * 32 * 2) "concurrent diagnostics lost events")

let concurrent_output ~run_workers () =
  let path = Filename.temp_file "cerberus-concurrent" ".log" in
  let reporter, close = match Cerb_log.open_reporter (File path) Json with
    | Ok result -> result | Error msg -> failwith msg in
  (* A source created after the reporter is shared by all workers. *)
  let src = Logs.Src.create "Concurrent_output.run" in
  Fun.protect ~finally:(fun () -> close (); Sys.remove path) (fun () ->
    let message id i = Printf.sprintf "%d:%d %s" id i (String.make 1024 'x') in
    run_workers 8 (fun id ->
      for i = 0 to 63 do
        reporter.Logs.report src Logs.Debug ~over:(fun () -> ()) (fun () -> ())
          (fun m -> m "%s" (message id i))
      done);
    close ();
    let channel = open_in path in
    let actual = Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
      let rec read acc = match input_line channel with
        | line ->
            let open Yojson.Basic.Util in
            let event = Yojson.Basic.from_string line in
            check (event |> member "source" |> to_string = "Concurrent_output.run")
              "concurrent source metadata";
            read ((event |> member "message" |> to_string) :: acc)
        | exception End_of_file -> acc in
      read []) in
    let expected = List.init 8 (fun id -> List.init 64 (message id)) |> List.concat in
    check (List.sort String.compare actual = List.sort String.compare expected)
      "concurrent records were lost, duplicated or interleaved")
