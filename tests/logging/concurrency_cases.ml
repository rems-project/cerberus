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
  | Logs.Warning -> Cerb_log.warn_string raw message
  | Logs.Error -> Cerb_log.err_string raw message
  | _ -> assert false

let concurrent_misses ~run_workers literals =
  (* Distinct static addresses normalize to one enabled or disabled name. *)
  let enabled = [|"Concurrent_misses.enabled"; "Concurrent_misses.enabled.local";
                  "Concurrent_misses.enabled.(fun)"; "Concurrent_misses.enabled.other"|] in
  let disabled = [|"Concurrent_misses.disabled"; "Concurrent_misses.disabled.local"|] in
  let before = count_sources () in
  let events = Atomic.make 0 in
  let previous = Logs.reporter () in
  Logs.set_reporter {Logs.report = fun src level ~over k msgf ->
    check (Logs.Src.name src = "Concurrent_misses.enabled" && level = Logs.Debug)
      "wrong source published during concurrent admission";
    msgf (fun ?header:_ ?tags:_ fmt -> Format.kasprintf (fun _ ->
      Atomic.incr events; over (); k ()) fmt)};
  Fun.protect ~finally:(fun () -> Logs.set_reporter previous) (fun () ->
    for _ = 1 to 8 do
      configure ["Concurrent_misses.enabled"];
      let worker id =
        Array.iter (fun raw ->
          Cerb_log.debug raw (fun _ -> never ());
          Cerb_log.debug enabled.(id mod Array.length enabled) (fun m -> m "event");
          Cerb_log.debug_string disabled.(id mod Array.length disabled) never) literals in
      run_workers 8 worker;
      check (count_sources () = before + 1) "concurrent aliases registered duplicate sources";
      let names = List.filter (String.starts_with ~prefix:"Concurrent_misses.")
        (Cerb_log.sources ()) in
      check (names = ["Concurrent_misses.disabled"; "Concurrent_misses.enabled"])
        "concurrent positive or negative decisions missing from discovery"
    done;
    check (Atomic.get events = 8 * 8 * Array.length literals) "concurrent admission lost events")

let concurrent_severities ~run_workers () =
  Cerb_log.configure (Some Logs.Warning) ["Missing.fn"];
  let names = [|"Concurrent_severity.target"; "Concurrent_severity.target.local";
                "Concurrent_severity.target.(fun)"; "Concurrent_severity.target.other"|] in
  let before = count_sources () in
  let events = Atomic.make 0 in
  let previous = Logs.reporter () in
  Logs.set_reporter {Logs.report = fun src level ~over k msgf ->
    check (Logs.Src.name src = "Concurrent_severity.target" &&
           Logs.Src.level src = Some Logs.Warning && level <> Logs.Debug)
      "wrong source or threshold published";
    msgf (fun ?header:_ ?tags:_ fmt -> Format.kasprintf (fun _ ->
      Atomic.incr events; over (); k ()) fmt)};
  Fun.protect ~finally:(fun () -> Logs.set_reporter previous) (fun () ->
    (* Start every address with a rejected Debug call. Warning/Error workers
       then race to attach sources to already-published entries. *)
    Array.iter (fun raw -> Cerb_log.debug_string raw never) names;
    check (count_sources () = before) "rejected first calls registered a source";
    run_workers 8 (fun id ->
      let raw = names.(id mod Array.length names) in
      let order = if id mod 2 = 0 then [Logs.Debug; Logs.Warning; Logs.Error]
        else [Logs.Error; Logs.Warning; Logs.Debug] in
      for _ = 1 to 200 do
        List.iter (fun level -> emit level raw
          (if level = Logs.Debug then never else fun emit -> emit "event")) order
      done);
    check (count_sources () = before + 1) "concurrent severities duplicated a source";
    check (Atomic.get events = 8 * 200 * 2) "concurrent diagnostics lost events")
