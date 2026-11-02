let check condition reason = if not condition then failwith reason
let never _ = failwith "disabled message evaluated"
let count_sources () = List.length (Logs.Src.list ())
let emit level raw message = match level with
  | Logs.Debug -> Cerb_log.debug_string raw message
  | Logs.Info -> Cerb_log.info raw (fun m -> message (m "%s"))
  | Logs.Warning -> Cerb_log.warn_string raw message
  | Logs.Error -> Cerb_log.err_string raw message
  | _ -> assert false

let with_events f =
  let events = ref [] in
  let previous = Logs.reporter () in
  Logs.set_reporter {Logs.report = fun src level ~over k msgf ->
    msgf (fun ?header:_ ?tags:_ fmt -> Format.kasprintf (fun message ->
      events := (src, level, message) :: !events;
      over (); k ()) fmt)};
  Fun.protect ~finally:(fun () -> Logs.set_reporter previous) (fun () -> f events)

let severity_rules () = with_events (fun events ->
  let open Logs in
  let all = [Debug; Info; Warning; Error] in
  let cases = [
    None, [], [];
    None, ["all"], [];
    Some App, [], [];
    Some Error, [], [Error];
    Some Error, ["Missing.fn"], [Error];
    Some Error, ["Severity.target"], all;
    Some Warning, [], [Warning; Error];
    Some Warning, ["Missing.fn"], [Warning; Error];
    Some Warning, ["Severity"], all;
    Some Info, [], [Info; Warning; Error];
    Some Debug, [], all;
  ] in
  List.iter (fun discover ->
    List.iter (fun (level, selectors, expected) ->
      List.iter (fun order ->
        Cerb_log.configure ~discover level selectors;
        let callbacks = ref 0 in
        (* Repeating through an alias exercises both cache hits and sharing. *)
        List.iter (fun raw ->
          events := [];
          callbacks := 0;
          List.iter (fun severity -> emit severity raw (fun m ->
            incr callbacks; m "message")) order;
          let actual = List.rev !events in
          check (List.map (fun (_, level, _) -> level) actual =
            List.filter (fun level -> List.mem level expected) order)
            "cached decision leaked between severities or policies";
          check (!callbacks = List.length expected) "wrong callback count";
          List.iter (fun (src, _, message) ->
            check (Src.name src = "Severity.target" && message = "message")
              "automatic diagnostic source or message changed") actual;
          match actual with
          | [] -> ()
          | (src, _, _) :: rest ->
              check (List.for_all (fun (other, _, _) -> Src.equal src other) rest)
                "severities did not share a source")
          ["Severity.target"; "Severity.target"; "Severity.target.local"])
        [all; List.rev all]) cases) [false; true])

let no_allocations f =
  f ();
  Gc.full_major ();
  let before = Gc.allocated_bytes () in
  for _ = 1 to 100_000 do f () done;
  check (Gc.allocated_bytes () -. before < 1024.) "disabled calls allocated"

let gates_and_discovery () =
  let heap = Bytes.to_string (Bytes.of_string "Skipped.debug") in
  Cerb_log.configure (Some Logs.Warning) [];
  no_allocations (fun () -> Cerb_log.debug_string heap never);
  no_allocations (fun () -> Cerb_log.info heap never);
  Cerb_log.debug heap never;
  check (not (List.mem "Skipped.debug" (Cerb_log.sources ())))
    "globally disabled Debug resolved its name";
  Cerb_log.warn_string "Gates.warning" (fun m -> m "warning");
  Cerb_log.debug_string heap never;
  Cerb_log.debug_string "Gates.warning" never;
  List.iter (fun log ->
    match log heap never with
    | () -> failwith "active diagnostic accepted a heap string"
    | exception Invalid_argument _ -> ()) [Cerb_log.warn_string; Cerb_log.err_string];
  Cerb_log.configure (Some Logs.Error) [];
  no_allocations (fun () -> Cerb_log.warn_string heap never);
  Cerb_log.configure (Some Logs.Error) ["Missing.fn"];
  let before = count_sources () in
  no_allocations (fun () -> Cerb_log.warn_string "Negative.only_warning" never);
  check (count_sources () = before) "rejected warning registered a source";
  Cerb_log.configure None ["all"];
  no_allocations (fun () ->
    Cerb_log.warn_string heap never; Cerb_log.err_string heap never;
    Cerb_log.info heap never; Cerb_log.debug_string heap never);
  Cerb_log.configure ~discover:true None ["all"];
  Cerb_log.info "Discovery.info_only" never;
  Cerb_log.warn_string "Discovery.warning_only" never;
  Cerb_log.err_string "Discovery.error_only" never;
  check (count_sources () = before) "quiet discovery registered a source";
  let listed = Cerb_log.sources () in
  check (List.mem "Discovery.info_only" listed &&
         List.mem "Discovery.warning_only" listed && List.mem "Discovery.error_only" listed)
    "quiet discovery missed diagnostics";
  Cerb_log.configure None [];
  check (not (List.mem "Discovery.warning_only" (Cerb_log.sources ())))
    "stale diagnostic decisions after reconfiguration"

let callback_contract () = with_events (fun events ->
  let calls = ref 0 in
  Cerb_log.configure (Some Logs.Warning) [];
  Cerb_log.debug_string "Callbacks.conditional" (fun _ -> incr calls);
  check (!calls = 0) "disabled string callback ran";
  Cerb_log.configure (Some Logs.Warning) ["Callbacks"];
  Cerb_log.debug_string "Callbacks.conditional" (fun _ -> incr calls);
  check (!calls = 1 && !events = []) "empty callback emitted a record";
  Cerb_log.debug_string "Callbacks.conditional" (fun m ->
    incr calls; m "first"; m "second");
  check (!calls = 2 && List.map (fun (_, _, text) -> text) (List.rev !events) =
    ["first"; "second"]) "multiple string emissions changed";
  events := [];
  Cerb_log.warn "Callbacks.native" (fun m -> m ~header:"warning" "value=%a" Format.pp_print_int 7);
  Cerb_log.err "Callbacks.native" (fun m -> m "error=%d" 8);
  check (List.map (fun (_, level, text) -> level, text) (List.rev !events) =
    [Logs.Warning, "value=7"; Logs.Error, "error=8"]) "native warning/error formats";
  events := [];
  Cerb_log.configure (Some Logs.Error) [];
  Cerb_log.warn "Callbacks.native" never;
  Cerb_log.warn_string "Callbacks.native" never;
  check (!events = []) "disabled warning emitted";
  Cerb_log.configure None [];
  Cerb_log.err "Callbacks.native" never;
  Cerb_log.err_string "Callbacks.native" never)

let shared_source_level () = with_events (fun events ->
  let name = "Shared_level.target" in
  Cerb_log.configure (Some Logs.Warning) ["Missing.fn"];
  let before = count_sources () in
  Cerb_log.debug_string name never;
  check (count_sources () = before) "Debug rejection registered a source";
  Cerb_log.err_string name (fun m -> m "first enabled call");
  let src = match !events with
    | [(src, Logs.Error, _)] -> src
    | _ -> failwith "source promotion lost the Error" in
  check (Logs.Src.level src = Some Logs.Warning) "first Error changed the function level";
  Cerb_log.warn_string name (fun m -> m "warning");
  Cerb_log.debug_string name never;
  check (List.length !events = 2 && count_sources () = before + 1)
    "source promotion changed filtering or registered twice";
  Cerb_log.configure (Some Logs.Error) ["Shared_level.target"];
  events := [];
  Cerb_log.err_string name (fun m -> m "selected error");
  Cerb_log.debug_string name (fun m -> m "selected debug");
  check (Logs.Src.level src = Some Logs.Debug && List.length !events = 2)
    "selected source adopted the first requested severity")

let () =
  severity_rules ();
  callback_contract ();
  shared_source_level ();
  Logs.set_reporter Logs.nop_reporter;
  gates_and_discovery ();
  Concurrency_cases.concurrent_severities ~run_workers:Concurrency_cases.run_threads ();
  print_endline "Automatic severities: filtering, gates, allocation, discovery and concurrency passed"
