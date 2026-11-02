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
  List.iter (fun (level, selectors, expected) ->
    Cerb_log.configure level selectors;
    events := [];
    let callbacks = ref 0 in
    List.iter (fun severity -> emit severity "Severity.target" (fun m ->
      incr callbacks; m "message")) all;
    let actual = List.rev !events in
    check (List.map (fun (_, level, _) -> level) actual = expected) "severity filtering";
    check (!callbacks = List.length expected) "disabled callback evaluated";
    List.iter (fun (src, _, message) ->
      check (Src.name src = "Severity.target" && message = "message")
        "automatic diagnostic source or message changed") actual)
    [None, ["all"], [];
     Some Error, [], [Error];
     Some Warning, ["Missing.fn"], [Warning; Error];
     Some Info, [], [Info; Warning; Error];
     Some Debug, [], all;
     Some Error, ["Severity.target"], all;
     Some Warning, ["Severity"], all])

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
    [Logs.Warning, "value=7"; Logs.Error, "error=8"]) "native warning/error formats")

let () =
  severity_rules (); callback_contract ();
  print_endline "Severity and callback tests passed"
