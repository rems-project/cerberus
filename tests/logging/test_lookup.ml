let literals = Array.sub Lookup_literals.names 0 128
let check condition reason = if not condition then failwith reason
let never () = failwith "disabled callback evaluated"
let rejects f = match f () with
  | _ -> failwith "invalid name accepted"
  | exception Invalid_argument _ -> ()
let configure selectors = Cerb_log_auto.configure (Some Logs.Warning) selectors
let count_sources () = List.length (Logs.Src.list ())

let names () =
  let canonical = Cerb_log_names.canonical in
  check (canonical "Cerb_frontend__M.N.fn0.(fun)" = "M.N.fn0") "wrapper and closure";
  check (canonical "Cerb_backend__Pipeline.cpp" = "Pipeline.cpp") "backend wrapper";
  check (canonical "Dune__exe__Absint.assign.aux" = "Absint.assign") "executable wrapper";
  check (canonical "M.fn0.local" = "M.fn0") "nested function";
  check (canonical "M.fn" <> canonical "M.fn0") "digits are significant";
  List.iter (fun s -> rejects (fun () -> canonical s)) [""; "M"; "M."; "M..fn"; "M._"; "fn"];
  List.iter (fun s -> check (not (Cerb_log_names.valid_selector s)) "invalid selector")
    [""; "file:m.lem"; "M*"; "fn"; "m.fn"; "M._"; "M.1fn"; "M..fn"];
  List.iter (fun s -> check (Cerb_log_names.valid_selector s) "valid selector")
    ["M"; "M.N"; "M.N.fn0"; "M._fn"; "M.fn'"];
  let selected = Cerb_log_names.selected ["M.N"; "A.fn0"] in
  check (selected "M.N.fn" && selected "M.N") "exact module";
  check (not (selected "M.Nested.fn") && not (selected "M.N.Sub.fn")) "no prefix/glob matching";
  check (selected "A.fn0" && not (selected "A.fn")) "exact function"

let warm_allocation raw =
  ignore (Cerb_log_auto.debug_enabled raw);
  Gc.full_major ();
  let before = Gc.allocated_bytes () in
  for _ = 1 to 100_000 do ignore (Cerb_log_auto.debug_enabled raw) done;
  let allocated = Gc.allocated_bytes () -. before in
  check (allocated < 1024.) "cached decisions allocated on hits"

let formatted callback =
  Cerb_log_auto.debugf __FUNCTION__ (fun m ->
    callback ();
    m ~header:"native"
      ~tags:Logs.Tag.(add Cerb_log.location_tag "input.c:7" empty)
      "value: %a" Format.pp_print_int 7)

let other_formatted callback =
  Cerb_log_auto.debugf __FUNCTION__ (fun m -> callback (); m "other")

let native_formatted () =
  let before = count_sources () in
  Cerb_log_auto.configure ~discover:true None [];
  formatted never;
  check (count_sources () = before) "native discovery registered a source";
  check (List.mem "Test_lookup.formatted" (Cerb_log_auto.sources ()))
    "native function name missing from discovery";
  check (not (List.mem "Test_lookup.other_formatted" (Cerb_log_auto.sources ())))
    "unvisited native function discovered";
  let events = ref [] in
  let previous = Logs.reporter () in
  Logs.set_reporter {Logs.report = fun src level ~over k msgf ->
    msgf (fun ?header ?tags fmt -> Format.kasprintf (fun message ->
      events := (Logs.Src.name src, level, header, tags, message) :: !events;
      over (); k ()) fmt)};
  Fun.protect ~finally:(fun () -> Logs.set_reporter previous) (fun () ->
    configure ["Test_lookup.formatted"];
    let callbacks = ref 0 in
    for _ = 1 to 2 do formatted (fun () -> incr callbacks) done;
    other_formatted never;
    check (!callbacks = 2 && List.length !events = 2) "native callback count";
    check (count_sources () = before + 1) "native source not shared on repeat call";
    List.iter (function
      | ("Test_lookup.formatted", Logs.Debug, Some "native", Some tags, "value: 7") ->
          check (Logs.Tag.get Cerb_log.location_tag tags = "input.c:7") "native tag"
      | _ -> failwith "native source, format or metadata changed") !events;
    configure ["Test_lookup"];
    other_formatted (fun () -> ());
    check (List.length !events = 3) "native module selection";
    configure ["Missing.fn"];
    formatted never;
    Cerb_log_auto.configure None [];
    formatted never)

let concurrent_misses () =
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
      let start = Atomic.make false and ready = Atomic.make 0 in
      let worker id =
        Atomic.incr ready;
        while not (Atomic.get start) do Domain.cpu_relax () done;
        Array.iter (fun raw ->
          Cerb_log_auto.debugf raw (fun _ -> never ());
          Cerb_log_auto.debugf enabled.(id mod Array.length enabled) (fun m -> m "event");
          Cerb_log_auto.debug disabled.(id mod Array.length disabled) never) literals in
      let workers = Array.init 8 (fun id -> Domain.spawn (fun () -> worker id)) in
      while Atomic.get ready <> Array.length workers do Domain.cpu_relax () done;
      Atomic.set start true;
      (* Join everyone before reporting an exception or reconfiguring. *)
      let results = Array.map (fun worker ->
        try Ok (Domain.join worker) with exn -> Error exn) workers in
      Array.iter (function Ok () -> () | Error exn -> raise exn) results;
      check (count_sources () = before + 1) "concurrent aliases registered duplicate sources";
      let names = List.filter (String.starts_with ~prefix:"Concurrent_misses.")
        (Cerb_log_auto.sources ()) in
      check (names = ["Concurrent_misses.disabled"; "Concurrent_misses.enabled"])
        "concurrent positive or negative decisions missing from discovery"
    done;
    check (Atomic.get events = 8 * 8 * Array.length literals) "concurrent admission lost events")

let () =
  names ();
  configure ["Missing.fn"];
  let before = count_sources () in
  Array.iter (fun name -> Cerb_log_auto.debug name never) literals;
  check (count_sources () = before) "negative decisions registered sources";
  check (List.for_all (fun name -> List.mem name (Cerb_log_auto.sources ()))
    (Array.to_list literals)) "negative decisions missing from listing";
  warm_allocation literals.(0);
  Cerb_log_auto.configure ~discover:true None ["all"];
  Cerb_log_auto.debug "Discovery.disabled" never;
  check (not (Cerb_log_auto.debug_enabled "Discovery.disabled.(fun)")) "discovery enabled logging";
  check (count_sources () = before) "discovery registered a disabled source";
  let listed = Cerb_log_auto.sources () in
  check (List.filter (String.starts_with ~prefix:"Discovery.") listed =
    ["Discovery.disabled"]) "discovery did not deduplicate aliases";
  check (not (List.mem literals.(0) listed)) "stale negative decisions after reconfiguration";
  configure ["Lookup_literals"];
  let events = Atomic.make 0 in
  Logs.set_reporter {Logs.report = fun _ _ ~over k msgf ->
    msgf (fun ?header:_ ?tags:_ fmt -> Format.kasprintf (fun _ ->
      Atomic.incr events; over (); k ()) fmt)};
  let start = Atomic.make false in
  let worker () =
    while not (Atomic.get start) do Domain.cpu_relax () done;
    for _ = 1 to 40 do
      Array.iter (fun name ->
        check (Cerb_log_auto.debug_enabled name) "lost positive decision";
        Cerb_log_auto.debug name (fun () -> "event")) literals
    done in
  let workers = Array.init 4 (fun _ -> Domain.spawn worker) in
  Atomic.set start true;
  Array.iter Domain.join workers;
  check (Atomic.get events = 4 * 40 * Array.length literals) "lost events";
  check (count_sources () = before + Array.length literals) "duplicate sources";
  check (Cerb_log_auto.debug_enabled "Lookup_literals.function000.(fun)") "alias decision";
  check (count_sources () = before + Array.length literals) "alias source duplication";
  warm_allocation literals.(0);
  let copies = Array.map (fun s -> Bytes.to_string (Bytes.of_string s)) literals in
  Gc.compact ();
  Array.iter (fun s ->
    rejects (fun () -> Cerb_log_auto.debug_enabled s);
    rejects (fun () -> Cerb_log_auto.debug s never);
    rejects (fun () -> Cerb_log_auto.debug_located s Cerb_location.unknown never)) copies;
  Array.iter (fun s -> check (Cerb_log_auto.debug_enabled s) "static key after compaction") literals;
  (* Reconfiguration is allowed only after workers have joined. It must
     replace both positive and negative decisions from the previous policy. *)
  configure ["Missing.fn"];
  Array.iter (fun name -> Cerb_log_auto.debug name never) literals;
  configure ["Lookup_literals"];
  let threads = Array.init 4 (fun _ -> Thread.create worker ()) in
  Array.iter Thread.join threads;
  List.iter (fun s -> rejects (fun () -> Cerb_log_auto.debug_enabled s)) [""; "M."; "M"];
  Cerb_log_auto.configure None ["all"];
  Array.iter (fun s -> Cerb_log_auto.debug s never) copies;
  check (not (Cerb_log_auto.debug_enabled "Lookup_literals.function000")) "quiet";
  configure [];
  Array.iter (fun s -> Cerb_log_auto.debug s never) copies;
  Cerb_log_auto.debug "Discovery.not_recorded" never;
  check (not (List.mem "Discovery.not_recorded" (Cerb_log_auto.sources ())))
    "inactive logging performed discovery";
  native_formatted ();
  concurrent_misses ();
  print_endline "Static lookup: matching, lazy cached options, GC, concurrent first use and reconfiguration passed"
