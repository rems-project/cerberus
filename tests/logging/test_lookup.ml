let literals = Array.sub Lookup_literals.names 0 128
let check condition reason = if not condition then failwith reason
let never () = failwith "disabled callback evaluated"
let rejects f = match f () with
  | _ -> failwith "invalid name accepted"
  | exception Invalid_argument _ -> ()
let configure selectors = Cerb_log.configure (Some Logs.Warning) selectors
let count_sources () = List.length (Logs.Src.list ())

let names () =
  let canonical = Cerb_log_names.canonical in
  check (canonical "Cerb_frontend__M.N.fn0.(fun)" = "M.N.fn0") "wrapper and closure";
  check (canonical "Cerb_backend__Pipeline.cpp" = "Pipeline.cpp") "backend wrapper";
  check (canonical "Dune__exe__Absint.assign.aux" = "Absint.assign") "executable wrapper";
  check (canonical "M.fn0.local" = "M.fn0") "nested function";
  check (canonical "M.fn" <> canonical "M.fn0") "digits are significant";
  List.iter (fun suffix ->
    check (canonical ("M.fn" ^ suffix) = "M.fn") "outer function ignores closure suffix";
    check (not (Cerb_log_names.valid_selector ("M.fn" ^ suffix))) "selector includes a suffix")
    [".local"; ".(fun)"; "."; ".."; ".bad-ignored"; ".\000"];
  List.iter (fun raw ->
    check (canonical raw = raw) "valid identifier or near-matching wrapper changed")
    ["M.N2'.fn0'"; "M.__"; "M._fn"; "Cerb_frontend_X.fn";
     "Cerb_backend_X.fn"; "Dune__exe_X.fn"];
  List.iter (fun wrapper ->
    for length = 1 to String.length wrapper - 1 do
      let raw = String.sub wrapper 0 length ^ ".fn" in
      check (canonical raw == raw) "partial wrapper was stripped or copied"
    done) ["Cerb_frontend__"; "Cerb_backend__"; "Dune__exe__"];
  check (canonical "Cerb_frontend__Cerb_frontend__M.fn" = "Cerb_frontend__M.fn")
    "strip only one wrapper";
  List.iter (fun s -> rejects (fun () -> canonical s))
    [""; "M"; "M."; "M..fn"; "M._"; "fn"; "M.1fn"; "M.f-n";
     "M.f\000n"; "M.f\255n"; "Cerb_frontend__"; "Cerb_frontend__M";
     "Cerb_frontend__M."; "Cerb_frontend__.fn"; "Cerb_backend__M._"; "Dune__exe__"];
  List.iter (fun s -> check (not (Cerb_log_names.valid_selector s)) "invalid selector")
    [""; "file:m.lem"; "M*"; "fn"; "m.fn"; "M._"; "M.1fn"; "M..fn";
     ".M"; "M."; "M.f-n"; "M.f\000n"; "M.f\255n"];
  List.iter (fun s -> check (Cerb_log_names.valid_selector s) "valid selector")
    ["M"; "M.N"; "M.N.fn0"; "M._fn"; "M.fn'"; "M.N2'.fn0'"; "M.__"];
  let selected = Cerb_log_names.selected ["M.N"; "A.fn0"] in
  check (selected "M.N.fn" && selected "M.N") "exact module";
  check (not (selected "M.Nested.fn") && not (selected "M.N.Sub.fn")) "no prefix/glob matching";
  check (selected "A.fn0" && not (selected "A.fn")) "exact function"

let name_allocation () =
  Gc.full_major ();
  let before = Gc.allocated_bytes () in
  for i = 0 to 9_999 do
    let raw = literals.(i mod Array.length literals) in
    check (Cerb_log_names.valid_selector raw) "canonical name is not a selector";
    check (Cerb_log_names.canonical raw == raw) "canonical name was copied"
  done;
  check (Gc.allocated_bytes () -. before < 1024.)
    "validation or unchanged normalization allocated per name"

let warm_allocation raw =
  ignore (Cerb_log.debug_enabled raw);
  Gc.full_major ();
  let before = Gc.allocated_bytes () in
  for _ = 1 to 100_000 do ignore (Cerb_log.debug_enabled raw) done;
  let allocated = Gc.allocated_bytes () -. before in
  check (allocated < 1024.) "cached decisions allocated on hits"

let formatted callback =
  Cerb_log.debugf __FUNCTION__ (fun m ->
    callback ();
    m ~header:"native"
      ~tags:Logs.Tag.(add Cerb_log.location_tag "input.c:7" empty)
      "value: %a" Format.pp_print_int 7)

let other_formatted callback =
  Cerb_log.debugf __FUNCTION__ (fun m -> callback (); m "other")

let native_formatted () =
  let before = count_sources () in
  Cerb_log.configure ~discover:true None [];
  formatted never;
  check (count_sources () = before) "native discovery registered a source";
  check (List.mem "Test_lookup.formatted" (Cerb_log.sources ()))
    "native function name missing from discovery";
  check (not (List.mem "Test_lookup.other_formatted" (Cerb_log.sources ())))
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
    Cerb_log.configure None [];
    formatted never)

let () =
  names ();
  name_allocation ();
  configure ["Missing.fn"];
  let before = count_sources () in
  Array.iter (fun name -> Cerb_log.debug name never) literals;
  check (count_sources () = before) "negative decisions registered sources";
  check (List.for_all (fun name -> List.mem name (Cerb_log.sources ()))
    (Array.to_list literals)) "negative decisions missing from listing";
  warm_allocation literals.(0);
  Cerb_log.configure ~discover:true None ["all"];
  Cerb_log.debug "Discovery.disabled" never;
  check (not (Cerb_log.debug_enabled "Discovery.disabled.(fun)")) "discovery enabled logging";
  check (count_sources () = before) "discovery registered a disabled source";
  let listed = Cerb_log.sources () in
  check (List.filter (String.starts_with ~prefix:"Discovery.") listed =
    ["Discovery.disabled"]) "discovery did not deduplicate aliases";
  check (not (List.mem literals.(0) listed)) "stale negative decisions after reconfiguration";
  configure ["Lookup_literals"];
  let events = Atomic.make 0 in
  Logs.set_reporter {Logs.report = fun _ _ ~over k msgf ->
    msgf (fun ?header:_ ?tags:_ fmt -> Format.kasprintf (fun _ ->
      Atomic.incr events; over (); k ()) fmt)};
  let worker _ =
    for _ = 1 to 40 do
      Array.iter (fun name ->
        check (Cerb_log.debug_enabled name) "lost positive decision";
        Cerb_log.debug name (fun () -> "event")) literals
    done in
  Concurrency_cases.run_threads 4 worker;
  check (Atomic.get events = 4 * 40 * Array.length literals) "lost events";
  check (count_sources () = before + Array.length literals) "duplicate sources";
  check (Cerb_log.debug_enabled "Lookup_literals.function000.(fun)") "alias decision";
  check (count_sources () = before + Array.length literals) "alias source duplication";
  warm_allocation literals.(0);
  let copies = Array.map (fun s -> Bytes.to_string (Bytes.of_string s)) literals in
  (* Check young strings, promoted strings and strings surviving full GC and
     compaction. OCaml 4 heap header colours must never imply static storage. *)
  List.iter (fun collect ->
    collect ();
    Array.iter (fun s ->
      rejects (fun () -> Cerb_log.debug_enabled s);
      rejects (fun () -> Cerb_log.debug s never);
      rejects (fun () -> Cerb_log.debug_located s Cerb_location.unknown never)) copies;
    Array.iter (fun s -> check (Cerb_log.debug_enabled s) "static key after GC") literals)
    [(fun () -> ()); Gc.minor; Gc.full_major; Gc.compact];
  (* Reconfiguration is allowed only after workers have joined. It must
     replace both positive and negative decisions from the previous policy. *)
  configure ["Missing.fn"];
  Array.iter (fun name -> Cerb_log.debug name never) literals;
  configure ["Lookup_literals"];
  Concurrency_cases.run_threads 4 worker;
  List.iter (fun s -> rejects (fun () -> Cerb_log.debug_enabled s)) [""; "M."; "M"];
  Cerb_log.configure None ["all"];
  Array.iter (fun s -> Cerb_log.debug s never) copies;
  check (not (Cerb_log.debug_enabled "Lookup_literals.function000")) "quiet";
  configure [];
  Array.iter (fun s -> Cerb_log.debug s never) copies;
  Cerb_log.debug "Discovery.not_recorded" never;
  check (not (List.mem "Discovery.not_recorded" (Cerb_log.sources ())))
    "inactive logging performed discovery";
  native_formatted ();
  Concurrency_cases.concurrent_misses ~run_workers:Concurrency_cases.run_threads literals;
  print_endline "Static lookup: matching, lazy cached options, GC, concurrent first use and reconfiguration passed"
