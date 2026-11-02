let check condition reason = if not condition then failwith reason
let never _ = failwith "disabled callback evaluated"
let rejects f = match f () with
  | _ -> failwith "invalid name accepted"
  | exception Invalid_argument _ -> ()
let configure selectors = Cerb_log.configure (Some Logs.Warning) selectors
let count_sources () = List.length (Logs.Src.list ())

let names () =
  let canonical = Cerb_log_names.canonical in
  List.iter (fun (raw, expected) ->
    check (canonical raw = expected) "canonical function name")
    ["Cerb_frontend__M.N.fn0.(fun)", "M.N.fn0";
     "Cerb_backend__Pipeline.cpp", "Pipeline.cpp";
     "Dune__exe__Absint.assign.aux", "Absint.assign";
     "Cerb_frontend__Cerb_frontend__M.fn", "Cerb_frontend__M.fn";
     "M.N2'.fn0'", "M.N2'.fn0'";
     "M.__", "M.__";
     "Cerb_frontend_X.fn", "Cerb_frontend_X.fn";
     "Cerb_backend_X.fn", "Cerb_backend_X.fn";
     "Dune__exe_X.fn", "Dune__exe_X.fn"];
  List.iter (fun s -> rejects (fun () -> canonical s))
    [""; "M"; "M."; "M..fn"; "M._"; "M.1fn"; "M.f-n"; "M.f\000n";
     "Cerb_frontend__"; "Dune__exe__"];
  List.iter (fun s -> check (not (Cerb_log_names.valid_selector s)) "invalid selector")
    [""; "M."; "M._"; "M.1fn"; "M.f-n"; "file:m.lem"; "M*";
     "fn"; "m.fn"; "M.fn.local"; "M.fn.(fun)"];
  List.iter (fun s -> check (Cerb_log_names.valid_selector s) "valid selector")
    ["M"; "M.N"; "M.N.fn0"; "M._fn"; "M.fn'"];
  let selected = Cerb_log_names.selected ["M.N"; "A.fn0"] in
  check (selected "M.N.fn" && selected "M.N") "exact module";
  check (not (selected "M.Nested.fn") && not (selected "M.N.Sub.fn")) "no prefix/glob matching";
  check (selected "A.fn0" && not (selected "A.fn")) "exact function"

let formatted callback =
  Cerb_log.debug __FUNCTION__ (fun m ->
    callback ();
    m ~header:"native"
      ~tags:Logs.Tag.(add Cerb_log.location_tag "input.c:7" empty)
      "value: %a" Format.pp_print_int 7)

let other_formatted callback =
  Cerb_log.debug __FUNCTION__ (fun m -> callback (); m "other")

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

let literals = [|"Cache.first"; "Cache.second"; "Cache.third"; "Cache.fourth"|]

let admitted raw =
  let called = ref false in
  (* The string bridge runs enabled callbacks even with a nop reporter. *)
  Cerb_log.debug_string raw (fun _ -> called := true);
  !called

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
  let previous = Logs.reporter () in
  Logs.set_reporter Logs.nop_reporter;
  Cerb_log.debug raw (fun _ -> ());
  let reference = if admitted raw then
      let src = List.find (fun src -> Logs.Src.name src = Cerb_log_names.canonical raw)
          (Logs.Src.list ()) in
      (fun () -> Logs.debug ~src (fun _ -> ()))
    else (fun () -> ()) in
  let allocated call =
    Gc.full_major ();
    let before = Gc.allocated_bytes () in
    for _ = 1 to 100_000 do call () done;
    Gc.allocated_bytes () -. before in
  let extra = allocated (fun () -> Cerb_log.debug raw (fun _ -> ())) -. allocated reference in
  Logs.set_reporter previous;
  check (extra < 1024.) "cached lookup allocated beyond Logs dispatch"

let cached_decisions () =
  configure ["Missing.fn"];
  let before = count_sources () in
  Array.iter (fun raw -> check (not (admitted raw)) "negative decision") literals;
  check (count_sources () = before) "negative decisions registered sources";
  check (List.for_all (fun raw -> List.mem raw (Cerb_log.sources ()))
    (Array.to_list literals)) "negative decisions missing from listing";
  warm_allocation literals.(0);
  configure ["Cache"];
  Array.iter (fun raw -> check (admitted raw) "lost positive decision") literals;
  check (admitted "Cache.first.(fun)") "alias decision";
  check (count_sources () = before + Array.length literals) "alias source duplication";
  warm_allocation literals.(0);
  let copies = Array.map (fun s -> Bytes.to_string (Bytes.of_string s)) literals in
  (* All four GC states matter: heap header colours on OCaml 4 must never
     be mistaken for the marker used for static storage on OCaml 5. *)
  List.iter (fun collect ->
    collect ();
    Array.iter (fun s -> rejects (fun () -> admitted s)) copies;
    Array.iter (fun s -> check (admitted s) "static key after GC") literals)
    [(fun () -> ()); Gc.minor; Gc.full_major; Gc.compact];
  configure ["Missing.fn"];
  Array.iter (fun raw -> check (not (admitted raw)) "stale positive decision") literals;
  check (count_sources () = before + Array.length literals) "reconfiguration duplicated sources"

let () =
  name_allocation ();
  cached_decisions ();
  names ();
  native_formatted ();
  Cerb_log.configure ~discover:true None [];
  Cerb_log.debug_string "Discovery.disabled" never;
  Cerb_log.debug_string "Discovery.disabled.(fun)" never;
  check (List.filter (String.starts_with ~prefix:"Discovery.") (Cerb_log.sources ()) =
    ["Discovery.disabled"]) "discovery did not deduplicate aliases";
  configure [];
  Cerb_log.debug_string "Discovery.not_recorded" never;
  check (not (List.mem "Discovery.disabled" (Cerb_log.sources ())))
    "stale disabled names after reconfiguration";
  check (not (List.mem "Discovery.not_recorded" (Cerb_log.sources ())))
    "inactive logging performed discovery";
  print_endline "Source names: validation, selection and discovery passed"
