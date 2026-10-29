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
  print_endline "Static lookup: matching, lazy cached options, GC, concurrent first use and reconfiguration passed"
