(* Optional experiment, not a timing-sensitive test. Each memory sample runs
   in a fresh process. Native calls with a no-op reporter measure lookup and
   dispatch without formatting; there is no public decision-query API. *)
let live_bytes () =
  Gc.full_major ();
  (Gc.stat ()).live_words * (Sys.word_size / 8)

let no_message _ = ()

let () =
  if Array.length Sys.argv <> 4 then
    failwith "usage: bench_lookup.exe memory|micro N off|negative|positive|mixed";
  let operation = Sys.argv.(1) in
  let n = int_of_string Sys.argv.(2) in
  if n < 1 || n > Array.length Lookup_literals.names then invalid_arg "N must be 1..16384";
  let names = Array.sub Lookup_literals.names 0 n in
  let mode = Sys.argv.(3) in
  let selectors, accepted, calls_per_name = match mode with
    | "off" -> [], 0, 1
    | "negative" -> ["Missing.fn"], 0, 1
    | "positive" -> ["Lookup_literals"], 1, 1
    | "mixed" -> ["Missing.fn"], 2, 3
    | _ -> invalid_arg "expected off|negative|positive|mixed" in
  let call = if mode = "mixed" then (fun name ->
      Cerb_log.debug name no_message;
      Cerb_log.warn name no_message;
      Cerb_log.err name no_message)
    else (fun name -> Cerb_log.debug name no_message) in
  Cerb_log.configure (Some Logs.Warning) selectors;
  let seen = ref 0 in
  Logs.set_reporter {Logs.report = fun _ _ ~over k _ -> incr seen; over (); k ()};
  let sources_before = List.length (Logs.Src.list ()) in
  let before = live_bytes () in
  let allocated_before = Gc.allocated_bytes () in
  Array.iter call names;
  let allocated_first = Gc.allocated_bytes () -. allocated_before in
  if !seen <> n * accepted then failwith "wrong decisions";
  Logs.set_reporter Logs.nop_reporter;
  (* Finish deferred bucket bookkeeping before measuring retained memory. *)
  Array.iter call names;
  let retained = live_bytes () - before in
  if operation = "memory" then
    Printf.printf "{\"names\":%d,\"mode\":%S,\"retained_bytes\":%d,\"first_allocated_bytes\":%.0f,\"new_sources\":%d}\n%!"
      n mode retained allocated_first (List.length (Logs.Src.list ()) - sources_before)
  else if operation = "micro" then begin
    let iterations = 3_000_000 / calls_per_name in
    let count = float (iterations * calls_per_name) in
    let iterate () = for i = 0 to iterations - 1 do call names.(i mod n) done in
    iterate (); Gc.full_major ();
    let before = Gc.allocated_bytes () in
    let start = Unix.gettimeofday () in
    iterate ();
    let seconds = Unix.gettimeofday () -. start in
    let allocated = Gc.allocated_bytes () -. before in
    Printf.printf "{\"names\":%d,\"mode\":%S,\"ns_per_call\":%.3f,\"bytes_per_call\":%.6f}\n%!"
      n mode (seconds *. 1e9 /. count) (allocated /. count)
  end else invalid_arg "expected memory|micro"
