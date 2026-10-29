(* Optional experiment, not a timing-sensitive test. Each memory sample should
   run in a fresh process so the global Logs source registry starts equally. *)
let live_bytes () =
  Gc.full_major ();
  (Gc.stat ()).live_words * (Sys.word_size / 8)

let () =
  if Array.length Sys.argv <> 4 then
    failwith "usage: bench_lookup.exe memory|micro N negative|positive";
  let operation = Sys.argv.(1) in
  let n = int_of_string Sys.argv.(2) in
  if n < 1 || n > Array.length Lookup_literals.names then invalid_arg "N must be 1..16384";
  let names = Array.sub Lookup_literals.names 0 n in
  let positive = match Sys.argv.(3) with
    | "positive" -> true | "negative" -> false | _ -> invalid_arg "expected negative|positive" in
  Cerb_log_auto.configure (Some Logs.Warning) [if positive then "Lookup_literals" else "Missing.fn"];
  let sources_before = List.length (Logs.Src.list ()) in
  let before = live_bytes () in
  let allocated_before = Gc.allocated_bytes () in
  Array.iter (fun name ->
    if Cerb_log_auto.debug_enabled name <> positive then failwith "wrong decision") names;
  let allocated_first = Gc.allocated_bytes () -. allocated_before in
  (* Complete any deferred bookkeeping in table buckets before the retained
     measurement. This does not create additional bindings or source objects. *)
  Array.iter (fun name -> ignore (Cerb_log_auto.debug_enabled name)) names;
  let retained = live_bytes () - before in
  if operation = "memory" then
    Printf.printf "{\"names\":%d,\"positive\":%b,\"retained_bytes\":%d,\"first_allocated_bytes\":%.0f,\"new_sources\":%d}\n%!"
      n positive retained allocated_first (List.length (Logs.Src.list ()) - sources_before)
  else if operation = "micro" then begin
    let count = 3_000_000 in
    let iterate () = for i = 0 to count - 1 do
      ignore (Cerb_log_auto.debug_enabled names.(i mod n)) done in
    iterate (); Gc.full_major ();
    let before = Gc.allocated_bytes () in
    let start = Unix.gettimeofday () in
    iterate ();
    let seconds = Unix.gettimeofday () -. start in
    let allocated = Gc.allocated_bytes () -. before in
    Printf.printf "{\"names\":%d,\"positive\":%b,\"ns_per_decision\":%.3f,\"bytes_per_decision\":%.6f}\n%!"
      n positive (seconds *. 1e9 /. float count) (allocated /. float count)
  end else invalid_arg "expected memory|micro"
