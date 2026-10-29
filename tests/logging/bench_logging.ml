(* Run in release mode. Report absolute costs and allocations; this is not a
   timing-sensitive test. End-to-end Cerberus measurements are also required. *)
let iterations = 20_000_000
let level = ref 0
let source = Logs.Src.create "Bench.disabled"
let old_debug n _doms msg = if !level >= n then ignore (msg ())
let measure ?(count = iterations) name f =
  Gc.full_major ();
  let allocated = Gc.allocated_bytes () in
  let start = Unix.gettimeofday () in
  f ();
  let elapsed = Unix.gettimeofday () -. start in
  let allocated = Gc.allocated_bytes () -. allocated in
  Printf.printf "%s: %.3f ns/call, %.3f bytes/call\n%!" name
    (elapsed *. 1e9 /. float count) (allocated /. float count)

let run () =
  Logs.set_level ~all:true (Some Logs.Warning);
  Cerb_log_auto.configure (Some Logs.Warning) [];
  for _ = 1 to 5 do
    measure "old integer gate" (fun () ->
      for i = 1 to iterations do old_debug 2 [] (fun () -> string_of_int i) done);
    measure "native Logs" (fun () ->
      for i = 1 to iterations do Logs.debug ~src:source (fun m -> m "%d" i) done);
    measure "Lem adapter" (fun () ->
      for i = 1 to iterations do Cerb_log_auto.debug __FUNCTION__ (fun () -> string_of_int i) done)
  done;
  let count = 100_000 in
  let sink = open_out "/dev/null" in
  let get = function Ok x -> x | Error msg -> failwith msg in
  let text, close_text = get (Cerb_log.open_reporter (File "/dev/null") Text) in
  let json, close_json = get (Cerb_log.open_reporter (File "/dev/null") Json) in
  Fun.protect ~finally:(fun () ->
    Logs.set_reporter Logs.nop_reporter;
    close_out sink; close_text (); close_json ()) (fun () ->
    Logs.set_level ~all:true (Some Logs.Debug);
    level := 2;
    Cerb_log_auto.configure (Some Logs.Debug) ["all"];
    for _ = 1 to 5 do
      measure ~count "old enabled text" (fun () ->
        for i = 1 to count do
          if !level >= 2 then begin
            output_string sink (Cerb_colour.ansi_format [Red] ("(debug 2): " ^ string_of_int i));
            output_char sink '\n'; flush sink
          end
        done);
      Logs.set_reporter text;
      measure ~count "enabled text" (fun () ->
        for i = 1 to count do Cerb_log_auto.debug __FUNCTION__ (fun () -> string_of_int i) done);
      Logs.set_reporter json;
      measure ~count "enabled JSON" (fun () ->
        for i = 1 to count do Cerb_log_auto.debug __FUNCTION__ (fun () -> string_of_int i) done)
    done)

let () = run ()
