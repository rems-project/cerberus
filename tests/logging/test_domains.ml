(* This test deliberately uses real OCaml 5 domains, not just systhreads. *)
let () =
  let get = function Ok x -> x | Error msg -> failwith msg in
  let path = Filename.temp_file "cerberus-domains" ".jsonl" in
  let reporter, close = get (Cerb_log.open_reporter (File path) Json) in
  Logs.set_reporter reporter;
  Logs.set_level ~all:true (Some Logs.Debug);
  let sources = Array.init 8 (fun id -> Logs.Src.create ("Worker.run" ^ string_of_int id)) in
  Fun.protect ~finally:(fun () -> Logs.set_reporter Logs.nop_reporter; close (); Sys.remove path) (fun () ->
    let domains = List.init 8 (fun id -> Domain.spawn (fun () ->
      let source = sources.(id) in
      let tags = Logs.Tag.(add Cerb_log.translation_unit_tag (Printf.sprintf "tu%d.c" id) empty) in
      for i = 1 to 1000 do
        Logs.debug ~src:source (fun m -> m ~tags "%d:%d\n%s" id i (String.make 1024 'x'))
      done)) in
    List.iter Domain.join domains;
    close ();
    let ic = open_in path in
    let seen = Hashtbl.create 8000 in
    Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
      let rec loop () = match input_line ic with
        | line ->
            let open Yojson.Basic.Util in
            let json = Yojson.Basic.from_string line in
            let message = json |> member "message" |> to_string in
            let name = json |> member "function" |> to_string in
            let worker = String.sub name 3 (String.length name - 3) in
            assert (String.starts_with ~prefix:(worker ^ ":") message);
            assert (json |> member "translation_unit" |> to_string = "tu" ^ worker ^ ".c");
            assert (not (Hashtbl.mem seen message));
            Hashtbl.add seen message (); loop ()
        | exception End_of_file -> () in
      loop ());
    assert (Hashtbl.length seen = 8000));
  print_endline "OCaml 5 domain logging tests passed"

let () =
  let path = Filename.temp_file "cerberus-late-sources" ".log" in
  let reporter, close = match Cerb_log.open_reporter (File path) Text with
    | Ok x -> x | Error msg -> failwith msg in
  (* Create sources serially after opening the reporter. All workers then hit
     cold prefix entries together, including a source shared by every worker. *)
  let sources = Array.init 9 (fun id -> Logs.Src.create ("Late.worker" ^ string_of_int id)) in
  let ready = Atomic.make 0 in
  Fun.protect ~finally:(fun () -> close (); Sys.remove path) (fun () ->
    let workers = List.init 8 (fun id -> Domain.spawn (fun () ->
      Atomic.incr ready;
      while Atomic.get ready <> 8 do Domain.cpu_relax () done;
      for i = 0 to 199 do
        let src = sources.(if i = 0 then 8 else id) in
        reporter.Logs.report src Logs.Debug ~over:(fun () -> ()) (fun () -> ())
          (fun m -> m "%s" (Printf.sprintf "%d:%d" id i))
      done)) in
    List.iter Domain.join workers;
    close ();
    let expected = Hashtbl.create 1600 in
    for id = 0 to 7 do
      for i = 0 to 199 do
        Hashtbl.add expected (Printf.sprintf "[debug] Late.worker%d: %d:%d"
          (if i = 0 then 8 else id) id i) ()
      done
    done;
    let channel = open_in path in
    Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
      let rec read () = match input_line channel with
        | line -> assert (Hashtbl.mem expected line); Hashtbl.remove expected line; read ()
        | exception End_of_file -> () in
      read ());
    assert (Hashtbl.length expected = 0));
  print_endline "Late text source cache tests passed across 8 domains"
