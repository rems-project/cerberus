let check condition reason = if not condition then failwith reason

let parse args =
  let cmd = Cmdliner.Cmd.v (Cmdliner.Cmd.info "logging-options") Cerb_log_cli.options in
  match Cmdliner.Cmd.eval_value ~argv:(Array.of_list ("logging-options" :: args)) cmd with
  | Ok (`Ok options) -> options
  | _ -> failwith "logging options did not parse"

let setup args = match Cerb_log_cli.setup (parse args) with
  | Ok () -> ()
  | Error error -> failwith error

let enabled args =
  setup args;
  let levels = ref [] in
  List.iter (fun (level, log) -> log "Cli.target" (fun _ -> levels := level :: !levels))
    [Logs.Debug, Cerb_log.debug; Logs.Info, Cerb_log.info;
     Logs.Warning, Cerb_log.warn; Logs.Error, Cerb_log.err];
  List.rev !levels

let () =
  let open Logs in
  check (enabled [] = [Warning; Error]) "default Warning";
  check (enabled ["-v"] = [Info; Warning; Error]) "verbose Info";
  check (enabled ["-vv"] = [Debug; Info; Warning; Error]) "verbose Debug";
  check (enabled ["--debug=Cli"; "--debug=Other.fn"] = [Debug; Info; Warning; Error])
    "selected module";
  check (enabled ["--debug=Other.fn"] = [Warning; Error]) "unselected source";
  check (enabled ["-q"; "-vv"; "--debug=all"] = []) "quiet precedence";
  check (enabled ["-vv"; "--verbosity=error"] = [Error]) "explicit verbosity";
  check (Result.is_error (Cerb_log_cli.setup (parse ["--debug=M*"])))
    "invalid selector accepted";
  let path = Filename.temp_file "logging-cli" ".jsonl" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
    setup ["--debug=Cli.target"; "--debug-format=json"; "--debug-output=file:" ^ path];
    Cerb_log.debug "Cli.target" (fun m -> m "test message");
    let input = open_in path in
    let line = Fun.protect ~finally:(fun () -> close_in input) (fun () -> input_line input) in
    let open Yojson.Basic.Util in
    let event = Yojson.Basic.from_string line in
    check (event |> member "message" |> to_string = "test message") "JSON output";
    check (event |> member "source" |> to_string = "Cli.target") "selected function");
  ignore (parse ["--list-debug-sources"; "--debug-output=stdout"]);
  print_endline "Logging CLI: defaults, selection, quiet and reporter options passed"
