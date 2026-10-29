type t = {
  level: Logs.level option;
  selectors: string list;
  list_sources: bool;
  output: Cerb_log.output;
  format: Cerb_log.format;
}

let options =
  let open Cmdliner in
  let selectors = Arg.(value & opt_all string [] & info ["debug"] ~docv:"SOURCE"
      ~doc:"Enable Debug for an exact Module or Module.function name. Repeat to select several sources, or use all. Other sources keep the usual verbosity. Automatic Lem function sources are discovered when called; syntactically valid unknown names are accepted. Filenames and globs are not supported. --quiet takes precedence.") in
  let list_sources = Arg.(value & flag & info ["list-debug-sources"]
      ~doc:"Process the input, then print logging source names to stdout at exit. Includes explicitly registered sources and automatic functions encountered during this run, even when their messages are disabled. Unvisited automatic functions are absent. Discovery adds lookup work to this invocation; no binary scan is performed.") in
  let output = Arg.(value & opt string "stderr" & info ["debug-output"] ~docv:"DEST"
      ~doc:"Write logs to stderr, stdout, or an appended file. Prefix a path with file: to disambiguate it from stdout/stderr.") in
  let format = Arg.(value & opt (enum ["text", Cerb_log.Text; "json", Cerb_log.Json]) Cerb_log.Text &
      info ["debug-format"] ~docv:"FORMAT" ~doc:"Log format: text or newline-delimited json.") in
  let make level selectors list_sources output format =
    let output = match output with
      | "stderr" -> Cerb_log.Stderr
      | "stdout" -> Cerb_log.Stdout
      | path when String.starts_with ~prefix:"file:" path ->
          Cerb_log.File (String.sub path 5 (String.length path - 5))
      | path -> Cerb_log.File path in
    { level; selectors; list_sources; output; format } in
  Term.(const make $ Logs_cli.level () $ selectors $ list_sources $ output $ format)

let setup options =
  match List.find_opt (fun name ->
      name <> "all" && not (Cerb_log_names.valid_selector name)) options.selectors with
  | Some name -> Error (Printf.sprintf
      "invalid debug selector %S: use an exact Module or Module.function name" name)
  | None ->
      (* Global startup policy. Automatic sources are registered only when a
         selected function first logs; do not scan or enumerate binary strings. *)
      Logs.set_level ~all:true options.level;
      Cerb_log_auto.configure ~discover:options.list_sources options.level options.selectors;
      match Cerb_log.open_reporter options.output options.format with
      | Error msg -> Error ("debug output: " ^ msg)
      | Ok (reporter, close) ->
          Logs.set_reporter reporter;
          at_exit close;
          if options.list_sources then
            at_exit (fun () -> List.iter print_endline (Cerb_log_auto.sources ()));
          Ok ()
