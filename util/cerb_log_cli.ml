type t = {
  level: Logs.level option;
  selectors: string list;
  list_sources: bool;
  output: Cerb_log.output;
  format: Cerb_log.format;
}

let options =
  let open Cmdliner in
  let selectors =
    let doc = "Enable debug messages for an exact $(i,Module) or $(i,Module.function). \
               Repeat to select several names, or use $(i,all). $(b,--quiet) takes precedence." in
    Arg.(value & opt_all string [] & info ["debug"] ~docv:"SOURCE" ~doc) in
  let list_sources =
    let doc = "List logging sources after processing the input. Unvisited functions are omitted." in
    Arg.(value & flag & info ["list-debug-sources"] ~doc) in
  let output =
    let doc = "Write logs to stderr, stdout, or append to a file. \
               Use file:PATH for a file named stdout or stderr." in
    Arg.(value & opt string "stderr" & info ["debug-output"] ~docv:"DEST" ~doc) in
  let format =
    let doc = "Log format: text or newline-delimited JSON." in
    Arg.(value & opt (enum ["text", Cerb_log.Text; "json", Cerb_log.Json]) Cerb_log.Text &
         info ["debug-format"] ~docv:"FORMAT" ~doc) in
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
      Logs.set_level ~all:true options.level;
      Cerb_log.configure ~discover:options.list_sources options.level options.selectors;
      match Cerb_log.open_reporter options.output options.format with
      | Error msg -> Error ("debug output: " ^ msg)
      | Ok (reporter, close) ->
          Logs.set_reporter reporter;
          at_exit close;
          if options.list_sources then
            at_exit (fun () -> List.iter print_endline (Cerb_log.sources ()));
          Ok ()
