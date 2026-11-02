let location_tag = Logs.Tag.def "location" Format.pp_print_string

(* Configure once before workers start. Source levels and selectors remain
   fixed while logging; the shared registries grow concurrently. *)
type policy = {
  debug_active : bool;
  info_active : bool;
  warn_active : bool;
  err_active : bool;
  select : string -> bool;
  sources : (string, Logs.src) Saturn.Htbl.t;
  sources_mutex : Mutex.t;
  encountered : (string, unit) Saturn.Htbl.t;
  default_level : Logs.level option;
}

let admits (threshold : Logs.level option) level = match threshold with
  | None -> false
  | Some threshold -> level <= threshold

let fresh ~discover level select active = {
  debug_active = active || discover; select;
  sources = Saturn.Htbl.create ~hashed_type:(module Cerb_log_compat.String_key) ();
  sources_mutex = Mutex.create ();
  encountered = Saturn.Htbl.create ~hashed_type:(module Cerb_log_compat.String_key) ();
  default_level = level;
  (* Selectors can enable any severity regardless of the global threshold. *)
  info_active = discover || active || admits level Logs.Info;
  warn_active = discover || active || admits level Logs.Warning;
  err_active = discover || active || admits level Logs.Error;
}
let policy = ref (fresh ~discover:false None (fun _ -> false) false)

let source_for_name p name level =
  match Saturn.Htbl.find_exn p.sources name with
  | src -> src
  | exception Not_found ->
      (* Different raw names can normalize to the same function. Recheck under
         the creation mutex: a losing [try_add] cannot undo [Logs.Src.create]'s
         global registration. Publish only after configuring the new source. *)
      Cerb_log_compat.protect p.sources_mutex (fun () ->
        match Saturn.Htbl.find_exn p.sources name with
        | src -> src
        | exception Not_found ->
            let src = Logs.Src.create name in
            Logs.Src.set_level src level;
            ignore (Saturn.Htbl.try_add p.sources name src);
            src)

let source_for p requested raw =
  let name = Cerb_log_names.canonical raw in
  ignore (Saturn.Htbl.try_add p.encountered name ());
  let level = if p.select name then Some Logs.Debug else p.default_level in
  if not (admits level requested) then None
  else Some (source_for_name p name level)

let configure ?(discover=false) level selectors =
  List.iter (fun name ->
    if name <> "all" && not (Cerb_log_names.valid_selector name) then
      invalid_arg ("invalid debug selector: " ^ name)) selectors;
  let all = level = Some Logs.Debug || List.mem "all" selectors in
  let active = level <> None && (all || selectors <> []) in
  let select = if not active then (fun _ -> false) else if all then (fun _ -> true)
    else Cerb_log_names.selected selectors in
  (* Listing observes disabled sites too, without enabling their messages. *)
  let p = fresh ~discover level select active in
  List.iter (fun src ->
    let name = Logs.Src.name src in
    Logs.Src.set_level src (if select name then Some Logs.Debug else level);
    if not (Saturn.Htbl.try_add p.sources name src) then
      ignore (Saturn.Htbl.try_set p.sources name src)) (Logs.Src.list ());
  policy := p

let sources () =
  let encountered = Saturn.Htbl.to_seq (!policy).encountered |> Seq.map fst |> List.of_seq in
  List.sort_uniq String.compare
    (encountered @ List.map Logs.Src.name (Logs.Src.list ()))

let debug raw message =
  let p = !policy in
  if p.debug_active then match source_for p Logs.Debug raw with
    | None -> ()
    | Some src -> Logs.debug ~src message

let info raw message =
  let p = !policy in
  if p.info_active then match source_for p Logs.Info raw with
    | None -> ()
    | Some src -> Logs.info ~src message

let warn raw message =
  let p = !policy in
  if p.warn_active then match source_for p Logs.Warning raw with
    | None -> ()
    | Some src -> Logs.warn ~src message

let err raw message =
  let p = !policy in
  if p.err_active then match source_for p Logs.Error raw with
    | None -> ()
    | Some src -> Logs.err ~src message

(* Lem callbacks may emit zero or several strings. Invoke them only after
   selection, and make each emission a complete Logs call: skipping a message
   must not leave a reporter waiting for its [over] continuation. *)
let debug_string raw message =
  let p = !policy in
  if p.debug_active then match source_for p Logs.Debug raw with
    | None -> ()
    | Some src -> message (fun text -> Logs.debug ~src (fun m -> m "%s" text))

let warn_string raw message =
  let p = !policy in
  if p.warn_active then match source_for p Logs.Warning raw with
    | None -> ()
    | Some src -> message (fun text -> Logs.warn ~src (fun m -> m "%s" text))

let err_string raw message =
  let p = !policy in
  if p.err_active then match source_for p Logs.Error raw with
    | None -> ()
    | Some src -> message (fun text -> Logs.err ~src (fun m -> m "%s" text))

let debug_located_string raw loc message =
  let p = !policy in
  if p.debug_active then match source_for p Logs.Debug raw with
    | None -> ()
    | Some src -> message (fun text ->
        Logs.debug ~src (fun m ->
          let tags = Logs.Tag.(add location_tag (Cerb_location.location_to_string loc) empty) in
          m ~tags "%s" text))

type format = Text | Json
type output = Stderr | Stdout | File of string

let fields src level header tags message =
  let fields = ["schema_version", `Int 1;
                "level", `String (Logs.level_to_string (Some level));
                "source", `String (Logs.Src.name src);
                "message", `String message] in
  let fields = match header with None -> fields | Some h -> ("header", `String h) :: fields in
  let name = Logs.Src.name src in
  let fields = match String.rindex_opt name '.' with
    | None -> ("module", `String name) :: fields
    | Some i when i + 1 = String.length name || (name.[i + 1] >= 'A' && name.[i + 1] <= 'Z') ->
        ("module", `String name) :: fields
    | Some i ->
        ("module", `String (String.sub name 0 i)) ::
        ("function", `String (String.sub name (i + 1) (String.length name - i - 1))) :: fields in
  let fields = List.fold_left (fun fields (name, tag) ->
      match Logs.Tag.find tag tags with
      | None -> fields | Some s -> (name, `String s) :: fields)
      fields ["location", location_tag] in
  let extra = Logs.Tag.fold (fun (Logs.Tag.V (def, value)) acc ->
      let name = Logs.Tag.name def in
      if name = "location" then acc
      else (name, `String (Format.asprintf "%a" (Logs.Tag.printer def) value)) :: acc) tags [] in
  if extra = [] then fields else ("tags", `Assoc extra) :: fields

let render format src level header tags message =
  match format with
  | Json -> Yojson.Basic.to_string (`Assoc (fields src level header tags message)) ^ "\n"
  | Text ->
      let suffix tag = match Logs.Tag.find tag tags with
        | None -> "" | Some s -> " [" ^ s ^ "]" in
      String.concat ""
        ["["; Logs.level_to_string (Some level); "] "; Logs.Src.name src;
         suffix location_tag;
         (match header with None -> "" | Some h -> " [" ^ h ^ "]"); ": "; message; "\n"]

let open_reporter output format =
  try
    let channel, owned = match output with
      | Stderr -> stderr, false
      | Stdout -> stdout, false
      | File path -> open_out_gen [Open_creat; Open_wronly; Open_append; Open_binary] 0o666 path, true in
    let mutex = Mutex.create () in
    let closed = ref false in
    let close () = Cerb_log_compat.protect mutex (fun () ->
      if not !closed then begin
        closed := true;
        if owned then close_out channel else flush channel
      end) in
    let report src level ~over k msgf =
      msgf (fun ?header ?(tags = Logs.Tag.empty) fmt ->
        Format.kasprintf (fun message ->
          let line = render format src level header tags message in
          Cerb_log_compat.protect mutex (fun () ->
            if !closed then invalid_arg "Cerb_log: reporter is closed";
            output_string channel line;
            flush channel);
          over ();
          k ()) fmt)
    in
    Ok ({ Logs.report }, close)
  with Sys_error msg -> Error msg
