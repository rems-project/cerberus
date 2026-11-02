let location_tag = Logs.Tag.def "location" Format.pp_print_string

(* Configure once before starting workers. The policy, selector table and
   source levels remain unchanged until all workers have joined. Only the
   decision tables and source registry grow during use. Source creation is
   serialized; all tables support concurrent lookup. *)
external pointer_hash : string -> int = "cerb_log_pointer_hash" [@@noalloc]
external is_static : string -> bool = "cerb_log_is_static" [@@noalloc]
module Pointer = struct
  type t = string
  let equal = (==)
  let hash = pointer_hash
end

type decisions = (string, Logs.src option) Saturn.Htbl.t

type policy = {
  debug_active : bool;
  select : string -> bool;
  debug_decisions : decisions;
  sources : (string, Logs.src) Saturn.Htbl.t;
  sources_mutex : Mutex.t;
  level : Logs.level option;
  warn_active : bool;
  err_active : bool;
  warn_decisions : decisions;
  err_decisions : decisions;
}

let admits (threshold : Logs.level option) level = match threshold with
  | None -> false
  | Some threshold -> level <= threshold

let new_decisions () = Saturn.Htbl.create ~hashed_type:(module Pointer) ()

let fresh ~discover level select active = {
  debug_active = active || discover; select;
  debug_decisions = new_decisions ();
  sources = Saturn.Htbl.create ~hashed_type:(module Cerb_log_compat.String_key) ();
  sources_mutex = Mutex.create ();
  level;
  (* A selected source is raised to Debug even if the global threshold is
     Error. These gates only skip levels that cannot be enabled anywhere. *)
  warn_active = discover || active || admits level Logs.Warning;
  err_active = discover || active || admits level Logs.Error;
  warn_decisions = new_decisions ();
  err_decisions = new_decisions ();
}
let policy = ref (fresh ~discover:false None (fun _ -> false) false)

let source_for_name p name level =
  match Saturn.Htbl.find_exn p.sources name with
  | src -> src
  | exception Not_found ->
      (* Different static addresses can name the same function. Recheck under
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

let[@inline never] first_use p decisions level raw =
  (* Heap strings can move, changing their address hash. They never enter the
     table. Looking one up before this check cannot match a static address;
     validation therefore belongs only on the miss path. *)
  if not (is_static raw) then
    invalid_arg "Cerb_log: expected a static source name (use __FUNCTION__)";
  let name = Cerb_log_names.canonical raw in
  let threshold = if p.select name then Some Logs.Debug else p.level in
  let decision =
    if admits threshold level then Some (source_for_name p name threshold)
    else None in
  if Saturn.Htbl.try_add decisions raw decision then decision
  else
    (* Concurrent misses may compute the same decision. Reuse the winner's
       cached option. This policy never removes or replaces pointer entries. *)
    Saturn.Htbl.find_exn decisions raw

let debug_source p raw =
  (* [find_exn] returns the cached option itself. [find_opt] would allocate an
     additional outer [Some] on each hit. [None] is a cached rejection, while
     [Not_found] means this address has not yet been resolved. *)
  match Saturn.Htbl.find_exn p.debug_decisions raw with
  | decision -> decision
  | exception Not_found -> first_use p p.debug_decisions Logs.Debug raw

(* Keep diagnostic decisions separate: a cached Debug or Warning rejection
   must not hide an Error from the same function. Sources are shared by name. *)
let diagnostic_source p decisions level raw =
  match Saturn.Htbl.find_exn decisions raw with
  | decision -> decision
  | exception Not_found -> first_use p decisions level raw

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
  (* Call after workers join. Include negative entries without registering
     Logs sources for them or retaining a second table of their names. *)
  let p = !policy in
  let encountered = List.concat_map (fun decisions ->
    Saturn.Htbl.to_seq decisions
      |> Seq.map (fun (raw, _) -> Cerb_log_names.canonical raw)
      |> List.of_seq) [p.debug_decisions; p.warn_decisions; p.err_decisions] in
  List.sort_uniq String.compare
    (encountered @ List.map Logs.Src.name (Logs.Src.list ()))

let debug raw message =
  let p = !policy in
  if p.debug_active then match debug_source p raw with
    | None -> ()
    | Some src -> Logs.debug ~src message

let warn raw message =
  let p = !policy in
  if p.warn_active then match diagnostic_source p p.warn_decisions Logs.Warning raw with
    | None -> ()
    | Some src -> Logs.warn ~src message

let err raw message =
  let p = !policy in
  if p.err_active then match diagnostic_source p p.err_decisions Logs.Error raw with
    | None -> ()
    | Some src -> Logs.err ~src message

(* Lem callbacks may emit zero or several strings. Invoke them only after
   selection, and make each emission a complete Logs call: skipping a message
   must not leave a reporter waiting for its [over] continuation. *)
let debug_string raw message =
  let p = !policy in
  if p.debug_active then match debug_source p raw with
    | None -> ()
    | Some src -> message (fun text -> Logs.debug ~src (fun m -> m "%s" text))

let warn_string raw message =
  let p = !policy in
  if p.warn_active then match diagnostic_source p p.warn_decisions Logs.Warning raw with
    | None -> ()
    | Some src -> message (fun text -> Logs.warn ~src (fun m -> m "%s" text))

let err_string raw message =
  let p = !policy in
  if p.err_active then match diagnostic_source p p.err_decisions Logs.Error raw with
    | None -> ()
    | Some src -> message (fun text -> Logs.err ~src (fun m -> m "%s" text))

let debug_located_string raw loc message =
  let p = !policy in
  if p.debug_active then match debug_source p raw with
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

(* The Lem facade supplies a prebuilt string. Avoid a second formatter for
   the unpadded [%s] case; all native OCaml formats use Format as usual. *)
let format_message : type a b.
    (string -> b) -> (a, Format.formatter, unit, b) format4 -> a =
  fun k ((CamlinternalFormatBasics.Format (fmt, _)) as format) ->
    match fmt with
    | CamlinternalFormatBasics.String
        (CamlinternalFormatBasics.No_padding, CamlinternalFormatBasics.End_of_format) -> k
    | _ -> Format.kasprintf k format

module Sources = Map.Make (struct
  type t = Logs.src
  let compare = Logs.Src.compare
end)

let level_index = function
  | Logs.App -> 0 | Logs.Error -> 1 | Logs.Warning -> 2 | Logs.Info -> 3 | Logs.Debug -> 4

let source_prefixes src =
  Array.of_list (List.map (fun level ->
    "[" ^ Logs.level_to_string (Some level) ^ "] " ^ Logs.Src.name src ^ ": ")
    [Logs.App; Logs.Error; Logs.Warning; Logs.Info; Logs.Debug])

(* Readers use immutable snapshots. A source registered after the reporter
   opens gets its prefixes on first use; CAS preserves simultaneous additions
   from other domains without taking the output mutex during formatting. *)
let text_prefixes () =
  List.fold_left (fun prefixes src ->
    Sources.add src (source_prefixes src) prefixes) Sources.empty (Logs.Src.list ())

let[@inline never] add_text_prefixes cache src =
  let values = source_prefixes src in
  let rec publish () =
    let before = Atomic.get cache in
    match Sources.find_opt src before with
    | Some values -> values
    | None ->
        if Atomic.compare_and_set cache before (Sources.add src values before)
        then values else publish () in
  publish ()

let cached_text_prefixes cache src =
  match Sources.find_opt src (Atomic.get cache) with
  | Some values -> values
  | None -> add_text_prefixes cache src

let open_reporter output format =
  try
    let channel, owned = match output with
      | Stderr -> stderr, false
      | Stdout -> stdout, false
      | File path -> open_out_gen [Open_creat; Open_wronly; Open_append; Open_binary] 0o666 path, true in
    let prefixes = Atomic.make (match format with Text -> text_prefixes () | Json -> Sources.empty) in
    let mutex = Mutex.create () in
    let closed = ref false in
    let close () = Cerb_log_compat.protect mutex (fun () ->
      if not !closed then begin
        closed := true;
        if owned then close_out channel else flush channel
      end) in
    let report src level ~over k msgf =
      msgf (fun ?header ?(tags = Logs.Tag.empty) fmt ->
        format_message (fun message ->
          let line = match format, header with
            | Text, None when Logs.Tag.is_empty tags ->
                let values = cached_text_prefixes prefixes src in
                String.concat "" [values.(level_index level); message; "\n"]
            | _ -> render format src level header tags message in
          Cerb_log_compat.protect mutex (fun () ->
            if !closed then invalid_arg "Cerb_log: reporter is closed";
            output_string channel line;
            flush channel);
          over ();
          k ()) fmt)
    in
    Ok ({ Logs.report }, close)
  with Sys_error msg -> Error msg
