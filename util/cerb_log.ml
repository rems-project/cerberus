(* These severity adapters are for Lem, whose format strings are not OCaml's.
   OCaml callers use Logs directly. Filtering happens before forcing [msg]. *)
let info src msg = Logs.info ~src (fun m -> m "%s" (msg ()))
let warn src msg = Logs.warn ~src (fun m -> m "%s" (msg ()))
let err src msg = Logs.err ~src (fun m -> m "%s" (msg ()))

let location_tag = Logs.Tag.def "location" Format.pp_print_string
let translation_unit_tag = Logs.Tag.def "translation_unit" Format.pp_print_string
let log_located src loc msg =
  Logs.debug ~src (fun m ->
    let tags = Logs.Tag.(add location_tag (Cerb_location.location_to_string loc) empty) in
    m ~tags "%s" (msg ()))

(* Configure once before starting workers. The policy, selector table and
   source levels remain unchanged until all workers have joined. Only the
   memo table and source registry grow during use. Source creation is serialized;
   both tables support concurrent lookup. *)
external pointer_hash : string -> int = "cerb_log_pointer_hash" [@@noalloc]
external is_static : string -> bool = "cerb_log_is_static" [@@noalloc]
module Pointer = struct
  type t = string
  let equal = (==)
  let hash = pointer_hash
end

type policy = {
  active : bool;
  select : string -> bool;
  pointers : (string, Logs.src option) Saturn.Htbl.t;
  sources : (string, Logs.src) Saturn.Htbl.t;
  sources_mutex : Mutex.t;
}

let fresh active select = {
  active; select;
  pointers = Saturn.Htbl.create ~hashed_type:(module Pointer) ();
  sources = Saturn.Htbl.create ~hashed_type:(module String) ();
  sources_mutex = Mutex.create ();
}
let policy = ref (fresh false (fun _ -> false))

let source_for_name p name =
  match Saturn.Htbl.find_exn p.sources name with
  | src -> src
  | exception Not_found ->
      (* Different static addresses can name the same function. Recheck under
         the creation mutex: a losing [try_add] cannot undo [Logs.Src.create]'s
         global registration. Publish only after configuring the new source. *)
      Mutex.protect p.sources_mutex (fun () ->
        match Saturn.Htbl.find_exn p.sources name with
        | src -> src
        | exception Not_found ->
            let src = Logs.Src.create name in
            Logs.Src.set_level src (Some Logs.Debug);
            ignore (Saturn.Htbl.try_add p.sources name src);
            src)

let[@inline never] first_use p raw =
  (* Heap strings can move, changing their address hash. They never enter the
     table. Looking one up before this check cannot match a static address;
     validation therefore belongs only on the miss path. *)
  if not (is_static raw) then
    invalid_arg "Cerb_log: expected a static source name (use __FUNCTION__)";
  let name = Cerb_log_names.canonical raw in
  let decision = if p.select name then Some (source_for_name p name) else None in
  if Saturn.Htbl.try_add p.pointers raw decision then decision
  else
    (* Concurrent misses may compute the same decision. Reuse the winner's
       cached option. This policy never removes or replaces pointer entries. *)
    Saturn.Htbl.find_exn p.pointers raw

let source p raw =
  (* [find_exn] returns the cached option itself. [find_opt] would allocate an
     additional outer [Some] on each hit. [None] is a cached rejection, while
     [Not_found] means this address has not yet been resolved. *)
  match Saturn.Htbl.find_exn p.pointers raw with
  | decision -> decision
  | exception Not_found -> first_use p raw

let configure ?(discover=false) level selectors =
  List.iter (fun name ->
    if name <> "all" && not (Cerb_log_names.valid_selector name) then
      invalid_arg ("invalid debug selector: " ^ name)) selectors;
  let all = level = Some Logs.Debug || List.mem "all" selectors in
  let active = level <> None && (all || selectors <> []) in
  let select = if not active then (fun _ -> false) else if all then (fun _ -> true)
    else Cerb_log_names.selected selectors in
  (* Listing observes disabled sites too, without enabling their messages. *)
  let p = fresh (active || discover) select in
  List.iter (fun src ->
    let name = Logs.Src.name src in
    Logs.Src.set_level src (if select name then Some Logs.Debug else level);
    if not (Saturn.Htbl.try_add p.sources name src) then
      ignore (Saturn.Htbl.try_set p.sources name src)) (Logs.Src.list ());
  policy := p

let sources () =
  (* Call after workers join. Include negative entries without registering
     Logs sources for them or retaining a second table of their names. *)
  let encountered = Saturn.Htbl.to_seq (!policy).pointers
    |> Seq.map (fun (raw, _) -> Cerb_log_names.canonical raw)
    |> List.of_seq in
  List.sort_uniq String.compare
    (encountered @ List.map Logs.Src.name (Logs.Src.list ()))

let debug_enabled raw =
  let p = !policy in
  p.active && Option.is_some (source p raw)

let debugf raw message =
  let p = !policy in
  if p.active then match source p raw with
    | None -> ()
    | Some src -> Logs.debug ~src message

let debug raw message =
  let p = !policy in
  if p.active then match source p raw with
    | None -> ()
    | Some src -> Logs.debug ~src (fun m -> m "%s" (message ()))

let debug_located raw loc message =
  let p = !policy in
  if p.active then match source p raw with
    | None -> ()
    | Some src -> log_located src loc message

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
      fields ["location", location_tag; "translation_unit", translation_unit_tag] in
  let extra = Logs.Tag.fold (fun (Logs.Tag.V (def, value)) acc ->
      let name = Logs.Tag.name def in
      if List.mem name ["location"; "translation_unit"] then acc
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
         suffix translation_unit_tag; suffix location_tag;
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
    let close () = Mutex.protect mutex (fun () ->
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
          Mutex.protect mutex (fun () ->
            if !closed then invalid_arg "Cerb_log: reporter is closed";
            output_string channel line;
            flush channel);
          over ();
          k ()) fmt)
    in
    Ok ({ Logs.report }, close)
  with Sys_error msg -> Error msg
