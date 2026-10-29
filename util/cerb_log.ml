(* These severity adapters are for Lem, whose format strings are not OCaml's.
   OCaml callers use Logs directly. Filtering happens before forcing [msg]. *)
let info src msg = Logs.info ~src (fun m -> m "%s" (msg ()))
let warn src msg = Logs.warn ~src (fun m -> m "%s" (msg ()))
let err src msg = Logs.err ~src (fun m -> m "%s" (msg ()))

let location_tag = Logs.Tag.def "location" Format.pp_print_string
let translation_unit_tag = Logs.Tag.def "translation_unit" Format.pp_print_string
let debug_located src loc msg =
  Logs.debug ~src (fun m ->
    let tags = Logs.Tag.(add location_tag (Cerb_location.location_to_string loc) empty) in
    m ~tags "%s" (msg ()))

let with_lock mutex f =
  Mutex.lock mutex;
  Fun.protect ~finally:(fun () -> Mutex.unlock mutex) f

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
    let close () = with_lock mutex (fun () ->
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
          with_lock mutex (fun () ->
            if !closed then invalid_arg "Cerb_log: reporter is closed";
            output_string channel line;
            flush channel);
          over ();
          k ()) fmt)
    in
    Ok ({ Logs.report }, close)
  with Sys_error msg -> Error msg
