type cursor =
  | NoCursor
  | PointCursor of Lexing.position
  | RegionCursor of Lexing.position * Lexing.position

type t = private
  | Loc_unknown
  | Loc_other of string
  | Loc_point of Lexing.position
    (* start, end, cursor *)
  | Loc_region of Lexing.position * Lexing.position * cursor
  | Loc_regions of (Lexing.position * Lexing.position) list * cursor

val unknown: t
val is_unknown_location: t -> bool
val other: string -> t
val point: Lexing.position -> t
val region: Lexing.position * Lexing.position -> cursor -> t
val regions: (Lexing.position * Lexing.position) list -> cursor -> t

val with_cursor: t -> t (* NOTE: useful when pointing to an expanded macro *)
val with_cursor_from: t -> t -> t
val bbox_location: t list -> t
val with_regions_and_cursor: t list -> t option -> t

val from_main_file: t -> bool
val location_to_string: ?charon:bool -> t -> string

val to_json: t -> Cerb_json.json
val to_cartesian: t -> ((int * int) * (int * int)) option
val print_location: t -> PPrint.document
val pp_location: ?clever:bool -> t -> PPrint.document
val head_pos_of_location: t -> (string * string)

val get_filename: t -> string option

val is_unknown: t -> bool
val is_other: t -> string option


val simple_location : t -> string

val is_library_location: t -> bool

val line_numbers : t -> (int * int) option
