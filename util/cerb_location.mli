
type cursor =
  | NoCursor
  | PointCursor of Cerb_position.t
  | RegionCursor of Cerb_position.t * Cerb_position.t

type t = private
  | Loc_unknown
  | Loc_other of string
  | Loc_point of Cerb_position.t
    (* start, end, cursor *)
  | Loc_region of Cerb_position.t * Cerb_position.t * cursor
  | Loc_regions of (Cerb_position.t * Cerb_position.t) list * cursor

val unknown: t
val is_unknown_location: t -> bool
val other: string -> t
val point: Cerb_position.t -> t
val region: Cerb_position.t * Cerb_position.t -> cursor -> t
val regions: (Cerb_position.t * Cerb_position.t) list -> cursor -> t

val with_cursor: t -> t (* NOTE: useful when pointing to an expanded macro *)
val with_cursor_from: t -> t -> t
val bbox: t list -> [ `Bbox of Cerb_position.t * Cerb_position.t | `Other of t ]
val bbox_location: t list -> t
val with_regions_and_cursor: t list -> t option -> t

val from_main_file: t -> bool
val location_to_string: ?charon:bool -> t -> string

val to_json: t -> Cerb_json.json

(** The range corresponding to this location, in the user visible source.
Returns ((start_line, start_col), (end_line, end_col)) *)
val to_cartesian_user: t -> ((int * int) * (int * int)) option


(** The range corresponding to this location,
in the actual (pre-processed) source.
Returns ((start_line, start_col), (end_line, end_col)) *)
val to_cartesian_raw: t -> ((int * int) * (int * int)) option



val print_location: t -> PPrint.document
val pp_location: ?clever:bool -> t -> PPrint.document
val head_pos_of_location: t -> (string * string)

val get_filename: t -> string option

val is_unknown: t -> bool
val is_other: t -> string option


val simple_location : t -> string

val is_library_location: t -> bool

val line_numbers : t -> (int * int) option
