type t

val unknown: t
val other: string -> t
val point: Lexing.position -> t
val region: Lexing.position * Lexing.position -> Lexing.position option -> t
val regions: (Lexing.position * Lexing.position) list -> Lexing.position option -> t

val with_cursor_from: t -> t -> t
val bbox_location: t list -> t
val with_regions_and_cursor: t list -> t option -> t

val from_main_file: t -> bool
val location_to_string: ?charon:bool -> t -> string

val to_json: t -> Json.json
val to_cartesian: t -> ((int * int) * (int * int)) option
val print_location: t -> PPrint.document
val pp_location: t -> PPrint.document
val head_pos_of_location: t -> (string * string)

val get_filename: t -> string option
