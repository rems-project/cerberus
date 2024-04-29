(* taking things from ocaml_locations *)


type t = Cerb_location.t

type loc = t

type info = loc * string option

type path = t list

val other : string -> t

val is_unknown_location : t -> bool

val pp : t -> PPrint.document

val to_string : t -> string

val good_location : Cerb_location.t -> bool

val update : t -> Cerb_location.t -> t

val updateB : t -> Cerb_location.t -> t * bool

val log : path -> Cerb_location.t -> path

val head_pos_of_location : t -> string * string

val unpack : t -> Cerb_location.t

(* todo *)
val json_loc : t -> Yojson.Safe.t
val json_path : path -> Yojson.Safe.t

type region = Lexing.position * Lexing.position

val point: Lexing.position -> t
val region: region -> Cerb_location.cursor -> t
val regions: region list -> Cerb_location.cursor -> t



val simple_location : t -> string

val line_numbers : t -> (int * int) option

val is_region : t -> region option

val start_pos : t -> Lexing.position option

val end_pos : t -> Lexing.position option

val get_region : t -> (Lexing.position * Lexing.position * Cerb_location.cursor) option

