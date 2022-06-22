(* taking things from ocaml_locations *)


type t = Location_ocaml.t

type loc = t

type info = loc * string option

type path = t list

val unknown : t

val other : string -> t

val is_unknown_location : t -> bool

val pp : t -> PPrint.document

val to_string : t -> string

val good_location : Location_ocaml.t -> bool

val update : t -> Location_ocaml.t -> t

val updateB : t -> Location_ocaml.t -> t * bool

val log : path -> Location_ocaml.t -> path

val head_pos_of_location : t -> string * string

val unpack : t -> Location_ocaml.t

(* todo *)
val json_loc : t -> Yojson.Safe.t
val json_path : path -> Yojson.Safe.t

type region = Lexing.position * Lexing.position

val point: Lexing.position -> t
val region: region -> Location_ocaml.cursor -> t
val regions: region list -> Location_ocaml.cursor -> t



val simple_location : t -> string

val line_numbers : t -> (int * int) option

val is_region : t -> region option


