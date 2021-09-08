(* taking things from ocaml_locations *)


type t = Location_ocaml.t

type loc = t

type info = loc * string option

type path = t List1.t

val unknown : t

val other : string -> t

val is_unknown : t -> bool

val pp : t -> PPrint.document

val good_location : Location_ocaml.t -> bool

val update : t -> Location_ocaml.t -> t

val updateB : t -> Location_ocaml.t -> t * bool

val log : path -> Location_ocaml.t -> path

val head_pos_of_location : t -> string * string

val unpack : t -> Location_ocaml.t

(* todo *)
val json_loc : t -> Yojson.Safe.t
val json_path : path -> Yojson.Safe.t


val point: Lexing.position -> t
val region: Lexing.position * Lexing.position -> Lexing.position option -> t
val regions: (Lexing.position * Lexing.position) list -> Lexing.position option -> t



val simple_location : t -> string
