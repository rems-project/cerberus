type t

type loc = t
type path = t List1.t

val unknown : t

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
