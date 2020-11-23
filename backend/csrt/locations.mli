type t

type loc = t
type path = t OneList.t

val unknown : t

val is_unknown : t -> bool

val pp : t -> PPrint.document

val update : t -> Location_ocaml.t -> t

val log : path -> Location_ocaml.t -> path

val head_pos_of_location : t -> string * string

val unpack : t -> Location_ocaml.t


val one : path -> loc
