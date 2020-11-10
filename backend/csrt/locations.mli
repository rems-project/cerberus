type t

val unknown : t

val is_unknown : t -> bool

val pp : t -> Pp.document

val update : t -> Location_ocaml.t -> t

val update_a : t -> Cerb_frontend.Annot.annot list -> t

val head_pos_of_location : t -> string * string


val unpack : t -> Location_ocaml.t
