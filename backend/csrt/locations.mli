type t

val unknown : t

val pp : t -> Pp.document

val precise : t -> Location_ocaml.t -> t

val update : t -> Cerb_frontend.Annot.annot list -> t

val head_pos_of_location : t -> string * string
