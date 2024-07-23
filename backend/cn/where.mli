type label = Cerb_frontend.Annot.label_annot

type section =
  | Label of
      { loc : Locations.t;
        label : label
      }
  | Body

type t = private
  { fnction : Sym.t option;
    section : section option;
    statement : Locations.t option;
    expression : Locations.t option
  }

val empty : t

val set_function : Sym.t -> t -> t

val set_section : section -> t -> t

val set_statement : Locations.t -> t -> t

val set_expression : Locations.t -> t -> t

val label_prefix : label -> string

val pp_section : section -> Pp.document
