val set_tagDefs: (Cerb_symbol.Sym.t, Cerb_location.t * Ctype.tag_definition) Pmap.map -> unit
val tagDefs: unit -> (Cerb_symbol.Sym.t, Cerb_location.t * Ctype.tag_definition) Pmap.map
val reset_tagDefs: unit -> unit

val with_tagDefs: (Cerb_symbol.Sym.t, Cerb_location.t * Ctype.tag_definition) Pmap.map -> (unit -> 'a) -> 'a
