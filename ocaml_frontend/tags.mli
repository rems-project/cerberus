val set_tagDefs: (Symbol.sym, Cerb_location.t * Ctype.tag_definition) Pmap.map -> unit
val tagDefs: unit -> (Symbol.sym, Cerb_location.t * Ctype.tag_definition) Pmap.map
val reset_tagDefs: unit -> unit

val with_tagDefs: (Symbol.sym, Cerb_location.t * Ctype.tag_definition) Pmap.map -> (unit -> 'a) -> 'a
