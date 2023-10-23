val set_tagDefs: (Symbol.sym, Ctype.tag_definition) Pmap.map -> unit
val tagDefs: unit -> (Symbol.sym, Ctype.tag_definition) Pmap.map
val reset_tagDefs: unit -> unit

val with_tagDefs: (Symbol.sym, Ctype.tag_definition) Pmap.map -> (unit -> 'a) -> 'a