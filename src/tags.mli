type tag_definition =
  | StructDef of (Cabs.cabs_identifier * Core_ctype.ctype0) list
  | UnionDef of (Cabs.cabs_identifier * Core_ctype.ctype0) list

val set_tagDefs: (Symbol.sym, tag_definition) Pmap.map -> unit
val tagDefs: unit -> (Symbol.sym, tag_definition) Pmap.map
val reset_tagDefs: unit -> unit
