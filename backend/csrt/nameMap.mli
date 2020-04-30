type t

val sym_of : 
  Locations.t -> 
  string -> 
  t -> 
  (Sym.symbol,Location_ocaml.t * TypeErrors.type_error) Except.m

val name_of : 
  Locations.t -> 
  Sym.t -> 
  t -> 
  (string,Location_ocaml.t * TypeErrors.type_error) Except.m

val loc_of : 
  Locations.t -> 
  Sym.t -> 
  t  -> 
  (Locations.t,Location_ocaml.t * TypeErrors.type_error) Except.m

val all_names : 
  t ->
  (string * Sym.t) list

val empty : 
  t

val record : 
  Locations.t ->
  string ->
  Sym.t ->
  t ->
  t

val record_without_loc : 
  string ->
  Sym.t ->
  t ->
  t
