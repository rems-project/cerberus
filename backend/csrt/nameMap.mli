open Except

type t

val sym_of : 
  Locations.t -> 
  string -> 
  t -> 
  Sym.symbol m

val name_of : 
  Locations.t -> 
  Sym.t -> 
  t -> 
  string m

val loc_of : 
  Locations.t -> 
  Sym.t -> 
  t  -> 
  Locations.t m

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
