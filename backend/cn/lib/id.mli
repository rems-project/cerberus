(* Module Id -- Utility functions for Cerberus identifiers

   This module adds a number of useful functions on identifiers to the ones already
   provided by Cerberus. *)

type t = Cerb_frontend.Symbol.identifier

val get_string : t -> string

val get_loc : t -> Cerb_location.t

val pp : t -> PPrint.document

val equal : t -> t -> bool

val compare : t -> t -> int

val make : Cerb_location.t -> string -> t

val equal_string : String.t -> t -> bool

val subst : 'a -> 'b -> 'b
