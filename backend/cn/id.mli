(* Module Id -- Utility functions for Cerberus identifiers

   This module adds a number of useful functions on identifiers to the
   ones already provided by Cerberus. *)

(* TODO: BCP: I'm a bit surprised that some of these are not already provided by Cerberus! *)

type t = Cerb_frontend.Symbol.identifier

val s : t -> string
val loc : t -> Cerb_location.t
val pp_string : t -> string
val pp : t -> PPrint.document
val equal : t -> t -> bool
val compare : t -> t -> int
val parse : Cerb_location.t -> string -> t
val id : string -> t
val is_str : String.t -> t -> bool
val subst : 'a -> 'b -> 'b
