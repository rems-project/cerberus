(* Module Locations -- Utility functions for Cerberus locations

   This module adds a number of useful functions on locations to the ones already provided
   by Cerberus. *)

(* taking things from ocaml_locations *)
(* TODO: BCP: What does that mean? *)

type t = Cerb_location.t

type info = t * string option

type path = t list

(* TODO: BCP: All the rest could perhaps be organized a little... *)

val other : string -> t

val is_unknown_location : t -> bool

val pp : t -> PPrint.document

val to_string : t -> string

val good_location : Cerb_location.t -> bool

val update : t -> Cerb_location.t -> t

val updateB : t -> Cerb_location.t -> t * bool

val log : path -> Cerb_location.t -> path

val head_pos_of_location : t -> string * string

val unpack : t -> Cerb_location.t

(* TODO: BCP: What's to do? *)
(* todo *)
val json_loc : t -> Yojson.Safe.t

val json_path : path -> Yojson.Safe.t

type region = Cerb_position.t * Cerb_position.t

val point : Cerb_position.t -> t

val region : region -> Cerb_location.cursor -> t

val regions : region list -> Cerb_location.cursor -> t

val simple_location : t -> string

val line_numbers : t -> (int * int) option

val is_region : t -> region option

val start_pos : t -> Cerb_position.t option

val end_pos : t -> Cerb_position.t option

val get_region : t -> (Cerb_position.t * Cerb_position.t * Cerb_location.cursor) option
