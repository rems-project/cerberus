type t

(** A placeholder position *)
val dummy: t

(** A position in the pre-processed file. The source file and line are
the same as the pre-processed file *)
val from_lexing: Lexing.position -> t

(** Change the column number by the given amount. *)
val change_cnum: t -> int -> t

(** Set the file and line in the original source file. *)
val set_source: (string * int) -> t -> t

(** Source file for position *)
val file: t -> string

(** Source line for the position. 1 based *)
val line: t -> int

(** Column of position, 1 based. *)
val column: t -> int


(** Location in the pre-processed file *)
val to_file_lexing: t -> Lexing.position



module LineMap : sig
  (** Information about original source locations in a pre-processed file. *)
  type t

  (** No source location information. The argument is the name of the
      pre-processed file, which will be used for locations that have no
      additional information. *)
  val empty: string -> t

  (** [add line (srouce_file, souce_line) mp] updates [mp] with the
      information that on line [line] of the pre-processd file there was
      a declaration that the following lines
      correspond to [(source_file,souce_line)] *)
  val add: int -> (string * int) -> t -> t

  (** [lookup line mp] consults [mp] to get source information about [line]
      in the prepcoessed file.   If there is no additional source information
      we return a location in the pre-processed file. *)
  val lookup: int -> t -> (string * int)

  (** Display the line map, for debugging. *)
  val dump: t -> unit
end
