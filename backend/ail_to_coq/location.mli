open Extra

type t

type loc_data =
  { loc_key   : int
  ; loc_file  : string
  ; loc_line1 : int
  ; loc_col1  : int
  ; loc_line2 : int
  ; loc_col2  : int }

val none : unit -> t
val make : string -> int -> int -> int -> int -> t
val get : t -> loc_data option

val iter : (loc_data -> unit) -> unit

val pp_data : loc_data pp
val pp_loc : t pp

type 'a located = { elt : 'a ; loc : t }
