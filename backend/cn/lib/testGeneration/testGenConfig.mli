type t =
  { max_backtracks : int;
    max_unfolds : int;
    max_array_length : int
  }

val initialize : t -> unit

val get_max_backtracks : unit -> int

val get_max_unfolds : unit -> int

val get_max_array_length : unit -> int
