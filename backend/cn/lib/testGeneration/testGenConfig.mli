type t =
  { (* Compile time *)
    max_backtracks : int;
    max_unfolds : int;
    max_array_length : int;
    (* Run time *)
    seed : string option;
    logging_level : int option;
    interactive : bool
  }

val default : t

val initialize : t -> unit

val get_max_backtracks : unit -> int

val get_max_unfolds : unit -> int

val get_max_array_length : unit -> int

val has_seed : unit -> string option

val has_logging_level : unit -> int option

val is_interactive : unit -> bool
