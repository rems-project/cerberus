type t =
  { (* Compile time *)
    num_samples : int;
    max_backtracks : int;
    num_resets : int
  }

val default : t

val initialize : t -> unit

val get_num_samples : unit -> int

val get_max_backtracks : unit -> int

val get_max_resets : unit -> int
