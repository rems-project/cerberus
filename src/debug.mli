(* val assert_false: unit -> 'a *)
val error: string -> 'a

val debug_level: int ref
val get_debug_level: unit -> int

val print_success: string -> unit
val print_debug: int -> string -> unit
val print_debug_located: int -> Location_ocaml.t -> string -> unit

(* val print_deubg2: string -> 'a -> 'a *)

val output_string2: string -> unit (* TODO: rename *)



(* Profiling stuff *)
val begin_timing: string -> unit
val end_timing: unit -> unit
