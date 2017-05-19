type domain =
  | DB_clexer
  | DB_cparser
  | DB_desugaring
  | DB_ail_typing
  | DB_elaboration
  | DB_core_typing
  | DB_core_dynamics
  | DB_driver
  | DB_concurrency
  | DB_driver_step
  | DB_memory


(* val assert_false: unit -> 'a *)
val error: string -> 'a

val debug_level: int ref
val get_debug_level: unit -> int

val print_success: string -> unit
val print_debug: int -> domain list -> string -> unit
val print_debug_located: int -> domain list -> Location_ocaml.t -> string -> unit
val warn: domain list -> string -> unit

(* val print_deubg2: string -> 'a -> 'a *)

val output_string2: string -> unit (* TODO: rename *)



(* Profiling stuff *)
val begin_timing: string -> unit
val end_timing: unit -> unit
