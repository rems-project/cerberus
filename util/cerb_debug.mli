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
  | DB_core_rewriting


(* val assert_false: unit -> 'a *)
val error: string -> 'a

val debug_level: int ref
val get_debug_level: unit -> int

val print_success: string -> unit
val print_debug: int -> domain list -> (unit -> string) -> unit
val print_debug_located: int -> domain list -> Cerb_location.t -> (unit -> string) -> unit
val print_unsupported: string -> unit
val warn: ?always:bool -> domain list -> (unit -> string) -> unit

(* val print_deubg2: string -> 'a -> 'a *)

val output_string2: string -> unit (* TODO: rename *)



(* Profiling stuff *)
val begin_timing: string -> unit
val end_timing: unit -> unit

val begin_csv_timing: unit -> unit
val end_csv_timing: string -> unit


val maybe_open_csv_timing_file: unit -> unit
val maybe_close_csv_timing_file: unit -> unit
val maybe_close_csv_timing_file_no_err: unit -> unit
