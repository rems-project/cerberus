type build_tool = Bash

type logging_level =
  | None
  | Error
  | Info

type trace_granularity =
  | None
  | End
  | All

type progress_level =
  | Silent
  | PerFunc
  | PerTestCase

type sizing_strategy =
  | Uniform
  | Quartile
  | QuickCheck

type t =
  { (* Compile time *)
    num_samples : int;
    max_backtracks : int;
    max_unfolds : int option;
    max_array_length : int;
    with_static_hack : bool;
    build_tool : build_tool;
    sanitizers : string option * string option;
    (* Run time *)
    input_timeout : int option;
    null_in_every : int option;
    seed : string option;
    logging_level : logging_level option;
    trace_granularity : trace_granularity option;
    progress_level : progress_level option;
    until_timeout : int option;
    exit_fast : bool;
    max_stack_depth : int option;
    allowed_depth_failures : int option;
    max_generator_size : int option;
    sizing_strategy : sizing_strategy option;
    random_size_splits : bool;
    allowed_size_split_backtracks : int option;
    sized_null : bool;
    coverage : bool;
    disable_passes : string list;
    trap : bool
  }

val default : t

module Options : sig
  val build_tool : (string * build_tool) list

  val logging_level : (string * logging_level) list

  val trace_granularity : (string * trace_granularity) list

  val progress_level : (string * progress_level) list

  val sizing_strategy : (string * sizing_strategy) list
end

val initialize : t -> unit

val get_num_samples : unit -> int

val get_max_backtracks : unit -> int

val get_max_unfolds : unit -> int option

val get_max_array_length : unit -> int

val with_static_hack : unit -> bool

val get_build_tool : unit -> build_tool

val has_sanitizers : unit -> string option * string option

val has_input_timeout : unit -> int option

val has_null_in_every : unit -> int option

val has_seed : unit -> string option

val has_logging_level : unit -> logging_level option

val has_logging_level_str : unit -> string option

val has_trace_granularity : unit -> trace_granularity option

val has_trace_granularity_str : unit -> string option

val has_progress_level : unit -> progress_level option

val has_progress_level_str : unit -> string option

val is_until_timeout : unit -> int option

val is_exit_fast : unit -> bool

val has_max_stack_depth : unit -> int option

val has_allowed_depth_failures : unit -> int option

val has_max_generator_size : unit -> int option

val has_sizing_strategy : unit -> sizing_strategy option

val has_sizing_strategy_str : unit -> string option

val is_random_size_splits : unit -> bool

val has_allowed_size_split_backtracks : unit -> int option

val is_sized_null : unit -> bool

val is_coverage : unit -> bool

val has_pass : string -> bool

val is_trap : unit -> bool
