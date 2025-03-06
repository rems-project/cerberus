type build_tool = Bash

type logging_level =
  | None
  | Error
  | Info

type trace_granularity =
  | None
  | Ends
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
    trap : bool;
    replicas : bool
  }

let default =
  { num_samples = 100;
    max_backtracks = 25;
    max_unfolds = None;
    max_array_length = 50;
    with_static_hack = false;
    build_tool = Bash;
    sanitizers = (None, None);
    input_timeout = None;
    null_in_every = None;
    seed = None;
    logging_level = None;
    trace_granularity = None;
    progress_level = None;
    until_timeout = None;
    exit_fast = false;
    max_stack_depth = None;
    allowed_depth_failures = None;
    max_generator_size = None;
    sizing_strategy = None;
    random_size_splits = false;
    allowed_size_split_backtracks = None;
    sized_null = false;
    coverage = false;
    disable_passes = [];
    trap = false;
    replicas = false
  }


let string_of_logging_level (logging_level : logging_level) =
  match logging_level with None -> "none" | Error -> "error" | Info -> "info"


let string_of_trace_granularity (trace_granularity : trace_granularity) =
  match trace_granularity with None -> "none" | Ends -> "ends" | All -> "all"


let string_of_progress_level (progress_level : progress_level) =
  match progress_level with
  | Silent -> "silent"
  | PerFunc -> "function"
  | PerTestCase -> "testcase"


let string_of_sizing_strategy (sizing_strategy : sizing_strategy) =
  match sizing_strategy with
  | Uniform -> "uniform"
  | Quartile -> "quartile"
  | QuickCheck -> "quickcheck"


module Options = struct
  let build_tool = [ ("bash", Bash) ]

  let logging_level : (string * logging_level) list =
    List.map (fun lvl -> (string_of_logging_level lvl, lvl)) [ None; Error; Info ]


  let trace_granularity : (string * trace_granularity) list =
    List.map (fun gran -> (string_of_trace_granularity gran, gran)) [ None; Ends; All ]


  let progress_level : (string * progress_level) list =
    List.map
      (fun lvl -> (string_of_progress_level lvl, lvl))
      [ Silent; PerFunc; PerTestCase ]


  let sizing_strategy : (string * sizing_strategy) list =
    List.map
      (fun strat -> (string_of_sizing_strategy strat, strat))
      [ Uniform; Quartile; QuickCheck ]
end

let instance = ref default

let initialize (cfg : t) = instance := cfg

let get_num_samples () = !instance.num_samples

let get_max_backtracks () = !instance.max_backtracks

let get_max_unfolds () = !instance.max_unfolds

let get_max_array_length () = !instance.max_array_length

let with_static_hack () = !instance.with_static_hack

let get_build_tool () = !instance.build_tool

let has_sanitizers () = !instance.sanitizers

let has_input_timeout () = !instance.input_timeout

let has_null_in_every () = !instance.null_in_every

let has_seed () = !instance.seed

let has_logging_level () = !instance.logging_level

let has_logging_level_str () = Option.map string_of_logging_level !instance.logging_level

let has_trace_granularity () = !instance.trace_granularity

let has_trace_granularity_str () =
  Option.map string_of_trace_granularity !instance.trace_granularity


let has_progress_level () = !instance.progress_level

let has_progress_level_str () =
  Option.map string_of_progress_level !instance.progress_level


let is_until_timeout () = !instance.until_timeout

let is_exit_fast () = !instance.exit_fast

let has_max_stack_depth () = !instance.max_stack_depth

let has_allowed_depth_failures () = !instance.allowed_depth_failures

let has_max_generator_size () = !instance.max_generator_size

let has_sizing_strategy () = !instance.sizing_strategy

let has_sizing_strategy_str () =
  Option.map string_of_sizing_strategy !instance.sizing_strategy


let is_random_size_splits () = !instance.random_size_splits

let has_allowed_size_split_backtracks () = !instance.allowed_size_split_backtracks

let is_sized_null () = !instance.sized_null

let is_coverage () = !instance.coverage

let has_pass s = not (List.mem String.equal s !instance.disable_passes)

let is_trap () = !instance.trap

let has_replicas () = !instance.replicas
