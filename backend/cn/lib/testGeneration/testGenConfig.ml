type t =
  { (* Compile time *)
    num_samples : int;
    max_backtracks : int;
    max_unfolds : int option;
    max_array_length : int;
    (* Run time *)
    null_in_every : int option;
    seed : string option;
    logging_level : int option;
    interactive : bool;
    until_timeout : int option;
    exit_fast : bool;
    max_stack_depth : int option;
    allowed_depth_failures : int option;
    max_generator_size : int option;
    random_size_splits : bool;
    sized_null : bool;
    coverage : bool;
    disable_passes : string list
  }

let default =
  { num_samples = 100;
    max_backtracks = 25;
    max_unfolds = None;
    max_array_length = 50;
    null_in_every = None;
    seed = None;
    logging_level = None;
    interactive = false;
    until_timeout = None;
    exit_fast = false;
    max_stack_depth = None;
    allowed_depth_failures = None;
    max_generator_size = None;
    random_size_splits = false;
    sized_null = false;
    coverage = false;
    disable_passes = []
  }


let instance = ref default

let initialize (cfg : t) = instance := cfg

let get_num_samples () = !instance.num_samples

let get_max_backtracks () = !instance.max_backtracks

let get_max_unfolds () = !instance.max_unfolds

let get_max_array_length () = !instance.max_array_length

let has_null_in_every () = !instance.null_in_every

let has_seed () = !instance.seed

let has_logging_level () = !instance.logging_level

let is_interactive () = !instance.interactive

let is_until_timeout () = !instance.until_timeout

let is_exit_fast () = !instance.exit_fast

let has_max_stack_depth () = !instance.max_stack_depth

let has_allowed_depth_failures () = !instance.allowed_depth_failures

let has_max_generator_size () = !instance.max_generator_size

let is_random_size_splits () = !instance.random_size_splits

let is_sized_null () = !instance.sized_null

let is_coverage () = !instance.coverage

let has_pass s = not (List.mem String.equal s !instance.disable_passes)
