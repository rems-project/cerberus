type t =
  { (* Compile time *)
    max_backtracks : int;
    max_unfolds : int;
    max_array_length : int;
    (* Run time *)
    null_in_every : int option;
    seed : string option;
    logging_level : int option;
    interactive : bool
  }

let default =
  { max_backtracks = 10;
    max_unfolds = 5;
    max_array_length = 50;
    null_in_every = None;
    seed = None;
    logging_level = None;
    interactive = false
  }


let instance = ref default

let initialize (cfg : t) = instance := cfg

let get_max_backtracks () = !instance.max_backtracks

let get_max_unfolds () = !instance.max_unfolds

let get_max_array_length () = !instance.max_array_length

let has_null_in_every () = !instance.null_in_every

let has_seed () = !instance.seed

let has_logging_level () = !instance.logging_level

let is_interactive () = !instance.interactive
