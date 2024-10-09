type t =
  { max_backtracks : int;
    max_unfolds : int;
    max_array_length : int
  }

let default = { max_backtracks = 10; max_unfolds = 10; max_array_length = 50 }

let instance = ref default

let initialize (cfg : t) = instance := cfg

let get_max_backtracks () = !instance.max_backtracks

let get_max_unfolds () = !instance.max_unfolds

let get_max_array_length () = !instance.max_array_length
