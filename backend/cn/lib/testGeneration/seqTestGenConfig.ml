type t =
  { (* Compile time *)
    num_samples : int;
    max_backtracks : int;
    num_resets : int
  }

let default = { num_samples = 100; max_backtracks = 25; num_resets = 0 }

let instance = ref default

let initialize (cfg : t) = instance := cfg

let get_num_samples () = !instance.num_samples

let get_max_backtracks () = !instance.max_backtracks

let get_max_resets () = !instance.num_resets
