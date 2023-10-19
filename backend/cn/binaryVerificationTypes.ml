type t = {
  filename_elf : string;
  filename_objdump : string;
  coq : out_channel;
  coq_dir : string;
}

let args : t option ref = ref None

let when_args_exist (f : t -> unit) : unit =
  Option.iter f !args

let enabled () : bool = Option.is_some !args

module Make(M : Effectful.S) = struct
  open M

  let when_args_exist_m (f : t -> unit m) : unit m =
    Option.fold ~none:(return ()) ~some:f !args
end