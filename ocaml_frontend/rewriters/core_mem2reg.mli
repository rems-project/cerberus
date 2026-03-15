(** Promote function-local, non-address-taken C variables from
    Create/Store0/Load0/Kill sequences to pure Core let-bindings. *)

val transform_file : unit Core.file -> unit Core.file
