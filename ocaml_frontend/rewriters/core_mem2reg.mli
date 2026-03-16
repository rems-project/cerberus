(** Promote function-local, non-address-taken C variables — and, under
    [Inner_arg_callconv], callee-owned parameter temporaries — from
    Create/Store0/Load0/Kill sequences to pure Core let-bindings.
    Which categories are considered is determined by
    [file.calling_convention]. *)

val transform_file : unit Core.file -> unit Core.file
