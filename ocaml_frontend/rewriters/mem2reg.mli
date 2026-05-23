(** [analyse_file file] is a map. Its keys are the subset of
    [file.funs] keys which are [Proc _], and have a non-zero
    number of promotable function-local variables. The values
    are the symbols of those locals. Note that this list may
    include symbols not present in the user/Ail program, (ones
    generated during elaboration, e.g. when initialiser syntax
    is used).

    Promotable symbols are function-local, non-address-taken
    C variables — and, under [Inner_arg_callconv], callee-owned
    parameter temporaries — which are used only in a series of
    creates, stores, loads, and kills which do not have a weak-
    or un-sequenced races. *)
val analyse_file : unit Core.file -> (Symbol.sym, Symbol.sym list) Pmap.map

(** [transform_file file] returns [file] where [Proc _] in
    [file.funs] has some function-local variables promoted, i.e.
    the body has some series of creates, stores, loads, and kills
    replaced with pure variable bindings. It calls [analyse_file] to
    determine which variables are promotable. *)
val transform_file : unit Core.file -> unit Core.file
