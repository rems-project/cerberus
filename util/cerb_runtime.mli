(** Discover the path to the Cerberus runtime. *)

val set_package : string -> unit

(** [specified_runtime] can be used to override the runtime that is "detected"
    by the [runtime] function. Its initial value is [None], and it must be set
    before the first call to [runtime] otherwise it is not taken into account.
    This flag is useful to, e.g., override the runtime patch from the CLI. *)
val specified_runtime : string option ref

(** [runtime ()] detects and returns an absolute path to the Cerberus runtime.
    If [specified_runtime] is set then its value is used, and otherwise if the
    [CERB_RUNTIME] environment variable is set then its value is used. If none
    of these are set and the function runs in build mode (i.e., from a program
    run with [dune exec]) then the runtime is looked for under dune's [_build]
    directory. Otherwise it is assumed that the runtime is installed under the
    Opam switch prefix, as part of the Cerberus library folder. Note that this
    relies on Opam being used and properly configured. The exception [Failure]
    can be raised if that is not the case. Note also that the actual detection
    of the runtime only runs for the first call to [runtime ()]. In subsequent
    calls the result is returned directly. *)
val runtime : unit -> string

(** [in_runtime path] appends [path] to the Cerberus runtime path (as returned
    by [runtime ()]. Exceptions [Failure] can be raised accordingly. *)
val in_runtime : string -> string
