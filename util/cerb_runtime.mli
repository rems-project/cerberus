(** Discover the path to the Cerberus runtime. *)

(** [specified_runtime] can be used to override the runtime that is "detected"
    by the [runtime] function. Its initial value is [None], and it must be set
    before the first call to [runtime] otherwise it is not taken into account.
    This flag is useful to, e.g., override the runtime patch from the CLI. *)
val specified_runtime : string option ref

type runtime_loc = {
  cerblib_sourceroot_opt: string option;
  mk: pkg:string -> [ `SPECIFIED | `ENV_VAR | `OPAM ] * string;
}

(** [runtime ()] detects and returns an absolute path to the Cerberus runtime.
    If [specified_runtime] is set then its value is used, and otherwise if the
    [CERB_INSTALL_PREFIX] environment variable is set then its value is used.
    If none of these are set and the function runs in build mode (i.e., from a
    program run with [dune exec]) in the Cerberus source tree, the local
    runtime is found by detecting dune's [_build] directory in the [PATH] and
    the cerberus-lib.opam file. Otherwise it is assumed that the runtime is
    installed under the Opam switch prefix, as part of the Cerberus library
    folder. Note that this relies on Opam being used and properly configured.
    The exception [Failure] can be raised if that is not the case. Note also
    that the actual detection of the runtime only runs for the first call
    to [runtime ()]. In subsequent calls the result is returned directly. *)
val runtime : unit -> runtime_loc

(** [in_runtime pkg path] appends [path] to the Cerberus' package [pkg]
    (["cerberus-lib"] when absent) runtime path (as returned by [runtime ()].
    Exceptions [Failure] can be raised accordingly. *)
val in_runtime : ?pkg:string -> string -> string
