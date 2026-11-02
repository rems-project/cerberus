(** Logging with automatic function sources.

    Pass [__FUNCTION__] directly. Names must contain a qualified function
    component. Globally disabled severities return immediately, unless
    discovery was requested. Logging supports concurrent threads and OCaml 5
    domains. *)

val configure : ?discover:bool -> Logs.level option -> string list -> unit
(** Configure before workers start, or after all have joined. Selectors
    are exact [Module] or [Module.function] names, or [all]. Source levels and
    the reporter must not be reconfigured concurrently with logging. Invalid
    selector syntax raises [Invalid_argument]; unseen names are allowed.
    Selected sources have a Debug threshold; other sources use [level].
    [None] suppresses every level, including selected sources.
    [discover] defaults to [false]. When [true], record encountered names even
    with logging disabled, without evaluating disabled message callbacks. *)

val sources : unit -> string list
(** After workers join, list sorted, unique explicit sources and automatic
    names encountered under this policy, including disabled sites when discovery is enabled.
    Unvisited automatic sites are absent. *)

val debug : string -> 'a Logs.log
val info : string -> 'a Logs.log
val warn : string -> 'a Logs.log
val err : string -> 'a Logs.log
(** OCaml call sites use [debug __FUNCTION__ (fun m -> m "value: %a" pp v)].
    The callback, including format arguments, printers and tags, is evaluated
    only when enabled. *)

val debug_string : string -> ((string -> unit) -> unit) -> unit
val warn_string : string -> ((string -> unit) -> unit) -> unit
val err_string : string -> ((string -> unit) -> unit) -> unit
(** String-emitting adapters for Lem's OCaml export. For example,
    [debug_string __FUNCTION__ (fun m -> if condition then m message)].
    The callback runs only when enabled and may emit zero or several messages.
    Each emission is a separate Logs call. Keep diagnostic work inside the
    callback, and use the emitter only during that callback. *)
val debug_located_string : string -> Cerb_location.t -> ((string -> unit) -> unit) -> unit
(** Attach a location to each emitted message. Its formatting is deferred
    until emission, so a callback that emits nothing does not format it. *)

val location_tag : string Logs.Tag.def

type format = Text | Json
type output = Stderr | Stdout | File of string
(** Open an append-only reporter. Formatting runs outside the lock; complete
    records and closure are serialized. The close function is idempotent and
    leaves borrowed stdout/stderr open. Install before starting workers,
    and close after they have joined. *)
val open_reporter : output -> format -> ((Logs.reporter * (unit -> unit)), string) result
