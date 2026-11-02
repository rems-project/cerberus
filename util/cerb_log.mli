(** Logging with automatic sources for native OCaml function-name literals.

    Pass [__FUNCTION__] directly. Active policies reject heap strings and names
    without a qualified function component with [Invalid_argument]. Globally
    disabled severities return immediately, unless discovery was requested.
    This API is for native OCaml 4.14 or 5; ordinary explicit [Logs.src] calls remain
    available for other uses. *)

val configure : ?discover:bool -> Logs.level option -> string list -> unit
(** Configure once before workers start, or after all have joined. Selectors
    are exact [Module] or [Module.function] names, or [all]. Source levels and
    the reporter must not be reconfigured concurrently with logging. Invalid
    selector syntax raises [Invalid_argument]; unseen names are allowed.
    Selected sources have a Debug threshold; other sources use [level].
    [None] suppresses every level, including selected sources.
    [discover] defaults to [false]. When [true], cache encountered names even
    with logging disabled, without evaluating disabled message callbacks. *)

val sources : unit -> string list
(** After workers join, list sorted, unique explicit sources and automatic
    names encountered under this policy, including negative cache entries.
    Unvisited automatic sites are absent. No binary scanning is performed. *)

val debug : string -> 'a Logs.log
val warn : string -> 'a Logs.log
val err : string -> 'a Logs.log
(** OCaml call sites use [debug __FUNCTION__ (fun m -> m "value: %a" pp v)].
    All severities share an address cache. The callback, including format
    arguments, printers and tags, is evaluated only when enabled. *)

val debug_string : string -> ((string -> unit) -> unit) -> unit
val warn_string : string -> ((string -> unit) -> unit) -> unit
val err_string : string -> ((string -> unit) -> unit) -> unit
(** String-emitting adapters for Lem's OCaml export. For example,
    [debug_string __FUNCTION__ (fun emit -> if condition then emit message)].
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
    records and closure are serialized. Plain text prefixes are cached per
    reporter, including for sources registered later, safely across domains.
    The close function is idempotent and
    leaves borrowed stdout/stderr open. Install once before starting workers,
    and close after they have joined. *)
val open_reporter : output -> format -> ((Logs.reporter * (unit -> unit)), string) result
