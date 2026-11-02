(** Lazy Debug sources for native OCaml function-name literals.

    Pass [__FUNCTION__] directly. Active policies reject heap strings and names
    without a qualified function component with [Invalid_argument]. Globally
    disabled logging returns immediately, unless discovery was requested.
    This API is for native OCaml 5; ordinary explicit [Logs.src] calls remain
    available for other uses. *)

val configure : ?discover:bool -> Logs.level option -> string list -> unit
(** Configure once before workers start, or after all have joined. Selectors
    are exact [Module] or [Module.function] names, or [all]. Source levels and
    the reporter must not be reconfigured concurrently with logging. Invalid
    selector syntax raises [Invalid_argument]; unseen names are allowed.
    [discover] defaults to [false]. When [true], cache encountered names even
    with logging disabled, without evaluating disabled message callbacks. *)

val sources : unit -> string list
(** After workers join, list sorted, unique explicit sources and automatic
    names encountered under this policy, including negative cache entries.
    Unvisited automatic sites are absent. No binary scanning is performed. *)

val debug_enabled : string -> bool
(** Only needed before an expensive condition for logging. Ordinary message
    construction belongs in the callback below. *)
val debugf : string -> 'a Logs.log
(** OCaml call sites use [debugf __FUNCTION__ (fun m -> m "value: %a" pp v)].
    Selection uses the same cache as [debug]. The callback, including format
    arguments, printers and tags, is evaluated only when enabled. *)
val debug : string -> (unit -> string) -> unit
(** String-thunk adapter for Lem's OCaml export. *)
val debug_located : string -> Cerb_location.t -> (unit -> string) -> unit

(** Lem adapters for explicit non-Debug sources. *)
val info : Logs.src -> (unit -> string) -> unit
val warn : Logs.src -> (unit -> string) -> unit
val err : Logs.src -> (unit -> string) -> unit

val location_tag : string Logs.Tag.def
val translation_unit_tag : string Logs.Tag.def

type format = Text | Json
type output = Stderr | Stdout | File of string
(** Open an append-only reporter. Formatting runs outside the lock; complete
    records and closure are serialized. Plain text prefixes are cached per
    reporter, including for sources registered later, safely across domains.
    The close function is idempotent and
    leaves borrowed stdout/stderr open. Install once before starting workers,
    and close after they have joined. *)
val open_reporter : output -> format -> ((Logs.reporter * (unit -> unit)), string) result
