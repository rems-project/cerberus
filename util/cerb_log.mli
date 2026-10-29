(** Non-monadic Lem adapters. OCaml callers should use [Logs] directly. *)
val info : Logs.src -> (unit -> string) -> unit
val warn : Logs.src -> (unit -> string) -> unit
val err : Logs.src -> (unit -> string) -> unit
val debug_located : Logs.src -> Cerb_location.t -> (unit -> string) -> unit

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
