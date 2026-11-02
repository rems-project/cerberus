(** Logging policy for executable startup, before any workers are spawned. *)
type t
val options : t Cmdliner.Term.t
val setup : t -> (unit, string) result
