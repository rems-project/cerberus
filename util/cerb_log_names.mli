(** Exact selectors and normalization for automatic function sources. *)
val valid_selector : string -> bool
val canonical : string -> string
val selected : string list -> string -> bool
