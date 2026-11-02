(** Internal compatibility with OCaml 4.14. *)
val protect : Mutex.t -> (unit -> 'a) -> 'a

(** Content hashing for selectors and source registration, used only during
    configuration and pointer-cache misses. *)
module String_key : Hashtbl.HashedType with type t = string
