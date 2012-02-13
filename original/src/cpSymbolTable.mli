type ('a, 'b) t

val empty : ('a, 'b) t
val add : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t
val mem : 'a -> ('a, 'b) t -> bool
val find : 'a -> ('a, 'b) t -> 'b

val symbols : ('a, 'b) t -> 'b list

val create_scope : ('a, 'b) t -> ('a, 'b) t
val destroy_scope : ('a, 'b) t -> ('a, 'b) t
val return_scope : ('a, 'b) t -> ('a, 'b) t

val push_table : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
