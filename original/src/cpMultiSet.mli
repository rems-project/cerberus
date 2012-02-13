type 'a t

val empty : 'a t
val add : 'a -> 'a t -> 'a t
val find : 'a -> 'a t -> int
val compare : 'a t -> 'a t -> int

val from_list : 'a list -> 'a t
