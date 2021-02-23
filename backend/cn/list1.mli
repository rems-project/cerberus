type 'a list1
type 'a t = 'a list1

val dest : 'a t -> ('a * 'a list)
val make : ('a * 'a list) -> 'a t

val to_list : 'a t -> 'a list

val head : 'a t -> 'a
val tail : 'a t -> 'a list

val cons : 'a -> 'a t -> 'a t

val one : 'a -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

val concat : 'a t -> 'a t -> 'a t
val (@) : 'a t -> 'a t -> 'a t


val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
