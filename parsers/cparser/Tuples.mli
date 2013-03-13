type __ = Obj.t

type tuple = __

val tuple_rev_app : __ list -> tuple -> __ list -> tuple -> tuple

type 'res arrows = __

val uncurry : __ list -> 'a1 arrows -> tuple -> 'a1

