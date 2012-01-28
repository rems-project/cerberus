open List0

type 'a set = 'a list

val empty_set : 'a1 set

val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set

val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool

val set_remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set

val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set

val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set

val set_diff : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set

val set_In_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool

val set_prod : 'a1 set -> 'a2 set -> ('a1*'a2) set

val set_power : 'a1 set -> 'a2 set -> ('a1*'a2) set set

val set_fold_left : ('a2 -> 'a1 -> 'a2) -> 'a1 set -> 'a2 -> 'a2

val set_fold_right : ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 -> 'a2

val set_map : ('a2 -> 'a2 -> bool) -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set

