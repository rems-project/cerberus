include module type of BatPervasives

exception BUG
exception ERROR

val raise_bug : string -> 'a
val raise_error : string -> 'a

val (%>) : 'a option -> ('a -> 'b option) -> 'b option
