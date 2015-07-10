exception BUG   of string
exception ERROR of string

val raise_bug : string -> 'a
val raise_error : string -> 'a
