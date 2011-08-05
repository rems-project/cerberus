type level = BUG | ERROR | WARNING | INFO | DEBUG
type 'a printer = 'a -> string
type t

val make : level -> 'a printer -> 'a -> t

val bug : 'a printer -> 'a -> t
val error : 'a printer -> 'a -> t
val warning : 'a printer -> 'a -> t
val info : 'a printer -> 'a -> t
val debug : 'a printer -> 'a -> t

val to_string : t -> string
val level : t -> level
