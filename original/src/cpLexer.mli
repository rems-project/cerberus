open CpPervasives

type token_stream = unit -> Cparser.token

type t

val name : t -> string
val lexbuf : (Lexing.lexbuf -> 'a) -> t -> 'a
val stream : (token_stream -> 'a)  -> t -> 'a

val make : CpInput.t -> t
