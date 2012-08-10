module type LOGGER = sig
  val log : CpMessage.t -> unit
end

module StdOut : LOGGER

val set : (module LOGGER) -> unit

val log : CpMessage.t -> unit

val bug : 'a CpMessage.printer -> 'a -> unit
val error : 'a CpMessage.printer -> 'a -> unit
val warning : 'a CpMessage.printer -> 'a -> unit
val info : 'a CpMessage.printer -> 'a -> unit
val debug : 'a CpMessage.printer -> 'a -> unit
