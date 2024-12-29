val use_ity : bool ref

include WellTyped_intf.S

module type ErrorReader = sig
  type 'a t

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val get_context : unit -> Context.t t

  val lift : 'a Or_TypeError.t -> 'a t
end

module Lift : functor (M : ErrorReader) -> WellTyped_intf.S with type 'a t := 'a M.t
