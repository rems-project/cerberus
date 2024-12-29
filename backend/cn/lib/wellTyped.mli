val use_ity : bool ref

module NoSolver : Sigs.NoSolver

module Exposed : Sigs.Exposed with type 'a t := 'a NoSolver.t

module type ErrorReader = sig
  type 'a t

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  type state

  val get : unit -> state t

  val to_context : state -> Context.t

  val lift : 'a Or_TypeError.t -> 'a t
end

module Lift : functor (M : ErrorReader) -> Sigs.Exposed with type 'a t := 'a M.t
