val use_ity : bool ref

module Make : functor (Monad : Sigs.NoSolver) -> sig
  module Exposed : Sigs.Exposed with type 'a t := 'a Monad.t
end
