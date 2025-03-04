val use_ity : bool ref

type message =
  | Global of Global.error
  | Mismatch of
      { has : Pp.document;
        expect : Pp.document
      }
  | Generic of Pp.document [@deprecated "Please add a specific constructor"]
  | Illtyped_it of
      { it : Pp.document;
        has : Pp.document;
        expected : string;
        reason : string
      }
  | Number_arguments of
      { type_ : [ `Other | `Input | `Output ];
        has : int;
        expect : int
      }
  | Missing_member of Id.t
  | NIA of
      { it : IndexTerms.t;
        hint : string
      }
  | Empty_pattern
  | Redundant_pattern of Pp.document
  | Unknown_variable of Sym.t

type error =
  { loc : Locations.t;
    msg : message
  }

include WellTyped_intf.S

module type ErrorReader = sig
  type 'a t

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val get_context : unit -> Context.t t

  val lift : ('a, error) Result.t -> 'a t
end

module Lift : functor (M : ErrorReader) -> WellTyped_intf.S with type 'a t := 'a M.t
