module History : sig
  val str : string

  val sym : Sym.t

  val loc : Locations.t

  val base_id : Id.t

  val base_bt : BaseTypes.t

  val size_id : Id.t

  val size_bt : BaseTypes.t

  val value_bt : BaseTypes.t

  val make_value : base:IndexTerms.t -> size:int -> Locations.t -> IndexTerms.t

  val bt : BaseTypes.t

  val it : IndexTerms.t

  val lookup_ptr : IndexTerms.t -> Locations.t -> IndexTerms.t

  val get_base_size : IndexTerms.t -> Cerb_location.t -> IndexTerms.t * IndexTerms.t

  val sbt : SurfaceBaseTypes.t
end

module Predicate : sig
  val str : string

  val loc : Locations.t

  val sym : Sym.t
end
