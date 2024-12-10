val debug_constraint_failure_diagnostics
  :  int ->
  Solver.model_with_q ->
  Global.t ->
  Simplify.simp_ctxt ->
  LogicalConstraints.logical_constraint ->
  unit

module General : sig
  type uiinfo = TypeErrors.situation * TypeErrors.request_chain

  val ftyp_args_request_step
    :  ([ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t -> 'a -> 'a) ->
    Locations.t ->
    uiinfo ->
    'b ->
    'a LogicalArgumentTypes.t ->
    'a LogicalArgumentTypes.t Typing.m
end

module Special : sig
  val get_live_alloc
    :  [ `Copy_alloc_id | `Ptr_cmp | `Ptr_diff | `ISO_array_shift ] ->
    Locations.t ->
    IndexTerms.t ->
    IndexTerms.t Typing.m

  val predicate_request
    :  Locations.t ->
    TypeErrors.situation ->
    Request.Predicate.t * (Locations.t * string) option ->
    ((Request.Predicate.t * Resources.oargs) * int list) Typing.m

  val qpredicate_request
    :  Locations.t ->
    TypeErrors.situation ->
    Request.QPredicate.t * (Locations.t * string) option ->
    ((Request.QPredicate.t * Resources.oargs) * int list) Typing.m
end
