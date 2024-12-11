val debug_constraint_failure_diagnostics
  :  int ->
  Solver.model_with_q ->
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
  val check_live_alloc
    :  [ `Copy_alloc_id | `Ptr_cmp | `Ptr_diff | `ISO_array_shift | `ISO_member_shift ] ->
    Locations.t ->
    IndexTerms.t ->
    unit Typing.m

  val predicate_request
    :  Locations.t ->
    TypeErrors.situation ->
    Request.Predicate.t * (Locations.t * string) option ->
    (Resource.predicate * int list) Typing.m

  val qpredicate_request
    :  Locations.t ->
    TypeErrors.situation ->
    Request.QPredicate.t * (Locations.t * string) option ->
    (Resource.qpredicate * int list) Typing.m
end
