type ('a, 'e) t
type ('a, 'e) m = ('a, 'e) t
type 'e failure = Context.t -> 'e

val return : 'a -> ('a, 'e) m
val bind : ('a, 'e) m -> ('a -> ('b, 'e) m) -> ('b, 'e) m
val pure : ('a, 'e) m -> ('a, 'e) m
val restore_resources : ('a, 'e) m -> ('a, 'e) m
val (let@) : ('a, 'e) m -> ('a -> ('b, 'e) m) -> ('b, 'e) m
val fail : 'e failure -> ('a, 'e) m
val run : Context.t -> ('a, 'e) m -> ('a, 'e) Result.t

(* val get: unit -> Context.t m *)
val print_with_ctxt : (Context.t -> unit) -> (unit, 'e) m
val get_trace_length : unit -> (int, 'e) m
val increase_trace_length : unit -> (unit, 'e) m
val get_global : unit -> (Global.t, 'e) m
val all_constraints : unit -> (Context.LCSet.t, 'e) m
val simp_constraints : unit ->
    ((IndexTerms.t IndexTerms.SymMap.t * Context.LCSet.t), 'e) m
val all_resources : unit -> (Resources.RE.t list, 'e) m
val provable : 
  Locations.t ->
  (?shortcut_false:bool -> LogicalConstraints.t -> [> `True | `False], 'e) m
val model : unit -> (Solver.model_with_q, 'e) m
val bound_a : Sym.t -> (bool, 'e) m
val bound_l : Sym.t -> (bool, 'e) m
val get_a : Sym.t -> (BaseTypes.t * Sym.t, 'e) m
val get_l : Sym.t -> (LogicalSorts.t, 'e) m
val add_a : Sym.t -> (BaseTypes.t * Sym.t) -> (unit, 'e) m
val add_l : Sym.t -> LogicalSorts.t -> (unit, 'e) m
val add_ls : (Sym.t * LogicalSorts.t) list -> (unit, 'e) m
val add_c : LogicalConstraints.t -> (unit, 'e) m
val add_cs : LogicalConstraints.t list -> (unit, 'e) m
val add_r : Context.where option -> Resources.RE.t -> (unit, 'e) m
val add_rs : Context.where option -> Resources.RE.t list -> (unit, 'e) m
val get_loc_trace : unit -> (Locations.loc list, 'e) m
val in_loc_trace : Locations.loc list -> (unit -> ('a, 'e) m) -> ('a, 'e) m

type changed = 
  | Deleted
  | Unchanged
  | Unfolded of Resources.RE.t list
  | Changed of Resources.RE.t

val map_and_fold_resources : 
  Locations.t ->
  (Resources.RE.t -> 'acc -> changed * 'acc) -> 
  'acc -> ('acc, 'e) m

val get_resource_predicate_def : Locations.t -> string ->
    (ResourcePredicates.definition, TypeErrors.type_error) m
val get_logical_predicate_def : Locations.t -> string ->
    (LogicalPredicates.definition, TypeErrors.type_error) m

