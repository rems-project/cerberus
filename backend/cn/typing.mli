type ('a, 'e) t
type ('a, 'e) m = ('a, 'e) t
type 'e failure = Context.t -> 'e

val return : 'a -> ('a, 'e) m
val bind : ('a, 'e) m -> ('a -> ('b, 'e) m) -> ('b, 'e) m
val pure : ('a, 'e) m -> ('a, 'e) m
val restore_resources : ('a, 'e) m -> ('a, 'e) m
val (let@) : ('a, 'e) m -> ('a -> ('b, 'e) m) -> ('b, 'e) m
val fail : 'e failure -> ('a, 'e) m
val fail_with_trace : (Trace.t -> 'e failure) -> ('a, 'e) m
val run : Context.t -> ('a, 'e) m -> ('a, 'e) Result.t

(* val get: unit -> Context.t m *)
val print_with_ctxt : (Context.t -> unit) -> (unit, 'e) m
val get_trace_length : unit -> (int, 'e) m
val increase_trace_length : unit -> (unit, 'e) m
val get_global : unit -> (Global.t, 'e) m
val all_constraints : unit -> (Context.LCSet.t, 'e) m
val simp_constraints : unit ->
    ((IndexTerms.t IndexTerms.SymMap.t 
      * bool Simplify.ITPairMap.t
      * Context.LCSet.t), 'e) m
val all_resources : unit -> (Resources.t list, 'e) m
val all_resources_tagged : unit -> ((Resources.t * int) list * int, 'e) m
val provable : Locations.t -> (LogicalConstraints.t -> [> `True | `False], 'e) m
val model : unit -> (Solver.model_with_q, 'e) m
val model_with : Locations.t -> IndexTerms.t -> (Solver.model_with_q option, 'e) m
val prev_models_with : Locations.t -> IndexTerms.t -> (Solver.model_with_q list, 'e) m
val bound_a : Sym.t -> (bool, 'e) m
val bound_l : Sym.t -> (bool, 'e) m
val get_a : Sym.t -> (BaseTypes.t * Sym.t, 'e) m
val get_l : Sym.t -> (LogicalSorts.t, 'e) m
val add_a : Sym.t -> (BaseTypes.t * Sym.t) -> (unit, 'e) m
val remove_a : Sym.t -> (unit, 'e) m
val add_l : Sym.t -> LogicalSorts.t -> (unit, 'e) m
val add_as : (Sym.t * (BaseTypes.t * Sym.t)) list -> (unit, 'e) m
val remove_as : Sym.t list -> (unit, 'e) m
val add_ls : (Sym.t * LogicalSorts.t) list -> (unit, 'e) m
val add_c : LogicalConstraints.t -> (unit, 'e) m
val add_cs : LogicalConstraints.t list -> (unit, 'e) m
val add_r : Context.where option -> Resources.t -> (unit, 'e) m
val add_rs : Context.where option -> Resources.t list -> (unit, 'e) m
val get_loc_trace : unit -> (Locations.loc list, 'e) m
val in_loc_trace : Locations.loc list -> (unit -> ('a, 'e) m) -> ('a, 'e) m
val get_step_trace : unit -> (Trace.t, 'e) m

val begin_trace_of_step : Trace.opt_pat -> 'a NewMu.New.mu_expr -> (unit -> (unit, 'e) m, 'e) m
val begin_trace_of_pure_step : Trace.opt_pat -> 'a NewMu.New.mu_pexpr -> (unit -> (unit, 'e) m, 'e) m

type changed = 
  | Deleted
  | Unchanged
  | Unfolded of Resources.t list
  | Changed of Resources.t

val map_and_fold_resources : 
  Locations.t ->
  (Resources.t -> 'acc -> changed * 'acc) -> 
  'acc -> ('acc, 'e) m

val get_struct_decl : Locations.t -> Sym.t -> (Memory.struct_decl, TypeErrors.t) m
val get_member_type : Locations.t -> Sym.t -> Id.t -> Memory.struct_layout -> (Sctypes.t, TypeErrors.t) m
val get_struct_member_type : Locations.t -> Sym.t -> Id.t -> (Sctypes.t, TypeErrors.t) m
val get_fun_decl : Locations.t -> Sym.t -> (Locations.t * Global.AT.ft * Cerb_frontend.Mucore.trusted, TypeErrors.t) m

val get_resource_predicate_def : Locations.t -> Sym.t ->
    (ResourcePredicates.definition, TypeErrors.type_error) m
val get_logical_predicate_def : Locations.t -> Sym.t ->
    (LogicalPredicates.definition, TypeErrors.type_error) m
val todo_get_resource_predicate_def_s : Locations.t -> string ->
    (Sym.t * ResourcePredicates.definition, TypeErrors.type_error) m
val todo_get_logical_predicate_def_s : Locations.t -> string ->
    (Sym.t * LogicalPredicates.definition, TypeErrors.type_error) m


val add_struct_decl : Sym.t -> Memory.struct_layout -> (unit, 'e) m
val add_fun_decl : Sym.t -> (Locations.t * ArgumentTypes.ft * Cerb_frontend.Mucore.trusted) -> (unit, 'e) m
(* val add_impl_fun_decl : Cerb_frontend.Implementation.implementation_constant -> ArgumentTypes.ift -> (unit, 'e) m *)
(* val add_impl_constant : Cerb_frontend.Implementation.implementation_constant -> IndexTerms.t -> (unit, 'e) m *)
val add_resource_predicate : Sym.t -> ResourcePredicates.definition -> (unit, 'e) m
val add_logical_predicate : Sym.t -> LogicalPredicates.definition -> (unit, 'e) m
