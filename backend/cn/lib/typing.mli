type solver

type 'a t

type 'a m = 'a t

type failure = Context.t * Explain.log -> TypeErrors.t

type 'a pause

val return : 'a -> 'a m

val bind : 'a m -> ('a -> 'b m) -> 'b m

val pure : 'a m -> 'a m

val ( let@ ) : 'a m -> ('a -> 'b m) -> 'b m

val fail : failure -> 'a m

val run : Context.t -> 'a m -> ('a, TypeErrors.t) Result.t

val run_to_pause : Context.t -> 'a m -> 'a pause

val run_from_pause : ('a -> 'b m) -> 'a pause -> ('b, TypeErrors.t) Result.t

val pause_to_result : 'a pause -> ('a, TypeErrors.t) Result.t

val sandbox : 'a t -> 'a Resultat.t t

val get_typing_context : unit -> Context.t m

val print_with_ctxt : (Context.t -> unit) -> unit m

val get_global : unit -> Global.t m

val get_cs : unit -> Context.LC.Set.t m

val simp_ctxt : unit -> Simplify.simp_ctxt m

val all_resources : Locations.t -> Resource.t list m

val all_resources_tagged : Locations.t -> ((Resource.t * int) list * int) m

val provable : Locations.t -> (LogicalConstraints.t -> [> `True | `False ]) m

val model : unit -> Solver.model_with_q m

val model_with : Locations.t -> IndexTerms.t -> Solver.model_with_q option m

val prev_models_with : Locations.t -> IndexTerms.t -> Solver.model_with_q list m

val bound_a : Sym.t -> bool m

val bound_l : Sym.t -> bool m

val bound : Sym.t -> bool m

val get_a : Sym.t -> Context.basetype_or_value m

val get_l : Sym.t -> Context.basetype_or_value m

val remove_a : Sym.t -> unit m

val remove_as : Sym.t list -> unit m

val add_a : Sym.t -> BaseTypes.t -> Context.l_info -> unit m

val add_a_value : Sym.t -> IndexTerms.t -> Context.l_info -> unit m

val add_l : Sym.t -> BaseTypes.t -> Context.l_info -> unit m

val add_l_value : Sym.t -> IndexTerms.t -> Context.l_info -> unit m

val add_ls : (Sym.t * BaseTypes.t * Context.l_info) list -> unit m

val add_c : Locations.t -> LogicalConstraints.t -> unit m

val add_cs : Locations.t -> LogicalConstraints.t list -> unit m

val add_r : Locations.t -> Resource.t -> unit m

val add_rs : Locations.t -> Resource.t list -> unit m

val set_datatype_order : Sym.t list list option -> unit m

val get_datatype_order : unit -> Sym.t list list option m

val res_history : Locations.t -> int -> Context.resource_history m

type changed =
  | Deleted
  | Unchanged
  | Changed of Resource.t

val map_and_fold_resources
  :  Locations.t ->
  (Resource.t -> 'acc -> changed * 'acc) ->
  'acc ->
  ('acc * int list) m

val get_struct_decl : Locations.t -> Sym.t -> Memory.struct_decl m

val get_struct_member_type : Locations.t -> Sym.t -> Id.t -> Sctypes.t m

val get_member_type : Locations.t -> Sym.t -> Id.t -> Memory.struct_layout -> Sctypes.t m

val get_datatype : Locations.t -> Sym.t -> BaseTypes.dt_info m

val get_datatype_constr : Locations.t -> Sym.t -> BaseTypes.constr_info m

val get_fun_decl
  :  Locations.t ->
  Sym.t ->
  (Locations.t * Global.AT.ft option * Sctypes.c_concrete_sig) m

val get_lemma : Locations.t -> Sym.t -> (Locations.t * Global.AT.lemmat) m

val get_resource_predicate_def : Locations.t -> Sym.t -> ResourcePredicates.definition m

val get_logical_function_def : Locations.t -> Sym.t -> LogicalFunctions.definition m

val add_struct_decl : Sym.t -> Memory.struct_layout -> unit m

val add_fun_decl
  :  Sym.t ->
  Locations.t * ArgumentTypes.ft option * Sctypes.c_concrete_sig ->
  unit m

val add_lemma : Sym.t -> Locations.t * ArgumentTypes.lemmat -> unit m

val add_resource_predicate : Sym.t -> ResourcePredicates.definition -> unit m

val add_logical_function : Sym.t -> LogicalFunctions.definition -> unit m

val add_datatype : Sym.t -> BaseTypes.dt_info -> unit m

val add_datatype_constr : Sym.t -> BaseTypes.constr_info -> unit m

(* val set_statement_locs : Locations.loc CStatements.LocMap.t -> (unit) m *)

val value_eq_group : IndexTerms.t option -> IndexTerms.t -> EqTable.ITSet.t m

val test_value_eqs
  :  Locations.t ->
  IndexTerms.t option ->
  IndexTerms.t ->
  IndexTerms.t list ->
  unit m

val embed_resultat : 'a Resultat.t -> 'a m

val ensure_logical_sort : Locations.t -> expect:LogicalSorts.t -> LogicalSorts.t -> unit m

val ensure_base_type : Locations.t -> expect:LogicalSorts.t -> LogicalSorts.t -> unit m

val make_return_record
  :  Locations.t ->
  string ->
  BaseTypes.member_types ->
  (IndexTerms.t * IndexTerms.t list) m

val bind_logical_return
  :  Locations.t ->
  IndexTerms.t list ->
  LogicalReturnTypes.t ->
  unit m

val bind_return : Locations.t -> IndexTerms.t list -> ReturnTypes.t -> IndexTerms.t m

val add_movable_index
  :  Locations.t ->
  (* verbose:bool -> *)
  Request.name * IndexTerms.t ->
  unit m

val get_movable_indices : unit -> (Request.name * IndexTerms.t) list m

val record_action : Explain.action * Locations.t -> unit m

val modify_where : (Where.t -> Where.t) -> unit m

(* val add_label_to_trace : (Locations.t * Context.label_kind) option -> unit m *)
(* val add_trace_item_to_trace : Context.trace_item * Locations.t -> unit m *)

val init_solver : unit -> unit m
