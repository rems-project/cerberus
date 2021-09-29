type ('a, 'e) t
type ('a, 'e) m = ('a, 'e) t
type 'e failure = Context.t -> 'e

val return : 'a -> ('a, 'e) m
val bind : ('a, 'e) m -> ('a -> ('b, 'e) m) -> ('b, 'e) m
val pure : ('a, 'e) m -> ('a, 'e) m
val (let@) : ('a, 'e) m -> ('a -> ('b, 'e) m) -> ('b, 'e) m
val fail : 'e failure -> ('a, 'e) m
val run : Context.t -> ('a, 'e) m -> ('a, 'e) Result.t

(* val get: unit -> Context.t m *)
val print_with_ctxt : (Context.t -> unit) -> (unit, 'e) m
val get_global : unit -> (Global.t, 'e) m
val all_constraints : unit -> (LogicalConstraints.t list, 'e) m
val all_resources : unit -> (Resources.RE.t list, 'e) m
val provable : (LogicalConstraints.t -> [> `True | `False], 'e) m
val provable_or_model : (LogicalConstraints.t -> [> `True | `False of Z3.Model.model], 'e) m
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
val map_and_fold_resources : 
  (Resources.RE.t -> 'acc -> Resources.RE.t * 'acc) -> 
  'acc -> ('acc, 'e) m
val all_vars : unit -> (Sym.t list, 'e) m
val bind_return_type : Context.where option -> Sym.t -> ReturnTypes.t -> (unit, 'e) m
val bind_logical_return_type : Context.where option -> LogicalReturnTypes.t -> (unit, 'e) m
val logically_bind_return_type : Context.where option -> ReturnTypes.t -> (BaseTypes.t * Sym.t, 'e) m
