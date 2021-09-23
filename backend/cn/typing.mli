type e = TypeErrors.type_error
type error = (Locations.loc * e) * string option (* stack trace*)


type 'a t
type 'a m = 'a t
type failure = Context.t -> TypeErrors.type_error 
val return : 'a -> 'a m
val bind : 'a m -> ('a -> 'b m) -> 'b m
val pure : 'a m -> 'a m
val (let@) : 'a m -> ('a -> 'b m) -> 'b m
val fail : Locations.t -> e -> 'a m
val failS : Locations.t -> failure -> 'a m
val run : Context.t -> 'a m -> ('a, error) Result.t

(* val get: unit -> Context.t m *)
val print_with_ctxt : (Context.t -> unit) -> unit m
val get_global : unit -> Global.t m
val all_constraints : unit -> (LogicalConstraints.t list) m
val all_resources : unit -> (Resources.RE.t list) m
val provable : (LogicalConstraints.t -> bool) m
val model : unit -> Z3.Model.model m
val bound_a : Sym.t -> bool m
val bound_l : Sym.t -> bool m
val get_a : Sym.t -> (BaseTypes.t * Sym.t) m
val get_l : Sym.t -> LogicalSorts.t m
val add_a : Sym.t -> (BaseTypes.t * Sym.t) -> unit m
val add_l : Sym.t -> LogicalSorts.t -> unit m
val add_ls : (Sym.t * LogicalSorts.t) list -> unit m
val add_c : LogicalConstraints.t -> unit m
val add_cs : LogicalConstraints.t list -> unit m
val add_r : Context.where option -> Resources.RE.t -> unit m
val map_and_fold_resources : 
  (Resources.RE.t -> 'acc -> Resources.RE.t * 'acc) -> 
  'acc -> 'acc m
val all_vars : unit -> (Sym.t list) m
val bind_return_type : Context.where option -> Sym.t -> ReturnTypes.t -> unit m
val bind_logical_return_type : Context.where option -> LogicalReturnTypes.t -> unit m
val logically_bind_return_type : Context.where option -> ReturnTypes.t -> (BaseTypes.t * Sym.t) m
