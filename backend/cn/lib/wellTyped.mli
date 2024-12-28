module type NoSolver = sig
  type 'a t = 'a Typing.t

  type failure = Context.t * Explain.log -> TypeErrors.t

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val pure : 'a t -> 'a t

  val fail : failure -> 'a t

  val bound_a : Sym.t -> bool t

  val bound_l : Sym.t -> bool t

  val get_a : Sym.t -> Context.basetype_or_value t

  val get_l : Sym.t -> Context.basetype_or_value t

  val add_a : Sym.t -> BaseTypes.t -> Context.l_info -> unit t

  val add_l : Sym.t -> BaseTypes.t -> Context.l_info -> unit t

  val get_struct_decl : Locations.t -> Sym.t -> Memory.struct_layout t

  val get_struct_member_type : Locations.t -> Sym.t -> Id.t -> Sctypes.ctype t

  val get_datatype : Locations.t -> Sym.t -> BaseTypes.dt_info t

  val get_datatype_constr : Locations.t -> Sym.t -> BaseTypes.constr_info t

  val get_resource_predicate_def : Locations.t -> Sym.t -> Definition.Predicate.t t

  val get_logical_function_def : Locations.t -> Sym.t -> Definition.Function.t t

  val get_lemma : Locations.t -> Sym.t -> (Locations.t * ArgumentTypes.lemmat) t

  val get_fun_decl
    :  Locations.t ->
    Sym.t ->
    (Locations.t * ArgumentTypes.ft option * Sctypes.c_concrete_sig) t

  val ensure_base_type : Locations.t -> expect:BaseTypes.t -> BaseTypes.t -> unit t

  val lift : 'a Or_TypeError.t -> 'a t
end

val use_ity : bool ref

module Exposed : sig
  val ensure_bits_type : Locations.t -> BaseTypes.t -> unit Typing.t

  val ensure_same_argument_number
    :  Locations.t ->
    [< `General | `Input | `Output ] ->
    int ->
    expect:int ->
    unit Typing.t

  val compare_by_fst_id : Id.t * 'a -> Id.t * 'b -> int

  val check_ct : Locations.t -> Sctypes.ctype -> unit Typing.t

  val infer_term : 'bt IndexTerms.annot -> IndexTerms.t Typing.t

  val check_term
    :  Locations.t ->
    BaseTypes.t ->
    'bt IndexTerms.annot ->
    IndexTerms.t Typing.t

  val default_quantifier_bt : BaseTypes.t

  val oarg_bt_of_pred : Locations.t -> Request.name -> BaseTypes.t Typing.t

  val logical_constraint
    :  Locations.t ->
    LogicalConstraints.t ->
    LogicalConstraints.t Typing.t

  val function_type_consistent
    :  string ->
    Locations.t ->
    ReturnTypes.t ArgumentTypes.t ->
    unit Typing.t

  val function_type
    :  string ->
    Locations.t ->
    ReturnTypes.t ArgumentTypes.t ->
    ReturnTypes.t ArgumentTypes.t Typing.t

  val integer_annot
    :  Cerb_frontend.Annot.annot list ->
    Cerb_frontend.IntegerType.integerType option

  val infer_expr
    :  (ArgumentTypes.lt * Where.label * Locations.t) Sym.Map.t ->
    'TY Mucore.expr ->
    BaseTypes.t Mucore.expr Typing.t

  val check_expr
    :  (ArgumentTypes.lt * Where.label * Locations.t) Sym.Map.t ->
    BaseTypes.t ->
    'TY Mucore.expr ->
    BaseTypes.t Mucore.expr Typing.t

  val procedure
    :  Locations.t ->
    'TY1 Mucore.args_and_body ->
    BaseTypes.t Mucore.args_and_body Typing.t

  val label_context
    :  ReturnTypes.t ->
    (Sym.Map.key, 'a Mucore.label_def) Pmap.map ->
    (False.t ArgumentTypes.t * Cerb_frontend.Annot.label_annot * Locations.t) Sym.Map.t

  val to_argument_type : ('a * 'b * 'c) Mucore.arguments -> 'c ArgumentTypes.t

  val procedure_consistent : Locations.t -> 'TY1 Mucore.args_and_body -> unit Typing.t

  val predicate_consistent : Definition.Predicate.t -> unit Typing.m

  val predicate : Definition.Predicate.t -> Definition.Predicate.t Typing.t

  val function_ : Definition.Function.t -> Definition.Function.t Typing.t

  val lemma_consistent
    :  Locations.t ->
    'a ->
    LogicalReturnTypes.t ArgumentTypes.t ->
    unit Typing.t

  val lemma
    :  Locations.t ->
    'a ->
    LogicalReturnTypes.t ArgumentTypes.t ->
    LogicalReturnTypes.t ArgumentTypes.t Typing.t

  val datatype : 'a * Mucore.datatype -> ('a * Mucore.datatype) Typing.t

  val datatype_recursion : (Sym.t * Mucore.datatype) list -> Sym.t list list Typing.t
end
