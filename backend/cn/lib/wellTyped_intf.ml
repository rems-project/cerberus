module type S = sig
  type 'a t

  val ensure_bits_type : Locations.t -> BaseTypes.t -> unit t

  val ensure_base_type : Locations.t -> expect:BaseTypes.t -> BaseTypes.t -> unit t

  val ensure_same_argument_number
    :  Locations.t ->
    [ `Other | `Input | `Output ] ->
    int ->
    expect:int ->
    unit t

  val check_ct : Locations.t -> Sctypes.ctype -> unit t

  val infer_term : 'bt IndexTerms.annot -> IndexTerms.t t

  val check_term : Locations.t -> BaseTypes.t -> 'bt IndexTerms.annot -> IndexTerms.t t

  val default_quantifier_bt : BaseTypes.t

  val oarg_bt_of_pred : Locations.t -> Request.name -> BaseTypes.t t

  val logical_constraint : Locations.t -> LogicalConstraints.t -> LogicalConstraints.t t

  val function_type
    :  string ->
    Locations.t ->
    ReturnTypes.t ArgumentTypes.t ->
    ReturnTypes.t ArgumentTypes.t t

  val integer_annot
    :  Cerb_frontend.Annot.annot list ->
    Cerb_frontend.IntegerType.integerType option

  val infer_expr
    :  (ArgumentTypes.lt * Where.label * Locations.t) Sym.Map.t ->
    'TY Mucore.expr ->
    BaseTypes.t Mucore.expr t

  val check_expr
    :  (ArgumentTypes.lt * Where.label * Locations.t) Sym.Map.t ->
    BaseTypes.t ->
    'TY Mucore.expr ->
    BaseTypes.t Mucore.expr t

  val procedure
    :  Locations.t ->
    'TY1 Mucore.args_and_body ->
    BaseTypes.t Mucore.args_and_body t

  val label_context
    :  ReturnTypes.t ->
    (Sym.Map.key, 'a Mucore.label_def) Pmap.map ->
    (False.t ArgumentTypes.t * Cerb_frontend.Annot.label_annot * Locations.t) Sym.Map.t

  val to_argument_type : ('a * 'b * 'c) Mucore.arguments -> 'c ArgumentTypes.t

  val predicate : Definition.Predicate.t -> Definition.Predicate.t t

  val function_ : Definition.Function.t -> Definition.Function.t t

  val lemma
    :  Locations.t ->
    'a ->
    LogicalReturnTypes.t ArgumentTypes.t ->
    LogicalReturnTypes.t ArgumentTypes.t t

  val datatype : 'a * Mucore.datatype -> ('a * Mucore.datatype) t

  val datatype_recursion : (Sym.t * Mucore.datatype) list -> Sym.t list list t

  val logical_function_order : Definition.Function.t Sym.Map.t -> Sym.t list list

  val resource_predicate_order : Definition.Predicate.t Sym.Map.t -> Sym.t list list

end
