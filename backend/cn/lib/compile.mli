type function_sig =
  { args : (Sym.t * BaseTypes.t) list;
    return_bty : BaseTypes.t
  }

type predicate_sig =
  { pred_iargs : (Sym.t * BaseTypes.t) list;
    pred_output : BaseTypes.t
  }

type env =
  { computationals : (BaseTypes.Surface.t * Sym.t option) Sym.Map.t;
    logicals : BaseTypes.Surface.t Sym.Map.t;
    predicates : predicate_sig Sym.Map.t;
    functions : function_sig Sym.Map.t;
    datatypes : BaseTypes.dt_info Sym.Map.t;
    datatype_constrs : BaseTypes.constr_info Sym.Map.t;
    tagDefs : (Sym.t, Mucore.tag_definition) Pmap.map;
    fetch_enum_expr :
      Locations.t -> Sym.t -> unit Cerb_frontend.AilSyntax.expression Or_TypeError.t;
    fetch_typedef : Locations.t -> Sym.t -> Cerb_frontend.Ctype.ctype Or_TypeError.t
  }

val init_env
  :  (Sym.t, Mucore.tag_definition) Pmap.map ->
  (Locations.t -> Sym.t -> unit Cerb_frontend.AilSyntax.expression Or_TypeError.t) ->
  (Locations.t -> Sym.t -> Cerb_frontend.Ctype.ctype Or_TypeError.t) ->
  env

val symtable : BaseTypes.Surface.t Hashtbl.Make(Sym).t

val add_computational : Sym.t -> BaseTypes.Surface.t -> env -> env

val add_renamed_computational : Sym.t -> Sym.t -> BaseTypes.Surface.t -> env -> env

val add_logical : Sym.t -> BaseTypes.Surface.t -> env -> env

val translate_cn_base_type
  :  env ->
  Sym.t Cerb_frontend.Cn.cn_base_type ->
  Sctypes.ctype option BaseTypes.t_gen

val register_cn_predicates
  :  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_predicate list ->
  env

val register_cn_functions
  :  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_function list ->
  env Or_TypeError.t

val add_datatype_infos
  :  env ->
  Sym.t Cerb_frontend.Cn.cn_datatype list ->
  env Or_TypeError.t

module E : sig
  type evaluation_scope = string

  type 'a t =
    | Done of 'a
    | Error of TypeErrors.t
    | ScopeExists of Locations.t * evaluation_scope * (bool -> 'a t)
    | Value_of_c_variable of
        Locations.t
        * Sym.t
        * evaluation_scope option
        * (IndexTerms.Surface.t option -> 'a t)
    | Deref of
        Locations.t
        * IndexTerms.Surface.t
        * evaluation_scope option
        * (IndexTerms.Surface.t option -> 'a t)
end

val start_evaluation_scope : string

module EffectfulTranslation : sig
  val translate_cn_expr
    :  Sym.Set.t ->
    env ->
    (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_expr ->
    BaseTypes.Surface.t IndexTerms.annot E.t

  val translate_cn_let_resource
    :  env ->
    Locations.t * Sym.t * (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_resource ->
    ((Request.t * BaseTypes.Surface.t)
    * (LogicalConstraints.t * (Locations.t * string option)) list
    * (BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot
      * BaseTypes.Surface.t IndexTerms.annot)
        list)
      E.t

  val translate_cn_assrt
    :  env ->
    Locations.t * (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_assertion ->
    LogicalConstraints.t E.t
end

module ET = EffectfulTranslation

val translate_cn_function
  :  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_function ->
  (Sym.t * Definition.Function.t) Or_TypeError.t

val ownership
  :  Locations.t * (Sym.t * Cerb_frontend.Ctype.ctype) ->
  env ->
  (Cerb_frontend__Symbol.sym
  * ((Request.t * BaseTypes.Surface.t)
    * (LogicalConstraints.t * (Locations.t * string option)) list)
  * BaseTypes.Surface.t IndexTerms.annot)
    Or_TypeError.t

val allocation_token
  :  Locations.t ->
  Sym.t ->
  (Cerb_frontend__Symbol.sym * (Request.t * BaseTypes.t)) * (Locations.t * 'a option)

module LocalState : sig
  type c_variable_state =
    | CVS_Value of Sym.t * BaseTypes.Surface.t
    | CVS_Pointer_pointing_to of IndexTerms.Surface.t

  type state =
    { c_variable_state : c_variable_state Sym.Map.t;
      pointee_values : IndexTerms.Surface.t Map.Make(IndexTerms.Surface).t
    }

  type states =
    { state : state;
      old_states : state Map.Make(String).t
    }

  val init_st : states

  val make_state_old : states -> string -> states

  val add_c_variable_state : Sym.t -> c_variable_state -> states -> states

  val add_c_variable_states : (Sym.t * c_variable_state) list -> states -> states

  val add_pointee_values
    :  (Map.Make(IndexTerms.Surface).key * IndexTerms.Surface.t) list ->
    states ->
    states

  val handle : states -> 'a E.t -> 'a Or_TypeError.t
end

val translate_cn_predicate
  :  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_predicate ->
  (Sym.t * Definition.Predicate.t) Or_TypeError.t

val make_rt
  :  Locations.t ->
  env ->
  LocalState.states ->
  Sym.t * Cerb_frontend.Ctype.ctype ->
  (Locations.t * (Sym.t * Cerb_frontend.Ctype.ctype)) list
  * (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list ->
  ReturnTypes.t Or_TypeError.t

val translate_cn_lemma
  :  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_lemma ->
  (Sym.t * (Cerb_location.t * LogicalReturnTypes.t ArgumentTypes.t)) Or_TypeError.t

val translate_cn_statement
  :  (Sym.t -> Cerb_frontend.Ctype.ctype) ->
  LocalState.state Map.Make(String).t ->
  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_statement ->
  Cnprog.t Or_TypeError.t
