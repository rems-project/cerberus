module STermMap : module type of Map.Make (IndexTerms.Surface)

module StringMap : module type of Map.Make (String)

module StringSet : module type of Set.Make (String)

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
    tagDefs : (Cerb_frontend.Symbol.sym, Mucore.tag_definition) Pmap.map;
    fetch_enum_expr :
      Locations.t -> Sym.t -> unit Cerb_frontend.AilSyntax.expression Or_TypeError.t;
    fetch_typedef : Locations.t -> Sym.t -> Cerb_frontend.Ctype.ctype Or_TypeError.t
  }

val init_env
  :  (Cerb_frontend.Symbol.sym, Mucore.tag_definition) Pmap.map ->
  (Locations.t -> Sym.t -> unit Cerb_frontend.AilSyntax.expression Or_TypeError.t) ->
  (Locations.t -> Sym.t -> Cerb_frontend.Ctype.ctype Or_TypeError.t) ->
  env

val pointer_eq_warned : bool ref

module SymTable : module type of Hashtbl.Make (Sym)

val symtable : BaseTypes.Surface.t SymTable.t

val add_computational : SymTable.key -> BaseTypes.Surface.t -> env -> env

val add_renamed_computational : SymTable.key -> Sym.t -> BaseTypes.Surface.t -> env -> env

val add_logical : SymTable.key -> BaseTypes.Surface.t -> env -> env

val add_predicate : Sym.Map.key -> predicate_sig -> env -> env

val lookup_computational_or_logical
  :  Sym.Map.key ->
  env ->
  (BaseTypes.Surface.t * Sym.t option) option

val lookup_predicate : Sym.Map.key -> env -> predicate_sig option

val lookup_function : Sym.Map.key -> env -> function_sig option

val lookup_struct_opt : Cerb_frontend.Symbol.sym -> env -> Memory.struct_layout option

val add_datatype : Sym.Map.key -> BaseTypes.dt_info -> env -> env

val add_datatype_constr : Sym.Map.key -> BaseTypes.constr_info -> env -> env

val get_datatype_maps
  :  env ->
  (Sym.Map.key * BaseTypes.dt_info) list * (Sym.Map.key * BaseTypes.constr_info) list

type cn_predicate =
  (Cerb_frontend.Symbol.sym, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_predicate

type cn_function =
  (Cerb_frontend.Symbol.sym, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_function

type cn_lemma =
  (Cerb_frontend.Symbol.sym, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_lemma

type cn_datatype = Cerb_frontend.Symbol.sym Cerb_frontend.Cn.cn_datatype

val symset_bigunion : Sym.Set.t list -> Sym.Set.t

val bound_by_pattern : Sym.Set.elt Cerb_frontend.Cn.cn_pat -> Sym.Set.t

val free_in_expr : (Sym.Set.elt, 'a) Cerb_frontend.Cn.cn_expr -> Sym.Set.t

val free_in_exprs : (Sym.Set.elt, 'a) Cerb_frontend.Cn.cn_expr list -> Sym.Set.t

val translate_cn_base_type
  :  env ->
  Cerb_frontend.Symbol.sym Cerb_frontend.Cn.cn_base_type ->
  Sctypes.ctype option BaseTypes.t_gen

val register_cn_predicates : env -> cn_predicate list -> env

val convert_enum_expr
  :  'a Cerb_frontend.AilSyntax.expression ->
  BaseTypes.Surface.t Cn__IndexTerms.annot Or_TypeError.t

val do_decode_enum
  :  env ->
  Locations.t ->
  Sym.t ->
  BaseTypes.Surface.t Cn__IndexTerms.annot Or_TypeError.t

val add_function : 'a -> Sym.Map.key -> function_sig -> env -> env Or_TypeError.t

val register_cn_functions : env -> cn_function list -> env Or_TypeError.t

val add_datatype_info : env -> cn_datatype -> env Or_TypeError.t

val add_datatype_infos : env -> cn_datatype list -> env Or_TypeError.t

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

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val fail : TypeErrors.t -> 'a t

  val scope_exists : Locations.t -> evaluation_scope -> bool t

  val deref
    :  Locations.t ->
    IndexTerms.Surface.t ->
    evaluation_scope option ->
    IndexTerms.Surface.t option t

  val value_of_c_variable
    :  Locations.t ->
    Sym.t ->
    evaluation_scope option ->
    IndexTerms.Surface.t option t

  val liftResult : ('a, TypeErrors.t) Result.result -> 'a t
end

val start_evaluation_scope : string

module EffectfulTranslation : sig
  val pp_in_scope : string option -> Cerb_pp_prelude.P.document

  val lookup_struct
    :  Locations.t ->
    Cerb_frontend.Symbol.sym ->
    env ->
    Memory.struct_layout E.t

  val lookup_member
    :  Locations.t ->
    'a * Memory.struct_piece list ->
    Id.t ->
    Sctypes.t E.t

  val lookup_datatype : Locations.t -> Sym.Map.key -> env -> BaseTypes.dt_info E.t

  val lookup_constr : Locations.t -> Sym.Map.key -> env -> BaseTypes.constr_info E.t

  val cannot_tell_pointee_ctype : Locations.t -> 'a IndexTerms.annot -> 'b E.t

  val mk_translate_binop
    :  Locations.t ->
    Cerb_frontend.Cn.cn_binop ->
    BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot
    * BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot ->
    BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot E.t

  val translate_member_access
    :  Locations.t ->
    env ->
    IndexTerms.Surface.t ->
    Id.t ->
    BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot E.t

  val translate_cn_pat
    :  env ->
    Sym.Set.t ->
    SymTable.key Cerb_frontend.Cn.cn_pat * BaseTypes.Surface.t ->
    (env * Sym.Set.t * BaseTypes.Surface.t IndexTerms.pattern) E.t

  val check_quantified_base_type
    :  env ->
    Locations.t ->
    Cerb_frontend.Symbol.sym Cerb_frontend.Cn.cn_base_type ->
    Sctypes.ctype option BaseTypes.t_gen E.t

  val translate_cn_expr
    :  Sym.Set.t ->
    env ->
    (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_expr ->
    BaseTypes.Surface.t IndexTerms.annot E.t

  val translate_cn_res_info
    :  Locations.t ->
    Locations.t ->
    env ->
    (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_pred ->
    BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot list ->
    (Request.name
    * BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot
    * BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot list
    * BaseTypes.Surface.t)
      E.t

  val split_pointer_linear_step
    :  Locations.t ->
    Sym.t * BaseTypes.Surface.t * Locations.t ->
    IndexTerms.Surface.t ->
    (BaseTypes.Surface.t IndexTerms.annot * BaseTypes.t IndexTerms.annot) E.t

  val owned_good
    :  'a ->
    Request.t * 'b ->
    (LogicalConstraints.t * (Locations.t * string option)) list

  val translate_cn_let_resource__pred
    :  env ->
    Locations.t ->
    Sym.t ->
    Locations.t
    * (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_pred
    * (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_expr list ->
    ((Request.t * BaseTypes.Surface.t)
    * (BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot
      * BaseTypes.Surface.t IndexTerms.annot)
        list)
      E.t

  val translate_cn_let_resource__each
    :  env ->
    Locations.t ->
    SymTable.key
    * Cerb_frontend.Symbol.sym Cerb_frontend.Cn.cn_base_type
    * (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_expr
    * Locations.t
    * (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_pred
    * (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_expr list ->
    ((Request.t * BaseTypes.Surface.loc_t Cn__BaseTypes.t_gen) * 'a list) E.t

  val translate_cn_let_resource
    :  env ->
    Locations.t
    * Sym.t
    * (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_resource ->
    ((Request.t * BaseTypes.Surface.t)
    * (LogicalConstraints.t * (Locations.t * string option)) list
    * (BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot
      * BaseTypes.Surface.t IndexTerms.annot)
        list)
      E.t

  val translate_cn_assrt
    :  env ->
    Locations.t * (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_assertion ->
    LogicalConstraints.t E.t
end

module ET = EffectfulTranslation

module Pure : sig
  val handle : string -> 'a E.t -> 'a Or_TypeError.t
end

val translate_cn_func_body
  :  env ->
  (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_expr ->
  unit Cn__BaseTypes.t_gen Cn__IndexTerms.annot Or_TypeError.t

val known_attrs : string list

val translate_cn_function
  :  env ->
  cn_function ->
  (Cerb_frontend.Symbol.sym * Definition.Function.t) Or_TypeError.t

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
      pointee_values : IndexTerms.Surface.t STermMap.t
    }

  val empty_state : state

  type states =
    { state : state;
      old_states : state StringMap.t
    }

  val init_st : states

  val make_state_old : states -> StringMap.key -> states

  val add_c_variable_state : Sym.Map.key -> c_variable_state -> states -> states

  val add_pointee_value : STermMap.key -> IndexTerms.Surface.t -> states -> states

  val add_c_variable_states : (Sym.Map.key * c_variable_state) list -> states -> states

  val add_pointee_values : (STermMap.key * IndexTerms.Surface.t) list -> states -> states

  val handle : states -> 'a E.t -> 'a Or_TypeError.t
end

val translate_cn_clause
  :  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_clause ->
  unit Cn__BaseTypes.t_gen Cn__IndexTerms.annot Cn__LogicalArgumentTypes.t Or_TypeError.t

val translate_cn_clauses
  :  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_clauses ->
  Definition.Clause.t list Or_TypeError.t

val translate_option_cn_clauses
  :  env ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_clauses option ->
  Definition.Clause.t list option Or_TypeError.t

val translate_cn_predicate
  :  env ->
  cn_predicate ->
  (Cerb_frontend.Symbol.sym * Definition.Predicate.t) Or_TypeError.t

val make_lrt_generic
  :  env ->
  LocalState.states ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list ->
  (LogicalReturnTypes.t * env * LocalState.states) Or_TypeError.t

val make_lrt
  :  env ->
  LocalState.states ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list ->
  LogicalReturnTypes.t Or_TypeError.t

val make_lat
  :  env ->
  LocalState.states ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list
  * (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list ->
  LogicalReturnTypes.t LogicalArgumentTypes.t Or_TypeError.t

val make_lrt_with_accesses
  :  env ->
  LocalState.states ->
  (Locations.t * (Sym.t * Cerb_frontend.Ctype.ctype)) list
  * (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list ->
  LogicalReturnTypes.t Or_TypeError.t

val make_rt
  :  Locations.t ->
  env ->
  LocalState.states ->
  SymTable.key * Cerb_frontend.Ctype.ctype ->
  (Locations.t * (Sym.t * Cerb_frontend.Ctype.ctype)) list
  * (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list ->
  ReturnTypes.t Or_TypeError.t

val translate_cn_lemma
  :  env ->
  cn_lemma ->
  (Cerb_frontend.Symbol.sym * (Cerb_location.t * LogicalReturnTypes.t ArgumentTypes.t))
    Or_TypeError.t

module UsingLoads : sig
  val pointee_ct
    :  Locations.t ->
    BaseTypes.Surface.loc_t BaseTypes.t_gen IndexTerms.annot ->
    Sctypes.t Or_TypeError.t

  val handle
    :  (Sym.t -> Cerb_frontend.Ctype.ctype) ->
    LocalState.state StringMap.t ->
    Cnprog.t E.t ->
    Cnprog.t Or_TypeError.t
end

val translate_cn_statement
  :  (Sym.t -> Cerb_frontend.Ctype.ctype) ->
  LocalState.state StringMap.t ->
  env ->
  (Sym.Map.key, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_statement ->
  Cnprog.t Or_TypeError.t
