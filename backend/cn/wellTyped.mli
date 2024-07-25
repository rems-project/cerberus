(* Module WellTyped *)

(* TODO: AM: Needs a header explaining what it is *)

module LS = LogicalSorts
module BT = BaseTypes

module SymSet : Set.S with type elt = Sym.t

module TE = TypeErrors
module RE = Resources
module RET = ResourceTypes
module LRT = LogicalReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module Mu = Mucore

module IdSet : Set.S with type elt = Id.t

val use_ity : bool ref

val ensure_base_type
  :  Locations.t ->
  expect:LogicalSorts.t ->
  LogicalSorts.t ->
  unit Typing.m

val illtyped_index_term
  :  Locations.t ->
  'a Terms.term ->
  TE.BT.basetype ->
  expected:string ->
  reason:(Locations.t, string) Either.either ->
  'b * 'c ->
  TE.type_error

val ensure_bits_type : TE.Loc.t -> TE.BT.t -> unit Typing.m

val ensure_z_fits_bits_type : Locations.t -> TE.BT.sign * int -> Z.t -> unit Typing.m

val ensure_arith_type : reason:Locations.t -> TE.BT.basetype Terms.term -> unit Typing.m

val ensure_set_type
  :  reason:Locations.t ->
  TE.BT.basetype Terms.term ->
  TE.BT.basetype Typing.m

val ensure_list_type
  :  reason:Locations.t ->
  TE.BT.basetype Terms.term ->
  TE.BT.basetype Typing.m

val ensure_map_type
  :  reason:Locations.t ->
  TE.BT.basetype Terms.term ->
  (TE.BT.basetype * TE.BT.basetype) Typing.m

val ensure_same_argument_number
  :  Locations.t ->
  [< `General | `Input | `Output ] ->
  int ->
  expect:int ->
  unit Typing.m

val compare_by_fst_id : Id.t * 'a -> Id.t * 'b -> int

val correct_members : Locations.t -> (Id.t * 'a) list -> (Id.t * 'b) list -> unit Typing.m

val correct_members_sorted_annotated
  :  Locations.t ->
  (Id.t * 'a) list ->
  (Id.t * 'b) list ->
  ('a * (Id.t * 'b)) list Typing.m

module WBT : sig
  val is_bt : Locations.t -> TE.BT.basetype -> TE.BT.basetype Typing.m

  val pick_integer_encoding_type : Locations.t -> Z.t -> TE.BT.basetype Typing.m
end

module WLS : sig
  val is_ls : Locations.t -> TE.BT.basetype -> TE.BT.basetype Typing.m
end

module WCT : sig
  val is_ct : Locations.t -> Sctypes.ctype -> unit Typing.m
end

module WIT : sig
  type t = IndexTerms.t

  val check_and_bind_pattern
    :  BaseTypes.t ->
    'a IndexTerms.pattern ->
    BaseTypes.t IndexTerms.pattern Typing.m

  val leading_sym_or_wild : 'a IndexTerms.pattern list -> bool

  val expand_constr
    :  Sym.S.sym * BaseTypes.constr_info ->
    IndexTerms.BT.t IndexTerms.pattern list ->
    BaseTypes.basetype IndexTerms.pattern list option

  val cases_complete
    :  Locations.t ->
    IndexTerms.BT.t list ->
    IndexTerms.BT.t IndexTerms.pattern list list ->
    unit Typing.m

  val cases_necessary : 'a IndexTerms.pattern list -> unit Typing.m

  val get_location_for_type : 'a IndexTerms.term -> Locations.t Typing.m

  val infer : 'bt IndexTerms.term -> IndexTerms.BT.t IndexTerms.term Typing.m

  val check
    :  IndexTerms.loc ->
    IndexTerms.BT.basetype ->
    'bt IndexTerms.term ->
    IndexTerms.BT.t IndexTerms.term Typing.m
end

module WRET : sig
  val welltyped : Locations.t -> TE.RET.resource_type -> TE.RET.resource_type Typing.m
end

val oarg_bt_of_pred : Locations.t -> TE.RET.predicate_name -> Memory.BT.basetype Typing.m

val oarg_bt : Locations.t -> TE.RET.resource_type -> Memory.BT.basetype Typing.m

module WRS : sig
  val welltyped
    :  Locations.t ->
    TE.RET.resource_type * TE.BT.basetype ->
    (TE.RET.resource_type * TE.BT.basetype) Typing.m
end

module WLC : sig
  type t = LogicalConstraints.t

  val welltyped
    :  IndexTerms.loc ->
    TE.LC.logical_constraint ->
    TE.LC.logical_constraint Typing.m
end

module WLRT : sig
  module LRT = LogicalReturnTypes

  type t = LogicalReturnTypes.t

  val welltyped : 'a -> LRT.t -> LRT.t Typing.m
end

module WRT : sig
  type t = ReturnTypes.t

  val subst
    :  [ `Rename of Sym.t | `Term of LogicalConstraints.IT.typed ] Subst.t ->
    ReturnTypes.t ->
    ReturnTypes.t

  val pp : ReturnTypes.t -> Pp.document

  val welltyped : 'a -> Global.RT.t -> Global.RT.t Typing.m
end

module WFalse : sig
  type t = False.t

  val subst : 'a -> False.t -> False.t

  val pp : False.t -> Pp.document

  val welltyped : 'a -> False.t -> False.t Typing.m
end

module WLAT : sig
  val welltyped
    :  'a ->
    (Locations.t -> 'i -> 'i Typing.m) ->
    string ->
    Locations.t ->
    'i LAT.t ->
    'i LAT.t Typing.m
end

module WAT : sig
  val welltyped
    :  'a ->
    (Locations.t -> 'i -> 'i Typing.m) ->
    string ->
    Locations.t ->
    'i Global.AT.t ->
    'i Global.AT.t Typing.m
end

module WFT : sig
  val welltyped
    :  string ->
    Locations.t ->
    Global.RT.t Global.AT.t ->
    Global.RT.t Global.AT.t Typing.m
end

module WLT : sig
  val welltyped
    :  string ->
    Locations.t ->
    False.t Global.AT.t ->
    False.t Global.AT.t Typing.m
end

module WLArgs : sig
  val typ : ('a -> 'b) -> 'a Mu.mu_arguments_l -> 'b LAT.t

  val welltyped
    :  (TE.Loc.t -> 'i -> 'j Typing.m) ->
    string ->
    Locations.t ->
    'i Mu.mu_arguments_l ->
    'j Mu.mu_arguments_l Typing.m
end

module WArgs : sig
  val typ : ('a -> 'b) -> 'a Mu.mu_arguments -> 'b Global.AT.t

  val welltyped
    :  (TE.Loc.t -> 'i -> 'j Typing.m) ->
    string ->
    TE.Loc.t ->
    'i Mu.mu_arguments ->
    'j Mu.mu_arguments Typing.m
end

module BaseTyping : sig
  module SymMap : sig
    type key = Sym.t

    type 'a t = 'a Stdlib__Map.Make(Sym).t

    val empty : 'a t

    val add : key -> 'a -> 'a t -> 'a t

    val add_to_list : key -> 'a -> 'a list t -> 'a list t

    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t

    val singleton : key -> 'a -> 'a t

    val remove : key -> 'a t -> 'a t

    val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

    val cardinal : 'a t -> int

    val bindings : 'a t -> (key * 'a) list

    val min_binding : 'a t -> key * 'a

    val min_binding_opt : 'a t -> (key * 'a) option

    val max_binding : 'a t -> key * 'a

    val max_binding_opt : 'a t -> (key * 'a) option

    val choose : 'a t -> key * 'a

    val choose_opt : 'a t -> (key * 'a) option

    val find : key -> 'a t -> 'a

    val find_opt : key -> 'a t -> 'a option

    val find_first : (key -> bool) -> 'a t -> key * 'a

    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option

    val find_last : (key -> bool) -> 'a t -> key * 'a

    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option

    val iter : (key -> 'a -> unit) -> 'a t -> unit

    val fold : (key -> 'a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc

    val map : ('a -> 'b) -> 'a t -> 'b t

    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t

    val filter : (key -> 'a -> bool) -> 'a t -> 'a t

    val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t

    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t

    val split : key -> 'a t -> 'a t * 'a option * 'a t

    val is_empty : 'a t -> bool

    val mem : key -> 'a t -> bool

    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

    val for_all : (key -> 'a -> bool) -> 'a t -> bool

    val exists : (key -> 'a -> bool) -> 'a t -> bool

    val to_list : 'a t -> (key * 'a) list

    val of_list : (key * 'a) list -> 'a t

    val to_seq : 'a t -> (key * 'a) Seq.t

    val to_rev_seq : 'a t -> (key * 'a) Seq.t

    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t

    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t

    val of_seq : (key * 'a) Seq.t -> 'a t
  end

  module BT = BaseTypes
  module RT = ReturnTypes
  module AT = ArgumentTypes

  type label_context = (AT.lt * TypeErrors.label_kind * Locations.t) SymMap.t

  val check_against_core_bt
    :  Locations.t ->
    Pp.document ->
    Cerb_frontend.Core.core_base_type ->
    CoreTypeChecks.BT.basetype ->
    unit Typing.m

  val check_and_bind_pattern
    :  CoreTypeChecks.BT.basetype ->
    'a Mucore.mu_pattern ->
    CoreTypeChecks.BT.basetype Mucore.mu_pattern Typing.m

  val check_and_bind_pattern_
    :  CoreTypeChecks.BT.basetype ->
    Mucore.loc ->
    'a Mucore.mu_pattern_ ->
    CoreTypeChecks.BT.basetype Mucore.mu_pattern_ Typing.m

  val infer_object_value
    :  Locations.t ->
    'TY Mucore.mu_object_value ->
    BT.t Mucore.mu_object_value Typing.m

  val check_object_value
    :  Locations.t ->
    BT.t ->
    'TY Mucore.mu_object_value ->
    BT.t Mucore.mu_object_value Typing.m

  val infer_value : Locations.t -> 'TY Mucore.mu_value -> BT.t Mucore.mu_value Typing.m

  val check_value
    :  Locations.t ->
    BT.t ->
    'TY Mucore.mu_value ->
    BT.t Mucore.mu_value Typing.m

  val is_integer_annot
    :  TypeErrors.CF.Annot.annot ->
    Cerb_frontend.IntegerType.integerType option

  val integer_annot
    :  TypeErrors.CF.Annot.annot list ->
    TypeErrors.CF.IntegerType.integerType option

  val remove_integer_annot
    :  TypeErrors.CF.Annot.annot list ->
    TypeErrors.CF.Annot.annot list

  val remove_integer_annot_expr : 'a Mucore.mu_expr -> 'a Mucore.mu_expr

  val remove_integer_annot_pexpr : 'a Mucore.mu_pexpr -> 'a Mucore.mu_pexpr

  val infer_pexpr : 'TY Mucore.mu_pexpr -> BT.t Mucore.mu_pexpr Typing.m

  val check_pexpr : BT.t -> 'TY Mucore.mu_pexpr -> BT.t Mucore.mu_pexpr Typing.m

  val check_infer_apply_fun
    :  BT.t option ->
    Mucore.mu_function ->
    'TY Mucore.mu_pexpr list ->
    'TY Mucore.mu_pexpr ->
    (Context.BT.t * BT.t Mucore.mu_pexpr list) Typing.m

  val check_cn_statement
    :  Locations.t ->
    Cnprog.cn_statement ->
    Cnprog.cn_statement Typing.m

  val check_cnprog : Cnprog.cn_prog -> Cnprog.cn_prog Typing.m

  val signed_int_ty : Memory.BT.basetype

  val infer_expr : label_context -> 'TY Mucore.mu_expr -> BT.t Mucore.mu_expr Typing.m

  val check_expr
    :  label_context ->
    BT.t ->
    'TY Mucore.mu_expr ->
    BT.t Mucore.mu_expr Typing.m
end

module WLabel : sig
  val typ : 'a Mu.mu_arguments -> False.t Global.AT.t

  val welltyped
    :  Mu.Loc.t ->
    'a Mu.mu_expr Mu.mu_arguments ->
    'a Mu.mu_expr Mu.mu_arguments Typing.m
end

module WProc : sig
  val label_context
    :  Global.AT.RT.t ->
    (Global.SymMap.key, 'a Mu.mu_label_def) Pmap.map ->
    (False.t Global.AT.t * TE.CF.Annot.label_annot * Mu.loc) Global.SymMap.t

  val typ : ('a * 'b * 'c) Mu.mu_arguments -> 'c Global.AT.t

  val welltyped
    :  Mu.Loc.t ->
    'TY Mu.mu_proc_args_and_body ->
    BaseTyping.BT.t Mu.mu_proc_args_and_body Typing.m
end

module WRPD : sig
  val welltyped : ResourcePredicates.definition -> ResourcePredicates.definition Typing.m
end

module WLFD : sig
  val welltyped : LogicalFunctions.definition -> LogicalFunctions.definition Typing.m
end

module WLemma : sig
  val welltyped
    :  Locations.t ->
    'a ->
    WLRT.LRT.t Global.AT.t ->
    WLRT.LRT.t Global.AT.t Typing.m
end

module WDT : sig
  val welltyped : 'a * Mu.mu_datatype -> ('a * Mu.mu_datatype) Typing.m

  module G : module type of Graph.Persistent.Digraph.Concrete (Sym)

  module Components : module type of Graph.Components.Make (G)

  val bts_in_dt_constructor_argument : 'a * TE.BT.t -> TE.BT.t list

  val bts_in_dt_case : 'a * ('b * TE.BT.t) list -> TE.BT.t list

  val bts_in_dt_definition : Mu.mu_datatype -> TE.BT.t list

  val dts_in_dt_definition : Mu.mu_datatype -> Sym.t list

  val check_recursion_ok : (Sym.S.sym * Mu.mu_datatype) list -> G.V.t list list Typing.m
end
