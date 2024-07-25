(* Module Check -- Preforms the type checking on the C code *)

module CF = Cerb_frontend
module IT = IndexTerms
module BT = BaseTypes
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module IdSet : Set.S with type elt = Id.t
module SymSet : Set.S with type elt = Sym.t
module SymMap : Map.S with type key = Sym.t
module Loc = Locations
module RI = ResourceInference

(* some of this is informed by impl_mem *)
type mem_value = ResourceTypes.CF.Impl_mem.mem_value

type pointer_value = ResourceTypes.CF.Impl_mem.pointer_value

(*** pattern matching *********************************************************)

(*pattern-matches and binds*)
val check_and_match_pattern
  :  TypeErrors.BT.basetype Mucore.mu_pattern ->
  IndexTerms.t ->
  Cerb_frontend.Symbol.sym List.t Typing.m

(*** pure value inference *****************************************************)

val check_computational_bound : Locations.t -> Sym.t -> unit Typing.m

val unsupported : Locations.t -> Cerb_pp_prelude.P.document -> 'a Typing.m

val check_ptrval
  :  Mucore.loc ->
  expect:LogicalConstraints.BT.t ->
  pointer_value ->
  LogicalConstraints.IT.t Typing.m

val expect_must_be_map_bt
  :  Locations.t ->
  expect:LogicalConstraints.BT.basetype ->
  (LogicalConstraints.BT.basetype * LogicalConstraints.BT.basetype) Typing.m

val check_mem_value
  :  Mucore.loc ->
  expect:LogicalConstraints.BT.t ->
  mem_value ->
  LogicalConstraints.IT.t Typing.m

val check_struct
  :  Mucore.loc ->
  Sym.t ->
  (Id.t * Sctypes.t * mem_value) list ->
  LogicalConstraints.IT.t Typing.m

val check_union
  :  Mucore.loc ->
  Sym.t ->
  Id.t ->
  mem_value ->
  LogicalConstraints.IT.t Typing.m

val ensure_bitvector_type
  :  Mucore.Loc.t ->
  expect:LogicalConstraints.BT.t ->
  (TypeErrors.BT.sign * int) Typing.m

val check_object_value
  :  Mucore.loc ->
  LogicalConstraints.BT.t Mucore.mu_object_value ->
  LogicalConstraints.IT.t Typing.m

val check_value
  :  Mucore.loc ->
  LogicalSorts.t Mucore.mu_value ->
  LogicalConstraints.IT.t Typing.m

(*** pure expression inference ************************************************)

val is_representable_integer
  :  LogicalConstraints.BT.basetype Terms.term ->
  Cerb_frontend.Ctype.integerType ->
  IT.BT.basetype IT.term

val eq_value_with
  :  (IndexTerms.t -> 'a Option.t) ->
  IndexTerms.t ->
  (IndexTerms.t * 'a) option Typing.m

val prefer_value_with : (IndexTerms.t -> bool) -> IndexTerms.t -> IndexTerms.t Typing.m

val try_prove_constant : Locations.t -> IndexTerms.t -> IndexTerms.t Typing.m

val check_single_ct
  :  IndexTerms.loc ->
  IndexTerms.BT.t IndexTerms.term ->
  Sctypes.ctype Typing.m

val is_fun_addr : Global.t -> 'a LogicalConstraints.IT.term -> Sym.t option

val known_function_pointer : Locations.t -> IndexTerms.t -> Sym.t Typing.m

val check_conv_int
  :  Locations.t ->
  expect:TypeErrors.BT.basetype ->
  Sctypes.ctype ->
  TypeErrors.IT.t ->
  IT.BT.basetype IT.term Typing.m

val _check_array_shift
  :  Locations.t ->
  expect:LogicalSorts.t ->
  IT.BT.basetype IT.term ->
  Locations.t * Sctypes.ctype ->
  IT.BT.basetype IT.term ->
  (IT.loc -> IT.BT.basetype IT.term) Typing.m

val check_against_core_bt
  :  Locations.t ->
  Pp.document ->
  Cerb_frontend.Core.core_base_type ->
  CoreTypeChecks.BT.basetype ->
  unit Typing.m

(* Type checks if pure expressions within C are valid expressions *)
val check_pexpr
  :  LogicalConstraints.BT.t Mucore.mu_pexpr ->
  (LogicalConstraints.IT.t -> unit Typing.m) ->
  unit Typing.m

val check_pexprs
  :  LogicalConstraints.BT.t Mucore.mu_pexpr list ->
  (LogicalConstraints.IT.t list -> unit Typing.m) ->
  unit Typing.m

module Spine : sig
  val calltype_ft
    :  Mucore.Loc.t ->
    fsym:Sym.t ->
    LogicalConstraints.BT.t Mucore.mu_pexpr list ->
    AT.ft ->
    (RT.t -> unit Typing.m) ->
    unit Typing.m

  val calltype_lt
    :  Mucore.Loc.t ->
    LogicalConstraints.BT.t Mucore.mu_pexpr list ->
    AT.lt * TypeErrors.label_kind ->
    (False.t -> unit Typing.m) ->
    unit Typing.m

  val calltype_lemma
    :  Mucore.Loc.t ->
    lemma:Sym.t ->
    (Mucore.Loc.t * LogicalConstraints.IT.t) list ->
    AT.lemmat ->
    (LRT.t -> unit Typing.m) ->
    unit Typing.m

  val subtype : Mucore.Loc.t -> LRT.t -> (unit -> unit Typing.m) -> unit Typing.m
end

(*** impure expression inference **********************************************)

val filter_empty_resources
  :  Locations.t ->
  (Resources.t * ResourcePredicates.LC.logical_constraint * Solver.model_with_q) List.t
    Typing.m

val all_empty : Locations.t -> 'a -> unit Typing.m

val compute_used
  :  Locations.t ->
  ('a * Int.t) list * int ->
  ('a * Int.t) list * 'b ->
  (('a * Context.resource_history * Int.t) list
  * ('a * Context.resource_history * Int.t) list)
    Typing.m

val _check_used_distinct
  :  Locations.t ->
  (((ResourceTypes.resource_type * Resources.oargs)
   * Context.resource_history
   * Context.IntMap.key)
     list
  * ((ResourceTypes.resource_type * Resources.oargs)
    * Context.resource_history
    * Context.IntMap.key)
      list)
    list ->
  unit Typing.m

val load : Locations.t -> ResourceTypes.IT.t -> Sctypes.t -> ResourceTypes.IT.t Typing.m

val instantiate
  :  IT.loc ->
  (LogicalConstraints.IT.t -> bool) ->
  BaseTypes.t Terms.term ->
  unit Typing.m

val add_trace_information : 'a -> ResourceTypes.CF.Annot.annot list -> unit Typing.m

(* Type checks if impure expressions within C & CN are valid expressions *)
val check_expr
  :  (AT.lt * TypeErrors.label_kind * 'a) IT.SymMap.t ->
  LogicalConstraints.BT.t Mucore.mu_expr ->
  (LogicalConstraints.IT.t -> unit Typing.m) ->
  unit Typing.m

val check_expr_top
  :  Locations.t ->
  (AT.lt * TypeErrors.label_kind * 'a) IT.SymMap.t ->
  RT.t ->
  LogicalSorts.t Mucore.mu_expr ->
  unit Typing.m

val bind_arguments
  :  Mucore.Loc.t ->
  'a Mucore.mu_arguments ->
  ('a * (ResourceTypes.t * Resources.oargs) List.t) Typing.m

val post_state_of_rt : Mucore.Loc.t -> AT.RT.t -> Context.t Typing.m

(* check_procedure: type check an (impure) procedure *)
val check_procedure
  :  Mucore.loc ->
  Sym.t ->
  LogicalSorts.t Mucore.mu_proc_args_and_body ->
  unit Typing.m

val skip_and_only : (string list * string list) ref

val batch : bool ref

val record_tagdefs : (Sym.t, Mucore.mu_tag_definition) Pmap.map -> unit Typing.m

val check_tagdefs : ('a, Mucore.mu_tag_definition) Pmap.map -> unit Typing.m

val record_and_check_logical_functions
  :  (Cerb_frontend.Symbol.sym * LogicalFunctions.definition) list ->
  unit Typing.m

val record_and_check_resource_predicates
  :  (Cerb_frontend.Symbol.sym * ResourcePredicates.definition) list ->
  unit Typing.m

val record_globals : (Mucore.symbol * 'bty Mucore.mu_globs) list -> unit Typing.m

val register_fun_syms : 'a Mucore.mu_file -> unit Typing.m

val wf_check_and_record_functions
  :  (Cerb_frontend.Symbol.sym, 'a Mucore.mu_fun_map_decl) Pmap.map ->
  (Cerb_frontend.Symbol.sym, Sctypes.c_concrete_sig) Pmap.map ->
  ((Cerb_frontend.Symbol.sym * (Cerb_location.t * Mucore.T.rt Global.AT.t)) List.t
  * (Cerb_frontend.Symbol.sym * (Cerb_location.t * BT.t Mucore.mu_proc_args_and_body))
      List.t)
    Typing.m

val check_c_functions
  :  (Sym.t * (Mucore.loc * LogicalSorts.t Mucore.mu_proc_args_and_body)) list ->
  unit Typing.m

val wf_check_and_record_lemma
  :  Sym.t * (Locations.t * LRT.t Global.AT.t) ->
  (Sym.t * (Locations.t * LRT.t Global.AT.t)) Typing.m

val ctz_proxy_ft : RT.t ResourcePredicates.AT.t

val ffs_proxy_ft : Cerb_frontend.Ctype.integerBaseType -> RT.t ResourcePredicates.AT.t

val add_stdlib_spec
  :  (Sym.CF.Symbol.sym, Sctypes.c_concrete_sig) Pmap.map ->
  Sym.CF.Symbol.sym ->
  unit Typing.m

val record_and_check_datatypes : (Sym.t * Mucore.mu_datatype) list -> unit Typing.m

val check_decls_lemmata_fun_specs
  :  unit Mucore.mu_file ->
  ((Cerb_frontend.Symbol.sym * (Cerb_location.t * BT.t Mucore.mu_proc_args_and_body))
     List.t
  * (Sym.t * (Locations.t * LRT.t Global.AT.t)) list)
    Typing.m

val check
  :  (Sym.t * (Mucore.loc * LogicalSorts.t Mucore.mu_proc_args_and_body)) list
     * (Sym.t * (Lemmata.Loc.t * Lemmata.AT.lemmat)) list ->
  string option ->
  unit Typing.m
