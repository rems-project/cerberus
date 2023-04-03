(*
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_1 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_2 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_3 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_4 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_5 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_6 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_7 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_8 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_9 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_10 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_11 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_12 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_13 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_14 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_15 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_16 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_17 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_18 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_19 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_20 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_21 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_22 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_23 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_24 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_25 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_26 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_27 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_28 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_29 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_30 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_31 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_32 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_33 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_34 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_35 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_36 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_37 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_38 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_39 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_40 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_41 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_42 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_43 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_44 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_45 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_46 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_47 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_48 :
  Landmark.landmark
val __generated_landmark_877e51fc6bfdd166ce77f67ca279b753_49 :
  Landmark.landmark
module CF = Cerb_frontend
module RE = Resources
module RET = ResourceTypes
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module TE = TypeErrors
module SymSet :
  sig
    type elt = BT.tag
    type t = AT.SymSet.t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val disjoint : t -> t -> bool
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val filter_map : (elt -> elt option) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
    val to_seq_from : elt -> t -> elt Seq.t
    val to_seq : t -> elt Seq.t
    val to_rev_seq : t -> elt Seq.t
    val add_seq : elt Seq.t -> t -> t
    val of_seq : elt Seq.t -> t
  end
module SymMap :
  sig
    type key = BT.tag
    type 'a t = 'a IT.SymMap.t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_rev_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t
  end
module S = Solver
module Loc = Locations
module LP = LogicalPredicates
module Mu = Mucore
module RI = ResourceInference
val ( let@ ) : 'a Typing.t -> ('a -> 'b Typing.t) -> 'b Typing.t
module ListM :
  sig
    val mapM : ('a -> 'b Typing.t) -> 'a list -> 'b list Typing.t
    val mapfstM :
      ('a -> 'b Typing.t) -> ('a * 'c) list -> ('b * 'c) list Typing.t
    val mapsndM :
      ('a -> 'b Typing.t) -> ('c * 'a) list -> ('c * 'b) list Typing.t
    val mapiM : (int -> 'a -> 'b Typing.t) -> 'a list -> 'b list Typing.t
    val map2M :
      ('a -> 'b -> 'c Typing.t) -> 'a list -> 'b list -> 'c list Typing.t
    val iterM : ('a -> unit Typing.t) -> 'a list -> unit Typing.t
    val concat_mapM : ('a -> 'b list Typing.t) -> 'a list -> 'b list Typing.t
    val filter_mapM :
      ('a -> 'b option Typing.t) -> 'a list -> 'b list Typing.t
    val filterM : ('a -> bool Typing.t) -> 'a list -> 'a list Typing.t
    val fold_leftM :
      ('a -> 'b -> 'a Typing.t) -> 'a -> 'b list -> 'a Typing.t
    val fold_rightM :
      ('a -> 'b -> 'b Typing.t) -> 'a list -> 'b -> 'b Typing.t
  end
module PmapM :
  sig
    val foldM :
      ('a -> 'b -> 'c -> 'c Typing.t) ->
      ('a, 'b) Pmap.map -> 'c -> 'c Typing.t
    val iterM :
      ('a -> 'b -> unit Typing.t) -> ('a, 'b) Pmap.map -> unit Typing.t
    val mapM :
      ('a -> 'b -> 'c Typing.t) ->
      ('a, 'b) Pmap.map -> ('a -> 'a -> int) -> ('a, 'c) Pmap.map Typing.t
  end
type lvt = IT.t
type mem_value = CF.Impl_mem.mem_value
type pointer_value = CF.Impl_mem.pointer_value
val infer_pattern : Mucore.mu_pattern -> BaseTypes.basetype Typing.t
val infer_pattern : Mucore.mu_pattern -> BaseTypes.basetype Typing.t
val pattern_match :
  Mucore.mu_pattern ->
  BaseTypes.basetype Terms.term -> BaseTypes.tag list Typing.t
val pattern_match :
  Mucore.mu_pattern ->
  BaseTypes.basetype Terms.term -> BaseTypes.tag list Typing.t
module InferenceEqs :
  sig
    val use_model_eqs : bool ref
    val res_pointer_kind :
      RET.resource_type * 'a ->
      (((string * string) * Sctypes.ctype) * lvt) option
    val div_groups : ('a -> 'a -> int) -> 'a list -> 'a list list
    val div_groups_discard :
      ('a -> 'a -> int) -> ('a * 'b) list -> 'b list list
    val unknown_eq_in_group :
      Simplify.simp_ctxt ->
      (BT.basetype Terms.term * bool) list -> BT.basetype Terms.term option
    val upd_ptr_gps_for_model :
      Global.t -> S.model -> (lvt * 'a) list list -> (lvt * 'a) list list
    val add_eqs_for_infer : Location_ocaml.t -> 'a LAT.t -> unit Typing.t
  end
val check_computational_bound :
  Location_ocaml.t -> BaseTypes.tag -> unit Typing.t
val check_computational_bound :
  Location_ocaml.t -> BaseTypes.tag -> unit Typing.t
val check_ptrval :
  Location_ocaml.t ->
  expect:BaseTypes.basetype -> pointer_value -> lvt Typing.t
val check_ptrval :
  Location_ocaml.t ->
  expect:BaseTypes.basetype -> pointer_value -> lvt Typing.t
val check_mem_value :
  Location_ocaml.t -> expect:BaseTypes.basetype -> mem_value -> lvt Typing.t
val check_struct :
  Location_ocaml.t ->
  BaseTypes.tag ->
  (BaseTypes.member * Cerb_frontend.Impl_mem.mem_value) list -> lvt Typing.t
val check_union :
  Location_ocaml.t ->
  BaseTypes.tag ->
  BaseTypes.member -> Cerb_frontend.Impl_mem.mem_value -> lvt Typing.t
val check_mem_value :
  Location_ocaml.t -> expect:BaseTypes.basetype -> mem_value -> lvt Typing.t
val check_struct :
  Location_ocaml.t ->
  BaseTypes.tag ->
  (BaseTypes.member * Cerb_frontend.Impl_mem.mem_value) list -> lvt Typing.t
val check_union :
  Location_ocaml.t ->
  BaseTypes.tag ->
  BaseTypes.member -> Cerb_frontend.Impl_mem.mem_value -> lvt Typing.t
val check_object_value :
  Location_ocaml.t ->
  expect:BaseTypes.basetype -> 'bty Mucore.mu_object_value -> lvt Typing.t
val check_object_value :
  Location_ocaml.t ->
  expect:BaseTypes.basetype -> 'a Mucore.mu_object_value -> lvt Typing.t
val check_value :
  Location_ocaml.t ->
  expect:BaseTypes.basetype -> 'bty Mucore.mu_value -> lvt Typing.t
val check_value :
  Location_ocaml.t ->
  expect:BaseTypes.basetype -> 'a Mucore.mu_value -> lvt Typing.t
val warn_uf : Location_ocaml.t -> string -> unit
val warn_uf : Location_ocaml.t -> string -> unit
val wrapI :
  'a ->
  Cerb_frontend.Ctype.integerType ->
  IT.BT.basetype IT.term -> IT.BT.basetype IT.term
val wrapI :
  'a ->
  Cerb_frontend.Ctype.integerType ->
  IT.BT.basetype IT.term -> IT.BT.basetype IT.term
val is_representable_integer :
  IT.BT.basetype IT.term ->
  Cerb_frontend.Ctype.integerType -> IT.BT.basetype IT.term
val is_representable_integer :
  IT.BT.basetype IT.term ->
  Cerb_frontend.Ctype.integerType -> IT.BT.basetype IT.term
val check_conv_int :
  Location_ocaml.t ->
  expect:BaseTypes.basetype ->
  'a Mucore.act -> IndexTerms.t -> IT.BT.basetype IT.term Typing.t
val check_conv_int :
  Location_ocaml.t ->
  expect:BaseTypes.basetype ->
  'a Mucore.act -> IndexTerms.t -> IT.BT.basetype IT.term Typing.t
val check_array_shift :
  Location_ocaml.t ->
  expect:BaseTypes.basetype ->
  IT.BT.basetype IT.term ->
  Location_ocaml.t * Sctypes.ctype ->
  IT.BT.basetype IT.term -> IT.BT.basetype IT.term Typing.t
val check_array_shift :
  Location_ocaml.t ->
  expect:BaseTypes.basetype ->
  IT.BT.basetype IT.term ->
  Location_ocaml.t * Sctypes.ctype ->
  IT.BT.basetype IT.term -> IT.BT.basetype IT.term Typing.t
val check_pexpr :
  'bty Mucore.mu_pexpr ->
  expect:BaseTypes.basetype -> (lvt -> unit Typing.t) -> unit Typing.t
val check_pexprs :
  ('bty Mucore.mu_pexpr * BaseTypes.basetype) list ->
  (lvt list -> unit Typing.t) -> unit Typing.t
val check_pexpr :
  'a Mucore.mu_pexpr ->
  expect:BaseTypes.basetype -> (lvt -> unit Typing.t) -> unit Typing.t
val check_pexprs :
  ('a Mucore.mu_pexpr * BaseTypes.basetype) list ->
  (lvt list -> unit Typing.t) -> unit Typing.t
module Spine :
  sig
    val calltype_ft :
      Location_ocaml.t ->
      fsym:BT.tag ->
      'a Mu.mu_pexpr list ->
      AT.ft -> (RT.t -> unit Typing.t) -> unit Typing.t
    val calltype_lt :
      Location_ocaml.t ->
      'a Mu.mu_pexpr list ->
      AT.lt * TE.label_kind -> (False.t -> unit Typing.t) -> unit Typing.t
    val calltype_lemma :
      Location_ocaml.t ->
      lemma:BT.tag ->
      (Location_ocaml.t * lvt) list ->
      AT.lemmat -> (LRT.t -> unit Typing.t) -> unit Typing.t
    val calltype_packing :
      Location_ocaml.t ->
      BT.tag -> LAT.packing_ft -> (lvt -> unit Typing.t) -> unit Typing.t
    val subtype :
      Location_ocaml.t -> LRT.t -> (unit -> unit Typing.t) -> unit Typing.t
  end
type 'a orFalse = Normal of 'a | False
val pp_or_false : ('a -> PPrint.document) -> 'a orFalse -> PPrint.document
val pp_or_false : ('a -> PPrint.document) -> 'a orFalse -> PPrint.document
val filter_empty_resources :
  Location_ocaml.t ->
  (Resources.resource * LogicalConstraints.logical_constraint *
   Solver.model_with_q)
  list Typing.t
val filter_empty_resources :
  Location_ocaml.t ->
  (Resources.resource * LogicalConstraints.logical_constraint *
   Solver.model_with_q)
  list Typing.t
val all_empty :
  Location_ocaml.t -> (Resources.resource * int) list * int -> unit Typing.t
val all_empty :
  Location_ocaml.t -> (Resources.resource * int) list * int -> unit Typing.t
type labels = (AT.lt * TE.label_kind) SymMap.t
val load :
  Location_ocaml.t -> IndexTerms.t -> Sctypes.ctype -> IndexTerms.t Typing.t
val load :
  Location_ocaml.t -> IndexTerms.t -> Sctypes.ctype -> IndexTerms.t Typing.t
val instantiate :
  Location_ocaml.t ->
  (IndexTerms.t -> bool) -> BaseTypes.basetype Terms.term -> unit Typing.t
val instantiate :
  Location_ocaml.t ->
  (IndexTerms.t -> bool) -> BaseTypes.basetype Terms.term -> unit Typing.t
val check_expr :
  (ArgumentTypes.lt * TypeErrors.label_kind) Context.SymMap.t ->
  typ:BaseTypes.basetype orFalse ->
  'bty Mucore.mu_expr -> (lvt -> unit Typing.t) -> unit Typing.t
val check_expr :
  (ArgumentTypes.lt * TypeErrors.label_kind) Context.SymMap.t ->
  typ:BaseTypes.basetype orFalse ->
  'a Mucore.mu_expr -> (lvt -> unit Typing.t) -> unit Typing.t
val check_expr_rt :
  Location_ocaml.t ->
  (ArgumentTypes.lt * TypeErrors.label_kind) Context.SymMap.t ->
  typ:ReturnTypes.t orFalse -> 'a Mucore.mu_expr -> unit Typing.t
val check_expr_rt :
  Location_ocaml.t ->
  (ArgumentTypes.lt * TypeErrors.label_kind) Context.SymMap.t ->
  typ:ReturnTypes.t orFalse -> 'a Mucore.mu_expr -> unit Typing.t
val check_pexpr_rt :
  Location_ocaml.t -> 'a Mucore.mu_pexpr -> ReturnTypes.t -> unit Typing.t
val check_pexpr_rt :
  Location_ocaml.t -> 'a Mucore.mu_pexpr -> ReturnTypes.t -> unit Typing.t
val bind_arguments :
  Location_ocaml.t ->
  'a Mucore.mu_arguments ->
  ('a * (ResourceTypes.resource_type * Resources.oargs) list) Typing.t
val bind_arguments :
  Location_ocaml.t ->
  'a Mucore.mu_arguments ->
  ('a * (ResourceTypes.resource_type * Resources.oargs) list) Typing.t
val check_procedure :
  Location_ocaml.t ->
  BaseTypes.tag -> 'bty Mucore.mu_proc_args_and_body -> unit Typing.t
val check_procedure :
  Location_ocaml.t ->
  BaseTypes.tag -> 'a Mucore.mu_proc_args_and_body -> unit Typing.t
val record_tagdefs :
  (BaseTypes.tag, Mucore.mu_tag_definition) Pmap.map -> unit Typing.t
val record_tagdefs :
  (BaseTypes.tag, Mucore.mu_tag_definition) Pmap.map -> unit Typing.t
val check_tagdefs : ('a, Mucore.mu_tag_definition) Pmap.map -> unit Typing.t
val check_tagdefs : ('a, Mucore.mu_tag_definition) Pmap.map -> unit Typing.t
val record_and_check_logical_functions :
  (BaseTypes.tag * LogicalPredicates.definition) list -> unit Typing.t
val record_and_check_logical_functions :
  (BaseTypes.tag * LogicalPredicates.definition) list -> unit Typing.t
val record_and_check_resource_predicates :
  (BaseTypes.tag * ResourcePredicates.definition) list -> unit Typing.t
val record_and_check_resource_predicates :
  (BaseTypes.tag * ResourcePredicates.definition) list -> unit Typing.t
val record_globals :
  (BaseTypes.tag * 'a Mucore.mu_globs) list -> unit Typing.t
val record_globals :
  (BaseTypes.tag * 'a Mucore.mu_globs) list -> unit Typing.t
val wf_check_and_record_functions :
  (BaseTypes.tag, 'a Mucore.mu_fun_map_decl) Pmap.map ->
  ((BaseTypes.tag * (Location_ocaml.t * ArgumentTypes.ft)) list *
   (BaseTypes.tag * (Location_ocaml.t * 'a Mucore.mu_proc_args_and_body))
   list)
  Typing.t
val wf_check_and_record_functions :
  (BaseTypes.tag, 'a Mucore.mu_fun_map_decl) Pmap.map ->
  ((BaseTypes.tag * (Location_ocaml.t * ArgumentTypes.ft)) list *
   (BaseTypes.tag * (Location_ocaml.t * 'a Mucore.mu_proc_args_and_body))
   list)
  Typing.t
val check_c_functions :
  (BaseTypes.tag * (Location_ocaml.t * 'a Mucore.mu_proc_args_and_body)) list ->
  unit Typing.t
val check_c_functions :
  (BaseTypes.tag * (Location_ocaml.t * 'a Mucore.mu_proc_args_and_body)) list ->
  unit Typing.t
val wf_check_and_record_lemma :
  BaseTypes.tag * (Location_ocaml.t * LogicalReturnTypes.t ArgumentTypes.t) ->
  (BaseTypes.tag * (Location_ocaml.t * LogicalReturnTypes.t ArgumentTypes.t))
  Typing.t
val wf_check_and_record_lemma :
  BaseTypes.tag * (Location_ocaml.t * LogicalReturnTypes.t ArgumentTypes.t) ->
  (BaseTypes.tag * (Location_ocaml.t * LogicalReturnTypes.t ArgumentTypes.t))
  Typing.t
val check :
  'a Mucore.mu_file ->
  Location_ocaml.t CStatements.LocMap.t -> string option -> unit Typing.t
  *)
  val use_model_eqs : bool ref
  val only : string option ref

  val check :
  'a Mucore.mu_file ->
  Location_ocaml.t CStatements.LocMap.t -> string option -> unit Typing.t
