(* module CF = Cerb_frontend *)
(* module BT = BaseTypes *)
(* module IT = IndexTerms *)
(* module Loc = Locations *)
module IdSet : Set.S with type elt = Id.t

(* val squotes : Pp.document -> Pp.document *)
(* val warn : Locations.t -> Pp.document -> unit *)
(* val dot : Pp.document *)
(* val string : string -> Pp.document *)
(* val debug : int -> Pp.document Lazy.t -> unit *)
(* val item : string -> Pp.document -> Pp.document *)
(* val colon : Pp.document *)
(* val comma : Pp.document *)
module type NoSolver = sig
  type 'a m = 'a Typing.t

  type failure = Context.t * Explain.log -> TypeErrors.t

  val pure : 'a m -> 'a m

  val fail : failure -> 'a m

  val bound_a : Sym.t -> bool m

  val bound_l : Sym.t -> bool m

  val get_a : Sym.t -> Context.basetype_or_value m

  val get_l : Sym.t -> Context.basetype_or_value m

  val add_a : Sym.t -> BaseTypes.t -> Context.l_info -> unit m

  val add_l : Sym.t -> BaseTypes.t -> Context.l_info -> unit m

  val get_struct_decl : Locations.t -> Sym.t -> Memory.struct_layout m

  val get_struct_member_type : Locations.t -> Sym.t -> Id.t -> Sctypes.ctype m

  val get_datatype : Locations.t -> Sym.t -> BaseTypes.dt_info m

  val get_datatype_constr : Locations.t -> Sym.t -> BaseTypes.constr_info m

  val get_resource_predicate_def : Locations.t -> Sym.t -> Definition.Predicate.t m

  val get_logical_function_def : Locations.t -> Sym.t -> Definition.Function.t m

  val get_lemma : Locations.t -> Sym.t -> (Locations.t * ArgumentTypes.lemmat) m

  val get_fun_decl
    :  Locations.t ->
    Sym.t ->
    (Locations.t * ArgumentTypes.ft option * Sctypes.c_concrete_sig) m

  val ensure_base_type : Locations.t -> expect:BaseTypes.t -> BaseTypes.t -> unit m

  val lift : 'a Or_TypeError.t -> 'a m
end

(* val fail : TypeErrors.t -> 'a Typing.t *)
val use_ity : bool ref

(* val illtyped_index_term : *)
(* Locations.t -> *)
(* 'a IT.annot -> *)
(* unit BT.t_gen -> *)
(* expected:string -> *)
(* reason:(Locations.t, string) Either.either -> TypeErrors.t *)
(* (* keep *) *)
val ensure_bits_type : Locations.t -> BaseTypes.t -> unit Typing.t

(* val ensure_z_fits_bits_type : *)
(* Locations.t -> BT.sign * int -> Z.t -> unit Typing.t *)
(* val ensure_arith_type : *)
(* reason:Locations.t -> unit BT.t_gen IT.annot -> unit Typing.t *)
(* val ensure_set_type : *)
(* reason:Locations.t -> *)
(* unit BT.t_gen IT.annot -> unit BT.t_gen Typing.t *)
(* val ensure_list_type : *)
(* reason:Locations.t -> *)
(* unit BT.t_gen IT.annot -> unit BT.t_gen Typing.t *)
(* val ensure_map_type : *)
(* reason:Locations.t -> *)
(* unit BT.t_gen IT.annot -> (unit BT.t_gen * unit BT.t_gen) Typing.t *)
(* keep *)
val ensure_same_argument_number
  :  Locations.t ->
  [< `General | `Input | `Output ] ->
  int ->
  expect:int ->
  unit Typing.t
(* keep *)

val compare_by_fst_id : Id.t * 'a -> Id.t * 'b -> int

(* val correct_members : *)
(* Locations.t -> *)
(* (Id.t * 'a) list -> (Id.t * 'b) list -> unit Typing.t *)
(* val correct_members_sorted_annotated : *)
(* Locations.t -> *)
(* (Id.t * 'a) list -> *)
(* (Id.t * 'b) list -> ('a * (Id.t * 'b)) list Typing.t *)
(* module WBT : *)
(* sig *)
(* val is_bt : Locations.t -> unit BT.t_gen -> unit BT.t_gen Typing.t *)
(* val pick_integer_encoding_type : *)
(* Locations.t -> Z.t -> 'a BT.t_gen Typing.t *)
(* end *)
module WCT : (* keep *) sig
  val is_ct : Locations.t -> Sctypes.ctype -> unit Typing.t
end

module WIT : sig
  (* module LC = LogicalConstraints *)
  (* type t = IndexTerms.t *)
  (* val check_and_bind_pattern : *)
  (* BT.t -> *)
  (* 'a IndexTerms.pattern -> BT.t IndexTerms.pattern Typing.t *)
  (* val leading_sym_or_wild : 'a IndexTerms.pattern list -> bool *)
  (* val expand_constr : *)
  (* Sym.S.sym * IndexTerms.BT.constr_info -> *)
  (* IndexTerms.BT.t IndexTerms.pattern list -> *)
  (* IndexTerms.BT.t IndexTerms.pattern list option *)
  (* val cases_complete : *)
  (* Locations.t -> *)
  (* IndexTerms.BT.t list -> *)
  (* IndexTerms.BT.t IndexTerms.pattern list list -> unit Typing.t *)
  (* val cases_necessary : 'a IndexTerms.pattern list -> unit Typing.t *)
  (* val get_location_for_type : *)
  (* 'a IndexTerms.annot -> Locations.t Typing.t *)
  (* keep *)
  val infer : 'bt IndexTerms.annot -> IndexTerms.t Typing.t
  (* keep *)

  val check : Locations.t -> BaseTypes.t -> 'bt IndexTerms.annot -> IndexTerms.t Typing.t
end
(* keep *)

val quantifier_bt : 'a BaseTypes.t_gen

(* val warn_when_not_quantifier_bt : *)
(* string -> Locations.t -> BaseTypes.t -> Pp.document option -> unit *)
(* module WReq : *)
(* sig *)
(* module Req = Request *)
(* val welltyped : Locations.t -> Req.t -> Req.t Typing.t *)
(* end *)
module WRS : sig
  (* keep *)
  val oarg_bt_of_pred : Locations.t -> Request.name -> BaseTypes.t Typing.t
  (* val oarg_bt : *)
  (* Locations.t -> Request.t -> unit Memory.BT.t_gen Typing.t *)
  (* val welltyped : *)
  (* Locations.t -> *)
  (* WReq.Req.t * unit BT.t_gen -> (WReq.Req.t * unit BT.t_gen) Typing.t *)
end

module WLC : sig
  (* module LC = LogicalConstraints *)
  (* keep *)
  val welltyped : Locations.t -> LogicalConstraints.t -> LogicalConstraints.t Typing.t
end

(* module WLRT : *)
(* sig *)
(* module LC = LogicalConstraints *)
(* module LRT = LogicalReturnTypes *)
(* val consistent : Locations.t -> LRT.t -> unit Typing.m *)
(* val welltyped : 'a -> LRT.t -> LRT.t Typing.t *)
(* end *)
(* module WRT : *)
(* sig *)
(* val subst : *)
(* [ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t -> *)
(* ReturnTypes.t -> ReturnTypes.t *)
(* val pp : ReturnTypes.t -> Pp.document *)
(* val consistent : Locations.t -> ReturnTypes.t -> unit Typing.t *)
(* val welltyped : 'a -> ReturnTypes.t -> ReturnTypes.t Typing.t *)
(* end *)
(* val pure_and_no_initial_resources : *)
(* Locations.t -> 'a Typing.m -> 'a Typing.m *)
(* module WLAT : *)
(* sig *)
(* module LC = LogicalConstraints *)
(* module LAT = LogicalArgumentTypes *)
(* val consistent : *)
(* (Locations.t -> 'i -> unit Typing.m) -> *)
(* ('i -> Pp.document) -> *)
(* string -> Locations.t -> 'i LAT.t -> unit Typing.t *)
(* val welltyped : *)
(* (Locations.t -> 'i -> 'i Typing.t) -> *)
(* ('i -> Pp.document) -> *)
(* string -> Locations.t -> 'i LAT.t -> 'i LAT.t Typing.t *)
(* end *)
(* module WAT : *)
(* sig *)
(* module AT = ArgumentTypes *)
(* val consistent : *)
(* (Locations.t -> 'i -> unit Typing.m) -> *)
(* ('i -> Pp.document) -> *)
(* string -> Locations.t -> 'i AT.t -> unit Typing.t *)
(* val welltyped : *)
(* (Locations.t -> 'i -> 'i Typing.t) -> *)
(* ('i -> Pp.document) -> *)
(* string -> Locations.t -> 'i AT.t -> 'i AT.t Typing.t *)
(* end *)
module WFT : sig
  (* keep *)
  val consistent : string -> Locations.t -> ReturnTypes.t ArgumentTypes.t -> unit Typing.t

  (* keep *)
  val welltyped
    :  string ->
    Locations.t ->
    ReturnTypes.t ArgumentTypes.t ->
    ReturnTypes.t ArgumentTypes.t Typing.t
end

(* module WLT : *)
(* sig *)
(* val welltyped : *)
(* string -> *)
(* Locations.t -> False.t WAT.AT.t -> False.t WAT.AT.t Typing.t *)
(* end *)
(* module WLArgs : *)
(* sig *)
(* module LC = LogicalConstraints *)
(* module LAT = LogicalArgumentTypes *)
(* module Mu = Mucore *)
(* val typ : ('a -> 'b) -> 'a Mu.arguments_l -> 'b LAT.t *)
(* val consistent : *)
(* (Locations.t -> 'i -> unit Typing.t) -> *)
(* string -> Locations.t -> 'i Mu.arguments_l -> unit Typing.t *)
(* val welltyped : *)
(* (Locations.t -> 'i -> 'j Typing.t) -> *)
(* 'a -> Locations.t -> 'i Mu.arguments_l -> 'j Mu.arguments_l Typing.t *)
(* end *)
(* module WArgs : *)
(* sig *)
(* module AT = ArgumentTypes *)
(* module Mu = Mucore *)
(* val typ : ('a -> 'b) -> 'a Mu.arguments -> 'b AT.t *)
(* val consistent : *)
(* (Locations.t -> 'i -> unit Typing.t) -> *)
(* string -> Locations.t -> 'i Mu.arguments -> unit Typing.t *)
(* val welltyped : *)
(* (Locations.t -> 'i -> 'j Typing.t) -> *)
(* string -> Locations.t -> 'i Mu.arguments -> 'j Mu.arguments Typing.t *)
(* end *)
module BaseTyping : sig
  (* module BT = BaseTypes *)
  (* module RT = ReturnTypes *)
  (* module AT = ArgumentTypes *)
  (* keep *)
  type label_context = (ArgumentTypes.lt * Where.label * Locations.t) Sym.Map.t

  (* val check_against_core_bt : *)
  (* Locations.t -> *)
  (* Cn__Pp.document -> *)
  (* Cerb_frontend.Core.core_base_type -> *)
  (* unit CoreTypeChecks.BT.t_gen -> unit Typing.t *)
  (* module Mu = Mucore *)
  (* val check_and_bind_pattern : *)
  (* unit CoreTypeChecks.BT.t_gen -> *)
  (* 'a Mu.pattern -> unit CoreTypeChecks.BT.t_gen Mu.pattern Typing.t *)
  (* val check_and_bind_pattern_ : *)
  (* unit CoreTypeChecks.BT.t_gen -> *)
  (* Locations.t -> *)
  (* 'a Mu.pattern_ -> *)
  (* unit CoreTypeChecks.BT.t_gen Mu.pattern_ Typing.t *)
  (* val infer_object_value : *)
  (* Locations.t -> *)
  (* 'TY Mu.object_value -> BT.t Mu.object_value Typing.t *)
  (* val check_object_value : *)
  (* Locations.t -> *)
  (* BT.t -> 'TY Mu.object_value -> BT.t Mu.object_value Typing.t *)
  (* val infer_value : *)
  (* Locations.t -> 'TY Mu.value -> BT.t Mu.value Typing.t *)
  (* val check_value : *)
  (* Locations.t -> BT.t -> 'TY Mu.value -> BT.t Mu.value Typing.t *)
  (* val is_integer_annot : *)
  (* Cerb_frontend.Annot.annot -> Cerb_frontend.IntegerType.integerType option *)
  (* keep *)
  val integer_annot
    :  Cerb_frontend.Annot.annot list ->
    Cerb_frontend.IntegerType.integerType option

  (* val remove_integer_annot : Cerb_frontend.Annot.annot list -> Cerb_frontend.Annot.annot list *)
  (* val remove_integer_annot_expr : 'a Mu.expr -> 'a Mu.expr *)
  (* val remove_integer_annot_pexpr : 'a Mu.pexpr -> 'a Mu.pexpr *)
  (* val infer_pexpr : 'TY Mu.pexpr -> BT.t Mu.pexpr Typing.t *)
  (* val check_pexpr : BT.t -> 'TY Mu.pexpr -> BT.t Mu.pexpr Typing.t *)
  (* val check_infer_apply_fun : *)
  (* BT.t option -> *)
  (* Mu.mu_function -> *)
  (* 'TY Mu.pexpr list -> *)
  (* 'TY Mu.pexpr -> (BaseTypes.t * BT.t Mu.pexpr list) Typing.t *)
  (* val check_cn_statement : *)
  (* Locations.t -> Cnprog.statement -> Cnprog.statement Typing.t *)
  (* val check_cnprog : Cnprog.t -> Cnprog.t Typing.t *)
  (* val signed_int_ty : unit Memory.BT.t_gen *)
  (* keep *)
  val infer_expr : label_context -> 'TY Mucore.expr -> BaseTypes.t Mucore.expr Typing.t

  val check_expr
    :  label_context ->
    BaseTypes.t ->
    'TY Mucore.expr ->
    BaseTypes.t Mucore.expr Typing.t
end

(* module WLabel : *)
(* sig *)
(* val typ : 'a WArgs.Mu.arguments -> False.t WArgs.AT.t *)
(* val consistent : *)
(* Locations.t -> 'a Mucore.expr Mucore.arguments -> unit Typing.t *)
(* val welltyped : *)
(* Locations.t -> *)
(* 'a Mucore.expr Mucore.arguments -> *)
(* 'a Mucore.expr Mucore.arguments Typing.t *)
(* end *)
module WProc : sig
  (* module AT = ArgumentTypes *)
  (* module LAT = LogicalArgumentTypes *)
  (* module Mu = Mucore *)
  val label_context
    :  ReturnTypes.t ->
    (Sym.Map.key, 'a Mucore.label_def) Pmap.map ->
    (False.t ArgumentTypes.t * Cerb_frontend.Annot.label_annot * Locations.t) Sym.Map.t
  (* keep *)

  val typ : ('a * 'b * 'c) Mucore.arguments -> 'c ArgumentTypes.t

  (* keep *)
  val consistent : Locations.t -> 'TY1 Mucore.args_and_body -> unit Typing.t

  (* keep *)
  val welltyped
    :  Locations.t ->
    'TY1 Mucore.args_and_body ->
    BaseTypes.t Mucore.args_and_body Typing.t
end

module WRPD : sig
  (* module Def = Definition *)
  (* module LC = LogicalConstraints *)
  (* keep *)
  val consistent : Definition.Predicate.t -> unit Typing.m

  val welltyped : Definition.Predicate.t -> Definition.Predicate.t Typing.t
end

module WLFD : sig
  (* keep *)
  val welltyped : Definition.Function.t -> Definition.Function.t Typing.t
end

module WLemma : (* keep *)
  sig
  val consistent
    :  Locations.t ->
    'a ->
    LogicalReturnTypes.t ArgumentTypes.t ->
    unit Typing.t

  val welltyped
    :  Locations.t ->
    'a ->
    LogicalReturnTypes.t ArgumentTypes.t ->
    LogicalReturnTypes.t ArgumentTypes.t Typing.t
end

module WDT : sig
  (* keep *)
  val welltyped : 'a * Mucore.datatype -> ('a * Mucore.datatype) Typing.t

  module G : sig
    type t = Graph__Persistent.Digraph.Concrete(Sym).t

    module V : sig
      type t = Sym.t

      val compare : t -> t -> int

      val hash : t -> int

      val equal : t -> t -> bool

      type label = Sym.t

      val create : label -> t

      val label : t -> label
    end

    type vertex = V.t

    module E : sig
      type t = Sym.t * Sym.t

      val compare : t -> t -> int

      type nonrec vertex = vertex

      val src : t -> vertex

      val dst : t -> vertex

      type label = unit

      val create : vertex -> label -> vertex -> t

      val label : t -> label
    end

    type edge = E.t

    val is_directed : bool

    val is_empty : t -> bool

    val nb_vertex : t -> int

    val nb_edges : t -> int

    val out_degree : t -> vertex -> int

    val in_degree : t -> vertex -> int

    val mem_vertex : t -> vertex -> bool

    val mem_edge : t -> vertex -> vertex -> bool

    val mem_edge_e : t -> edge -> bool

    val find_edge : t -> vertex -> vertex -> edge

    val find_all_edges : t -> vertex -> vertex -> edge list

    val succ : t -> vertex -> vertex list

    val pred : t -> vertex -> vertex list

    val succ_e : t -> vertex -> edge list

    val pred_e : t -> vertex -> edge list

    val iter_vertex : (vertex -> unit) -> t -> unit

    val fold_vertex : (vertex -> 'a -> 'a) -> t -> 'a -> 'a

    val iter_edges : (vertex -> vertex -> unit) -> t -> unit

    val fold_edges : (vertex -> vertex -> 'a -> 'a) -> t -> 'a -> 'a

    val iter_edges_e : (edge -> unit) -> t -> unit

    val fold_edges_e : (edge -> 'a -> 'a) -> t -> 'a -> 'a

    val map_vertex : (vertex -> vertex) -> t -> t

    val iter_succ : (vertex -> unit) -> t -> vertex -> unit

    val iter_pred : (vertex -> unit) -> t -> vertex -> unit

    val fold_succ : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a

    val fold_pred : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a

    val iter_succ_e : (edge -> unit) -> t -> vertex -> unit

    val fold_succ_e : (edge -> 'a -> 'a) -> t -> vertex -> 'a -> 'a

    val iter_pred_e : (edge -> unit) -> t -> vertex -> unit

    val fold_pred_e : (edge -> 'a -> 'a) -> t -> vertex -> 'a -> 'a

    val empty : t

    val add_vertex : t -> vertex -> t

    val remove_vertex : t -> vertex -> t

    val add_edge : t -> vertex -> vertex -> t

    val add_edge_e : t -> edge -> t

    val remove_edge : t -> vertex -> vertex -> t

    val remove_edge_e : t -> edge -> t
  end

  (* val bts_in_dt_constructor_argument : 'a * 'b BT.t_gen -> 'b BT.t_gen list *)
  (* val bts_in_dt_case : 'a * ('b * 'c BT.t_gen) list -> 'c BT.t_gen list *)
  (* val bts_in_dt_definition : Mucore.datatype -> unit BT.t_gen list *)
  (* val dts_in_dt_definition : Mucore.datatype -> Sym.t list *)
  (* keep *)
  val check_recursion_ok : (Sym.S.sym * Mucore.datatype) list -> G.V.t list list Typing.t
end
(*
   BaseTyping.infer_expr
   BaseTyping.integer_annot
   WCT.is_ct
   WDT.check_recursion_ok
   WDT.welltyped
   WFT.consistent
   WFT.welltyped
   WIT.check
   WIT.infer
   WLC.welltyped
   WLFD.welltyped
   WLemma.consistent
   WLemma.welltyped
   WProc.label_context
   WProc.typ
   WProc.welltyped
   WRPD.consistent
   WRPD.welltyped
   WRS.oarg_bt_of_pred
   compare_by_fst_id.
   ensure_bits_type.
   ensure_same_argument_number.
   infer.
   quantifier_bt.
*)
