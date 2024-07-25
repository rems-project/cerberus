(* Module Cn_internal_to_ail *)

(* TODO: AM: Needs a header explaining what it is *)

module CF = Cerb_frontend
module A = Executable_spec_utils.CF.AilSyntax
module C = Executable_spec_utils.CF.Ctype
module BT = BaseTypes
module T = Terms
module LRT = LogicalReturnTypes
module LAT = LogicalArgumentTypes
module AT = ArgumentTypes
module OE = Ownership_exec

val true_const : 'a A.expression_

val error_msg_info_sym : Cerb_frontend__Symbol.sym

val error_msg_struct_tag : Cerb_frontend__Symbol.sym

val error_msg_info_ctype : Executable_spec_utils.C.ctype

val ownership_ctypes : Cerb_frontend.Ctype.ctype list ref

(* converts a cn_base_type declared in the frontend to a cn basetype declared in baseTypes.ml *)
val cn_base_type_to_bt : Sym.t CF.Cn.cn_base_type -> BT.basetype

module MembersKey : sig
  type t = (Id.t * Mucore.symbol CF.Cn.cn_base_type) list

  val compare : t -> (Id.t * 'a) list -> int
end

val members_equal
  :  (Id.t * Sym.t CF.Cn.cn_base_type) list ->
  (Id.t * Sym.t CF.Cn.cn_base_type) list ->
  bool

module SymKey : sig
  type t = C.union_tag

  val compare : t -> t -> int
end

module RecordMap : Map.S with type key = MembersKey.t

val records : Cerb_frontend__Symbol.sym RecordMap.t ref

val generic_cn_dt_sym : Cerb_frontend__Symbol.sym

val create_id_from_sym : ?lowercase:bool -> Cerb_frontend.Symbol.sym -> Id.t

val create_sym_from_id : Id.t -> Cerb_frontend__Symbol.sym

val generate_sym_with_suffix
  :  ?suffix:string ->
  ?uppercase:bool ->
  ?lowercase:bool ->
  Cerb_frontend.Symbol.sym ->
  Cerb_frontend__Symbol.sym

val generate_error_msg_info_update_stats
  :  ?cn_source_loc_opt:Cerb_location.t option ->
  unit ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list

val cn_assert_sym : Cerb_frontend__Symbol.sym

val generate_cn_assert
  :  ?cn_source_loc_opt:Cerb_location.t option ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list

(* converts a cn basetype declared in baseTypes.ml to a cn_base_type declared in the frontend *)
val bt_to_cn_base_type : BT.basetype -> Sym.t CF.Cn.cn_base_type

(* converts cn_base_type bit vector to a string*)
val str_of_cn_bitvector_type : CF.Cn.sign -> int -> string

(* converts cn bitvector in baseTypes.ml to a string*)
val str_of_bt_bitvector_type : BT.sign -> int -> string

val generate_record_sym
  :  Cerb_frontend.Symbol.sym option ->
  RecordMap.key ->
  Cerb_frontend__Symbol.sym

(* converts cn_base_type to cerberus ctype *)
val cn_to_ail_base_type
  :  ?pred_sym:Cerb_frontend.Symbol.sym option ->
  Cerb_frontend.Symbol.sym CF.Cn.cn_base_type ->
  C.ctype

(* converts cn basetype declared in baseTypes.ml to cerberus ctype*)
val bt_to_ail_ctype : ?pred_sym:Cerb_frontend.Symbol.sym option -> BT.basetype -> C.ctype

(* converts cn unary operation to an intermediate representation *)
val cn_to_ail_unop_internal : BT.basetype -> Terms.unop -> A.unaryOperator * string option

(* converts cn binary operation to an intermediate representation *)
val cn_to_ail_binop_internal
  :  BT.basetype ->
  BT.basetype ->
  Terms.binop ->
  A.binaryOperator * string option

val get_underscored_typedef_string_from_bt
  :  ?is_record:bool ->
  BT.basetype ->
  string option

val get_conversion_fn_str : BT.basetype -> string option

val add_conversion_fn
  :  ?sct:Sctypes.ctype ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression_ ->
  BT.basetype ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression_

val get_equality_fn_call
  :  BT.basetype ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression ->
  'a ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression_

val rearrange_start_inequality
  :  Sym.S.sym ->
  'a Mucore.IT.term ->
  'a Mucore.IT.term ->
  'a Terms.term_

val generate_start_expr
  :  BT.basetype Mucore.IT.term ->
  Sym.S.sym ->
  BT.basetype Terms.term

(* gets the left side of an AND operation *)
val get_leftmost_of_and_expr : 'a Mucore.IT.term -> 'a Mucore.IT.term

(* gets the right side of an AND operation *)
val get_rest_of_expr_r_aux : BT.basetype Mucore.IT.term -> BT.basetype Mucore.IT.term

val get_rest_of_expr_r : BT.basetype Mucore.IT.term -> BT.basetype Terms.term

val convert_from_cn_bool_sym : Cerb_frontend__Symbol.sym

val wrap_with_convert_from_cn_bool
  :  Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory Executable_spec_utils.A.expression

val gen_bool_while_loop
  :  A.ail_identifier ->
  BT.basetype ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory Executable_spec_utils.A.expression_ ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression ->
  ?if_cond_opt:Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression option ->
  A.bindings
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression ->
  (Sym.S.sym
  * ((Cerb_location.t * Executable_spec_utils.A.storageDuration * bool)
    * 'a option
    * Executable_spec_utils.C.qualifiers
    * C.ctype))
    list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory Executable_spec_utils.A.expression

(* converts a constant cn internal represntation to AIL *)
val cn_to_ail_const_internal
  :  Terms.const ->
  Executable_spec_utils.CF.GenTypes.genTypeCategory Executable_spec_utils.A.expression_
  * bool

type ail_bindings_and_statements =
  A.bindings * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list

type ail_executable_spec =
  { pre : ail_bindings_and_statements;
    post : ail_bindings_and_statements;
    in_stmt : (Locations.t * ail_bindings_and_statements) list
  }

val empty_ail_executable_spec : ail_executable_spec

type 'a dest =
  | Assert : ail_bindings_and_statements dest
  | Return : ail_bindings_and_statements dest
  | AssignVar : C.union_tag -> ail_bindings_and_statements dest
  | PassBack
      : (A.bindings
        * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list
        * Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression)
          dest

(* bool flag for checking if expression is unit - needs special treatment *)
val dest_with_unit_check
  :  'a dest ->
  A.bindings
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression
  * bool ->
  'a

val dest
  :  'a dest ->
  A.bindings
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.expression ->
  'a

val prefix
  :  'a dest ->
  A.bindings * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list ->
  'a ->
  'a

val empty_for_dest : 'a dest -> 'a

val generate_ownership_function
  :  bool ->
  Executable_spec_utils.C.ctype ->
  (Cerb_frontend__Symbol.sym
  * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Cerb_frontend__Symbol.sym list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement))

val is_sym_obj_address : Cerb_frontend__Symbol.sym -> bool

(* converts a cn expression to an AIL representation *)
val cn_to_ail_expr_aux_internal
  :  (Executable_spec_utils.CF.Symbol.sym * Terms.const) option ->
  Cerb_frontend.Symbol.sym option ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.IT.t ->
  'a dest ->
  'a

val cn_to_ail_expr_internal
  :  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.IT.t ->
  'a dest ->
  'a

val cn_to_ail_expr_internal_with_pred_name
  :  Sym.sym option ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.IT.t ->
  'a dest ->
  'a

val create_member
  :  'a * 'b ->
  'b
  * (Executable_spec_utils.CF.Annot.attributes
    * 'c option
    * Executable_spec_utils.C.qualifiers
    * 'a)

(* generates definition for tags which in C is a struct or a union*)
(* However, CN at the moment only has structs, so this is only for a structs *)
val generate_tag_definition
  :  (Cerb_frontend.Symbol.identifier * Cerb_frontend.Symbol.sym CF.Cn.cn_base_type) list ->
  C.tag_definition

(* generates definition for struct *)
val generate_struct_definition
  :  ?lc:bool ->
  Cerb_frontend.Symbol.sym
  * (Cerb_frontend.Symbol.identifier * Cerb_frontend.Symbol.sym CF.Cn.cn_base_type) list ->
  Cerb_frontend.Symbol.sym
  * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition)

val cn_to_ail_pred_records
  :  ((Cerb_frontend.Symbol.identifier * Cerb_frontend.Symbol.sym CF.Cn.cn_base_type) list
     * Cerb_frontend.Symbol.sym)
       list ->
  (Cerb_frontend.Symbol.sym
  * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition))
    list

val cn_to_ail_datatype
  :  ?first:bool ->
  Compile.cn_datatype ->
  Cerb_location.t
  * (Cerb_frontend.Symbol.sym
    * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition))
      list

val generate_datatype_equality_function
  :  Compile.cn_datatype ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Cerb_frontend__Symbol.sym list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

val generate_datatype_default_function
  :  Compile.cn_datatype ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * 'a list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

(*** STRUCTS ***)
val generate_struct_equality_function
  :  ?is_record:bool ->
  'a ->
  A.ail_identifier
  * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition) ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Cerb_frontend__Symbol.sym list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

val generate_struct_default_function
  :  ?is_record:bool ->
  'a ->
  A.ail_identifier
  * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition) ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * 'b list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

val generate_struct_map_get
  :  ?is_record:bool ->
  'a ->
  A.ail_identifier
  * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition) ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Cerb_frontend__Symbol.sym list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

val generate_struct_conversion_function
  :  A.ail_identifier
     * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition) ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * A.ail_identifier list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

(*** RECORDS ***)
val generate_record_equality_function
  :  'a ->
  Cerb_frontend.Symbol.sym * BT.member_types ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Cerb_frontend__Symbol.sym list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

val generate_record_default_function
  :  'a ->
  Cerb_frontend.Symbol.sym * BT.member_types ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * 'b list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

val generate_record_map_get
  :  'a ->
  Cerb_frontend.Symbol.sym * BT.member_types ->
  ((Cerb_frontend__Symbol.sym
   * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * A.declaration))
  * (Cerb_frontend__Symbol.sym
    * (Cerb_location.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Cerb_frontend__Symbol.sym list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list

val cn_to_ail_struct
  :  A.ail_identifier
     * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition) ->
  (Cerb_frontend__Symbol.sym
  * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition))
    list

(* is_pre used for ownership checking, to see if ownership needs to be taken or put back *)
val cn_to_ail_resource_internal
  :  ?is_pre:bool ->
  ?is_toplevel:bool ->
  A.ail_identifier ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.T.resource_predicates ->
  Cerb_location.t ->
  ResourceTypes.resource_type ->
  (A.ail_identifier
  * ((Cerb_location.t * A.storageDuration * bool)
    * Cerb_frontend.Ctype.alignment option
    * Cerb_frontend.Ctype.qualifiers
    * Cerb_frontend.Ctype.ctype))
    list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list

(* converts logical constraints from CN into AIL code *)
val cn_to_ail_logical_constraint_internal
  :  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  'a dest ->
  Compile.LC.logical_constraint ->
  'a

(* converts cn basetype from baseTypes.ml to an record option *)
val generate_record_opt
  :  Cerb_frontend.Symbol.sym ->
  BT.basetype ->
  (Cerb_frontend.Symbol.sym
  * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition))
    option

(* converts function from cn to ail representation *)
val cn_to_ail_function_internal
  :  Cerb_frontend.Symbol.sym * LogicalFunctions.definition ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (A.ail_identifier, C.ctype) Executable_spec_utils.Cn.cn_function list ->
  ((Cerb_location.t
   * (Cerb_frontend.Symbol.sym
     * (Locations.t * Executable_spec_utils.CF.Annot.attributes * A.declaration)))
  * (Cerb_frontend.Symbol.sym
    * (Locations.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Sym.t list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement))
      option)
  * (Cerb_frontend.Symbol.sym
    * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition))
      option

(* converts from cn logical argument type (LAT) to ail representation *)
(* LAT type defintion can be found in logicalArgumentTypes.ml *)
val cn_to_ail_lat_internal
  :  ?is_toplevel:bool ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  Sym.sym option ->
  (C.union_tag * C.ctype) list ->
  Mucore.T.resource_predicates ->
  Mucore.IT.t LAT.t ->
  A.bindings * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list

(* convert CN predicate to ail representation *)
val cn_to_ail_predicate_internal
  :  Cerb_frontend.Symbol.sym * ResourcePredicates.definition ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.T.resource_predicates ->
  (A.ail_identifier, C.ctype) Executable_spec_utils.Cn.cn_predicate list ->
  ((Cerb_location.t
   * (Cerb_frontend.Symbol.sym
     * (ResourcePredicates.Loc.t
       * Executable_spec_utils.CF.Annot.attributes
       * A.declaration)))
  * (Cerb_frontend.Symbol.sym
    * (ResourcePredicates.Loc.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Sym.t list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
  * (Cerb_frontend.Symbol.sym
    * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition))
      option

(* converts multiple CN predicates to ail representation *)
val cn_to_ail_predicates_internal
  :  (Cerb_frontend.Symbol.sym * ResourcePredicates.definition) list ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.T.resource_predicates ->
  (A.ail_identifier, C.ctype) Executable_spec_utils.Cn.cn_predicate list ->
  ((Cerb_location.t
   * (Cerb_frontend.Symbol.sym
     * (ResourcePredicates.Loc.t
       * Executable_spec_utils.CF.Annot.attributes
       * A.declaration)))
  * (Cerb_frontend.Symbol.sym
    * (ResourcePredicates.Loc.t
      * int
      * Executable_spec_utils.CF.Annot.attributes
      * Sym.t list
      * Executable_spec_utils.CF.GenTypes.genTypeCategory
          Executable_spec_utils.A.statement)))
    list
  * (Cerb_frontend.Symbol.sym
    * (Cerb_location.t * Executable_spec_utils.CF.Annot.attributes * C.tag_definition))
      option
      list

val cn_to_ail_post_aux_internal
  :  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.T.resource_predicates ->
  LRT.t ->
  (A.ail_identifier
  * ((Cerb_location.t * A.storageDuration * bool)
    * Cerb_frontend.Ctype.alignment option
    * Cerb_frontend.Ctype.qualifiers
    * Cerb_frontend.Ctype.ctype))
    list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list

val cn_to_ail_post_internal
  :  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.T.resource_predicates ->
  Compile.RT.t ->
  (A.ail_identifier
  * ((Cerb_location.t * A.storageDuration * bool)
    * Cerb_frontend.Ctype.alignment option
    * Cerb_frontend.Ctype.qualifiers
    * Cerb_frontend.Ctype.ctype))
    list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory Executable_spec_utils.A.statement
      list

(* converts cn statement outlined in cnprog.ml to ail represenation *)
val cn_to_ail_cnstatement_internal
  :  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  'a dest ->
  Cnprog.cn_statement ->
  'a * bool

(* converts a cn prog type outlined in cnprog.ml to ail representation *)
val cn_to_ail_cnprog_internal_aux
  :  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Cnprog.cn_prog ->
  (A.bindings * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list)
  * bool

val cn_to_ail_cnprog_internal
  :  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Cnprog.cn_prog ->
  A.bindings * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list

val cn_to_ail_statements
  :  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  'a * Cnprog.cn_prog list ->
  'a
  * ((A.ail_identifier
     * ((Cerb_location.t * A.storageDuration * bool)
       * Cerb_frontend.Ctype.alignment option
       * Cerb_frontend.Ctype.qualifiers
       * Cerb_frontend.Ctype.ctype))
       list
    * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list)

val prepend_to_precondition
  :  ail_executable_spec ->
  (A.ail_identifier
  * ((Cerb_location.t * A.storageDuration * bool)
    * Cerb_frontend.Ctype.alignment option
    * Cerb_frontend.Ctype.qualifiers
    * Cerb_frontend.Ctype.ctype))
    list
  * Executable_spec_utils.CF.GenTypes.genTypeCategory A.statement_ list ->
  ail_executable_spec

(* Precondition and postcondition translation - LAT.I case means precondition translation finished *)
val cn_to_ail_lat_internal_2
  :  bool ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Mucore.T.resource_predicates ->
  Executable_spec_utils.C.ctype ->
  (ReturnTypes.t * Core_to_mucore.statements) LAT.t ->
  ail_executable_spec

(* converts cn pre & post conditions to ail representation *)
val cn_to_ail_pre_post_aux_internal
  :  bool ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  Mucore.T.resource_predicates ->
  (C.union_tag * C.ctype) list ->
  Executable_spec_utils.C.ctype ->
  (ReturnTypes.t * Core_to_mucore.statements) AT.t ->
  ail_executable_spec

val cn_to_ail_pre_post_internal
  :  bool ->
  Sym.S.sym Executable_spec_utils.Cn.cn_datatype list ->
  Mucore.T.resource_predicates ->
  (C.union_tag * C.ctype) list ->
  Executable_spec_utils.C.ctype ->
  (ReturnTypes.t * Core_to_mucore.statements) AT.t option ->
  ail_executable_spec
