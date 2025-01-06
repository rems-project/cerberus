module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module BT = BaseTypes

val ownership_ctypes : C.ctype list ref

module MembersKey : sig
  type t = (Id.t * BT.t) list

  val compare : t -> t -> int
end

module RecordMap : module type of Map.Make (MembersKey)

val records : Sym.t RecordMap.t ref

val augment_record_map : ?cn_sym:Sym.sym -> BT.t -> unit

val bt_to_cn_base_type : BT.t -> Sym.t CF.Cn.cn_base_type

val bt_to_ail_ctype : ?pred_sym:Sym.t option -> BT.t -> C.ctype

val get_conversion_to_fn_str : BT.t -> string option

val get_conversion_from_fn_str : BT.t -> string option

val wrap_with_convert_to
  :  ?sct:Sctypes.t ->
  CF.GenTypes.genTypeCategory A.expression_ ->
  BT.t ->
  CF.GenTypes.genTypeCategory A.expression_

val wrap_with_convert_from
  :  ?sct:Sctypes.t ->
  CF.GenTypes.genTypeCategory A.expression_ ->
  BT.t ->
  CF.GenTypes.genTypeCategory A.expression_

val wrap_with_convert_from_cn_bool
  :  CF.GenTypes.genTypeCategory A.expression ->
  CF.GenTypes.genTypeCategory A.expression

type ail_bindings_and_statements =
  A.bindings * CF.GenTypes.genTypeCategory A.statement_ list

type ail_executable_spec =
  { pre : ail_bindings_and_statements;
    post : ail_bindings_and_statements;
    in_stmt : (Locations.t * ail_bindings_and_statements) list;
    loops :
      ((Locations.t * ail_bindings_and_statements)
      * (Locations.t * ail_bindings_and_statements))
        list
  }

val generate_get_or_put_ownership_function
  :  without_ownership_checking:bool ->
  C.ctype ->
  A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition

val generate_assume_ownership_function
  :  without_ownership_checking:bool ->
  C.ctype ->
  A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition

val generate_datatype_equality_function
  :  A.sigma_cn_datatype ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_datatype_map_get
  :  Compile.cn_datatype ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_datatype_default_function
  :  Compile.cn_datatype ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_struct_conversion_to_function
  :  A.sigma_tag_definition ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_struct_conversion_from_function
  :  A.sigma_tag_definition ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_struct_equality_function
  :  ?is_record:bool ->
  'a ->
  A.sigma_tag_definition ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_struct_map_get
  :  A.sigma_tag_definition ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_struct_default_function
  :  ?is_record:bool ->
  'a ->
  A.sigma_tag_definition ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_record_opt : Sym.t -> BT.t -> A.sigma_tag_definition option

val generate_record_equality_function
  :  'a ->
  Sym.t * BT.member_types ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_record_default_function
  :  'a ->
  Sym.t * BT.member_types ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val generate_record_map_get
  :  Sym.t * 'a ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val cn_to_ail_expr
  :  A.sigma_cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  Sym.t option ->
  IndexTerms.t ->
  A.bindings
  * CF.GenTypes.genTypeCategory A.statement_ list
  * CF.GenTypes.genTypeCategory A.expression

val cn_to_ail_logical_constraint
  :  A.sigma_cn_datatype list ->
  (C.union_tag * C.ctype) list ->
  LogicalConstraints.t ->
  A.bindings
  * CF.GenTypes.genTypeCategory A.statement_ list
  * CF.GenTypes.genTypeCategory A.expression

val cn_to_ail_struct : A.sigma_tag_definition -> A.sigma_tag_definition list

val cn_to_ail_datatype
  :  ?first:bool ->
  A.sigma_cn_datatype ->
  Locations.t * A.sigma_tag_definition list

val cn_to_ail_records
  :  (MembersKey.t * A.ail_identifier) list ->
  A.sigma_tag_definition list

val cn_to_ail_function_internal
  :  Sym.t * Definition.Function.t ->
  A.sigma_cn_datatype list ->
  A.sigma_cn_function list ->
  ((Locations.t * A.sigma_declaration)
  * CF.GenTypes.genTypeCategory A.sigma_function_definition option)
  * A.sigma_tag_definition option

val cn_to_ail_predicates_internal
  :  (Sym.t * Definition.Predicate.t) list ->
  A.sigma_cn_datatype list ->
  (Sym.t * C.ctype) list ->
  (Sym.t * Definition.Predicate.t) list ->
  A.sigma_cn_predicate list ->
  ((Locations.t * A.sigma_declaration)
  * CF.GenTypes.genTypeCategory A.sigma_function_definition)
    list
  * A.sigma_tag_definition option list

val cn_to_ail_pre_post_internal
  :  without_ownership_checking:bool ->
  A.sigma_cn_datatype list ->
  (Sym.t * Definition.Predicate.t) list ->
  (Sym.t * C.ctype) list ->
  C.ctype ->
  Executable_spec_extract.fn_args_and_body option ->
  ail_executable_spec

val cn_to_ail_assume_predicates_internal
  :  (Sym.t * Definition.Predicate.t) list ->
  A.sigma_cn_datatype list ->
  (Sym.t * C.ctype) list ->
  (Sym.t * Definition.Predicate.t) list ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val cn_to_ail_assume_pre_internal
  :  A.sigma_cn_datatype list ->
  C.union_tag ->
  (C.union_tag * (BT.t * C.ctype)) list ->
  (C.union_tag * C.ctype) list ->
  (C.union_tag * Definition.Predicate.t) list ->
  'a LogicalArgumentTypes.t ->
  A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition
