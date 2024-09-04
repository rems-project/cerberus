module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module BT = BaseTypes
module AT = ArgumentTypes

val ownership_ctypes : C.ctype list ref

module MembersKey : sig
  type t = (Id.t * Sym.t CF.Cn.cn_base_type) list

  val compare : t -> t -> int
end

module RecordMap : module type of Map.Make (MembersKey)

val records : Sym.t RecordMap.t ref

val bt_to_cn_base_type : BT.t -> Sym.t CF.Cn.cn_base_type

val generate_sym_with_suffix
  :  ?suffix:string ->
  ?uppercase:bool ->
  ?lowercase:bool ->
  Sym.t ->
  Sym.t

type ail_bindings_and_statements =
  A.bindings * CF.GenTypes.genTypeCategory A.statement_ list

type ail_executable_spec =
  { pre : ail_bindings_and_statements;
    post : ail_bindings_and_statements;
    in_stmt : (Locations.t * ail_bindings_and_statements) list
  }

val generate_ownership_function
  :  with_ownership_checking:bool ->
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

val generate_struct_conversion_function
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

val cn_to_ail_struct : A.sigma_tag_definition -> A.sigma_tag_definition list

val cn_to_ail_datatype
  :  ?first:bool ->
  A.sigma_cn_datatype ->
  Locations.t * A.sigma_tag_definition list

val cn_to_ail_pred_records
  :  (MembersKey.t * A.ail_identifier) list ->
  A.sigma_tag_definition list

val cn_to_ail_function_internal
  :  Sym.t * LogicalFunctions.definition ->
  A.sigma_cn_datatype list ->
  A.sigma_cn_function list ->
  ((Locations.t * A.sigma_declaration)
  * CF.GenTypes.genTypeCategory A.sigma_function_definition option)
  * A.sigma_tag_definition option

val cn_to_ail_predicates_internal
  :  (Sym.t * ResourcePredicates.definition) list ->
  A.sigma_cn_datatype list ->
  (Sym.t * C.ctype) list ->
  Mucore.T.resource_predicates ->
  A.sigma_cn_predicate list ->
  ((Locations.t * A.sigma_declaration)
  * CF.GenTypes.genTypeCategory A.sigma_function_definition)
    list
  * A.sigma_tag_definition option list

val cn_to_ail_pre_post_internal
  :  with_ownership_checking:bool ->
  A.sigma_cn_datatype list ->
  Mucore.T.resource_predicates ->
  (Sym.t * C.ctype) list ->
  C.ctype ->
  Core_to_mucore.fn_spec_instrumentation option ->
  ail_executable_spec
