module CF = Cerb_frontend
module CB = Cerb_backend
module BT = BaseTypes
module A = Cn_to_ail.A
module IT = IndexTerms
module LRT = LogicalReturnTypes
module LAT = LogicalArgumentTypes
module AT = ArgumentTypes

type executable_spec =
  { pre_post : (A.ail_identifier * (string list * string list)) list;
    in_stmt : (Cerb_location.t * string list) list;
    returns :
      (Cerb_location.t * CF.GenTypes.genTypeCategory A.expression option * string list)
        list
  }

val generate_ail_stat_strs
  :  ?with_newline:bool ->
  Cn_to_ail.A.bindings * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list ->
  string list

val extract_global_variables
  :  ('a * 'b Mucore.globs) list ->
  ('a * Cn_to_ail.C.ctype) list

val generate_c_pres_and_posts_internal
  :  bool ->
  Executable_spec_extract.instrumentation ->
  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  unit Mucore.file ->
  (Sym.t * (string list * string list)) list
  * (Cerb_location.t * string list) list
  * (Cerb_location.t
    * Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.expression option
    * string list)
      list

val generate_c_assume_pres_internal
  :  Executable_spec_extract.instrumentation list ->
  Cerb_frontend.GenTypes.genTypeCategory A.sigma ->
  unit Mucore.file ->
  (Cn_to_ail.A.sigma_declaration
  * Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma_function_definition)
    list

val generate_c_specs_internal
  :  bool ->
  Executable_spec_extract.instrumentation list ->
  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  unit Mucore.file ->
  executable_spec

val concat_map_newline : PPrint.document list -> PPrint.document

val generate_doc_from_ail_struct
  :  Sym.t
     * (Cerb_location.t * Cerb_frontend.Annot.attributes * Cn_to_ail.C.tag_definition) ->
  PPrint.document

val generate_struct_decl_str : Sym.t * ('a * 'b * Cn_to_ail.C.tag_definition) -> string

val generate_c_records
  :  (Sym.t
     * (Cerb_location.t * Cerb_frontend.Annot.attributes * Cn_to_ail.C.tag_definition))
       list ->
  string * string

val generate_record_strs
  :  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  (Sym.t
  * (Cerb_location.t * Cerb_frontend.Annot.attributes * Cn_to_ail.C.tag_definition))
    list ->
  string * string

val generate_str_from_ail_struct
  :  Sym.t
     * (Cerb_location.t * Cerb_frontend.Annot.attributes * Cn_to_ail.C.tag_definition) ->
  string

val generate_str_from_ail_structs
  :  (Sym.t
     * (Cerb_location.t * Cerb_frontend.Annot.attributes * Cn_to_ail.C.tag_definition))
       list ->
  string

val generate_c_datatypes
  :  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  (Cerb_location.t * string) list * string * string list

val print_c_structs
  :  (Sym.t
     * (Cerb_location.t * Cerb_frontend.Annot.attributes * Cn_to_ail.C.tag_definition))
       list ->
  string * string

val generate_cn_versions_of_structs
  :  Cn_to_ail.A.sigma_tag_definition list ->
  string * string

val generate_struct_injs
  :  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  (Cerb_location.t * string list) list

val bt_is_record_or_tuple : 'a BT.t_gen -> bool

val fns_and_preds_with_record_rt
  :  ('a * Definition.Function.t) list * ('b * Definition.Predicate.t) list ->
  'a list * 'b list

val generate_c_functions_internal
  :  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  (Sym.t * Definition.Function.t) list ->
  string * string * (Cerb_location.t * string list) list * (string * string)

val remove_duplicates : ('a -> 'a -> bool) -> 'a list -> 'a list

val generate_c_predicates_internal
  :  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  (Sym.t * Definition.Predicate.t) list ->
  string * (Cerb_location.t * string list) list * (string * string)

val generate_ownership_functions
  :  bool ->
  Cn_to_ail.C.ctype list ref ->
  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  string * string

val generate_conversion_and_equality_functions
  :  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  string * string

val has_main : Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma -> bool

val generate_ownership_global_assignments
  :  Cerb_frontend.GenTypes.genTypeCategory Cn_to_ail.A.sigma ->
  unit Mucore.file ->
  (Sym.t * (string list * string list)) list
