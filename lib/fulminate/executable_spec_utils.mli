module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module Cn = CF.Cn
open PPrint

val empty_qualifiers : C.qualifiers

val const_qualifiers : C.qualifiers

val empty_attributes : CF.Annot.attributes

val mk_ctype : ?annots:Cerb_frontend.Annot.annot list -> C.ctype_ -> C.ctype

val rm_ctype : C.ctype -> C.ctype_

val get_typedef_string_aux : C.ctype -> string option

val get_typedef_string : C.ctype -> string option

val mk_expr
  :  ?loc:Cerb_location.t ->
  CF.GenTypes.genTypeCategory A.expression_ ->
  CF.GenTypes.genTypeCategory A.expression

val get_expr_strs : CF.GenTypes.genTypeCategory A.expression -> string list

val mk_cn_expr : ('a, 'b) Cn.cn_expr_ -> ('a, 'b) Cn.cn_expr

val rm_cn_expr : ('a, 'b) Cn.cn_expr -> ('a, 'b) Cn.cn_expr_

val mk_stmt : 'a A.statement_ -> 'a A.statement

val rm_expr : 'a A.expression -> 'a A.expression_

val rm_stmt : 'a A.statement -> 'a A.statement_

val empty_ail_str : string

val empty_ail_expr : 'a A.expression_

val empty_ail_stmt : CF.GenTypes.genTypeCategory A.statement_

val is_empty_ail_stmt : 'a A.statement_ -> bool

val list_split_three : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

type cn_dependencies = A.ail_identifier list

type cn_dependency_graph =
  { cn_functions_with_dependencies : (A.ail_identifier, C.ctype) Cn.cn_function list }

val compute_cn_dependencies : 'a -> 'a

val ifndef_wrap : string -> string -> string

val generate_include_header : string * bool -> string

val get_ctype_without_ptr : C.ctype -> C.ctype

val is_pointer : C.ctype -> bool

val _transform_ctype_for_ptr : C.ctype -> C.ctype

val str_of_ctype : C.ctype -> string

val execCtypeEqual : C.ctype -> C.ctype -> bool

val str_of_it_ : 'a Terms.term -> string

val create_binding
  :  'a ->
  'b ->
  'a * ((Cerb_location.t * A.storageDuration * bool) * 'c option * C.qualifiers * 'b)

val find_ctype_from_bindings : (Sym.t * ('a * 'b * 'c * 'd)) list -> Sym.t -> 'd

val create_decl_object : Cerb_frontend.Ctype.ctype -> A.declaration

val create_declaration : 'a -> 'b -> 'a * (Cerb_location.t * CF.Annot.attributes * 'b)

val concat_map_newline : document list -> document
