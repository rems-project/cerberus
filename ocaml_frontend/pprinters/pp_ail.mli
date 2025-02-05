open AilSyntax
open Ctype

val executable_spec: bool ref

val with_executable_spec: ('a -> 'b) -> 'a -> 'b

val pp_type_keyword: string -> PPrint.document
val pp_keyword: string -> PPrint.document
val pp_const: string -> PPrint.document


val pp_id: ?is_human:bool -> ail_identifier -> PPrint.document
val pp_id_obj: ail_identifier -> PPrint.document
val pp_id_func: ail_identifier -> PPrint.document

val pp_storageDuration: storageDuration -> PPrint.document

val pp_qualifiers: qualifiers -> PPrint.document

val string_of_integerBaseType: integerBaseType -> string


val pp_integerType: integerType -> PPrint.document
val pp_floatingType: floatingType -> PPrint.document

val pp_basicType: basicType -> PPrint.document

val pp_integer: Nat_big_num.num -> PPrint.document

val pp_tag_definition: union_tag * (Cerb_location.t * Annot.attributes * tag_definition) -> PPrint.document
(*
val pp_integerBaseType_raw: integerBaseType -> PPrint.document
let pp_integerType_raw
let pp_basicType_raw
let pp_qualifiers_raw
let rec pp_ctype_raw
*)

val pp_ctype: ?is_human:bool -> qualifiers -> ctype -> PPrint.document
val pp_ctype_declaration: PPrint.document -> qualifiers -> ctype -> PPrint.document

(*
let rec pp_ctype_declaration id
*)
val pp_qualifiers_human: qualifiers -> PPrint.document
(*
let rec pp_ctype_human qs ty
*)
val pp_ctype_human: qualifiers -> ctype -> PPrint.document

val pp_ail_builtin: ail_builtin -> PPrint.document



val pp_arithmeticOperator: arithmeticOperator -> PPrint.document
val pp_binaryOperator: binaryOperator -> PPrint.document
val pp_unaryOperator: unaryOperator -> PPrint.document
val pp_integerSuffix: integerSuffix -> PPrint.document
val pp_integerConstant: integerConstant -> PPrint.document
val pp_floatingConstant: floatingConstant -> PPrint.document
val pp_characterPrefix: characterPrefix -> PPrint.document
val pp_characterConstant: characterConstant -> PPrint.document
val pp_encodingPrefix: encodingPrefix -> PPrint.document
val pp_stringLiteral: stringLiteral -> PPrint.document
val pp_constant: constant -> PPrint.document
val pp_expression: 'a expression -> PPrint.document
val pp_generic_association: 'a generic_association -> PPrint.document
val pp_statement: ?bs:bindings -> 'a statement -> PPrint.document






(*
let pp_static_assertion (e, lit) =
  pp_keyword "_Static_assert" ^^ P.parens (pp_expression e ^^ P.comma ^^^ pp_stringLiteral lit)
*)

val pp_function_prototype: AilSyntax.ail_identifier -> AilSyntax.declaration -> PPrint.document

val pp_program: show_include:bool -> 'a ail_program -> PPrint.document
val pp_program_with_annot: GenTypes.genTypeCategory ail_program -> PPrint.document

(* DEBUG *)
val pp_genType: GenTypes.genType -> PPrint.document
val pp_genTypeCategory: GenTypes.genTypeCategory -> PPrint.document


val pp_attribute: Annot.attribute -> PPrint.document
val pp_attributes: Annot.attributes -> PPrint.document
