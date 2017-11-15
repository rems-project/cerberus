open Cabs

(*
val pp_cabs_integer_suffix: cabs_integer_suffix -> PPrint.document
val pp_cabs_integer_constant: cabs_integer_constant -> PPrint.document


val pp_cabs_character_prefix: cabs_character_prefix -> PPrint.document
val pp_cabs_character_constant: cabs_character_constant -> PPrint.document
val pp_cabs_constant: cabs_constant -> PPrint.document
val pp_cabs_encoding_prefix: cabs_encoding_prefix -> PPrint.document
val pp_cabs_string_literal: cabs_string_literal -> PPrint.document

val pp_cabs_generic_association: cabs_generic_association -> PPrint.document
val pp_cabs_unary_operator: cabs_unary_operator -> PPrint.document
val pp_cabs_binary_operator: cabs_binary_operator -> PPrint.document
val pp_cabs_assignment_operator: cabs_assignment_operator -> PPrint.document
val pp_declaration: declaration -> PPrint.document
val pp_specifiers: specifiers -> PPrint.document
val pp_init_declarator: init_declarator -> PPrint.document
val pp_storage_class_specifier: storage_class_specifier -> PPrint.document
val pp_struct_declaration: struct_declaration -> PPrint.document
val pp_struct_declarator: struct_declarator -> PPrint.document
val pp_enumerator: enumerator -> PPrint.document
val pp_cabs_type_qualifier: cabs_type_qualifier -> PPrint.document
val pp_function_specifier: function_specifier -> PPrint.document
val pp_alignment_specifier: alignment_specifier -> PPrint.document
val pp_declarator: declarator -> PPrint.document
val pp_direct_declarator: direct_declarator -> PPrint.document
val pp_array_declarator: array_declarator -> PPrint.document
val pp_array_declarator_size: array_declarator_size -> PPrint.document
val pp_pointer_declarator: pointer_declarator -> PPrint.document
val pp_cabs_type_specifier: cabs_type_specifier -> PPrint.document
*)

val pp_cabs_identifier: cabs_identifier -> PPrint.document
val pp_translate_unit: bool -> bool -> translation_unit -> PPrint.document
