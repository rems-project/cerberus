(************************************************************************************)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  Cerberus                                                                        *)
(*                                                                                  *)
(*  Copyright (c) 2011-2020                                                         *)
(*    Kayvan Memarian                                                               *)
(*    Victor Gomes                                                                  *)
(*    Justus Matthiesen                                                             *)
(*    Peter Sewell                                                                  *)
(*    Kyndylan Nienhuis                                                             *)
(*    Stella Lau                                                                    *)
(*    Jean Pichon-Pharabod                                                          *)
(*    Christopher Pulte                                                             *)
(*    Rodolphe Lepigre                                                              *)
(*    James Lingard                                                                 *)
(*                                                                                  *)
(*  All rights reserved.                                                            *)
(*                                                                                  *)
(*  Redistribution and use in source and binary forms, with or without              *)
(*  modification, are permitted provided that the following conditions are met:     *)
(*                                                                                  *)
(*  1. Redistributions of source code must retain the above copyright notice, this  *)
(*     list of conditions and the following disclaimer.                             *)
(*                                                                                  *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,    *)
(*     this list of conditions and the following disclaimer in the documentation    *)
(*     and/or other materials provided with the distribution.                       *)
(*                                                                                  *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            *)
(************************************************************************************)

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

val pp_translation_unit: bool -> bool -> translation_unit -> PPrint.document
