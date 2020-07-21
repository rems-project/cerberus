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

open AilSyntax
open Ctype

val pp_type_keyword: string -> PPrint.document
val pp_keyword: string -> PPrint.document
val pp_const: string -> PPrint.document


val pp_id: ail_identifier -> PPrint.document
val pp_id_obj: ail_identifier -> PPrint.document
val pp_id_func: ail_identifier -> PPrint.document

val pp_storageDuration: storageDuration -> PPrint.document

val pp_qualifiers: qualifiers -> PPrint.document

val string_of_integerBaseType: integerBaseType -> string


val pp_integerType: integerType -> PPrint.document
val pp_floatingType: floatingType -> PPrint.document

val pp_basicType: basicType -> PPrint.document

val pp_integer: Nat_big_num.num -> PPrint.document


(*
val pp_integerBaseType_raw: integerBaseType -> PPrint.document
let pp_integerType_raw
let pp_basicType_raw
let pp_qualifiers_raw
let rec pp_ctype_raw
*)

val pp_ctype: qualifiers -> ctype -> PPrint.document

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
val pp_statement: 'a statement -> PPrint.document






(*
let pp_static_assertion (e, lit) =
  pp_keyword "_Static_assert" ^^ P.parens (pp_expression e ^^ P.comma ^^^ pp_stringLiteral lit)
*)

val pp_program: bool -> bool -> 'a ail_program -> PPrint.document
val pp_program_with_annot: GenTypes.genTypeCategory ail_program -> PPrint.document

(* DEBUG *)
val pp_genType: GenTypes.genType -> PPrint.document
val pp_genTypeCategory: GenTypes.genTypeCategory -> PPrint.document


val pp_attribute: Annot.attribute -> PPrint.document
val pp_attributes: Annot.attributes -> PPrint.document
