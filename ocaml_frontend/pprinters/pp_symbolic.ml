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

open Symbolic
open Pp_prelude


let pp_symbolic_name = function
  | SYMBfsym sym -> !^ (Pp_symbol.to_string_pretty sym)
  | SYMBimpl iCst -> !^ (Implementation_.string_of_implementation_constant iCst)

let rec pp_symbolic ppA ppB = function
  | SYMBtrue ->
      !^ "true"
  | SYMBfalse ->
      !^ "false"
  | SYMBconst cst ->
      ppA cst
  | SYMBptrval ptr_val ->
      ppB ptr_val
  | SYMBmember_shift (symb, tag_sym, memb_ident) ->
      !^ "member_shift" ^^ P.parens (pp_symbolic ppA ppB symb ^^ P.comma ^^^ !^ (Pp_symbol.to_string_pretty tag_sym) ^^ P.comma ^^^ Pp_cabs.pp_cabs_identifier memb_ident)
  | SYMBctype ty ->
      Pp_core_ctype.pp_ctype ty
  | SYMBsym (_, sym) ->
      !^ (Pp_symbol.to_string_pretty sym)
  | SYMBnot symb ->
      !^ "not" ^^ P.parens (pp_symbolic ppA ppB symb)
  | SYMBop (op, symb1, symb2) ->
      let str_opt = match op with
        | Add0 -> "+"
        | Sub0 -> "-"
        | Mul0 -> "*"
        | Div0 -> "/"
        | Rem_t -> "rem_t"
        | Rem_f -> "rem_f"
        | Exp -> "exp"
        | Eq0  -> "=="
        | Neq -> "/="
        | Lt0  -> "<"
        | Ge0  -> ">="
        | And0 -> "and"
        | Or0  -> "or" in
      P.parens (!^ str_opt ^^^ pp_symbolic ppA ppB symb1 ^^^ pp_symbolic ppA ppB symb2)
  | SYMBite (symb1, symb2, symb3) ->
      P.parens (!^ "ite" ^^^ pp_symbolic ppA ppB symb1 ^^^ pp_symbolic ppA ppB symb2 ^^^ pp_symbolic ppA ppB symb3)
  | SYMBcall (symb_nm, symbs) ->
      P.parens (!^ "call" ^^^ pp_symbolic_name symb_nm ^^^ P.separate_map (P.space) (pp_symbolic ppA ppB) symbs)

