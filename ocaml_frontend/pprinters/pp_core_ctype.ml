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

open Ctype


module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f



let pp_symbol ?(compact = false) a = 
  !^ (Pp_symbol.to_string_pretty ~compact:compact a)

let pp_integer_base_ctype ibty =
  !^ (match ibty with
    | Ichar          -> "ichar"
    | Short          -> "short"
    | Int_           -> "int"
    | Long           -> "long"
    | LongLong       -> "long_long"
    | IntN_t n       -> "int" ^ string_of_int n ^ "_t"
    | Int_leastN_t n -> "int_least" ^ string_of_int n ^ "_t"
    | Int_fastN_t n  -> "int_fast" ^ string_of_int n ^ "_t"
    | Intmax_t       -> "intmax_t"
    | Intptr_t       -> "intptr_t")


let pp_integer_ctype ?(compact = false) ity =
  match ity with
    | Char             -> !^ "char"
    | Bool             -> !^ "_Bool"
    | Signed ((IntN_t _ | Int_leastN_t _ | Int_fastN_t _ | Intmax_t | Intptr_t) as ibty) ->
        pp_integer_base_ctype ibty
    | Unsigned ((IntN_t _ | Int_leastN_t _ | Int_fastN_t _ | Intmax_t | Intptr_t) as ibty) ->
        !^ "u" ^^ pp_integer_base_ctype ibty
    | Signed ibty      -> !^ "signed"   ^^^ pp_integer_base_ctype ibty
    | Unsigned ibty    -> !^ "unsigned" ^^^ pp_integer_base_ctype ibty
    | Enum sym         -> !^ "enum" ^^^ pp_symbol ~compact:compact sym
    | Size_t           -> !^ "size_t"
    | Wchar_t          -> !^ "wchar_t"
    | Wint_t           -> !^ "wint_t"
    | Ptrdiff_t        -> !^ "ptrdiff_t"

let pp_floating_ctype fty =
  match fty with
    | RealFloating Float ->
        !^ "float"
    | RealFloating Double ->
        !^ "double"
    | RealFloating LongDouble ->
        !^ "long_double"


let pp_basic_ctype bty =
  match bty with
    | Integer ity -> pp_integer_ctype ity
    | Floating fty -> pp_floating_ctype fty

let rec pp_ctype ?(compact = false) (Ctype (_, ty)) =
  match ty with
(*   let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)

  | Void ->
      !^ "void"
  | Basic bty ->
      pp_basic_ctype bty
  | Array (elem_ty, n_opt) ->
      pp_ctype elem_ty ^^ P.brackets (P.optional Pp_ail.pp_integer n_opt)
  | Function (_, (ret_qs, ret_ty), args_tys, is_variadic) ->
        pp_ctype (*TODO: ret_qs*) ret_ty ^^^ P.parens (
          comma_list (fun (qs, ty, _) -> pp_ctype (*TODO: qs*) ty) args_tys ^^
          (if is_variadic then P.comma ^^^ P.dot ^^ P.dot ^^ P.dot else P.empty)
        )
  | Pointer (qs, ref_ty) ->
      pp_ctype (* TODO:qs*) ref_ty ^^ P.star
  | Atomic atom_ty ->
      !^ "_Atomic" ^^^ P.parens (pp_ctype atom_ty)
  | Struct sym ->
      !^ "struct" ^^^ pp_symbol ~compact:compact sym (*!^(Pp_symbol.to_string sym)*)
  | Union sym ->
      !^ "union" ^^^ pp_symbol ~compact:compact sym (*!^(Pp_symbol.to_string sym)*)


(*
and pp_member = function
  | Core_ctype.MEMBER ty ->
      fun z -> pp_ctype ty ^^^ Pp_ail.pp_id z ^^ P.semi
  | Core_ctype.BITFIELD (ty, w, _) ->
      fun z -> pp_ctype ty ^^^ Pp_ail.pp_id z ^^ P.colon ^^^ Pp_ail.pp_integer w ^^ P.semi
 *)
