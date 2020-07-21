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

open Pp_ail

let string_of_integerType ity =
  Pp_utils.to_plain_string (Pp_ail.pp_integerType ity)

let string_of_integerType_raw ity =
  Pp_utils.to_plain_string (Pp_ail_raw.pp_integerType_raw ity)

let string_of_ctype qs ty =
  Pp_utils.to_plain_string (pp_ctype qs ty)

let string_of_expression e =
  Pp_utils.to_plain_string (pp_expression e)

let string_of_qualifiers_human qs =
  Pp_utils.to_plain_string (pp_qualifiers_human qs)


(* DEBUG*)
let string_of_genType gty =
  Pp_utils.to_plain_string (pp_genType gty)

let string_of_genTypeCategory gtc =
  Pp_utils.to_plain_string (pp_genTypeCategory gtc)

let string_of_ctype_raw ty =
  Pp_utils.to_plain_string (Pp_ail_raw.pp_ctype_raw ty)

let string_of_ctype_human qs ty =
  Pp_utils.to_plain_string (Pp_ail.pp_ctype_human qs ty)
