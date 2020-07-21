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

let string_pretty_of_integer_value ival =
  Pp_utils.to_plain_string (Impl_mem.pp_pretty_integer_value { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string begin
    (* TODO: factorise *)
    let saved = !Colour.do_colour in
    Colour.do_colour := false;
    let ret = Impl_mem.pp_mem_value mval in
    Colour.do_colour := saved;
    ret
  end

let string_pretty_of_mem_value format mval =
  Pp_utils.to_plain_string (Impl_mem.pp_pretty_mem_value format mval)


let string_pretty_of_mem_value_decimal mval =
  string_pretty_of_mem_value { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } mval



let string_of_pointer_value ptr_val =
  Pp_utils.to_plain_string (Impl_mem.pp_pointer_value ptr_val)


let string_of_iv_memory_constraint cs =
  let format = { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } in
  Pp_utils.to_plain_string (Pp_mem.pp_mem_constraint (Impl_mem.pp_pretty_integer_value format) cs)
