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

open Nat_big_num

let chars_of_num_with_basis b use_upper n =
  let char_of_digit = function
      | 10 -> if use_upper then 'A' else 'a'
      | 11 -> if use_upper then 'B' else 'b'
      | 12 -> if use_upper then 'C' else 'c'
      | 13 -> if use_upper then 'D' else 'd'
      | 14 -> if use_upper then 'E' else 'e'
      | 15 -> if use_upper then 'F' else 'f'
      | r  -> char_of_int (r + 48) in
  let rec f n acc =
    let (n', r) = quomod n (of_int b) in
    let c = char_of_digit (to_int r) in
    if equal n' (of_int 0) then
      c :: acc
    else
      f n' (c :: acc) in
  if less n zero then
    '-' :: f (negate n) []
  else
    f n []


let string_of_octal n =
  if equal n (of_int 0) then
    "0"
  else
    let l = chars_of_num_with_basis 8 false n in
    let ret = Bytes.create (List.length l+1) in
    Bytes.set ret 0 '0';
    List.iteri (fun i c ->
      Bytes.set ret (i+1) c
    ) l;
    Bytes.to_string ret


let string_of_decimal n =
  to_string n


let string_of_hexadecimal n =
  let l = chars_of_num_with_basis 16 false n in
  let ret = Bytes.create (List.length l + 2) in
  Bytes.set ret 0 '0';
  Bytes.set ret 1 'x';
  List.iteri (fun i c ->
    Bytes.set ret (i+2) c
  ) l;
  Bytes.to_string ret
