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

open Int64

let ctz n =
  let n = Nat_big_num.to_int64 n in
  assert (not (equal n zero));
  let rec aux acc z =
    if equal z zero then
      acc
    else
      aux (Nat_big_num.pred acc) (shift_left z 1) in
  aux (Nat_big_num.of_int 64) n

let bswap16 n =
  let n = Nat_big_num.to_int64 n in
  assert (equal zero (logand 0xffffffffffff0000L n));
  Nat_big_num.of_int64 begin
    logor (shift_right_logical (logand 0xff00L n) 8) (shift_left (logand 0xffL n) 8)
  end

let bswap32 n =
  let n = Nat_big_num.to_int64 n in
  assert (equal zero (logand 0xffffffff00000000L n));
  Nat_big_num.of_int64 begin
    logor
      (logor (shift_left (logand 0x0000ff00L n) 8) (shift_left (logand 0x000000ffL n) 24))
      (logor (shift_right_logical (logand 0xff000000L n) 24) (shift_right_logical (logand 0x00ff0000L n) 8))
  end

let bswap64 n =
  let n = Nat_big_num.to_int64 n in
  Nat_big_num.of_int64 begin
    logor
      (logor
        (logor (shift_left (logand 0x000000000000ff00L n) 40) (shift_left (logand 0x00000000000000ffL n) 56))
        (logor (shift_left (logand 0x0000000000ff0000L n) 24) (shift_left (logand 0x00000000ff000000L n) 8)))
      (logor
        (logor (shift_right_logical (logand 0x00ff000000000000L n) 40) (shift_right_logical (logand 0xff00000000000000L n) 56))
        (logor (shift_right_logical (logand 0x0000ff0000000000L n) 24) (shift_right_logical (logand 0x000000ff00000000L n) 8)))
  end
