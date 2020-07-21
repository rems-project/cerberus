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

module P = PPrint
let (!^ ) = P.(!^)
let (^^)  = P.(^^)


(* Part of the escape ANSI's "Select Graphic Rendition" parameters *)
type ansi_style =
  | Black
  | Red
  | Green
  | Yellow
  | Blue
  | Magenta
  | Cyan
  | White
  | Bold
  | Underline
  | Blinking
  | Inverted
  (* TODO: the complete list *)

type ansi_format = ansi_style list

let int_fg = function
  | Black     -> 30
  | Red       -> 31
  | Green     -> 32
  | Yellow    -> 33
  | Blue      -> 34
  | Magenta   -> 35
  | Cyan      -> 36
  | White     -> 37
  | Bold      -> 1
  | Underline -> 4
  | Blinking  -> 5
  | Inverted  -> 7

(* TODO: yuck!!!! *)
let do_colour =
  ref (Unix.isatty Unix.stdout)

let ansi_format f str =
  if !do_colour then
    let g f = String.concat ";" (List.map (fun z -> string_of_int (int_fg z)) f) ^ "m" in
    "\x1b[" ^ g f ^ str ^ "\x1b[0m" (* TODO: optimize, someday *)
  else
    str


let pp_ansi_format f doc =
  if !do_colour then
    let g f = String.concat ";" (List.map (fun z -> string_of_int (int_fg z)) f) ^ "m" in
    !^ ("\x1b[" ^ g f) ^^ doc ^^ !^ "\x1b[0m" (* TODO: optimize, someday *)
  else
    doc
