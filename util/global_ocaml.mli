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

val (-|): ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

type error_verbosity =
  | Basic    (* similar to a normal compiler *)
  | RefStd   (* add an std reference to Basic *)
  | QuoteStd (* print a full quote of the std text *)

type execution_mode =
  | Exhaustive
  | Random

type cerberus_conf = {
  exec_mode_opt:   execution_mode option;
  concurrency:     bool;
  error_verbosity: error_verbosity;
  defacto:         bool;
  agnostic:        bool;
  n1570:           Yojson.Basic.t option;
}

val (!!): (unit -> 'a) ref -> 'a

val cerb_conf: (unit -> cerberus_conf) ref

val set_cerb_conf:
    bool ->
    execution_mode ->
    bool ->
    error_verbosity ->
    bool ->
    bool ->
    bool ->
    unit

(* NOTE: used in driver.lem *)
val current_execution_mode: unit -> execution_mode option

val concurrency_mode: unit -> bool
val isDefacto: unit -> bool
val isAgnostic: unit -> bool

(* NOTE: used in pp_errors.ml *)
val verbose: unit -> error_verbosity
val n1570: unit -> Yojson.Basic.t option

(* print an error fatal message and exit with a given code (default is 1) *)
val error: ?code:int -> string -> 'a
