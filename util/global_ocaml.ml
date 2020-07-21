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

(*let (|-) f g x = g (f x)*)
let (-|) f g x = f (g x)
(*let (>?>) x b f g = if b then f x else g x*)

(* Requires ocaml at least 4.00.0 *)
(* let (|>) x f = f x *)
(* external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply" *)

type error_verbosity =
  | Basic    (* similar to a normal compiler *)
  | RefStd   (* add an std reference to Basic *)
  | QuoteStd (* print a full quote of the std text *)

type execution_mode =
  | Exhaustive
  | Random

type cerberus_conf = {
  exec_mode_opt:      execution_mode option;
  concurrency:        bool;
  error_verbosity:    error_verbosity;
  defacto:            bool;
  agnostic:           bool;
  n1570:              Yojson.Basic.t option;
}

let (!!) z = !z()

let cerb_conf =
  ref (fun () -> failwith "cerb_conf is Undefined")

let set_cerb_conf exec exec_mode concurrency error_verbosity defacto agnostic _bmc =
  let exec_mode_opt = if exec then Some exec_mode else None in
  let n1570 =
    if error_verbosity <> QuoteStd then None else Some (Lazy.force N1570.data)
  in
  let conf =
    {defacto; concurrency; error_verbosity; agnostic; exec_mode_opt; n1570}
  in
  cerb_conf := fun () -> conf

let concurrency_mode () =
  !!cerb_conf.concurrency

let isDefacto () =
  !!cerb_conf.defacto

let isAgnostic () =
  !!cerb_conf.agnostic

let current_execution_mode () =
  !!cerb_conf.exec_mode_opt

let verbose () =
  !!cerb_conf.error_verbosity

let n1570 () =
  !!cerb_conf.n1570

let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] ("ERROR: " ^ msg));
  exit code
