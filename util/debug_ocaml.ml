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

type domain =
  | DB_clexer
  | DB_cparser
  | DB_desugaring
  | DB_ail_typing
  | DB_elaboration
  | DB_core_typing
  | DB_core_dynamics
  | DB_driver
  | DB_concurrency
  | DB_driver_step
  | DB_memory

(*
type debug_state = {
  level:   int;
  domains: domain list; (* using all domains if the list is empty *)
}
*)

let error str =
  prerr_string (Colour.ansi_format [Red] "internal error: ");
  prerr_endline str;
  failwith @@ "internal error: " ^ str

let debug_level = ref 0

let get_debug_level () =
  !debug_level

let print_success msg =
  if !debug_level > 0 then
    prerr_endline Colour.(ansi_format [Green] msg)

let print_debug level _doms msg =
  if !debug_level >= level then
    prerr_endline Colour.(ansi_format [Red] ("(debug " ^ string_of_int level ^ "): " ^ msg ()))

let print_debug_located level doms loc msg =
  print_debug level doms (fun () -> "(" ^ Location_ocaml.location_to_string loc ^ ") - " ^ msg ())

let warn _doms msg =
  if !debug_level > 0 then
    prerr_endline Colour.(ansi_format [Yellow] ("WARNING: " ^ msg ()))

(*
let print_debug2 msg k =
  if !debug_level > 0 then
    let _ = prerr_endline Colour.(ansi_format [Red] ("\x1b[31mDEBUG: " ^ msg ^ "\x1b[0m")) in k
  else
    k
*)

let output_string2 msg =
  if !debug_level > 0 then
    prerr_endline msg




let timing_stack =
  ref []

let begin_timing (fun_name: string) =
  if !debug_level > 8 then
    timing_stack := (fun_name, Unix.gettimeofday ()) :: !timing_stack

let end_timing () =
  if !debug_level > 8 then
    let t' = Unix.gettimeofday () in
    match !timing_stack with
      | [] ->
          () (* this implies an improper use of end_timing, but we silently ignore *)
      | (str, t) :: xs ->
          let oc = open_out_gen [Open_creat; Open_wronly; Open_append] 0o666 "cerb.prof" in
          Printf.fprintf oc "[%s] %f\n" str (t' -. t);
          close_out oc;
          timing_stack := xs
