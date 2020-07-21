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

open Cerb_frontend

type language =
  | Cabs | Ail | Core

type pp_flag =
  | Annot | FOut

type configuration = {
  debug_level: int;
  pprints: language list;
  astprints: language list;
  ppflags: pp_flag list;
  typecheck_core: bool;
  rewrite_core: bool;
  sequentialise_core: bool;
  cpp_cmd: string;
  cpp_stderr: bool;
}

type io_helpers = {
  pass_message: string -> (unit, Errors.error) Exception.exceptM;
  set_progress: string -> (unit, Errors.error) Exception.exceptM;
  run_pp: (string * string) option -> PPrint.document -> (unit, Errors.error) Exception.exceptM;
  print_endline: string -> (unit, Errors.error) Exception.exceptM;
  print_debug: int -> (unit -> string) -> (unit, Errors.error) Exception.exceptM;
  warn: (unit -> string) -> (unit, Errors.error) Exception.exceptM;
}

val run_pp: ?remove_path:bool -> (string * string) option -> PPrint.document -> unit

val load_core_stdlib:
  unit -> ((string, Symbol.sym) Pmap.map * unit Core.fun_map, Location_ocaml.t * Errors.cause) Exception.exceptM

val load_core_impl:
  (string, Symbol.sym) Pmap.map * unit Core.fun_map -> string ->
  (Core.impl, Location_ocaml.t * Errors.cause) Exception.exceptM

val cpp: (configuration * io_helpers) -> filename:string -> (string, Location_ocaml.t * Errors.cause) Exception.exceptM

val c_frontend:
  (configuration * io_helpers) ->
  (((string, Symbol.sym) Pmap.map * (unit, unit) Core.generic_fun_map) * unit Core.generic_impl) ->
  filename:string ->
  ( Cabs.translation_unit option
  * (GenTypes.genTypeCategory AilSyntax.ail_program) option
  * unit Core.file
  , Location_ocaml.t * Errors.cause) Exception.exceptM

val core_frontend:
  'a * io_helpers ->
  ('b * (Symbol.sym, (unit, unit) Core.generic_fun_map_decl) Pmap.map) *
  (Implementation.implementation_constant, unit Core.generic_impl_decl)
  Pmap.map ->
  filename:string ->
  ((unit, unit) Core.generic_file, Location_ocaml.t * Errors.cause) Exception.exceptM


val typed_core_passes:
  (configuration * io_helpers) -> unit Core.file ->
  (unit Core.file * unit Core.typed_file, Location_ocaml.t * Errors.cause) Exception.exceptM

val core_passes:
  (configuration * io_helpers) -> filename:string -> unit Core.file ->
  (unit Core.file, Location_ocaml.t * Errors.cause) Exception.exceptM

val interp_backend:
  io_helpers -> 'a Core.file ->
  args:(string list) -> batch:[`Batch | `CharonBatch | `NotBatch] -> fs:string option -> driver_conf:Exhaustive_driver.driver_conf ->
(* TODO: we would be using poly variants if it weren't for Lem... *)
(*  [`Interactive | `Exhaustive | `Random] -> *)
  ((string list, int) Either.either, Location_ocaml.t * Errors.cause) Exception.exceptM

(*
val ocaml_backend:
  (configuration * io_helpers) -> filename:string -> ocaml_corestd:bool -> unit Core.file ->
  (int, Location_ocaml.t * Errors.cause) Exception.exceptM
   *)

val read_core_object:
  (((string, Symbol.sym) Pmap.map * (unit, unit) Core.generic_fun_map) * unit Core.generic_impl) ->
  string -> unit Core.file
val write_core_object: unit Core.file -> string -> unit


val untype_file: 
  'a Core.typed_file ->
  'a Core.file
