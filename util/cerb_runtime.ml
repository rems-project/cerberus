(************************************************************************************)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  Cerberus                                                                        *)
(*                                                                                  *)
(*  Copyright (c) 2020                                                              *)
(*    Rodolphe Lepigre                                                              *)
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

(** Discover the path to the Cerberus runtime. *)

(** If it is set, [specified_runtime] has highest priority, and it can thus be
    used to override the "detected" runtime path from the CLI for example. *)
let specified_runtime : string option ref = ref None

(** [find_build_runtime ()] attempts to locate the build-time Cerberus runtime
    (inside the Dune [_build] directory) using the PATH. Exception [Not_found]
    is raised in case of failure. *)
let find_build_runtime : unit -> string = fun _ ->
  let path = String.split_on_char ':' (Sys.getenv "PATH") in
  let suffix = "/_build/install/default/bin" in
  let len_suffix = String.length suffix in
  let rec find_prefix path =
    match path with
    | []        -> raise Not_found
    | p :: path ->
    let len = String.length p in
    if len < len_suffix then find_prefix path else
    let p_suffix = String.sub p (len - len_suffix) len_suffix in
    if p_suffix <> suffix then find_prefix path else
    String.sub p 0 (len - len_suffix)
  in
  let runtime_path =
    Filename.concat (find_prefix path)
      "_build/install/default/lib/cerberus/runtime"
  in
  if not (Sys.file_exists runtime_path) then raise Not_found;
  runtime_path

(** [detect_runtime ()] locates the cerberus runtime. Note that if opam is not
    properly initialized then the function may raise [Failure]. *)
let detect_runtime : unit -> string = fun _ ->
  (* First check for specified runtime. *)
  match !specified_runtime with Some(path) -> path | None ->
  (* Then check the CERB_RUNTIME environment variable. *)
  try Sys.getenv "CERB_RUNTIME" with Not_found ->
  (* Then check for build time runtime (in repository). *)
  try find_build_runtime () with Not_found ->
  (* Fall back to installed runtime under the opam switch prefix. *)
  let prefix =
    try Sys.getenv "OPAM_SWITCH_PREFIX"
    with Not_found -> failwith "OPAM_SWITCH_PREFIX not set."
  in
  Filename.concat prefix "lib/cerberus/runtime"

(** [runtime ()] is a memoised version of [detect_runtime ()]. This means that
    if [Failure] is not raised on its first call, it will not be raised later,
    during other calls. *)
let runtime : unit -> string =
  let runtime = Lazy.from_fun detect_runtime in
  fun _ -> Lazy.force runtime

(** [in_runtime path] appends [path] to the Cerberus runtime path (as returned
    by [runtime ()]. Exceptions [Failure] can be raised accordingly. *)
let in_runtime : string -> string = fun path ->
  Filename.concat (runtime ()) path
