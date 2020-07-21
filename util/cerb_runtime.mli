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

(** [specified_runtime] can be used to override the runtime that is "detected"
    by the [runtime] function. Its initial value is [None], and it must be set
    before the first call to [runtime] otherwise it is not taken into account.
    This flag is useful to, e.g., override the runtime patch from the CLI. *)
val specified_runtime : string option ref

(** [runtime ()] detects and returns an absolute path to the Cerberus runtime.
    If [specified_runtime] is set then its value is used, and otherwise if the
    [CERB_RUNTIME] environment variable is set then its value is used. If none
    of these are set and the function runs in build mode (i.e., from a program
    run with [dune exec]) then the runtime is looked for under dune's [_build]
    directory. Otherwise it is assumed that the runtime is installed under the
    Opam switch prefix, as part of the Cerberus library folder. Note that this
    relies on Opam being used and properly configured. The exception [Failure]
    can be raised if that is not the case. Note also that the actual detection
    of the runtime only runs for the first call to [runtime ()]. In subsequent
    calls the result is returned directly. *)
val runtime : unit -> string

(** [in_runtime path] appends [path] to the Cerberus runtime path (as returned
    by [runtime ()]. Exceptions [Failure] can be raised accordingly. *)
val in_runtime : string -> string
