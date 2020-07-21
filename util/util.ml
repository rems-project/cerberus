(************************************************************************************)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  Cerberus                                                                        *)
(*                                                                                  *)
(*  Copyright (c) 2016-2020                                                         *)
(*    Victor Gomes                                                                  *)
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

(* Some useful generic functions *)

let ( $ ) f x = f x

let ( % ) f g = (fun x -> f (g x))

let ( %% ) f g = (fun x y -> f x (g y))

let id = fun x -> x

let flip f a b = f b a

let apply f x = f x

let uncurry f = (fun (x, y) -> f x y)

module Option = struct
exception No_value

let case f g = function
  | Some x -> f x
  | None -> g ()

let map f = function
  | Some x -> Some (f x)
  | None -> None

let get x = case id (fun _ -> raise No_value) x

end

exception Unsupported of string
exception Unexpected of string

(* Debugging *)

module Debug =
struct

  let level = ref 0

  let print n msg =
    if !level >= n then Printf.fprintf stderr "[%d]: %s\n%!" n msg

  let warn msg  =
    if !level > 0 then Printf.fprintf stderr "\x1b[33m[ WARN  ]: %s\n\x1b[0m%!" msg

  let error msg =
    Printf.fprintf stderr "\x1b[31m[ ERROR ]: %s\n\x1b[0m%!" msg

  let warn_exception msg e =
    warn (msg ^ " " ^ Printexc.to_string e)

  let error_exception msg e =
    error (msg ^ " " ^ Printexc.to_string e)

end

let diff xs ys = List.filter (fun x -> not (List.mem x ys)) xs

let concatMap f xs = List.concat (List.map f xs)

let contains s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with
  | Exit -> true
  | e ->
    Debug.error_exception "contains" e;
    false


