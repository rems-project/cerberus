(****************************************************************************)
(*  Copyright (c) 2013, 2014, 2015, Tom Ridge, David Sheets, Thomas Tuerk,  *)
(*  Andrea Giugliano (as part of the SibylFS project)                       *)
(*                                                                          *)
(*  Permission to use, copy, modify, and/or distribute this software for    *)
(*  any purpose with or without fee is hereby granted, provided that the    *)
(*  above copyright notice and this permission notice appear in all         *)
(*  copies.                                                                 *)
(*                                                                          *)
(*  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL           *)
(*  WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED           *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE        *)
(*  AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL    *)
(*  DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR   *)
(*  PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER          *)
(*  TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR        *)
(*  PERFORMANCE OF THIS SOFTWARE.                                           *)
(*                                                                          *)
(*  Meta:                                                                   *)
(*    - Headers maintained using headache.                                  *)
(*    - License source: http://opensource.org/licenses/ISC                  *)
(****************************************************************************)

(* Abstract_string is a type isomorphic to string; we want to retain
   the possibility of substituting a possibly-more-efficient type in
   generated OCaml. *)

type t [@@deriving sexp]

val to_list : t -> char list

val of_list : char list -> t

val of_string : string -> t

val to_string : t -> string

val dim : t -> int

val resize : t -> int -> t

val equal : t -> t -> bool
