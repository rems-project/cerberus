open Ascii
open BinPos
open String0

type errcode =
  | MSG of string
  | CTX of positive

val errcode_rect : (string -> 'a1) -> (positive -> 'a1) -> errcode -> 'a1

val errcode_rec : (string -> 'a1) -> (positive -> 'a1) -> errcode -> 'a1

type errmsg = errcode list

val msg : string -> errmsg

type 'a res =
  | OK of 'a
  | Error of errmsg

val res_rect : ('a1 -> 'a2) -> (errmsg -> 'a2) -> 'a1 res -> 'a2

val res_rec : ('a1 -> 'a2) -> (errmsg -> 'a2) -> 'a1 res -> 'a2

val bind : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res

val bind2 : ('a1*'a2) res -> ('a1 -> 'a2 -> 'a3 res) -> 'a3 res

val assertion : bool -> unit res

val mmap : ('a1 -> 'a2 res) -> 'a1 list -> 'a2 list res

