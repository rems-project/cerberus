open Ascii
open Datatypes

type string =
  | EmptyString
  | String of ascii * string

val string_rect : 'a1 -> (ascii -> string -> 'a1 -> 'a1) -> string -> 'a1

val string_rec : 'a1 -> (ascii -> string -> 'a1 -> 'a1) -> string -> 'a1

val string_dec : string -> string -> bool

val append : string -> string -> string

val length : string -> nat

val get : nat -> string -> ascii option

val substring : nat -> nat -> string -> string

val prefix : string -> string -> bool

val index : nat -> string -> string -> nat option

val findex : nat -> string -> string -> nat

val coq_HelloWorld : string

