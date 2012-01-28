open Ascii
open BinPos
open String0

type errcode =
  | MSG of string
  | CTX of positive

(** val errcode_rect :
    (string -> 'a1) -> (positive -> 'a1) -> errcode -> 'a1 **)

let errcode_rect f f0 = function
  | MSG x -> f x
  | CTX x -> f0 x

(** val errcode_rec :
    (string -> 'a1) -> (positive -> 'a1) -> errcode -> 'a1 **)

let errcode_rec f f0 = function
  | MSG x -> f x
  | CTX x -> f0 x

type errmsg = errcode list

(** val msg : string -> errmsg **)

let msg s =
  (MSG s)::[]

type 'a res =
  | OK of 'a
  | Error of errmsg

(** val res_rect : ('a1 -> 'a2) -> (errmsg -> 'a2) -> 'a1 res -> 'a2 **)

let res_rect f f0 = function
  | OK x -> f x
  | Error x -> f0 x

(** val res_rec : ('a1 -> 'a2) -> (errmsg -> 'a2) -> 'a1 res -> 'a2 **)

let res_rec f f0 = function
  | OK x -> f x
  | Error x -> f0 x

(** val bind : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res **)

let bind f g =
  match f with
    | OK x -> g x
    | Error msg0 -> Error msg0

(** val bind2 : ('a1*'a2) res -> ('a1 -> 'a2 -> 'a3 res) -> 'a3 res **)

let bind2 f g =
  match f with
    | OK p -> let x,y = p in g x y
    | Error msg0 -> Error msg0

(** val assertion : bool -> unit res **)

let assertion = function
  | true -> OK ()
  | false -> Error
      (msg (String ((Ascii (true, false, false, false, false, false, true,
        false)), (String ((Ascii (true, true, false, false, true, true, true,
        false)), (String ((Ascii (true, true, false, false, true, true, true,
        false)), (String ((Ascii (true, false, true, false, false, true,
        true, false)), (String ((Ascii (false, true, false, false, true,
        true, true, false)), (String ((Ascii (false, false, true, false,
        true, true, true, false)), (String ((Ascii (true, false, false, true,
        false, true, true, false)), (String ((Ascii (true, true, true, true,
        false, true, true, false)), (String ((Ascii (false, true, true, true,
        false, true, true, false)), (String ((Ascii (false, false, false,
        false, false, true, false, false)), (String ((Ascii (false, true,
        true, false, false, true, true, false)), (String ((Ascii (true,
        false, false, false, false, true, true, false)), (String ((Ascii
        (true, false, false, true, false, true, true, false)), (String
        ((Ascii (false, false, true, true, false, true, true, false)),
        (String ((Ascii (true, false, true, false, false, true, true,
        false)), (String ((Ascii (false, false, true, false, false, true,
        true, false)), EmptyString)))))))))))))))))))))))))))))))))

(** val mmap : ('a1 -> 'a2 res) -> 'a1 list -> 'a2 list res **)

let rec mmap f = function
  | [] -> OK []
  | hd::tl ->
      bind (f hd) (fun hd' -> bind (mmap f tl) (fun tl' -> OK (hd'::tl')))

