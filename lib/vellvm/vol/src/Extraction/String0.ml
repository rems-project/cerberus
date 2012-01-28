open Ascii
open Datatypes

type string =
  | EmptyString
  | String of ascii * string

(** val string_rect :
    'a1 -> (ascii -> string -> 'a1 -> 'a1) -> string -> 'a1 **)

let rec string_rect f f0 = function
  | EmptyString -> f
  | String (a, s0) -> f0 a s0 (string_rect f f0 s0)

(** val string_rec :
    'a1 -> (ascii -> string -> 'a1 -> 'a1) -> string -> 'a1 **)

let rec string_rec f f0 = function
  | EmptyString -> f
  | String (a, s0) -> f0 a s0 (string_rec f f0 s0)

(** val string_dec : string -> string -> bool **)

let rec string_dec s s0 =
  match s with
    | EmptyString ->
        (match s0 with
           | EmptyString -> true
           | String (a, s1) -> false)
    | String (a, s1) ->
        (match s0 with
           | EmptyString -> false
           | String (a0, s2) ->
               if ascii_dec a a0 then string_dec s1 s2 else false)

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
    | EmptyString -> s2
    | String (c, s1') -> String (c, (append s1' s2))

(** val length : string -> nat **)

let rec length = function
  | EmptyString -> O
  | String (c, s') -> S (length s')

(** val get : nat -> string -> ascii option **)

let rec get n = function
  | EmptyString -> None
  | String (c, s') -> (match n with
                         | O -> Some c
                         | S n' -> get n' s')

(** val substring : nat -> nat -> string -> string **)

let rec substring n m s =
  match n with
    | O ->
        (match m with
           | O -> EmptyString
           | S m' ->
               (match s with
                  | EmptyString -> s
                  | String (c, s') -> String (c, (substring O m' s'))))
    | S n' ->
        (match s with
           | EmptyString -> s
           | String (c, s') -> substring n' m s')

(** val prefix : string -> string -> bool **)

let rec prefix s1 s2 =
  match s1 with
    | EmptyString -> true
    | String (a, s1') ->
        (match s2 with
           | EmptyString -> false
           | String (b, s2') ->
               if ascii_dec a b then prefix s1' s2' else false)

(** val index : nat -> string -> string -> nat option **)

let rec index n s1 s2 = match s2 with
  | EmptyString ->
      (match n with
         | O ->
             (match s1 with
                | EmptyString -> Some O
                | String (a, s1') -> None)
         | S n' -> None)
  | String (b, s2') ->
      (match n with
         | O ->
             if prefix s1 s2
             then Some O
             else (match index O s1 s2' with
                     | Some n0 -> Some (S n0)
                     | None -> None)
         | S n' ->
             (match index n' s1 s2' with
                | Some n0 -> Some (S n0)
                | None -> None))

(** val findex : nat -> string -> string -> nat **)

let findex n s1 s2 =
  match index n s1 s2 with
    | Some n0 -> n0
    | None -> O

(** val coq_HelloWorld : string **)

let coq_HelloWorld =
  String ((Ascii (true, false, false, true, false, false, false, false)),
    (String ((Ascii (false, true, false, false, false, true, false, false)),
    (String ((Ascii (false, false, false, true, false, false, true, false)),
    (String ((Ascii (true, false, true, false, false, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (true, true, true, true, false, true, true, false)),
    (String ((Ascii (false, false, false, false, false, true, false, false)),
    (String ((Ascii (true, true, true, false, true, true, true, false)),
    (String ((Ascii (true, true, true, true, false, true, true, false)),
    (String ((Ascii (false, true, false, false, true, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (false, false, true, false, false, true, true, false)),
    (String ((Ascii (true, false, false, false, false, true, false, false)),
    (String ((Ascii (false, true, false, false, false, true, false, false)),
    (String ((Ascii (true, true, true, false, false, false, false, false)),
    (String ((Ascii (false, true, false, true, false, false, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))

