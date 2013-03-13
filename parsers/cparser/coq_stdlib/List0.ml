open Datatypes
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| [] -> default
| x::l0 -> x

(** val hd_error : 'a1 list -> 'a1 option **)

let hd_error = function
| [] -> error
| x::l0 -> value x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| a::m -> m

(** val destruct_list : 'a1 list -> ('a1, 'a1 list) sigT sumor **)

let destruct_list = function
| [] -> Coq_inright
| y::l0 -> Coq_inleft (Coq_existT (y, l0))

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y::l0 -> let s = h y a in if s then true else in_dec h a l0

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O ->
    (match l with
     | [] -> default
     | x::l' -> x)
  | S m ->
    (match l with
     | [] -> default
     | x::t -> nth m t default)

(** val nth_ok : nat -> 'a1 list -> 'a1 -> bool **)

let rec nth_ok n l default =
  match n with
  | O ->
    (match l with
     | [] -> false
     | x::l' -> true)
  | S m ->
    (match l with
     | [] -> false
     | x::t -> nth_ok m t default)

(** val nth_in_or_default : nat -> 'a1 list -> 'a1 -> bool **)

let rec nth_in_or_default n l d =
  match l with
  | [] -> false
  | y::l0 ->
    (match n with
     | O -> true
     | S n1 -> nth_in_or_default n1 l0 d)

(** val nth_error : 'a1 list -> nat -> 'a1 coq_Exc **)

let rec nth_error l = function
| O ->
  (match l with
   | [] -> error
   | x::l0 -> value x)
| S n0 ->
  (match l with
   | [] -> error
   | a::l0 -> nth_error l0 n0)

(** val nth_default : 'a1 -> 'a1 list -> nat -> 'a1 **)

let nth_default default l n =
  match nth_error l n with
  | Some x -> x
  | None -> default

(** val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove eq_dec x = function
| [] -> []
| y::tl0 ->
  if eq_dec x y then remove eq_dec x tl0 else y::(remove eq_dec x tl0)

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a::l0 ->
    (match l0 with
     | [] -> a
     | a0::l1 -> last l0 d)

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| [] -> []
| a::l0 ->
  (match l0 with
   | [] -> []
   | a0::l1 -> a::(removelast l0))

(** val exists_last : 'a1 list -> ('a1 list, 'a1) sigT **)

let rec exists_last = function
| [] -> assert false (* absurd case *)
| y::l0 ->
  (match l0 with
   | [] -> Coq_existT ([], y)
   | a0::l1 ->
     let Coq_existT (l', s) = exists_last l0 in Coq_existT ((y::l'), s))

(** val count_occ : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> nat **)

let rec count_occ eq_dec l x =
  match l with
  | [] -> O
  | y::tl0 -> let n = count_occ eq_dec tl0 x in if eq_dec y x then S n else n

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a::l0 -> rev_append l0 (a::l')

(** val rev' : 'a1 list -> 'a1 list **)

let rev' l =
  rev_append l []

(** val list_eq_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec l l' =
  match l with
  | [] ->
    (match l' with
     | [] -> true
     | y::l'0 -> false)
  | y::l0 ->
    (match l' with
     | [] -> false
     | y0::l'0 ->
       let s = eq_dec y y0 in if s then list_eq_dec eq_dec l0 l'0 else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::t -> app (f x) (flat_map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t -> f b (fold_right f a0 t)

(** val list_power : 'a1 list -> 'a2 list -> ('a1*'a2) list list **)

let rec list_power l l' =
  match l with
  | [] -> []::[]
  | x::t -> flat_map (fun f -> map (fun y -> (x,y)::f) l') (list_power t l')

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a::l0 -> if f a then true else existsb f l0

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a::l0 -> if f a then forallb f l0 else false

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x::tl0 -> if f x then Some x else find f tl0

(** val partition : ('a1 -> bool) -> 'a1 list -> 'a1 list*'a1 list **)

let rec partition f = function
| [] -> [],[]
| x::tl0 -> let g,d = partition f tl0 in if f x then (x::g),d else g,(x::d)

(** val split : ('a1*'a2) list -> 'a1 list*'a2 list **)

let rec split = function
| [] -> [],[]
| p::tl0 -> let x,y = p in let g,d = split tl0 in (x::g),(y::d)

(** val combine : 'a1 list -> 'a2 list -> ('a1*'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x::tl0 ->
    (match l' with
     | [] -> []
     | y::tl' -> (x,y)::(combine tl0 tl'))

(** val list_prod : 'a1 list -> 'a2 list -> ('a1*'a2) list **)

let rec list_prod l l' =
  match l with
  | [] -> []
  | x::t -> app (map (fun y -> x,y) l') (list_prod t l')

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  match n with
  | O -> []
  | S n0 ->
    (match l with
     | [] -> []
     | a::l0 -> a::(firstn n0 l0))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  match n with
  | O -> l
  | S n0 ->
    (match l with
     | [] -> []
     | a::l0 -> skipn n0 l0)

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> []
| S len0 -> start::(seq (S start) len0)

(** val coq_Forall_rect :
    'a2 -> ('a1 -> 'a1 list -> __ -> 'a2) -> 'a1 list -> 'a2 **)

let coq_Forall_rect h h' = function
| [] -> h
| y::l0 -> h' y l0 __

