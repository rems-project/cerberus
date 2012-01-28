open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val induction_ltof1 :
    ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let induction_ltof1 f f0 =
  let h =
    let rec f1 n a =
      match n with
        | O -> assert false (* absurd case *)
        | S n0 -> f0 a (fun b _ -> f1 n0 b)
    in f1
  in
  (fun a -> h (S (f a)) a)

(** val induction_gtof1 :
    ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let induction_gtof1 f x a =
  induction_ltof1 f x a

(** val induction_ltof2 :
    ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec induction_ltof2 f x a =
  x a (fun y _ -> induction_ltof2 f x y)

(** val induction_gtof2 :
    ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let induction_gtof2 f x a =
  induction_ltof2 f x a

(** val lt_wf_rec1 : nat -> (nat -> (nat -> __ -> 'a1) -> 'a1) -> 'a1 **)

let lt_wf_rec1 p f =
  induction_ltof1 (fun m -> m) f p

(** val lt_wf_rec : nat -> (nat -> (nat -> __ -> 'a1) -> 'a1) -> 'a1 **)

let lt_wf_rec p f =
  induction_ltof2 (fun m -> m) f p

(** val gt_wf_rec : nat -> (nat -> (nat -> __ -> 'a1) -> 'a1) -> 'a1 **)

let gt_wf_rec n x =
  lt_wf_rec n x

(** val lt_wf_double_rec :
    (nat -> nat -> (nat -> nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1) ->
    nat -> nat -> 'a1 **)

let lt_wf_double_rec hrec p =
  lt_wf_rec p (fun n h q ->
    lt_wf_rec q (fun n0 h0 -> hrec n n0 (fun p0 q0 _ -> h p0 __ q0) h0))

(** val iter_nat : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter_nat n f x =
  match n with
    | O -> x
    | S n' -> f (iter_nat n' f x)

