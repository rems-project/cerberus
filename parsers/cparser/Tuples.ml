open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type tuple = __

(** val tuple_rev_app : __ list -> tuple -> __ list -> tuple -> tuple **)

let rec tuple_rev_app types1 tuple1 types2 tuple2 =
  match types1 with
  | [] -> tuple2
  | _::tq ->
    let Coq_pair (t, q) = Obj.magic tuple1 in
    tuple_rev_app tq q (__::types2) (Obj.magic (Coq_pair (t, tuple2)))

type 'res arrows = __

(** val uncurry : __ list -> 'a1 arrows -> tuple -> 'a1 **)

let rec uncurry args f x =
  match args with
  | [] -> Obj.magic f
  | _::q -> let Coq_pair (d, t) = Obj.magic x in uncurry q (Obj.magic f d) t

