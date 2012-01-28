open CoqFSetDecide
open Datatypes
open DecidableTypeEx
open FSetFacts
open FSetProperties
open List0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Make = 
 functor (X:UsualDecidableType) ->
 functor (KeySet:sig 
  type elt = X.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
 end) ->
 struct 
  module D = WDecide_fun(X)(KeySet)
  
  module KeySetProperties = WProperties_fun(X)(KeySet)
  
  module KeySetFacts = WFacts_fun(X)(KeySet)
  
  (** val one : 'a1 -> 'a1 list **)
  
  let one item =
    item::[]
  
  (** val dom : (X.t*'a1) list -> KeySet.t **)
  
  let rec dom = function
    | [] -> KeySet.empty
    | p::e' -> let x,y = p in KeySet.add x (dom e')
  
  (** val get : X.t -> (X.t*'a1) list -> 'a1 option **)
  
  let rec get x = function
    | [] -> None
    | p::f -> let y,c = p in if X.eq_dec x y then Some c else get x f
  
  (** val map : ('a1 -> 'a2) -> (X.t*'a1) list -> (X.t*'a2) list **)
  
  let map f e =
    map (fun b -> let x,a = b in x,(f a)) e
  
  (** val alist_ind :
      'a2 -> (X.t -> 'a1 -> (X.t*'a1) list -> 'a2 -> 'a2) -> (X.t*'a1) list
      -> 'a2 **)
  
  let rec alist_ind x x0 = function
    | [] -> x
    | y::l -> let iHxs = alist_ind x x0 l in let x1,a = y in x0 x1 a l iHxs
  
  (** val binds_dec :
      X.t -> 'a1 -> (X.t*'a1) list -> ('a1 -> 'a1 -> bool) -> bool **)
  
  let binds_dec x a e x0 =
    in_dec (fun x1 y ->
      let x2,x3 = x1 in
      let t0,a1 = y in if X.eq_dec x2 t0 then x0 x3 a1 else false) (x,a) e
  
  (** val binds_lookup : X.t -> (X.t*'a1) list -> ('a1, __) sum **)
  
  let binds_lookup x e =
    alist_ind (Coq_inr __) (fun x1 a1 l x0 ->
      match x0 with
        | Coq_inl s -> Coq_inl s
        | Coq_inr _ ->
            let s = X.eq_dec x x1 in if s then Coq_inl a1 else Coq_inr __) e
 end

