open Bool
open Datatypes
open FSetInterface
open List0
open ListSet
open Maps
open MetatheoryAtom
open Wf_nat

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type SEMILATTICE = 
 sig 
  type t 
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
 end

module type SEMILATTICE_WITH_TOP = 
 sig 
  type t 
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
  
  val top : t
 end

module LPMap = 
 functor (L:SEMILATTICE_WITH_TOP) ->
 struct 
  type t_ =
    | Bot_except of L.t ATree.t
    | Top_except of L.t ATree.t
  
  (** val t__rect :
      (L.t ATree.t -> 'a1) -> (L.t ATree.t -> 'a1) -> t_ -> 'a1 **)
  
  let t__rect f f0 = function
    | Bot_except x -> f x
    | Top_except x -> f0 x
  
  (** val t__rec :
      (L.t ATree.t -> 'a1) -> (L.t ATree.t -> 'a1) -> t_ -> 'a1 **)
  
  let t__rec f f0 = function
    | Bot_except x -> f x
    | Top_except x -> f0 x
  
  type t = t_
  
  (** val get : AtomImpl.atom -> t -> L.t **)
  
  let get p = function
    | Bot_except m ->
        (match ATree.get p m with
           | Some x0 -> x0
           | None -> L.bot)
    | Top_except m ->
        (match ATree.get p m with
           | Some x0 -> x0
           | None -> L.top)
  
  (** val set : AtomImpl.atom -> L.t -> t -> t **)
  
  let set p v = function
    | Bot_except m -> Bot_except
        (if L.beq v L.bot then ATree.remove p m else ATree.set p v m)
    | Top_except m -> Top_except
        (if L.beq v L.top then ATree.remove p m else ATree.set p v m)
  
  (** val beq : t -> t -> bool **)
  
  let beq x y =
    match x with
      | Bot_except m ->
          (match y with
             | Bot_except n -> ATree.beq L.beq m n
             | Top_except t0 -> false)
      | Top_except m ->
          (match y with
             | Bot_except t0 -> false
             | Top_except n -> ATree.beq L.beq m n)
  
  (** val bot : t_ **)
  
  let bot =
    Bot_except ATree.empty
  
  (** val top : t_ **)
  
  let top =
    Top_except ATree.empty
  
  (** val opt_lub : L.t -> L.t -> L.t option **)
  
  let opt_lub x y =
    let z = L.lub x y in if L.beq z L.top then None else Some z
  
  (** val lub : t -> t -> t **)
  
  let lub x y =
    match x with
      | Bot_except m ->
          (match y with
             | Bot_except n -> Bot_except
                 (ATree.combine (fun a b ->
                   match a with
                     | Some u ->
                         (match b with
                            | Some v -> Some (L.lub u v)
                            | None -> a)
                     | None -> b) m n)
             | Top_except n -> Top_except
                 (ATree.combine (fun a b ->
                   match a with
                     | Some u ->
                         (match b with
                            | Some v -> opt_lub u v
                            | None -> None)
                     | None -> b) m n))
      | Top_except m ->
          (match y with
             | Bot_except n -> Top_except
                 (ATree.combine (fun a b ->
                   match a with
                     | Some u ->
                         (match b with
                            | Some v -> opt_lub u v
                            | None -> a)
                     | None -> None) m n)
             | Top_except n -> Top_except
                 (ATree.combine (fun a b ->
                   match a with
                     | Some u ->
                         (match b with
                            | Some v -> opt_lub u v
                            | None -> None)
                     | None -> None) m n))
 end

module LFSet = 
 functor (S:S) ->
 struct 
  type t = S.t
  
  (** val beq : t -> t -> bool **)
  
  let beq =
    S.equal
  
  (** val bot : t **)
  
  let bot =
    S.empty
  
  (** val lub : t -> t -> t **)
  
  let lub =
    S.union
 end

module LFlat = 
 functor (X:EQUALITY_TYPE) ->
 struct 
  type t_ =
    | Bot
    | Inj of X.t
    | Top
  
  (** val t__rect : 'a1 -> (X.t -> 'a1) -> 'a1 -> t_ -> 'a1 **)
  
  let t__rect f f0 f1 = function
    | Bot -> f
    | Inj x -> f0 x
    | Top -> f1
  
  (** val t__rec : 'a1 -> (X.t -> 'a1) -> 'a1 -> t_ -> 'a1 **)
  
  let t__rec f f0 f1 = function
    | Bot -> f
    | Inj x -> f0 x
    | Top -> f1
  
  type t = t_
  
  (** val beq : t -> t -> bool **)
  
  let beq x y =
    match x with
      | Bot -> (match y with
                  | Bot -> true
                  | _ -> false)
      | Inj u ->
          (match y with
             | Inj v -> if X.eq u v then true else false
             | _ -> false)
      | Top -> (match y with
                  | Top -> true
                  | _ -> false)
  
  (** val bot : t **)
  
  let bot =
    Bot
  
  (** val top : t **)
  
  let top =
    Top
  
  (** val lub : t -> t -> t **)
  
  let lub x y =
    match x with
      | Bot -> y
      | Inj a ->
          (match y with
             | Bot -> x
             | Inj b -> if X.eq a b then Inj a else Top
             | Top -> Top)
      | Top -> (match y with
                  | Bot -> x
                  | _ -> Top)
 end

module LBoolean = 
 struct 
  type t = bool
  
  (** val beq : t -> t -> bool **)
  
  let beq =
    eqb
  
  (** val bot : bool **)
  
  let bot =
    false
  
  (** val top : bool **)
  
  let top =
    true
  
  (** val lub : t -> t -> bool **)
  
  let lub x y =
    if x then true else y
 end

module AtomSet = 
 struct 
  type incl_dec_prop = AtomImpl.atom list -> AtomImpl.atom list -> __ -> bool
  
  (** val incl_dec_aux :
      nat -> AtomImpl.atom list -> AtomImpl.atom list -> bool **)
  
  let incl_dec_aux n l1 l2 =
    lt_wf_rec n (fun n0 h l3 l4 _ ->
      match l3 with
        | [] -> true
        | a::l5 ->
            let s =
              h (length (remove AtomImpl.eq_atom_dec a l5)) __
                (remove AtomImpl.eq_atom_dec a l5) l4
            in
            if s __ then in_dec AtomImpl.eq_atom_dec a l4 else false) l1 l2
      __
  
  (** val incl_dec : AtomImpl.atom list -> AtomImpl.atom list -> bool **)
  
  let incl_dec l1 =
    let j = incl_dec_aux (length l1) in (fun l2 -> j l1 l2)
  
  (** val set_eq_dec : AtomImpl.atom set -> AtomImpl.atom set -> bool **)
  
  let set_eq_dec l1 l2 =
    let s = incl_dec l1 l2 in if s then incl_dec l2 l1 else false
 end

module Dominators = 
 struct 
  type coq_BoundedSet =
    AtomImpl.atom set
    (* singleton inductive, whose constructor was mkBoundedSet *)
  
  (** val coq_BoundedSet_rect :
      AtomImpl.atom set -> (AtomImpl.atom set -> __ -> 'a1) -> coq_BoundedSet
      -> 'a1 **)
  
  let coq_BoundedSet_rect bound f b =
    f b __
  
  (** val coq_BoundedSet_rec :
      AtomImpl.atom set -> (AtomImpl.atom set -> __ -> 'a1) -> coq_BoundedSet
      -> 'a1 **)
  
  let coq_BoundedSet_rec bound f b =
    f b __
  
  (** val bs_contents :
      AtomImpl.atom set -> coq_BoundedSet -> AtomImpl.atom set **)
  
  let bs_contents bound b =
    b
  
  type t = coq_BoundedSet
  
  (** val eq_dec : AtomImpl.atom set -> t -> t -> bool **)
  
  let eq_dec bound x y =
    AtomSet.set_eq_dec x y
  
  (** val beq : AtomImpl.atom set -> t -> t -> bool **)
  
  let beq bound x y =
    if eq_dec bound x y then true else false
  
  (** val top : AtomImpl.atom set -> t **)
  
  let top bound =
    empty_set
  
  (** val bot : AtomImpl.atom set -> t **)
  
  let bot bound =
    bound
  
  (** val lub : AtomImpl.atom set -> t -> t -> t **)
  
  let lub bound x y =
    set_inter AtomImpl.eq_atom_dec x y
  
  (** val add : AtomImpl.atom set -> t -> AtomImpl.atom -> t **)
  
  let add bound x a =
    if in_dec AtomImpl.eq_atom_dec a bound then a::x else x
  
  (** val lubs : AtomImpl.atom set -> t list -> t **)
  
  let lubs bound pds =
    fold_left (fun acc p -> lub bound acc p) pds (bot bound)
 end

