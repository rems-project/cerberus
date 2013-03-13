open Datatypes
open FMapList
open Int0
open Peano

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Raw = 
 functor (I:Int) ->
 functor (X:OrderedType.OrderedType) ->
 struct 
  type key = X.t
  
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.int
  
  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int ->
      'a2) -> 'a1 tree -> 'a2 **)
  
  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, e, t2, i) ->
    f0 t1 (tree_rect f f0 t1) k e t2 (tree_rect f f0 t2) i
  
  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int ->
      'a2) -> 'a1 tree -> 'a2 **)
  
  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, e, t2, i) ->
    f0 t1 (tree_rec f f0 t1) k e t2 (tree_rec f f0 t2) i
  
  (** val height : 'a1 tree -> I.int **)
  
  let height = function
  | Leaf -> I._0
  | Node (t0, k, e, t1, h) -> h
  
  (** val cardinal : 'a1 tree -> nat **)
  
  let rec cardinal = function
  | Leaf -> O
  | Node (l, k, e, r, i) -> S (plus (cardinal l) (cardinal r))
  
  (** val empty : 'a1 tree **)
  
  let empty =
    Leaf
  
  (** val is_empty : 'a1 tree -> bool **)
  
  let is_empty = function
  | Leaf -> true
  | Node (t0, k, e, t1, i) -> false
  
  (** val mem : X.t -> 'a1 tree -> bool **)
  
  let rec mem x = function
  | Leaf -> false
  | Node (l, y, e, r, i) ->
    (match X.compare x y with
     | OrderedType.LT -> mem x l
     | OrderedType.EQ -> true
     | OrderedType.GT -> mem x r)
  
  (** val find : X.t -> 'a1 tree -> 'a1 option **)
  
  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, i) ->
    (match X.compare x y with
     | OrderedType.LT -> find x l
     | OrderedType.EQ -> Some d
     | OrderedType.GT -> find x r)
  
  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let create l x e r =
    Node (l, x, e, r, (I.plus (I.max (height l) (height r)) I._1))
  
  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let assert_false =
    create
  
  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.plus hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, i) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, i0) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.plus hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, i) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, i0) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r
  
  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | OrderedType.LT -> bal (add x d l) y d' r
     | OrderedType.EQ -> Node (l, y, d, r, h)
     | OrderedType.GT -> bal l y d' (add x d r))
  
  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod **)
  
  let rec remove_min l x d r =
    match l with
    | Leaf -> Coq_pair (r, (Coq_pair (x, d)))
    | Node (ll, lx, ld, lr, lh) ->
      let Coq_pair (l', m) = remove_min ll lx ld lr in
      Coq_pair ((bal l' x d r), m)
  
  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, k, e, t1, i) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, h2) ->
         let Coq_pair (s2', p) = remove_min l2 x2 d2 r2 in
         let Coq_pair (x, d) = p in bal s1 x d s2')
  
  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)
  
  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, h) ->
    (match X.compare x y with
     | OrderedType.LT -> bal (remove x l) y d r
     | OrderedType.EQ -> merge l r
     | OrderedType.GT -> bal l y d (remove x r))
  
  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.plus rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.plus lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)
  
  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }
  
  (** val triple_rect :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2 **)
  
  let triple_rect f t0 =
    let { t_left = x; t_opt = x0; t_right = x1 } = t0 in f x x0 x1
  
  (** val triple_rec :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2 **)
  
  let triple_rec f t0 =
    let { t_left = x; t_opt = x0; t_right = x1 } = t0 in f x x0 x1
  
  (** val t_left : 'a1 triple -> 'a1 tree **)
  
  let t_left t0 =
    t0.t_left
  
  (** val t_opt : 'a1 triple -> 'a1 option **)
  
  let t_opt t0 =
    t0.t_opt
  
  (** val t_right : 'a1 triple -> 'a1 tree **)
  
  let t_right t0 =
    t0.t_right
  
  (** val split : X.t -> 'a1 tree -> 'a1 triple **)
  
  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, h) ->
    (match X.compare x y with
     | OrderedType.LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | OrderedType.EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | OrderedType.GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })
  
  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (t0, k, e, t1, i) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, i0) ->
         let Coq_pair (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')
  
  (** val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list **)
  
  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, i) ->
    elements_aux ((Coq_pair (x, d))::(elements_aux acc r)) l
  
  (** val elements : 'a1 tree -> (key, 'a1) prod list **)
  
  let elements m =
    elements_aux [] m
  
  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)
  
  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, i) -> fold f r (f x d (fold f l a))
  
  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration
  
  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)
  
  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)
  
  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)
  
  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)
  
  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)
  
  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, h) -> cons l (More (x, d, r, e))
  
  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)
  
  let equal_more cmp0 x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | OrderedType.EQ -> if cmp0 d1 d2 then cont (cons r2 e3) else false
     | _ -> false)
  
  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)
  
  let rec equal_cont cmp0 m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, i) ->
      equal_cont cmp0 l1 (equal_more cmp0 x1 d1 (equal_cont cmp0 r1 cont)) e2
  
  (** val equal_end : 'a1 enumeration -> bool **)
  
  let equal_end = function
  | End -> true
  | More (k, e, t0, e0) -> false
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)
  
  let equal cmp0 m1 m2 =
    equal_cont cmp0 m1 equal_end (cons m2 End)
  
  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)
  
  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)
  
  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)
  
  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)
  
  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)
  
  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))
  
  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)
  
  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, h1) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (t0, k, y, t1, i) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2')
              (map2_opt f mapl mapr r1 r2')))
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)
  
  let map2 f =
    map2_opt (fun x d o -> f (Some d) o)
      (map_option (fun x d -> f (Some d) None))
      (map_option (fun x d' -> f None (Some d')))
  
  module Proofs = 
   struct 
    module MX = OrderedType.OrderedTypeFacts(X)
    
    module PX = OrderedType.KeyOrderedType(X)
    
    module L = Raw(X)
    
    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * bool * 'elt coq_R_mem
    
    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)
    
    let rec coq_R_mem_rect x f f0 f1 f2 m b = function
    | R_mem_0 m0 -> f m0 __
    | R_mem_1 (m0, l, y, _x, r0, _x0, res, r1) ->
      f0 m0 l y _x r0 _x0 __ __ __ res r1
        (coq_R_mem_rect x f f0 f1 f2 l res r1)
    | R_mem_2 (m0, l, y, _x, r0, _x0) -> f1 m0 l y _x r0 _x0 __ __ __
    | R_mem_3 (m0, l, y, _x, r0, _x0, res, r1) ->
      f2 m0 l y _x r0 _x0 __ __ __ res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 res r1)
    
    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)
    
    let rec coq_R_mem_rec x f f0 f1 f2 m b = function
    | R_mem_0 m0 -> f m0 __
    | R_mem_1 (m0, l, y, _x, r0, _x0, res, r1) ->
      f0 m0 l y _x r0 _x0 __ __ __ res r1
        (coq_R_mem_rec x f f0 f1 f2 l res r1)
    | R_mem_2 (m0, l, y, _x, r0, _x0) -> f1 m0 l y _x r0 _x0 __ __ __
    | R_mem_3 (m0, l, y, _x, r0, _x0, res, r1) ->
      f2 m0 l y _x r0 _x0 __ __ __ res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 res r1)
    
    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt option * 'elt coq_R_find
    
    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option ->
        'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
        coq_R_find -> 'a2 **)
    
    let rec coq_R_find_rect x f f0 f1 f2 m o = function
    | R_find_0 m0 -> f m0 __
    | R_find_1 (m0, l, y, d, r0, _x, res, r1) ->
      f0 m0 l y d r0 _x __ __ __ res r1
        (coq_R_find_rect x f f0 f1 f2 l res r1)
    | R_find_2 (m0, l, y, d, r0, _x) -> f1 m0 l y d r0 _x __ __ __
    | R_find_3 (m0, l, y, d, r0, _x, res, r1) ->
      f2 m0 l y d r0 _x __ __ __ res r1
        (coq_R_find_rect x f f0 f1 f2 r0 res r1)
    
    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option ->
        'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
        coq_R_find -> 'a2 **)
    
    let rec coq_R_find_rec x f f0 f1 f2 m o = function
    | R_find_0 m0 -> f m0 __
    | R_find_1 (m0, l, y, d, r0, _x, res, r1) ->
      f0 m0 l y d r0 _x __ __ __ res r1
        (coq_R_find_rec x f f0 f1 f2 l res r1)
    | R_find_2 (m0, l, y, d, r0, _x) -> f1 m0 l y d r0 _x __ __ __
    | R_find_3 (m0, l, y, d, r0, _x, res, r1) ->
      f2 m0 l y d r0 _x __ __ __ res r1
        (coq_R_find_rec x f f0 f1 f2 r0 res r1)
    
    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * 
       I.int
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * 
       I.int
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
    
    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
        __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_bal -> 'a2 **)
    
    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 l x d r t0 = function
    | R_bal_0 (x0, x1, x2, x3) -> f x0 x1 x2 x3 __ __ __
    | R_bal_1 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f0 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f1 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f2 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13 __
    | R_bal_4 (x0, x1, x2, x3) -> f3 x0 x1 x2 x3 __ __ __ __ __
    | R_bal_5 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f4 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_6 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f5 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f6 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13
        __
    | R_bal_8 (x0, x1, x2, x3) -> f7 x0 x1 x2 x3 __ __ __ __
    
    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
        __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_bal -> 'a2 **)
    
    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 l x d r t0 = function
    | R_bal_0 (x0, x1, x2, x3) -> f x0 x1 x2 x3 __ __ __
    | R_bal_1 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f0 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f1 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f2 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13 __
    | R_bal_4 (x0, x1, x2, x3) -> f3 x0 x1 x2 x3 __ __ __ __ __
    | R_bal_5 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f4 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_6 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f5 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f6 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13
        __
    | R_bal_8 (x0, x1, x2, x3) -> f7 x0 x1 x2 x3 __ __ __ __
    
    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt tree * 'elt coq_R_add
    
    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add
        -> 'a2 **)
    
    let rec coq_R_add_rect x d f f0 f1 f2 m t0 = function
    | R_add_0 m0 -> f m0 __
    | R_add_1 (m0, l, y, d', r0, h, res, r1) ->
      f0 m0 l y d' r0 h __ __ __ res r1
        (coq_R_add_rect x d f f0 f1 f2 l res r1)
    | R_add_2 (m0, l, y, d', r0, h) -> f1 m0 l y d' r0 h __ __ __
    | R_add_3 (m0, l, y, d', r0, h, res, r1) ->
      f2 m0 l y d' r0 h __ __ __ res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 res r1)
    
    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add
        -> 'a2 **)
    
    let rec coq_R_add_rec x d f f0 f1 f2 m t0 = function
    | R_add_0 m0 -> f m0 __
    | R_add_1 (m0, l, y, d', r0, h, res, r1) ->
      f0 m0 l y d' r0 h __ __ __ res r1
        (coq_R_add_rec x d f f0 f1 f2 l res r1)
    | R_add_2 (m0, l, y, d', r0, h) -> f1 m0 l y d' r0 h __ __ __
    | R_add_3 (m0, l, y, d', r0, h, res, r1) ->
      f2 m0 l y d' r0 h __ __ __ res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 res r1)
    
    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.int * ('elt tree, (key, 'elt) prod) prod
       * 'elt coq_R_remove_min * 'elt tree * (key, 'elt) prod
    
    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
        -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 **)
    
    let rec coq_R_remove_min_rect f f0 l x d r p = function
    | R_remove_min_0 (l0, x0, d0, r1) -> f l0 x0 d0 r1 __
    | R_remove_min_1 (l0, x0, d0, r1, ll, lx, ld, lr, _x, res, r2, l', m) ->
      f0 l0 x0 d0 r1 ll lx ld lr _x __ res r2
        (coq_R_remove_min_rect f f0 ll lx ld lr res r2) l' m __
    
    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
        -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 **)
    
    let rec coq_R_remove_min_rec f f0 l x d r p = function
    | R_remove_min_0 (l0, x0, d0, r1) -> f l0 x0 d0 r1 __
    | R_remove_min_1 (l0, x0, d0, r1, ll, lx, ld, lr, _x, res, r2, l', m) ->
      f0 l0 x0 d0 r1 ll lx ld lr _x __ res r2
        (coq_R_remove_min_rec f f0 ll lx ld lr res r2) l' m __
    
    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.int
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.int * 'elt tree * key * 'elt * 'elt tree * I.int * 'elt tree
       * (key, 'elt) prod * key * 'elt
    
    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)
    
    let coq_R_merge_rect f f0 f1 s1 s2 t0 = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2
        (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __
    
    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)
    
    let coq_R_merge_rec f f0 f1 s1 s2 t0 = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2
        (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __
    
    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.int * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.int * 'elt tree * 'elt coq_R_remove
    
    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 **)
    
    let rec coq_R_remove_rect x f f0 f1 f2 m t0 = function
    | R_remove_0 m0 -> f m0 __
    | R_remove_1 (m0, l, y, d, r0, _x, res, r1) ->
      f0 m0 l y d r0 _x __ __ __ res r1
        (coq_R_remove_rect x f f0 f1 f2 l res r1)
    | R_remove_2 (m0, l, y, d, r0, _x) -> f1 m0 l y d r0 _x __ __ __
    | R_remove_3 (m0, l, y, d, r0, _x, res, r1) ->
      f2 m0 l y d r0 _x __ __ __ res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 res r1)
    
    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 **)
    
    let rec coq_R_remove_rec x f f0 f1 f2 m t0 = function
    | R_remove_0 m0 -> f m0 __
    | R_remove_1 (m0, l, y, d, r0, _x, res, r1) ->
      f0 m0 l y d r0 _x __ __ __ res r1
        (coq_R_remove_rec x f f0 f1 f2 l res r1)
    | R_remove_2 (m0, l, y, d, r0, _x) -> f1 m0 l y d r0 _x __ __ __
    | R_remove_3 (m0, l, y, d, r0, _x, res, r1) ->
      f2 m0 l y d r0 _x __ __ __ res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 res r1)
    
    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.int
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt tree * (key, 'elt) prod
    
    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2 **)
    
    let coq_R_concat_rect f f0 f1 m1 m2 t0 = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2
        (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __
    
    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2 **)
    
    let coq_R_concat_rec f f0 f1 m1 m2 t0 = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2
        (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __
    
    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    
    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
        'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree
        -> 'a1 triple -> 'a1 coq_R_split -> 'a2 **)
    
    let rec coq_R_split_rect x f f0 f1 f2 m t0 = function
    | R_split_0 m0 -> f m0 __
    | R_split_1 (m0, l, y, d, r0, _x, res, r1, ll, o, rl) ->
      f0 m0 l y d r0 _x __ __ __ res r1
        (coq_R_split_rect x f f0 f1 f2 l res r1) ll o rl __
    | R_split_2 (m0, l, y, d, r0, _x) -> f1 m0 l y d r0 _x __ __ __
    | R_split_3 (m0, l, y, d, r0, _x, res, r1, rl, o, rr) ->
      f2 m0 l y d r0 _x __ __ __ res r1
        (coq_R_split_rect x f f0 f1 f2 r0 res r1) rl o rr __
    
    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
        'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree
        -> 'a1 triple -> 'a1 coq_R_split -> 'a2 **)
    
    let rec coq_R_split_rec x f f0 f1 f2 m t0 = function
    | R_split_0 m0 -> f m0 __
    | R_split_1 (m0, l, y, d, r0, _x, res, r1, ll, o, rl) ->
      f0 m0 l y d r0 _x __ __ __ res r1
        (coq_R_split_rec x f f0 f1 f2 l res r1) ll o rl __
    | R_split_2 (m0, l, y, d, r0, _x) -> f1 m0 l y d r0 _x __ __ __
    | R_split_3 (m0, l, y, d, r0, _x, res, r1, rl, o, rr) ->
      f2 m0 l y d r0 _x __ __ __ res r1
        (coq_R_split_rec x f f0 f1 f2 r0 res r1) rl o rr __
    
    type ('elt, 'elt') coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.int * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
       * 'elt' tree * ('elt, 'elt') coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.int * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
       * ('elt, 'elt') coq_R_map_option
    
    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)
    
    let rec coq_R_map_option_rect f f0 f1 f2 m t0 = function
    | R_map_option_0 m0 -> f0 m0 __
    | R_map_option_1 (m0, l, x, d, r0, _x, d', res0, r1, res, r2) ->
      f1 m0 l x d r0 _x __ d' __ res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l res0 r1) res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 res r2)
    | R_map_option_2 (m0, l, x, d, r0, _x, res0, r1, res, r2) ->
      f2 m0 l x d r0 _x __ __ res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l res0 r1) res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 res r2)
    
    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)
    
    let rec coq_R_map_option_rec f f0 f1 f2 m t0 = function
    | R_map_option_0 m0 -> f0 m0 __
    | R_map_option_1 (m0, l, x, d, r0, _x, d', res0, r1, res, r2) ->
      f1 m0 l x d r0 _x __ d' __ res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l res0 r1) res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 res r2)
    | R_map_option_2 (m0, l, x, d, r0, _x, res0, r1, res, r2) ->
      f2 m0 l x d r0 _x __ __ res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l res0 r1) res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 res r2)
    
    type ('elt, 'elt', 'elt'') coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'elt' tree
    | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.int
    | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree * 
       I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree * 
       I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    
    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
        I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __
        -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree
        -> key -> 'a2 -> 'a2 tree -> I.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
        'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4 **)
    
    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 m1 m2 t0 = function
    | R_map2_opt_0 (m3, m4) -> f0 m3 m4 __
    | R_map2_opt_1 (m3, m4, l1, x1, d1, r1, _x) ->
      f1 m3 m4 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2
        (m3, m4, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2', o2, r2',
         e, res0, r0, res, r2) ->
      f2 m3 m4 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        res0 r0 (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' res0 r0)
        res r2 (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' res r2)
    | R_map2_opt_3
        (m3, m4, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2', o2, r2',
         res0, r0, res, r2) ->
      f3 m3 m4 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ res0
        r0 (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' res0 r0) res
        r2 (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' res r2)
    
    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
        I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __
        -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree
        -> key -> 'a2 -> 'a2 tree -> I.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
        'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4 **)
    
    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 m1 m2 t0 = function
    | R_map2_opt_0 (m3, m4) -> f0 m3 m4 __
    | R_map2_opt_1 (m3, m4, l1, x1, d1, r1, _x) ->
      f1 m3 m4 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2
        (m3, m4, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2', o2, r2',
         e, res0, r0, res, r2) ->
      f2 m3 m4 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' res0 r0)
        res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' res r2)
    | R_map2_opt_3
        (m3, m4, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2', o2, r2',
         res0, r0, res, r2) ->
      f3 m3 m4 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ res0
        r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' res0 r0) res r2
        (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' res r2)
    
    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)
    
    let fold' f s =
      L.fold f (elements s)
    
    (** val flatten_e : 'a1 enumeration -> (key, 'a1) prod list **)
    
    let rec flatten_e = function
    | End -> []
    | More (x, e0, t0, r) ->
      (Coq_pair (x, e0))::(app (elements t0) (flatten_e r))
   end
 end

module IntMake = 
 functor (I:Int) ->
 functor (X:OrderedType.OrderedType) ->
 struct 
  module E = X
  
  module Raw = Raw(I)(X)
  
  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)
  
  (** val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2 **)
  
  let bst_rect f b =
    f b __
  
  (** val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2 **)
  
  let bst_rec f b =
    f b __
  
  (** val this : 'a1 bst -> 'a1 Raw.tree **)
  
  let this b =
    b
  
  type 'elt t = 'elt bst
  
  type key = E.t
  
  (** val empty : 'a1 t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : 'a1 t -> bool **)
  
  let is_empty m =
    Raw.is_empty (this m)
  
  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let add x e m =
    Raw.add x e (this m)
  
  (** val remove : key -> 'a1 t -> 'a1 t **)
  
  let remove x m =
    Raw.remove x (this m)
  
  (** val mem : key -> 'a1 t -> bool **)
  
  let mem x m =
    Raw.mem x (this m)
  
  (** val find : key -> 'a1 t -> 'a1 option **)
  
  let find x m =
    Raw.find x (this m)
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    Raw.map f (this m)
  
  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let mapi f m =
    Raw.mapi f (this m)
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)
  
  let map2 f m m' =
    Raw.map2 f (this m) (this m')
  
  (** val elements : 'a1 t -> (key, 'a1) prod list **)
  
  let elements m =
    Raw.elements (this m)
  
  (** val cardinal : 'a1 t -> nat **)
  
  let cardinal m =
    Raw.cardinal (this m)
  
  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let fold f m i =
    Raw.fold f (this m) i
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let equal cmp0 m m' =
    Raw.equal cmp0 (this m) (this m')
 end

module IntMake_ord = 
 functor (I:Int) ->
 functor (X:OrderedType.OrderedType) ->
 functor (D:OrderedType.OrderedType) ->
 struct 
  module Data = D
  
  module MapS = IntMake(I)(X)
  
  module LO = Make_ord(X)(D)
  
  module R = MapS.Raw
  
  module P = MapS.Raw.Proofs
  
  type t = D.t MapS.t
  
  (** val cmp : D.t -> D.t -> bool **)
  
  let cmp e e' =
    match D.compare e e' with
    | OrderedType.EQ -> true
    | _ -> false
  
  (** val compare_more :
      X.t -> D.t -> (D.t R.enumeration -> comparison) -> D.t R.enumeration ->
      comparison **)
  
  let compare_more x1 d1 cont = function
  | R.End -> Gt
  | R.More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | OrderedType.LT -> Lt
     | OrderedType.EQ ->
       (match D.compare d1 d2 with
        | OrderedType.LT -> Lt
        | OrderedType.EQ -> cont (R.cons r2 e3)
        | OrderedType.GT -> Gt)
     | OrderedType.GT -> Gt)
  
  (** val compare_cont :
      D.t R.tree -> (D.t R.enumeration -> comparison) -> D.t R.enumeration ->
      comparison **)
  
  let rec compare_cont s1 cont e2 =
    match s1 with
    | R.Leaf -> cont e2
    | R.Node (l1, x1, d1, r1, i) ->
      compare_cont l1 (compare_more x1 d1 (compare_cont r1 cont)) e2
  
  (** val compare_end : D.t R.enumeration -> comparison **)
  
  let compare_end = function
  | R.End -> Eq
  | R.More (k, t0, t1, e) -> Lt
  
  (** val compare_pure : D.t R.tree -> D.t R.tree -> comparison **)
  
  let compare_pure s1 s2 =
    compare_cont s1 compare_end (R.cons s2 (Obj.magic MapS.Raw.End))
  
  (** val compare : t -> t -> t OrderedType.coq_Compare **)
  
  let compare s s' =
    match Obj.magic compare_pure s s' with
    | Eq -> OrderedType.EQ
    | Lt -> OrderedType.LT
    | Gt -> OrderedType.GT
  
  (** val selements : t -> D.t LO.MapS.slist **)
  
  let selements m1 =
    MapS.Raw.elements (MapS.this m1)
 end

module Make = 
 functor (X:OrderedType.OrderedType) ->
 IntMake(Z_as_Int)(X)

module Make_ord = 
 functor (X:OrderedType.OrderedType) ->
 functor (D:OrderedType.OrderedType) ->
 IntMake_ord(Z_as_Int)(X)(D)

