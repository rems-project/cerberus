open Datatypes
open Int0
open MSetInterface
open Orders
open OrdersFacts
open Peano

module Ops = 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct 
  type elt = X.t
  
  type tree =
  | Leaf
  | Node of tree * X.t * tree * I.int
  
  type t = tree
  
  (** val height : t -> I.int **)
  
  let height = function
  | Leaf -> I._0
  | Node (t0, t1, t2, h) -> h
  
  (** val cardinal : t -> nat **)
  
  let rec cardinal = function
  | Leaf -> O
  | Node (l, t0, r, i) -> S (plus (cardinal l) (cardinal r))
  
  (** val empty : tree **)
  
  let empty =
    Leaf
  
  (** val is_empty : tree -> bool **)
  
  let is_empty = function
  | Leaf -> true
  | Node (t0, t1, t2, i) -> false
  
  (** val mem : X.t -> tree -> bool **)
  
  let rec mem x = function
  | Leaf -> false
  | Node (l, y, r, i) ->
    (match X.compare x y with
     | Eq -> true
     | Lt -> mem x l
     | Gt -> mem x r)
  
  (** val singleton : X.t -> tree **)
  
  let singleton x =
    Node (Leaf, x, Leaf, I._1)
  
  (** val create : tree -> X.t -> tree -> tree **)
  
  let create l x r =
    Node (l, x, r, (I.plus (I.max (height l) (height r)) I._1))
  
  (** val assert_false : tree -> X.t -> tree -> tree **)
  
  let assert_false =
    create
  
  (** val bal : t -> X.t -> t -> tree **)
  
  let bal l x r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.plus hr I._2)
    then (match l with
          | Leaf -> assert_false l x r
          | Node (ll, lx, lr, i) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx (create lr x r)
            else (match lr with
                  | Leaf -> assert_false l x r
                  | Node (lrl, lrx, lrr, i0) ->
                    create (create ll lx lrl) lrx (create lrr x r)))
    else if I.gt_le_dec hr (I.plus hl I._2)
         then (match r with
               | Leaf -> assert_false l x r
               | Node (rl, rx, rr, i) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false l x r
                       | Node (rll, rlx, rlr, i0) ->
                         create (create l x rll) rlx (create rlr rx rr)))
         else create l x r
  
  (** val add : X.t -> tree -> tree **)
  
  let rec add x = function
  | Leaf -> Node (Leaf, x, Leaf, I._1)
  | Node (l, y, r, h) ->
    (match X.compare x y with
     | Eq -> Node (l, y, r, h)
     | Lt -> bal (add x l) y r
     | Gt -> bal l y (add x r))
  
  (** val join : tree -> elt -> t -> t **)
  
  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, lr, lh) ->
    (fun x ->
      let rec join_aux r = match r with
      | Leaf -> add x l
      | Node (rl, rx, rr, rh) ->
        if I.gt_le_dec lh (I.plus rh I._2)
        then bal ll lx (join lr x r)
        else if I.gt_le_dec rh (I.plus lh I._2)
             then bal (join_aux rl) rx rr
             else create l x r
      in join_aux)
  
  (** val remove_min : tree -> elt -> t -> (t, elt) prod **)
  
  let rec remove_min l x r =
    match l with
    | Leaf -> Coq_pair (r, x)
    | Node (ll, lx, lr, lh) ->
      let Coq_pair (l', m) = remove_min ll lx lr in
      Coq_pair ((bal l' x r), m)
  
  (** val merge : tree -> tree -> tree **)
  
  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, t1, t2, i) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, h2) ->
         let Coq_pair (s2', m) = remove_min l2 x2 r2 in bal s1 m s2')
  
  (** val remove : X.t -> tree -> tree **)
  
  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, r, h) ->
    (match X.compare x y with
     | Eq -> merge l r
     | Lt -> bal (remove x l) y r
     | Gt -> bal l y (remove x r))
  
  (** val min_elt : tree -> X.t option **)
  
  let rec min_elt = function
  | Leaf -> None
  | Node (l, y, t0, i) ->
    (match l with
     | Leaf -> Some y
     | Node (t1, t2, t3, i0) -> min_elt l)
  
  (** val max_elt : tree -> X.t option **)
  
  let rec max_elt = function
  | Leaf -> None
  | Node (t0, y, r, i) ->
    (match r with
     | Leaf -> Some y
     | Node (t1, t2, t3, i0) -> max_elt r)
  
  (** val choose : tree -> X.t option **)
  
  let choose =
    min_elt
  
  (** val concat : tree -> tree -> tree **)
  
  let concat s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, t1, t2, i) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, i0) ->
         let Coq_pair (s2', m) = remove_min l2 x2 r2 in join s1 m s2')
  
  type triple = { t_left : t; t_in : bool; t_right : t }
  
  (** val t_left : triple -> t **)
  
  let t_left t0 =
    t0.t_left
  
  (** val t_in : triple -> bool **)
  
  let t_in t0 =
    t0.t_in
  
  (** val t_right : triple -> t **)
  
  let t_right t0 =
    t0.t_right
  
  (** val split : X.t -> tree -> triple **)
  
  let rec split x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (l, y, r, h) ->
    (match X.compare x y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b; t_right = rl } = split x l in
       { t_left = ll; t_in = b; t_right = (join rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b; t_right = rr } = split x r in
       { t_left = (join l y rl); t_in = b; t_right = rr })
  
  (** val inter : tree -> tree -> tree **)
  
  let rec inter s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (t0, t1, t2, i) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then join (inter l1 l2') x1 (inter r1 r2')
         else concat (inter l1 l2') (inter r1 r2'))
  
  (** val diff : tree -> tree -> tree **)
  
  let rec diff s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t0, t1, t2, i) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then concat (diff l1 l2') (diff r1 r2')
         else join (diff l1 l2') x1 (diff r1 r2'))
  
  (** val union : tree -> tree -> tree **)
  
  let rec union s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t0, t1, t2, i) ->
         let { t_left = l2'; t_in = x; t_right = r2' } = split x1 s2 in
         join (union l1 l2') x1 (union r1 r2'))
  
  (** val elements_aux : X.t list -> t -> X.t list **)
  
  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, r, i) -> elements_aux (x::(elements_aux acc r)) l
  
  (** val elements : t -> X.t list **)
  
  let elements =
    elements_aux []
  
  (** val filter_acc : (elt -> bool) -> tree -> tree -> tree **)
  
  let rec filter_acc f acc = function
  | Leaf -> acc
  | Node (l, x, r, h) ->
    filter_acc f (filter_acc f (if f x then add x acc else acc) l) r
  
  (** val filter : (elt -> bool) -> tree -> tree **)
  
  let filter f =
    filter_acc f Leaf
  
  (** val partition_acc :
      (elt -> bool) -> (t, t) prod -> t -> (t, t) prod **)
  
  let rec partition_acc f acc = function
  | Leaf -> acc
  | Node (l, x, r, i) ->
    let Coq_pair (acct, accf) = acc in
    partition_acc f
      (partition_acc f
        (if f x
         then Coq_pair ((add x acct), accf)
         else Coq_pair (acct, (add x accf))) l) r
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition f =
    partition_acc f (Coq_pair (Leaf, Leaf))
  
  (** val for_all : (elt -> bool) -> tree -> bool **)
  
  let rec for_all f = function
  | Leaf -> true
  | Node (l, x, r, i) ->
    if if f x then for_all f l else false then for_all f r else false
  
  (** val exists_ : (elt -> bool) -> tree -> bool **)
  
  let rec exists_ f = function
  | Leaf -> false
  | Node (l, x, r, i) ->
    if if f x then true else exists_ f l then true else exists_ f r
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let rec fold f s a =
    match s with
    | Leaf -> a
    | Node (l, x, r, i) -> fold f r (f x (fold f l a))
  
  (** val subsetl : (t -> bool) -> X.t -> tree -> bool **)
  
  let rec subsetl subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, h2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl subset_l1 x1 l2
     | Gt -> if mem x1 r2 then subset_l1 s2 else false)
  
  (** val subsetr : (t -> bool) -> X.t -> tree -> bool **)
  
  let rec subsetr subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, h2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr subset_r1 x1 r2)
  
  (** val subset : tree -> tree -> bool **)
  
  let rec subset s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> false
       | Node (l2, x2, r2, h2) ->
         (match X.compare x1 x2 with
          | Eq -> if subset l1 l2 then subset r1 r2 else false
          | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
          | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))
  
  type enumeration =
  | End
  | More of elt * t * enumeration
  
  (** val cons : tree -> enumeration -> enumeration **)
  
  let rec cons s e =
    match s with
    | Leaf -> e
    | Node (l, x, r, h) -> cons l (More (x, r, e))
  
  (** val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison **)
  
  let compare_more x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match X.compare x1 x2 with
     | Eq -> cont (cons r2 e3)
     | x -> x)
  
  (** val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison **)
  
  let rec compare_cont s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (l1, x1, r1, i) ->
      compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2
  
  (** val compare_end : enumeration -> comparison **)
  
  let compare_end = function
  | End -> Eq
  | More (e, t0, e0) -> Lt
  
  (** val compare : tree -> tree -> comparison **)
  
  let compare s1 s2 =
    compare_cont s1 compare_end (cons s2 End)
  
  (** val equal : tree -> tree -> bool **)
  
  let equal s1 s2 =
    match compare s1 s2 with
    | Eq -> true
    | _ -> false
 end

module MakeRaw = 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct 
  type elt = X.t
  
  type tree =
  | Leaf
  | Node of tree * X.t * tree * I.int
  
  type t = tree
  
  (** val height : t -> I.int **)
  
  let height = function
  | Leaf -> I._0
  | Node (t0, t1, t2, h) -> h
  
  (** val cardinal : t -> nat **)
  
  let rec cardinal = function
  | Leaf -> O
  | Node (l, t0, r, i) -> S (plus (cardinal l) (cardinal r))
  
  (** val empty : tree **)
  
  let empty =
    Leaf
  
  (** val is_empty : tree -> bool **)
  
  let is_empty = function
  | Leaf -> true
  | Node (t0, t1, t2, i) -> false
  
  (** val mem : X.t -> tree -> bool **)
  
  let rec mem x = function
  | Leaf -> false
  | Node (l, y, r, i) ->
    (match X.compare x y with
     | Eq -> true
     | Lt -> mem x l
     | Gt -> mem x r)
  
  (** val singleton : X.t -> tree **)
  
  let singleton x =
    Node (Leaf, x, Leaf, I._1)
  
  (** val create : tree -> X.t -> tree -> tree **)
  
  let create l x r =
    Node (l, x, r, (I.plus (I.max (height l) (height r)) I._1))
  
  (** val assert_false : tree -> X.t -> tree -> tree **)
  
  let assert_false =
    create
  
  (** val bal : t -> X.t -> t -> tree **)
  
  let bal l x r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.plus hr I._2)
    then (match l with
          | Leaf -> assert_false l x r
          | Node (ll, lx, lr, i) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx (create lr x r)
            else (match lr with
                  | Leaf -> assert_false l x r
                  | Node (lrl, lrx, lrr, i0) ->
                    create (create ll lx lrl) lrx (create lrr x r)))
    else if I.gt_le_dec hr (I.plus hl I._2)
         then (match r with
               | Leaf -> assert_false l x r
               | Node (rl, rx, rr, i) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false l x r
                       | Node (rll, rlx, rlr, i0) ->
                         create (create l x rll) rlx (create rlr rx rr)))
         else create l x r
  
  (** val add : X.t -> tree -> tree **)
  
  let rec add x = function
  | Leaf -> Node (Leaf, x, Leaf, I._1)
  | Node (l, y, r, h) ->
    (match X.compare x y with
     | Eq -> Node (l, y, r, h)
     | Lt -> bal (add x l) y r
     | Gt -> bal l y (add x r))
  
  (** val join : tree -> elt -> t -> t **)
  
  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, lr, lh) ->
    (fun x ->
      let rec join_aux r = match r with
      | Leaf -> add x l
      | Node (rl, rx, rr, rh) ->
        if I.gt_le_dec lh (I.plus rh I._2)
        then bal ll lx (join lr x r)
        else if I.gt_le_dec rh (I.plus lh I._2)
             then bal (join_aux rl) rx rr
             else create l x r
      in join_aux)
  
  (** val remove_min : tree -> elt -> t -> (t, elt) prod **)
  
  let rec remove_min l x r =
    match l with
    | Leaf -> Coq_pair (r, x)
    | Node (ll, lx, lr, lh) ->
      let Coq_pair (l', m) = remove_min ll lx lr in
      Coq_pair ((bal l' x r), m)
  
  (** val merge : tree -> tree -> tree **)
  
  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, t1, t2, i) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, h2) ->
         let Coq_pair (s2', m) = remove_min l2 x2 r2 in bal s1 m s2')
  
  (** val remove : X.t -> tree -> tree **)
  
  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, r, h) ->
    (match X.compare x y with
     | Eq -> merge l r
     | Lt -> bal (remove x l) y r
     | Gt -> bal l y (remove x r))
  
  (** val min_elt : tree -> X.t option **)
  
  let rec min_elt = function
  | Leaf -> None
  | Node (l, y, t0, i) ->
    (match l with
     | Leaf -> Some y
     | Node (t1, t2, t3, i0) -> min_elt l)
  
  (** val max_elt : tree -> X.t option **)
  
  let rec max_elt = function
  | Leaf -> None
  | Node (t0, y, r, i) ->
    (match r with
     | Leaf -> Some y
     | Node (t1, t2, t3, i0) -> max_elt r)
  
  (** val choose : tree -> X.t option **)
  
  let choose =
    min_elt
  
  (** val concat : tree -> tree -> tree **)
  
  let concat s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, t1, t2, i) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, i0) ->
         let Coq_pair (s2', m) = remove_min l2 x2 r2 in join s1 m s2')
  
  type triple = { t_left : t; t_in : bool; t_right : t }
  
  (** val t_left : triple -> t **)
  
  let t_left t0 =
    t0.t_left
  
  (** val t_in : triple -> bool **)
  
  let t_in t0 =
    t0.t_in
  
  (** val t_right : triple -> t **)
  
  let t_right t0 =
    t0.t_right
  
  (** val split : X.t -> tree -> triple **)
  
  let rec split x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (l, y, r, h) ->
    (match X.compare x y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b; t_right = rl } = split x l in
       { t_left = ll; t_in = b; t_right = (join rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b; t_right = rr } = split x r in
       { t_left = (join l y rl); t_in = b; t_right = rr })
  
  (** val inter : tree -> tree -> tree **)
  
  let rec inter s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (t0, t1, t2, i) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then join (inter l1 l2') x1 (inter r1 r2')
         else concat (inter l1 l2') (inter r1 r2'))
  
  (** val diff : tree -> tree -> tree **)
  
  let rec diff s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t0, t1, t2, i) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then concat (diff l1 l2') (diff r1 r2')
         else join (diff l1 l2') x1 (diff r1 r2'))
  
  (** val union : tree -> tree -> tree **)
  
  let rec union s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t0, t1, t2, i) ->
         let { t_left = l2'; t_in = x; t_right = r2' } = split x1 s2 in
         join (union l1 l2') x1 (union r1 r2'))
  
  (** val elements_aux : X.t list -> t -> X.t list **)
  
  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, r, i) -> elements_aux (x::(elements_aux acc r)) l
  
  (** val elements : t -> X.t list **)
  
  let elements =
    elements_aux []
  
  (** val filter_acc : (elt -> bool) -> tree -> tree -> tree **)
  
  let rec filter_acc f acc = function
  | Leaf -> acc
  | Node (l, x, r, h) ->
    filter_acc f (filter_acc f (if f x then add x acc else acc) l) r
  
  (** val filter : (elt -> bool) -> tree -> tree **)
  
  let filter f =
    filter_acc f Leaf
  
  (** val partition_acc :
      (elt -> bool) -> (t, t) prod -> t -> (t, t) prod **)
  
  let rec partition_acc f acc = function
  | Leaf -> acc
  | Node (l, x, r, i) ->
    let Coq_pair (acct, accf) = acc in
    partition_acc f
      (partition_acc f
        (if f x
         then Coq_pair ((add x acct), accf)
         else Coq_pair (acct, (add x accf))) l) r
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition f =
    partition_acc f (Coq_pair (Leaf, Leaf))
  
  (** val for_all : (elt -> bool) -> tree -> bool **)
  
  let rec for_all f = function
  | Leaf -> true
  | Node (l, x, r, i) ->
    if if f x then for_all f l else false then for_all f r else false
  
  (** val exists_ : (elt -> bool) -> tree -> bool **)
  
  let rec exists_ f = function
  | Leaf -> false
  | Node (l, x, r, i) ->
    if if f x then true else exists_ f l then true else exists_ f r
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let rec fold f s a =
    match s with
    | Leaf -> a
    | Node (l, x, r, i) -> fold f r (f x (fold f l a))
  
  (** val subsetl : (t -> bool) -> X.t -> tree -> bool **)
  
  let rec subsetl subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, h2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl subset_l1 x1 l2
     | Gt -> if mem x1 r2 then subset_l1 s2 else false)
  
  (** val subsetr : (t -> bool) -> X.t -> tree -> bool **)
  
  let rec subsetr subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, h2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr subset_r1 x1 r2)
  
  (** val subset : tree -> tree -> bool **)
  
  let rec subset s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> false
       | Node (l2, x2, r2, h2) ->
         (match X.compare x1 x2 with
          | Eq -> if subset l1 l2 then subset r1 r2 else false
          | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
          | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))
  
  type enumeration =
  | End
  | More of elt * t * enumeration
  
  (** val cons : tree -> enumeration -> enumeration **)
  
  let rec cons s e =
    match s with
    | Leaf -> e
    | Node (l, x, r, h) -> cons l (More (x, r, e))
  
  (** val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison **)
  
  let compare_more x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match X.compare x1 x2 with
     | Eq -> cont (cons r2 e3)
     | x -> x)
  
  (** val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison **)
  
  let rec compare_cont s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (l1, x1, r1, i) ->
      compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2
  
  (** val compare_end : enumeration -> comparison **)
  
  let compare_end = function
  | End -> Eq
  | More (e, t0, e0) -> Lt
  
  (** val compare : tree -> tree -> comparison **)
  
  let compare s1 s2 =
    compare_cont s1 compare_end (cons s2 End)
  
  (** val equal : tree -> tree -> bool **)
  
  let equal s1 s2 =
    match compare s1 s2 with
    | Eq -> true
    | _ -> false
  
  (** val ltb_tree : X.t -> tree -> bool **)
  
  let rec ltb_tree x = function
  | Leaf -> true
  | Node (l, y, r, i) ->
    (match X.compare x y with
     | Gt -> if ltb_tree x l then ltb_tree x r else false
     | _ -> false)
  
  (** val gtb_tree : X.t -> tree -> bool **)
  
  let rec gtb_tree x = function
  | Leaf -> true
  | Node (l, y, r, i) ->
    (match X.compare x y with
     | Lt -> if gtb_tree x l then gtb_tree x r else false
     | _ -> false)
  
  (** val isok : tree -> bool **)
  
  let rec isok = function
  | Leaf -> true
  | Node (l, x, r, i) ->
    if if if isok l then isok r else false then ltb_tree x l else false
    then gtb_tree x r
    else false
  
  module MX = OrderedTypeFacts(X)
  
  type coq_R_bal =
  | R_bal_0 of t * X.t * t
  | R_bal_1 of t * X.t * t * tree * X.t * tree * I.int
  | R_bal_2 of t * X.t * t * tree * X.t * tree * I.int
  | R_bal_3 of t * X.t * t * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int
  | R_bal_4 of t * X.t * t
  | R_bal_5 of t * X.t * t * tree * X.t * tree * I.int
  | R_bal_6 of t * X.t * t * tree * X.t * tree * I.int
  | R_bal_7 of t * X.t * t * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int
  | R_bal_8 of t * X.t * t
  
  type coq_R_remove_min =
  | R_remove_min_0 of tree * elt * t
  | R_remove_min_1 of tree * elt * t * tree * X.t * tree * I.int
     * (t, elt) prod * coq_R_remove_min * t * elt
  
  type coq_R_merge =
  | R_merge_0 of tree * tree
  | R_merge_1 of tree * tree * tree * X.t * tree * I.int
  | R_merge_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * elt
  
  type coq_R_min_elt =
  | R_min_elt_0 of tree
  | R_min_elt_1 of tree * tree * X.t * tree * I.int
  | R_min_elt_2 of tree * tree * X.t * tree * I.int * tree * X.t * tree
     * I.int * X.t option * coq_R_min_elt
  
  type coq_R_max_elt =
  | R_max_elt_0 of tree
  | R_max_elt_1 of tree * tree * X.t * tree * I.int
  | R_max_elt_2 of tree * tree * X.t * tree * I.int * tree * X.t * tree
     * I.int * X.t option * coq_R_max_elt
  
  type coq_R_concat =
  | R_concat_0 of tree * tree
  | R_concat_1 of tree * tree * tree * X.t * tree * I.int
  | R_concat_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * elt
  
  type coq_R_inter =
  | R_inter_0 of tree * tree
  | R_inter_1 of tree * tree * tree * X.t * tree * I.int
  | R_inter_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  | R_inter_3 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  
  type coq_R_diff =
  | R_diff_0 of tree * tree
  | R_diff_1 of tree * tree * tree * X.t * tree * I.int
  | R_diff_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  | R_diff_3 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  
  type coq_R_union =
  | R_union_0 of tree * tree
  | R_union_1 of tree * tree * tree * X.t * tree * I.int
  | R_union_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_union * tree * coq_R_union
  
  module L = MakeListOrdering(X)
  
  (** val flatten_e : enumeration -> elt list **)
  
  let rec flatten_e = function
  | End -> []
  | More (x, t0, r) -> x::(app (elements t0) (flatten_e r))
 end

module IntMake = 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct 
  module Raw = MakeRaw(I)(X)
  
  module E = 
   struct 
    type t = X.t
    
    (** val compare : t -> t -> comparison **)
    
    let compare =
      X.compare
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
  
  type elt = X.t
  
  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val this : t_ -> Raw.t **)
  
  let this t0 =
    t0
  
  type t = t_
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    Raw.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    Raw.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    Raw.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    Raw.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    Raw.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    Raw.inter (this s) (this s')
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    Raw.diff (this s) (this s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    Raw.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    Raw.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    Raw.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    Raw.elements (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    Raw.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f s =
    Raw.fold f (this s)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    Raw.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f s =
    Raw.filter f (this s)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f s =
    Raw.for_all f (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f s =
    Raw.exists_ f (this s)
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition f s =
    let p = Raw.partition f (this s) in Coq_pair ((fst p), (snd p))
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    let b = Raw.equal s s' in if b then true else false
  
  (** val compare : t -> t -> comparison **)
  
  let compare s s' =
    Raw.compare (this s) (this s')
  
  (** val min_elt : t -> elt option **)
  
  let min_elt s =
    Raw.min_elt (this s)
  
  (** val max_elt : t -> elt option **)
  
  let max_elt s =
    Raw.max_elt (this s)
 end

module Make = 
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

