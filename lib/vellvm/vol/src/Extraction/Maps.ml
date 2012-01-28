open BinInt
open BinNat
open BinPos
open Coqlib
open Datatypes
open List0
open MetatheoryAtom
open Alist

module type TREE = 
 sig 
  type elt 
  
  val elt_eq : elt -> elt -> bool
  
  type 'x t 
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val empty : 'a1 t
  
  val get : elt -> 'a1 t -> 'a1 option
  
  val set : elt -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : elt -> 'a1 t -> 'a1 t
  
  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val map : (elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val combine :
    ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t -> 'a1 t
  
  val elements : 'a1 t -> (elt*'a1) list
  
  val fold : ('a2 -> elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module type MAP = 
 sig 
  type elt 
  
  val elt_eq : elt -> elt -> bool
  
  type 'x t 
  
  val init : 'a1 -> 'a1 t
  
  val get : elt -> 'a1 t -> 'a1
  
  val set : elt -> 'a1 -> 'a1 t -> 'a1 t
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module PTree = 
 struct 
  type elt = positive
  
  (** val elt_eq : positive -> positive -> bool **)
  
  let elt_eq =
    peq
  
  type 'a tree =
    | Leaf
    | Node of 'a tree * 'a option * 'a tree
  
  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> 'a1 option -> 'a1 tree -> 'a2 -> 'a2) -> 'a1
      tree -> 'a2 **)
  
  let rec tree_rect f f0 = function
    | Leaf -> f
    | Node (t1, o, t2) -> f0 t1 (tree_rect f f0 t1) o t2 (tree_rect f f0 t2)
  
  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> 'a1 option -> 'a1 tree -> 'a2 -> 'a2) -> 'a1
      tree -> 'a2 **)
  
  let rec tree_rec f f0 = function
    | Leaf -> f
    | Node (t1, o, t2) -> f0 t1 (tree_rec f f0 t1) o t2 (tree_rec f f0 t2)
  
  type 'a t = 'a tree
  
  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let rec eq eqA a b =
    match a with
      | Leaf -> (match b with
                   | Leaf -> true
                   | Node (t0, o, t1) -> false)
      | Node (t0, o, t1) ->
          (match b with
             | Leaf -> false
             | Node (t2, o0, t3) ->
                 if eq eqA t0 t2
                 then if match o with
                           | Some x ->
                               (match o0 with
                                  | Some a1 -> eqA x a1
                                  | None -> false)
                           | None ->
                               (match o0 with
                                  | Some a0 -> false
                                  | None -> true)
                      then eq eqA t1 t3
                      else false
                 else false)
  
  (** val empty : 'a1 t **)
  
  let empty =
    Leaf
  
  (** val get : positive -> 'a1 t -> 'a1 option **)
  
  let rec get i = function
    | Leaf -> None
    | Node (l, o, r) ->
        (match i with
           | Coq_xI ii -> get ii r
           | Coq_xO ii -> get ii l
           | Coq_xH -> o)
  
  (** val set : positive -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let rec set i v = function
    | Leaf ->
        (match i with
           | Coq_xI ii -> Node (Leaf, None, (set ii v Leaf))
           | Coq_xO ii -> Node ((set ii v Leaf), None, Leaf)
           | Coq_xH -> Node (Leaf, (Some v), Leaf))
    | Node (l, o, r) ->
        (match i with
           | Coq_xI ii -> Node (l, o, (set ii v r))
           | Coq_xO ii -> Node ((set ii v l), o, r)
           | Coq_xH -> Node (l, (Some v), r))
  
  (** val remove : positive -> 'a1 t -> 'a1 t **)
  
  let rec remove i m =
    match i with
      | Coq_xI ii ->
          (match m with
             | Leaf -> Leaf
             | Node (l, o, r) ->
                 (match l with
                    | Leaf ->
                        (match o with
                           | Some a -> Node (l, o, (remove ii r))
                           | None ->
                               (match remove ii r with
                                  | Leaf -> Leaf
                                  | Node (t0, o0, t1) -> Node (Leaf, None,
                                      (Node (t0, o0, t1)))))
                    | Node (t0, o0, t1) -> Node (l, o, (remove ii r))))
      | Coq_xO ii ->
          (match m with
             | Leaf -> Leaf
             | Node (l, o, r) ->
                 (match o with
                    | Some a -> Node ((remove ii l), o, r)
                    | None ->
                        (match r with
                           | Leaf ->
                               (match remove ii l with
                                  | Leaf -> Leaf
                                  | Node (t0, o0, t1) -> Node ((Node (t0, o0,
                                      t1)), None, Leaf))
                           | Node (t0, o0, t1) -> Node ((remove ii l), o, r))))
      | Coq_xH ->
          (match m with
             | Leaf -> Leaf
             | Node (l, o, r) ->
                 (match l with
                    | Leaf ->
                        (match r with
                           | Leaf -> Leaf
                           | Node (t0, o0, t1) -> Node (l, None, r))
                    | Node (t0, o0, t1) -> Node (l, None, r)))
  
  (** val bempty : 'a1 t -> bool **)
  
  let rec bempty = function
    | Leaf -> true
    | Node (l, o, r) ->
        (match o with
           | Some a -> false
           | None -> if bempty l then bempty r else false)
  
  (** val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let rec beq beqA m1 m2 =
    match m1 with
      | Leaf -> bempty m2
      | Node (l1, o1, r1) ->
          (match m2 with
             | Leaf -> bempty m1
             | Node (l2, o2, r2) ->
                 if if match o1 with
                         | Some y1 ->
                             (match o2 with
                                | Some y2 -> beqA y1 y2
                                | None -> false)
                         | None ->
                             (match o2 with
                                | Some a -> false
                                | None -> true)
                    then beq beqA l1 l2
                    else false
                 then beq beqA r1 r2
                 else false)
  
  (** val append : positive -> positive -> positive **)
  
  let rec append i j =
    match i with
      | Coq_xI ii -> Coq_xI (append ii j)
      | Coq_xO ii -> Coq_xO (append ii j)
      | Coq_xH -> j
  
  (** val xmap : (positive -> 'a1 -> 'a2) -> 'a1 t -> positive -> 'a2 t **)
  
  let rec xmap f m i =
    match m with
      | Leaf -> Leaf
      | Node (l, o, r) -> Node ((xmap f l (append i (Coq_xO Coq_xH))),
          (Coqlib.option_map (f i) o), (xmap f r (append i (Coq_xI Coq_xH))))
  
  (** val map : (positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    xmap f m Coq_xH
  
  (** val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t **)
  
  let coq_Node' l x r =
    match l with
      | Leaf ->
          (match x with
             | Some a -> Node (l, x, r)
             | None ->
                 (match r with
                    | Leaf -> Leaf
                    | Node (t0, o, t1) -> Node (l, x, r)))
      | Node (t0, o, t1) -> Node (l, x, r)
  
  (** val xcombine_l :
      ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t **)
  
  let rec xcombine_l f = function
    | Leaf -> Leaf
    | Node (l, o, r) ->
        coq_Node' (xcombine_l f l) (f o None) (xcombine_l f r)
  
  (** val xcombine_r :
      ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t **)
  
  let rec xcombine_r f = function
    | Leaf -> Leaf
    | Node (l, o, r) ->
        coq_Node' (xcombine_r f l) (f None o) (xcombine_r f r)
  
  (** val combine :
      ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t -> 'a1 t **)
  
  let rec combine f m1 m2 =
    match m1 with
      | Leaf -> xcombine_r f m2
      | Node (l1, o1, r1) ->
          (match m2 with
             | Leaf -> xcombine_l f m1
             | Node (l2, o2, r2) ->
                 coq_Node' (combine f l1 l2) (f o1 o2) (combine f r1 r2))
  
  (** val xelements : 'a1 t -> positive -> (positive*'a1) list **)
  
  let rec xelements m i =
    match m with
      | Leaf -> []
      | Node (l, o, r) ->
          (match o with
             | Some x ->
                 app (xelements l (append i (Coq_xO Coq_xH)))
                   ((i,x)::(xelements r (append i (Coq_xI Coq_xH))))
             | None ->
                 app (xelements l (append i (Coq_xO Coq_xH)))
                   (xelements r (append i (Coq_xI Coq_xH))))
  
  (** val elements : 'a1 t -> (positive*'a1) list **)
  
  let elements m =
    xelements m Coq_xH
  
  (** val xget : positive -> positive -> 'a1 t -> 'a1 option **)
  
  let rec xget i j m =
    match i with
      | Coq_xI ii ->
          (match j with
             | Coq_xI jj -> xget ii jj m
             | Coq_xO p -> None
             | Coq_xH -> get i m)
      | Coq_xO ii ->
          (match j with
             | Coq_xI p -> None
             | Coq_xO jj -> xget ii jj m
             | Coq_xH -> get i m)
      | Coq_xH -> (match j with
                     | Coq_xH -> get i m
                     | _ -> None)
  
  (** val xkeys : 'a1 t -> positive -> positive list **)
  
  let xkeys m i =
    List0.map fst (xelements m i)
  
  (** val xfold :
      ('a2 -> positive -> 'a1 -> 'a2) -> positive -> 'a1 t -> 'a2 -> 'a2 **)
  
  let rec xfold f i m v =
    match m with
      | Leaf -> v
      | Node (l, o, r) ->
          (match o with
             | Some x ->
                 let v1 = xfold f (append i (Coq_xO Coq_xH)) l v in
                 let v2 = f v1 i x in xfold f (append i (Coq_xI Coq_xH)) r v2
             | None ->
                 let v1 = xfold f (append i (Coq_xO Coq_xH)) l v in
                 xfold f (append i (Coq_xI Coq_xH)) r v1)
  
  (** val fold : ('a2 -> positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let fold f m v =
    xfold f Coq_xH m v
 end

module ATree = 
 struct 
  type elt = AtomImpl.atom
  
  (** val elt_eq : AtomImpl.atom -> AtomImpl.atom -> bool **)
  
  let elt_eq =
    AtomImpl.eq_atom_dec
  
  type 'a tree = (AtomImpl.atom*'a) list
  
  type 'a t = 'a tree
  
  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let rec eq eqA a b =
    match a with
      | [] -> (match b with
                 | [] -> true
                 | p::l -> false)
      | y::l ->
          (match b with
             | [] -> false
             | p::l0 ->
                 if let a0,a1 = y in
                    let a2,a3 = p in
                    if AtomImpl.eq_atom_dec a0 a2 then eqA a1 a3 else false
                 then eq eqA l l0
                 else false)
  
  (** val empty : 'a1 t **)
  
  let empty =
    []
  
  (** val get : AtomImpl.atom -> 'a1 t -> 'a1 option **)
  
  let get i m =
    lookupAL m i
  
  (** val set : AtomImpl.atom -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let set i v m =
    updateAddAL m i v
  
  (** val remove : AtomImpl.atom -> 'a1 t -> 'a1 t **)
  
  let remove i m =
    deleteAL m i
  
  (** val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let rec beq cmp m1 m2 =
    match m1 with
      | [] -> (match m2 with
                 | [] -> true
                 | p::l -> false)
      | p::m1' ->
          let id1,gv1 = p in
          (match m2 with
             | [] -> false
             | p0::m2' ->
                 let id2,gv2 = p0 in
                 if elt_eq id1 id2
                 then if cmp gv1 gv2 then beq cmp m1' m2' else false
                 else false)
  
  (** val map : (elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let rec map f = function
    | [] -> []
    | p::m' -> let id0,gv0 = p in (id0,(f id0 gv0))::(map f m')
  
  (** val combine :
      ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t -> 'a1 t **)
  
  let combine = fun x y z -> assert false
  
  (** val elements : 'a1 t -> 'a1 t **)
  
  let elements m =
    m
  
  (** val fold : ('a2 -> elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let rec fold f m v =
    match m with
      | [] -> v
      | p::m' -> let id0,gv0 = p in fold f m' (f v id0 gv0)
 end

module PMap = 
 struct 
  type elt = positive
  
  (** val elt_eq : positive -> positive -> bool **)
  
  let elt_eq =
    peq
  
  type 'a t = 'a*'a PTree.t
  
  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let eq x a b =
    let x0,x1 = a in
    let a1,t0 = b in if x x0 a1 then PTree.eq x x1 t0 else false
  
  (** val init : 'a1 -> 'a1*'a1 PTree.t **)
  
  let init x =
    x,PTree.empty
  
  (** val get : positive -> 'a1 t -> 'a1 **)
  
  let get i m =
    match PTree.get i (snd m) with
      | Some x -> x
      | None -> fst m
  
  (** val set : positive -> 'a1 -> 'a1 t -> 'a1*'a1 PTree.t **)
  
  let set i x m =
    (fst m),(PTree.set i x (snd m))
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    (f (fst m)),(PTree.map (fun x -> f) (snd m))
 end

module AMap = 
 struct 
  type elt = AtomImpl.atom
  
  (** val elt_eq : AtomImpl.atom -> AtomImpl.atom -> bool **)
  
  let elt_eq =
    AtomImpl.eq_atom_dec
  
  type 'a t = 'a*'a ATree.t
  
  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let eq x a b =
    let x0,x1 = a in
    let a1,t0 = b in if x x0 a1 then ATree.eq x x1 t0 else false
  
  (** val init : 'a1 -> 'a1*'a1 ATree.t **)
  
  let init x =
    x,ATree.empty
  
  (** val get : AtomImpl.atom -> 'a1 t -> 'a1 **)
  
  let get i m =
    match ATree.get i (snd m) with
      | Some x -> x
      | None -> fst m
  
  (** val set : AtomImpl.atom -> 'a1 -> 'a1 t -> 'a1*'a1 ATree.t **)
  
  let set i x m =
    (fst m),(ATree.set i x (snd m))
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    (f (fst m)),(ATree.map (fun x -> f) (snd m))
 end

module type INDEXED_TYPE = 
 sig 
  type t 
  
  val index : t -> positive
  
  val eq : t -> t -> bool
 end

module IMap = 
 functor (X:INDEXED_TYPE) ->
 struct 
  type elt = X.t
  
  (** val elt_eq : X.t -> X.t -> bool **)
  
  let elt_eq =
    X.eq
  
  type 'x t = 'x PMap.t
  
  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let eq x a b =
    PMap.eq x a b
  
  (** val init : 'a1 -> 'a1*'a1 PTree.t **)
  
  let init x =
    PMap.init x
  
  (** val get : X.t -> 'a1 t -> 'a1 **)
  
  let get i m =
    PMap.get (X.index i) m
  
  (** val set : X.t -> 'a1 -> 'a1 t -> 'a1*'a1 PTree.t **)
  
  let set i v m =
    PMap.set (X.index i) v m
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    PMap.map f m
 end

module ZIndexed = 
 struct 
  type t = coq_Z
  
  (** val index : coq_Z -> positive **)
  
  let index = function
    | Z0 -> Coq_xH
    | Zpos p -> Coq_xO p
    | Zneg p -> Coq_xI p
  
  (** val eq : coq_Z -> coq_Z -> bool **)
  
  let eq =
    zeq
 end

module ZMap = IMap(ZIndexed)

module NIndexed = 
 struct 
  type t = coq_N
  
  (** val index : coq_N -> positive **)
  
  let index = function
    | N0 -> Coq_xH
    | Npos p -> Coq_xO p
  
  (** val eq : coq_N -> coq_N -> bool **)
  
  let eq x y =
    match x with
      | N0 -> (match y with
                 | N0 -> true
                 | Npos p -> false)
      | Npos x0 -> (match y with
                      | N0 -> false
                      | Npos p0 -> peq x0 p0)
 end

module NMap = IMap(NIndexed)

module type EQUALITY_TYPE = 
 sig 
  type t 
  
  val eq : t -> t -> bool
 end

module EMap = 
 functor (X:EQUALITY_TYPE) ->
 struct 
  type elt = X.t
  
  (** val elt_eq : X.t -> X.t -> bool **)
  
  let elt_eq =
    X.eq
  
  type 'a t = X.t -> 'a
  
  (** val init : 'a1 -> X.t -> 'a1 **)
  
  let init v x =
    v
  
  (** val get : X.t -> 'a1 t -> 'a1 **)
  
  let get x m =
    m x
  
  (** val set : X.t -> 'a1 -> 'a1 t -> X.t -> 'a1 **)
  
  let set x v m y =
    if X.eq y x then v else m y
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> X.t -> 'a2 **)
  
  let map f m x =
    f (m x)
 end

module Tree_Properties = 
 functor (T:TREE) ->
 struct 
  (** val f' : ('a2 -> T.elt -> 'a1 -> 'a2) -> 'a2 -> (T.elt*'a1) -> 'a2 **)
  
  let f' f a p =
    f a (fst p) (snd p)
 end

module ATree_Properties = Tree_Properties(ATree)

