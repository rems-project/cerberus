open Datatypes
open Equalities
open Orders
open OrdersFacts

module type TypElt = 
 sig 
  type t 
  
  type elt 
 end

module type HasWOps = 
 functor (T:TypElt) ->
 sig 
  val empty : T.t
  
  val is_empty : T.t -> bool
  
  val mem : T.elt -> T.t -> bool
  
  val add : T.elt -> T.t -> T.t
  
  val singleton : T.elt -> T.t
  
  val remove : T.elt -> T.t -> T.t
  
  val union : T.t -> T.t -> T.t
  
  val inter : T.t -> T.t -> T.t
  
  val diff : T.t -> T.t -> T.t
  
  val equal : T.t -> T.t -> bool
  
  val subset : T.t -> T.t -> bool
  
  val fold : (T.elt -> 'a1 -> 'a1) -> T.t -> 'a1 -> 'a1
  
  val for_all : (T.elt -> bool) -> T.t -> bool
  
  val exists_ : (T.elt -> bool) -> T.t -> bool
  
  val filter : (T.elt -> bool) -> T.t -> T.t
  
  val partition : (T.elt -> bool) -> T.t -> T.t*T.t
  
  val cardinal : T.t -> nat
  
  val elements : T.t -> T.elt list
  
  val choose : T.t -> T.elt option
 end

module type WOps = 
 functor (E:DecidableType) ->
 sig 
  type elt = E.t
  
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
 end

module type WSetsOn = 
 functor (E:DecidableType) ->
 sig 
  type elt = E.t
  
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
  
  val eq_dec : t -> t -> bool
 end

module type WSets = 
 sig 
  module E : 
   DecidableType
  
  type elt = E.t
  
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
  
  val eq_dec : t -> t -> bool
 end

module type HasOrdOps = 
 functor (T:TypElt) ->
 sig 
  val compare : T.t -> T.t -> comparison
  
  val min_elt : T.t -> T.elt option
  
  val max_elt : T.t -> T.elt option
 end

module type Ops = 
 functor (E:OrderedType) ->
 sig 
  type elt = E.t
  
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
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end

module type SetsOn = 
 functor (E:OrderedType) ->
 sig 
  type elt = E.t
  
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
  
  val eq_dec : t -> t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end

module type Sets = 
 sig 
  module E : 
   OrderedType
  
  type elt = E.t
  
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
  
  val eq_dec : t -> t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end

module type S = 
 Sets

module type WRawSets = 
 functor (E:DecidableType) ->
 sig 
  type elt = E.t
  
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
  
  val isok : t -> bool
 end

module WRaw2SetsOn = 
 functor (E:DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
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
  
  val isok : t -> bool
 end) ->
 struct 
  type elt = E.t
  
  type t_ =
    M.t
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val this : t_ -> M.t **)
  
  let this t0 =
    t0
  
  type t = t_
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    M.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    M.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    M.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    M.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    M.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    M.inter (this s) (this s')
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    M.diff (this s) (this s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    M.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    M.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    M.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    M.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    M.elements (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    M.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f s =
    M.fold f (this s)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    M.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f s =
    M.filter f (this s)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f s =
    M.for_all f (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f s =
    M.exists_ f (this s)
  
  (** val partition : (elt -> bool) -> t -> t*t **)
  
  let partition f s =
    let p = M.partition f (this s) in (fst p),(snd p)
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    let b = M.equal s s' in if b then true else false
 end

module WRaw2Sets = 
 functor (D:DecidableType) ->
 functor (M:sig 
  type elt = D.t
  
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
  
  val isok : t -> bool
 end) ->
 struct 
  module E = D
  
  type elt = D.t
  
  type t_ =
    M.t
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val this : t_ -> M.t **)
  
  let this t0 =
    t0
  
  type t = t_
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    M.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    M.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    M.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    M.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    M.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    M.inter (this s) (this s')
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    M.diff (this s) (this s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    M.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    M.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    M.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    M.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    M.elements (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    M.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f s =
    M.fold f (this s)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    M.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f s =
    M.filter f (this s)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f s =
    M.for_all f (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f s =
    M.exists_ f (this s)
  
  (** val partition : (elt -> bool) -> t -> t*t **)
  
  let partition f s =
    let p = M.partition f (this s) in (fst p),(snd p)
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    let b = M.equal s s' in if b then true else false
 end

module type RawSets = 
 functor (E:OrderedType) ->
 sig 
  type elt = E.t
  
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
  
  val isok : t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end

module Raw2SetsOn = 
 functor (O:OrderedType) ->
 functor (M:sig 
  type elt = O.t
  
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
  
  val isok : t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end) ->
 struct 
  type elt = O.t
  
  type t_ =
    M.t
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val this : t_ -> M.t **)
  
  let this t0 =
    t0
  
  type t = t_
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    M.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    M.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    M.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    M.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    M.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    M.inter (this s) (this s')
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    M.diff (this s) (this s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    M.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    M.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    M.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    M.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    M.elements (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    M.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f s =
    M.fold f (this s)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    M.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f s =
    M.filter f (this s)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f s =
    M.for_all f (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f s =
    M.exists_ f (this s)
  
  (** val partition : (elt -> bool) -> t -> t*t **)
  
  let partition f s =
    let p = M.partition f (this s) in (fst p),(snd p)
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    let b = M.equal s s' in if b then true else false
  
  (** val compare : t -> t -> comparison **)
  
  let compare s s' =
    M.compare (this s) (this s')
  
  (** val min_elt : t -> elt option **)
  
  let min_elt s =
    M.min_elt (this s)
  
  (** val max_elt : t -> elt option **)
  
  let max_elt s =
    M.max_elt (this s)
 end

module Raw2Sets = 
 functor (O:OrderedType) ->
 functor (M:sig 
  type elt = O.t
  
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
  
  val isok : t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end) ->
 struct 
  module E = O
  
  type elt = O.t
  
  type t_ =
    M.t
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val this : t_ -> M.t **)
  
  let this t0 =
    t0
  
  type t = t_
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    M.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    M.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    M.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    M.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    M.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    M.inter (this s) (this s')
  
  (** val diff :
      t
      ->
      t
      ->
      t **)
  
  let diff s s' =
    M.diff
      (this
        s)
      (this
        s')
  
  (** val equal :
      t
      ->
      t
      ->
      bool **)
  
  let equal s s' =
    M.equal
      (this
        s)
      (this
        s')
  
  (** val subset :
      t
      ->
      t
      ->
      bool **)
  
  let subset s s' =
    M.subset
      (this
        s)
      (this
        s')
  
  (** val empty :
      t **)
  
  let empty =
    M.empty
  
  (** val is_empty :
      t
      ->
      bool **)
  
  let is_empty s =
    M.is_empty
      (this
        s)
  
  (** val elements :
      t
      ->
      elt
      list **)
  
  let elements s =
    M.elements
      (this
        s)
  
  (** val choose :
      t
      ->
      elt
      option **)
  
  let choose s =
    M.choose
      (this
        s)
  
  (** val fold :
      (elt
      ->
      'a1
      ->
      'a1)
      ->
      t
      ->
      'a1
      ->
      'a1 **)
  
  let fold f s =
    M.fold
      f
      (this
        s)
  
  (** val cardinal :
      t
      ->
      nat **)
  
  let cardinal s =
    M.cardinal
      (this
        s)
  
  (** val filter :
      (elt
      ->
      bool)
      ->
      t
      ->
      t **)
  
  let filter f s =
    M.filter
      f
      (this
        s)
  
  (** val for_all :
      (elt
      ->
      bool)
      ->
      t
      ->
      bool **)
  
  let for_all f s =
    M.for_all
      f
      (this
        s)
  
  (** val exists_ :
      (elt
      ->
      bool)
      ->
      t
      ->
      bool **)
  
  let exists_ f s =
    M.exists_
      f
      (this
        s)
  
  (** val partition :
      (elt
      ->
      bool)
      ->
      t
      ->
      t*t **)
  
  let partition f s =
    let p =
      M.partition
        f
        (this
          s)
    in
    (fst
      p),(snd
           p)
  
  (** val eq_dec :
      t
      ->
      t
      ->
      bool **)
  
  let eq_dec s s' =
    let b =
      M.equal
        s
        s'
    in
    if b
    then true
    else false
  
  (** val compare :
      t
      ->
      t
      ->
      comparison **)
  
  let compare s s' =
    M.compare
      (this
        s)
      (this
        s')
  
  (** val min_elt :
      t
      ->
      elt
      option **)
  
  let min_elt s =
    M.min_elt
      (this
        s)
  
  (** val max_elt :
      t
      ->
      elt
      option **)
  
  let max_elt s =
    M.max_elt
      (this
        s)
 end

module MakeListOrdering = 
 functor (O:OrderedType) ->
 struct 
  module MO = OrderedTypeFacts(O)
 end

