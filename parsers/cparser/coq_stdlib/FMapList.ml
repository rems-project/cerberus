open Datatypes
open List0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Raw = 
 functor (X:OrderedType.OrderedType) ->
 struct 
  module MX = OrderedType.OrderedTypeFacts(X)
  
  module PX = OrderedType.KeyOrderedType(X)
  
  type key = X.t
  
  type 'elt t = (X.t*'elt) list
  
  (** val empty : 'a1 t **)
  
  let empty =
    []
  
  (** val is_empty : 'a1 t -> bool **)
  
  let is_empty = function
  | [] -> true
  | x::x0 -> false
  
  (** val mem : key -> 'a1 t -> bool **)
  
  let rec mem k = function
  | [] -> false
  | p::l ->
    let k',e = p in
    (match X.compare k k' with
     | OrderedType.LT -> false
     | OrderedType.EQ -> true
     | OrderedType.GT -> mem k l)
  
  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * bool * 'elt coq_R_mem
  
  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
      'a1 coq_R_mem -> 'a2 **)
  
  let rec coq_R_mem_rect k f f0 f1 f2 s b = function
  | R_mem_0 s0 -> f s0 __
  | R_mem_1 (s0, k', _x, l) -> f0 s0 k' _x l __ __ __
  | R_mem_2 (s0, k', _x, l) -> f1 s0 k' _x l __ __ __
  | R_mem_3 (s0, k', _x, l, res, r0) ->
    f2 s0 k' _x l __ __ __ res r0 (coq_R_mem_rect k f f0 f1 f2 l res r0)
  
  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
      'a1 coq_R_mem -> 'a2 **)
  
  let rec coq_R_mem_rec k f f0 f1 f2 s b = function
  | R_mem_0 s0 -> f s0 __
  | R_mem_1 (s0, k', _x, l) -> f0 s0 k' _x l __ __ __
  | R_mem_2 (s0, k', _x, l) -> f1 s0 k' _x l __ __ __
  | R_mem_3 (s0, k', _x, l, res, r0) ->
    f2 s0 k' _x l __ __ __ res r0 (coq_R_mem_rec k f f0 f1 f2 l res r0)
  
  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let rec mem_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p::l ->
       let t0,e = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = mem_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | OrderedType.LT -> f10 __ __
        | OrderedType.EQ -> f9 __ __
        | OrderedType.GT -> f8 __ __))
  
  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let mem_rec k =
    mem_rect k
  
  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)
  
  let coq_R_mem_correct x x0 res =
    Obj.magic (fun x1 _ -> mem_rect x1) x __ (fun y _ z _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ z _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ z _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 z _ -> R_mem_3 (y, y0, y1, y2, (mem x y2),
      (y6 (mem x y2) __))) x0 res __
  
  (** val find : key -> 'a1 t -> 'a1 option **)
  
  let rec find k = function
  | [] -> None
  | p::s' ->
    let k',x = p in
    (match X.compare k k' with
     | OrderedType.LT -> None
     | OrderedType.EQ -> Some x
     | OrderedType.GT -> find k s')
  
  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt option
     * 'elt coq_R_find
  
  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
      'a1 option -> 'a1 coq_R_find -> 'a2 **)
  
  let rec coq_R_find_rect k f f0 f1 f2 s o = function
  | R_find_0 s0 -> f s0 __
  | R_find_1 (s0, k', x, s') -> f0 s0 k' x s' __ __ __
  | R_find_2 (s0, k', x, s') -> f1 s0 k' x s' __ __ __
  | R_find_3 (s0, k', x, s', res, r0) ->
    f2 s0 k' x s' __ __ __ res r0 (coq_R_find_rect k f f0 f1 f2 s' res r0)
  
  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
      'a1 option -> 'a1 coq_R_find -> 'a2 **)
  
  let rec coq_R_find_rec k f f0 f1 f2 s o = function
  | R_find_0 s0 -> f s0 __
  | R_find_1 (s0, k', x, s') -> f0 s0 k' x s' __ __ __
  | R_find_2 (s0, k', x, s') -> f1 s0 k' x s' __ __ __
  | R_find_3 (s0, k', x, s', res, r0) ->
    f2 s0 k' x s' __ __ __ res r0 (coq_R_find_rec k f f0 f1 f2 s' res r0)
  
  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let rec find_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p::l ->
       let t0,e = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = find_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | OrderedType.LT -> f10 __ __
        | OrderedType.EQ -> f9 __ __
        | OrderedType.GT -> f8 __ __))
  
  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let find_rec k =
    find_rect k
  
  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)
  
  let coq_R_find_correct x x0 res =
    Obj.magic (fun x1 _ -> find_rect x1) x __ (fun y _ z _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ z _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ z _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 z _ -> R_find_3 (y, y0, y1, y2, (find x y2),
      (y6 (find x y2) __))) x0 res __
  
  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let rec add k x s = match s with
  | [] -> (k,x)::[]
  | p::l ->
    let k',y = p in
    (match X.compare k k' with
     | OrderedType.LT -> (k,x)::s
     | OrderedType.EQ -> (k,x)::l
     | OrderedType.GT -> (k',y)::(add k x l))
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
     * 'elt coq_R_add
  
  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)
  
  let rec coq_R_add_rect k x f f0 f1 f2 s t0 = function
  | R_add_0 s0 -> f s0 __
  | R_add_1 (s0, k', y, l) -> f0 s0 k' y l __ __ __
  | R_add_2 (s0, k', y, l) -> f1 s0 k' y l __ __ __
  | R_add_3 (s0, k', y, l, res, r0) ->
    f2 s0 k' y l __ __ __ res r0 (coq_R_add_rect k x f f0 f1 f2 l res r0)
  
  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)
  
  let rec coq_R_add_rec k x f f0 f1 f2 s t0 = function
  | R_add_0 s0 -> f s0 __
  | R_add_1 (s0, k', y, l) -> f0 s0 k' y l __ __ __
  | R_add_2 (s0, k', y, l) -> f1 s0 k' y l __ __ __
  | R_add_3 (s0, k', y, l, res, r0) ->
    f2 s0 k' y l __ __ __ res r0 (coq_R_add_rec k x f f0 f1 f2 l res r0)
  
  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let rec add_rect k x f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p::l ->
       let t0,e = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | OrderedType.LT -> f10 __ __
        | OrderedType.EQ -> f9 __ __
        | OrderedType.GT -> f8 __ __))
  
  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
      list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let add_rec k x =
    add_rect k x
  
  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)
  
  let coq_R_add_correct x x0 x1 res =
    add_rect x x0 (fun y _ z _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ z _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ z _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 z _ -> R_add_3 (y, y0, y1, y2,
      (add x x0 y2), (y6 (add x x0 y2) __))) x1 res __
  
  (** val remove : key -> 'a1 t -> 'a1 t **)
  
  let rec remove k s = match s with
  | [] -> []
  | p::l ->
    let k',x = p in
    (match X.compare k k' with
     | OrderedType.LT -> s
     | OrderedType.EQ -> l
     | OrderedType.GT -> (k',x)::(remove k l))
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
     * 'elt coq_R_remove
  
  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1
      t -> 'a1 coq_R_remove -> 'a2 **)
  
  let rec coq_R_remove_rect k f f0 f1 f2 s t0 = function
  | R_remove_0 s0 -> f s0 __
  | R_remove_1 (s0, k', x, l) -> f0 s0 k' x l __ __ __
  | R_remove_2 (s0, k', x, l) -> f1 s0 k' x l __ __ __
  | R_remove_3 (s0, k', x, l, res, r0) ->
    f2 s0 k' x l __ __ __ res r0 (coq_R_remove_rect k f f0 f1 f2 l res r0)
  
  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1
      t -> 'a1 coq_R_remove -> 'a2 **)
  
  let rec coq_R_remove_rec k f f0 f1 f2 s t0 = function
  | R_remove_0 s0 -> f s0 __
  | R_remove_1 (s0, k', x, l) -> f0 s0 k' x l __ __ __
  | R_remove_2 (s0, k', x, l) -> f1 s0 k' x l __ __ __
  | R_remove_3 (s0, k', x, l, res, r0) ->
    f2 s0 k' x l __ __ __ res r0 (coq_R_remove_rec k f f0 f1 f2 l res r0)
  
  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let rec remove_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p::l ->
       let t0,e = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | OrderedType.LT -> f10 __ __
        | OrderedType.EQ -> f9 __ __
        | OrderedType.GT -> f8 __ __))
  
  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
      -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let remove_rec k =
    remove_rect k
  
  (** val coq_R_remove_correct :
      key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)
  
  let coq_R_remove_correct x x0 res =
    Obj.magic (fun x1 _ -> remove_rect x1) x __ (fun y _ z _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ z _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ z _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 z _ -> R_remove_3 (y, y0, y1, y2,
      (remove x y2), (y6 (remove x y2) __))) x0 res __
  
  (** val elements : 'a1 t -> 'a1 t **)
  
  let elements m =
    m
  
  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let rec fold f m acc =
    match m with
    | [] -> acc
    | p::m' -> let k,e = p in fold f m' (f k e acc)
  
  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
  | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
     * (X.t*'elt) list * 'a * ('elt, 'a) coq_R_fold
  
  (** val coq_R_fold_rect :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 ->
      'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2 **)
  
  let rec coq_R_fold_rect f f0 f1 m acc a = function
  | R_fold_0 (f2, m0, acc0) -> Obj.magic f __ f2 m0 acc0 __
  | R_fold_1 (f2, m0, acc0, k, e, m', res, r0) ->
    Obj.magic f0 __ f2 m0 acc0 k e m' __ res r0
      (coq_R_fold_rect f f0 f2 m' (f2 k e acc0) res r0)
  
  (** val coq_R_fold_rec :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 ->
      'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2 **)
  
  let rec coq_R_fold_rec f f0 f1 m acc a = function
  | R_fold_0 (f2, m0, acc0) -> Obj.magic f __ f2 m0 acc0 __
  | R_fold_1 (f2, m0, acc0, k, e, m', res, r0) ->
    Obj.magic f0 __ f2 m0 acc0 k e m' __ res r0
      (coq_R_fold_rec f f0 f2 m' (f2 k e acc0) res r0)
  
  (** val fold_rect :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 ->
      'a2 **)
  
  let rec fold_rect f0 f f1 m acc =
    let f2 = Obj.magic f0 __ f1 m acc in
    let f3 = Obj.magic f __ f1 m acc in
    (match m with
     | [] -> f2 __
     | p::l ->
       let t0,e = p in
       let f4 = f3 t0 e l __ in
       let hrec = fold_rect f0 f f1 l (f1 t0 e acc) in f4 hrec)
  
  (** val fold_rec :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t*'a1) list
      -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 ->
      'a2 **)
  
  let fold_rec f f0 f1 m acc =
    fold_rect f f0 f1 m acc
  
  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)
  
  let coq_R_fold_correct x0 x1 x2 res =
    Obj.magic (fun _ x x3 _ -> fold_rect x x3) __ (fun _ y0 y1 y2 _ z _ ->
      R_fold_0 (y0, y1, y2)) (fun _ y0 y1 y2 y3 y4 y5 _ y7 z _ -> R_fold_1
      (y0, y1, y2, y3, y4, y5, (fold y0 y5 (y0 y3 y4 y2)),
      (y7 (fold y0 y5 (y0 y3 y4 y2)) __))) __ x0 x1 x2 res __
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let rec equal cmp0 m m' =
    match m with
    | [] ->
      (match m' with
       | [] -> true
       | p::l -> false)
    | p::l ->
      let x,e = p in
      (match m' with
       | [] -> false
       | p0::l' ->
         let x',e' = p0 in
         (match X.compare x x' with
          | OrderedType.EQ -> if cmp0 e e' then equal cmp0 l l' else false
          | _ -> false))
  
  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * X.t * 
     'elt * (X.t*'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * X.t * 
     'elt * (X.t*'elt) list * X.t OrderedType.coq_Compare
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
  
  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
      (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t ->
      'a1 -> (X.t*'a1) list -> __ -> X.t OrderedType.coq_Compare -> __ -> __
      -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
      -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)
  
  let rec coq_R_equal_rect cmp0 f f0 f1 f2 m m' b = function
  | R_equal_0 (m0, m'0) -> f m0 m'0 __ __
  | R_equal_1 (m0, m'0, x, e, l, x', e', l', res, r0) ->
    f0 m0 m'0 x e l __ x' e' l' __ __ __ res r0
      (coq_R_equal_rect cmp0 f f0 f1 f2 l l' res r0)
  | R_equal_2 (m0, m'0, x, e, l, x', e', l', _x) ->
    f1 m0 m'0 x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m0, m'0, _x, _x0) -> f2 m0 m'0 _x __ _x0 __ __
  
  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
      (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t ->
      'a1 -> (X.t*'a1) list -> __ -> X.t OrderedType.coq_Compare -> __ -> __
      -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
      -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)
  
  let rec coq_R_equal_rec cmp0 f f0 f1 f2 m m' b = function
  | R_equal_0 (m0, m'0) -> f m0 m'0 __ __
  | R_equal_1 (m0, m'0, x, e, l, x', e', l', res, r0) ->
    f0 m0 m'0 x e l __ x' e' l' __ __ __ res r0
      (coq_R_equal_rec cmp0 f f0 f1 f2 l l' res r0)
  | R_equal_2 (m0, m'0, x, e, l, x', e', l', _x) ->
    f1 m0 m'0 x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m0, m'0, _x, _x0) -> f2 m0 m'0 _x __ _x0 __ __
  
  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
      (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1
      t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)
  
  let rec equal_rect cmp0 f2 f1 f0 f m m' =
    let f3 = f2 m m' in
    let f4 = f1 m m' in
    let f5 = f0 m m' in
    let f6 = f m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | [] ->
       let f9 = f3 __ in
       (match m' with
        | [] -> f9 __
        | p::l -> f8 __)
     | p::l ->
       let t0,e = p in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match m' with
        | [] -> f8 __
        | p0::l0 ->
          let t1,e0 = p0 in
          let f11 = f9 t1 e0 l0 __ in
          let f12 = let _x = X.compare t0 t1 in f11 _x __ in
          let f13 = f10 t1 e0 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp0 f2 f1 f0 f l l0 in f13 __ __ hrec
          in
          (match X.compare t0 t1 with
           | OrderedType.EQ -> f14 __ __
           | _ -> f12 __)))
  
  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
      (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1) list ->
      __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1
      t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)
  
  let equal_rec cmp0 =
    equal_rect cmp0
  
  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)
  
  let coq_R_equal_correct x x0 x1 res =
    equal_rect x (fun y y0 _ _ z _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal x y3 y7), (y11 (equal x y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ z _ -> R_equal_3 (y, y0, y1,
      y3)) x0 x1 res __
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let rec map f = function
  | [] -> []
  | p::m' -> let k,e = p in (k,(f e))::(map f m')
  
  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let rec mapi f = function
  | [] -> []
  | p::m' -> let k,e = p in (k,(f k e))::(mapi f m')
  
  (** val option_cons :
      key -> 'a1 option -> (key*'a1) list -> (key*'a1) list **)
  
  let option_cons k o l =
    match o with
    | Some e -> (k,e)::l
    | None -> l
  
  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)
  
  let rec map2_l f = function
  | [] -> []
  | p::l -> let k,e = p in option_cons k (f (Some e) None) (map2_l f l)
  
  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)
  
  let rec map2_r f = function
  | [] -> []
  | p::l' -> let k,e' = p in option_cons k (f None (Some e')) (map2_r f l')
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)
  
  let rec map2 f m = match m with
  | [] -> map2_r f
  | p::l ->
    let k,e = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0::l' ->
      let k',e' = p0 in
      (match X.compare k k' with
       | OrderedType.LT -> option_cons k (f (Some e) None) (map2 f l m')
       | OrderedType.EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | OrderedType.GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux
  
  (** val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t **)
  
  let rec combine m = match m with
  | [] -> map (fun e' -> None,(Some e'))
  | p::l ->
    let k,e = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> (Some e0),None) m
    | p0::l' ->
      let k',e' = p0 in
      (match X.compare k k' with
       | OrderedType.LT -> (k,((Some e),None))::(combine l m')
       | OrderedType.EQ -> (k,((Some e),(Some e')))::(combine l l')
       | OrderedType.GT -> (k',(None,(Some e')))::(combine_aux l'))
    in combine_aux
  
  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3 **)
  
  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l
  
  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key*'a3)
      list **)
  
  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []
  
  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option*'a2 option) option **)
  
  let at_least_one o o' =
    match o with
    | Some e -> Some (o,o')
    | None ->
      (match o' with
       | Some e -> Some (o,o')
       | None -> None)
  
  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)
  
  let at_least_one_then_f f o o' =
    match o with
    | Some e -> f o o'
    | None ->
      (match o' with
       | Some e -> f o o'
       | None -> None)
 end

module Make = 
 functor (X:OrderedType.OrderedType) ->
 struct 
  module Raw = Raw(X)
  
  module E = X
  
  type key = E.t
  
  type 'elt slist =
    'elt Raw.t
    (* singleton inductive, whose constructor was Build_slist *)
  
  (** val slist_rect : ('a1 Raw.t -> __ -> 'a2) -> 'a1 slist -> 'a2 **)
  
  let slist_rect f s =
    f s __
  
  (** val slist_rec : ('a1 Raw.t -> __ -> 'a2) -> 'a1 slist -> 'a2 **)
  
  let slist_rec f s =
    f s __
  
  (** val this : 'a1 slist -> 'a1 Raw.t **)
  
  let this s =
    s
  
  type 'elt t = 'elt slist
  
  (** val empty : 'a1 t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : 'a1 t -> bool **)
  
  let is_empty m =
    Raw.is_empty (this m)
  
  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let add x e m =
    Raw.add x e (this m)
  
  (** val find : key -> 'a1 t -> 'a1 option **)
  
  let find x m =
    Raw.find x (this m)
  
  (** val remove : key -> 'a1 t -> 'a1 t **)
  
  let remove x m =
    Raw.remove x (this m)
  
  (** val mem : key -> 'a1 t -> bool **)
  
  let mem x m =
    Raw.mem x (this m)
  
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
  
  (** val elements : 'a1 t -> (key*'a1) list **)
  
  let elements m =
    Raw.elements (this m)
  
  (** val cardinal : 'a1 t -> nat **)
  
  let cardinal m =
    length (this m)
  
  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let fold f m i =
    Raw.fold f (this m) i
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let equal cmp0 m m' =
    Raw.equal cmp0 (this m) (this m')
 end

module Make_ord = 
 functor (X:OrderedType.OrderedType) ->
 functor (D:OrderedType.OrderedType) ->
 struct 
  module Data = D
  
  module MapS = Make(X)
  
  module MD = OrderedType.OrderedTypeFacts(D)
  
  type t = D.t MapS.t
  
  (** val cmp : D.t -> D.t -> bool **)
  
  let cmp e e' =
    match D.compare e e' with
    | OrderedType.EQ -> true
    | _ -> false
  
  (** val compare :
      D.t MapS.slist -> D.t MapS.slist -> D.t MapS.slist
      OrderedType.coq_Compare **)
  
  let rec compare l m2 =
    match l with
    | [] ->
      (match m2 with
       | [] -> OrderedType.EQ
       | p::m3 -> OrderedType.LT)
    | y::l0 ->
      (match m2 with
       | [] -> OrderedType.GT
       | p::m3 ->
         let x,e = y in
         let x',e' = p in
         let c = X.compare x x' in
         (match c with
          | OrderedType.LT -> OrderedType.LT
          | OrderedType.EQ ->
            let c0 = D.compare e e' in
            (match c0 with
             | OrderedType.LT -> OrderedType.LT
             | OrderedType.EQ ->
               let c1 = compare l0 m3 in
               (match c1 with
                | OrderedType.LT -> OrderedType.LT
                | OrderedType.EQ -> OrderedType.EQ
                | OrderedType.GT -> OrderedType.GT)
             | OrderedType.GT -> OrderedType.GT)
          | OrderedType.GT -> OrderedType.GT))
 end

