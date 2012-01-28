open Coqlib
open Datatypes
open Iteration
open Lattice
open ListSet
open Maps
open MetatheoryAtom

type __ = Obj.t

(** val successors_list :
    AtomImpl.atom list ATree.t -> AtomImpl.atom -> AtomImpl.atom list **)

let successors_list successors pc =
  match ATree.get pc successors with
    | Some l -> l
    | None -> []

module type DATAFLOW_SOLVER = 
 sig 
  module L : 
   SEMILATTICE
  
  val fixpoint :
    AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
    (AtomImpl.atom*L.t) list -> L.t AMap.t option
 end

module type NODE_SET = 
 sig 
  type t 
  
  val add : AtomImpl.atom -> t -> t
  
  val pick : t -> (AtomImpl.atom*t) option
  
  val initial : AtomImpl.atom list ATree.t -> t
 end

module Dataflow_Solver = 
 functor (LAT:SEMILATTICE) ->
 functor (NS:NODE_SET) ->
 struct 
  module L = LAT
  
  type state = { st_in : L.t AMap.t; st_wrk : NS.t }
  
  (** val state_rect : (L.t AMap.t -> NS.t -> 'a1) -> state -> 'a1 **)
  
  let state_rect f s =
    let { st_in = x; st_wrk = x0 } = s in f x x0
  
  (** val state_rec : (L.t AMap.t -> NS.t -> 'a1) -> state -> 'a1 **)
  
  let state_rec f s =
    let { st_in = x; st_wrk = x0 } = s in f x x0
  
  (** val st_in : state -> L.t AMap.t **)
  
  let st_in s =
    s.st_in
  
  (** val st_wrk : state -> NS.t **)
  
  let st_wrk s =
    s.st_wrk
  
  (** val start_state_in : (AtomImpl.atom*L.t) list -> L.t AMap.t **)
  
  let rec start_state_in = function
    | [] -> AMap.init L.bot
    | p::rem ->
        let n,v = p in
        let m = start_state_in rem in AMap.set n (L.lub (AMap.get n m) v) m
  
  (** val start_state :
      AtomImpl.atom list ATree.t -> (AtomImpl.atom*L.t) list -> state **)
  
  let start_state successors entrypoints =
    { st_in = (start_state_in entrypoints); st_wrk =
      (NS.initial successors) }
  
  (** val propagate_succ : state -> L.t -> AtomImpl.atom -> state **)
  
  let propagate_succ s out n =
    let oldl = AMap.get n (st_in s) in
    let newl = L.lub oldl out in
    if L.beq oldl newl
    then s
    else { st_in = (AMap.set n newl (st_in s)); st_wrk =
           (NS.add n (st_wrk s)) }
  
  (** val propagate_succ_list :
      state -> L.t -> AtomImpl.atom list -> state **)
  
  let rec propagate_succ_list s out = function
    | [] -> s
    | n::rem -> propagate_succ_list (propagate_succ s out n) out rem
  
  (** val step :
      AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) -> state ->
      (L.t AMap.t, state) sum **)
  
  let step successors transf s =
    match NS.pick (st_wrk s) with
      | Some p ->
          let n,rem = p in
          Coq_inr
          (propagate_succ_list { st_in = (st_in s); st_wrk = rem }
            (transf n (AMap.get n (st_in s))) (successors_list successors n))
      | None -> Coq_inl (st_in s)
  
  (** val fixpoint :
      AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
      (AtomImpl.atom*L.t) list -> L.t AMap.t option **)
  
  let fixpoint successors transf entrypoints =
    PrimIter.iterate (step successors transf)
      (start_state successors entrypoints)
 end

(** val add_successors :
    AtomImpl.atom list ATree.t -> AtomImpl.atom -> AtomImpl.atom list ->
    AtomImpl.atom list ATree.t **)

let rec add_successors pred from = function
  | [] -> pred
  | to0::rem ->
      add_successors (ATree.set to0 (from::(successors_list pred to0)) pred)
        from rem

(** val make_predecessors :
    AtomImpl.atom list ATree.t -> AtomImpl.atom list ATree.t **)

let make_predecessors successors =
  ATree.fold add_successors successors ATree.empty

module type BACKWARD_DATAFLOW_SOLVER = 
 sig 
  module L : 
   SEMILATTICE
  
  val fixpoint :
    AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
    (AtomImpl.atom*L.t) list -> L.t AMap.t option
 end

module Backward_Dataflow_Solver = 
 functor (LAT:SEMILATTICE) ->
 functor (NS:NODE_SET) ->
 struct 
  module L = LAT
  
  module DS = Dataflow_Solver(L)(NS)
  
  (** val fixpoint :
      AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
      (AtomImpl.atom*L.t) list -> DS.L.t AMap.t option **)
  
  let fixpoint successors transf entrypoints =
    DS.fixpoint (make_predecessors successors) transf entrypoints
 end

module type ORDERED_TYPE_WITH_TOP = 
 sig 
  type t 
  
  val top : t
 end

module type BBLOCK_SOLVER = 
 sig 
  module L : 
   ORDERED_TYPE_WITH_TOP
  
  val fixpoint :
    AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
    AtomImpl.atom -> L.t AMap.t option
 end

module BBlock_solver = 
 functor (LAT:ORDERED_TYPE_WITH_TOP) ->
 struct 
  module L = LAT
  
  type bbmap = AtomImpl.atom -> bool
  
  type result = L.t AMap.t
  
  type state = { st_in : result; st_wrk : AtomImpl.atom list }
  
  (** val state_rect :
      (result -> AtomImpl.atom list -> 'a1) -> state -> 'a1 **)
  
  let state_rect f s =
    let { st_in = x; st_wrk = x0 } = s in f x x0
  
  (** val state_rec :
      (result -> AtomImpl.atom list -> 'a1) -> state -> 'a1 **)
  
  let state_rec f s =
    let { st_in = x; st_wrk = x0 } = s in f x x0
  
  (** val st_in : state -> result **)
  
  let st_in s =
    s.st_in
  
  (** val st_wrk : state -> AtomImpl.atom list **)
  
  let st_wrk s =
    s.st_wrk
  
  (** val propagate_successors :
      bbmap -> AtomImpl.atom list -> L.t -> state -> state **)
  
  let rec propagate_successors bb succs l st =
    match succs with
      | [] -> st
      | s1::sl ->
          if bb s1
          then propagate_successors bb sl l st
          else propagate_successors bb sl l { st_in =
                 (AMap.set s1 l (st_in st)); st_wrk = (s1::
                 (st_wrk st)) }
  
  (** val step :
      AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) -> bbmap ->
      state -> (result, state) sum **)
  
  let step successors transf bb st =
    match st_wrk st with
      | [] -> Coq_inl (st_in st)
      | pc::rem -> Coq_inr
          (propagate_successors bb (successors_list successors pc)
            (transf pc (AMap.get pc (st_in st))) { st_in = 
            (st_in st); st_wrk = rem })
  
  (** val is_basic_block_head :
      AtomImpl.atom -> AtomImpl.atom list ATree.t -> AtomImpl.atom -> bool **)
  
  let is_basic_block_head entrypoint preds pc =
    if AtomImpl.eq_atom_dec pc entrypoint
    then true
    else (match successors_list preds pc with
            | [] -> false
            | s::l ->
                (match l with
                   | [] -> proj_sumbool (AtomImpl.eq_atom_dec s pc)
                   | a::l0 -> true))
  
  (** val basic_block_map :
      AtomImpl.atom list ATree.t -> AtomImpl.atom -> bbmap **)
  
  let basic_block_map successors entrypoint =
    is_basic_block_head entrypoint (make_predecessors successors)
  
  (** val basic_block_list :
      AtomImpl.atom list ATree.t -> bbmap -> AtomImpl.atom list **)
  
  let basic_block_list successors bb =
    ATree.fold (fun l pc scs -> if bb pc then pc::l else l) successors []
  
  (** val fixpoint :
      AtomImpl.atom list ATree.t -> (AtomImpl.atom -> L.t -> L.t) ->
      AtomImpl.atom -> result option **)
  
  let fixpoint successors transf entrypoint =
    let bb = basic_block_map successors entrypoint in
    PrimIter.iterate (step successors transf bb) { st_in = 
      (AMap.init L.top); st_wrk = (basic_block_list successors bb) }
  
  (** val predecessors :
      AtomImpl.atom list ATree.t -> AtomImpl.atom list ATree.t **)
  
  let predecessors successors =
    make_predecessors successors
 end

module AtomNodeSet = 
 struct 
  type t = AtomImpl.atom set
  
  (** val add : AtomImpl.atom -> t -> t **)
  
  let add n s =
    set_add AtomImpl.eq_atom_dec n s
  
  (** val pick : t -> (AtomImpl.atom*AtomImpl.atom set) option **)
  
  let pick = function
    | [] -> None
    | n::s' -> Some (n,(set_remove AtomImpl.eq_atom_dec n s'))
  
  (** val initial : AtomImpl.atom list ATree.t -> t **)
  
  let initial successors =
    ATree.fold (fun s pc scs -> add pc s) successors empty_set
 end

module Dataflow_Solver_Var_Top = 
 functor (NS:NODE_SET) ->
 struct 
  module L = Dominators
  
  type dt = L.t
  
  type state = { st_in : dt AMap.t; st_wrk : NS.t }
  
  (** val state_rect :
      AtomImpl.atom set -> (dt AMap.t -> NS.t -> 'a1) -> state -> 'a1 **)
  
  let state_rect bound f s =
    let { st_in = x; st_wrk = x0 } = s in f x x0
  
  (** val state_rec :
      AtomImpl.atom set -> (dt AMap.t -> NS.t -> 'a1) -> state -> 'a1 **)
  
  let state_rec bound f s =
    let { st_in = x; st_wrk = x0 } = s in f x x0
  
  (** val st_in : AtomImpl.atom set -> state -> dt AMap.t **)
  
  let st_in bound s =
    s.st_in
  
  (** val st_wrk : AtomImpl.atom set -> state -> NS.t **)
  
  let st_wrk bound s =
    s.st_wrk
  
  (** val start_state_in :
      AtomImpl.atom set -> (AtomImpl.atom*dt) list -> dt AMap.t **)
  
  let rec start_state_in bound = function
    | [] -> AMap.init (L.bot bound)
    | p::rem ->
        let n,v = p in
        let m = start_state_in bound rem in
        AMap.set n (L.lub bound (AMap.get n m) v) m
  
  (** val start_state :
      AtomImpl.atom set -> AtomImpl.atom list ATree.t -> (AtomImpl.atom*dt)
      list -> state **)
  
  let start_state bound successors entrypoints =
    { st_in = (start_state_in bound entrypoints); st_wrk =
      (NS.initial successors) }
  
  (** val propagate_succ :
      AtomImpl.atom set -> state -> dt -> AtomImpl.atom -> state **)
  
  let propagate_succ bound s out n =
    let oldl = AMap.get n (st_in bound s) in
    let newl = L.lub bound oldl out in
    if L.beq bound oldl newl
    then s
    else { st_in = (AMap.set n newl (st_in bound s)); st_wrk =
           (NS.add n (st_wrk bound s)) }
  
  (** val propagate_succ_list :
      AtomImpl.atom set -> state -> dt -> AtomImpl.atom set -> state **)
  
  let rec propagate_succ_list bound s out = function
    | [] -> s
    | n::rem ->
        propagate_succ_list bound (propagate_succ bound s out n) out rem
  
  (** val step :
      AtomImpl.atom set -> AtomImpl.atom list ATree.t -> (AtomImpl.atom -> dt
      -> dt) -> state -> (dt AMap.t, state) sum **)
  
  let step bound successors transf s =
    match NS.pick (st_wrk bound s) with
      | Some p ->
          let n,rem = p in
          Coq_inr
          (propagate_succ_list bound { st_in = (st_in bound s); st_wrk =
            rem } (transf n (AMap.get n (st_in bound s)))
            (successors_list successors n))
      | None -> Coq_inl (st_in bound s)
  
  (** val fixpoint :
      AtomImpl.atom set -> AtomImpl.atom list ATree.t -> (AtomImpl.atom -> dt
      -> dt) -> (AtomImpl.atom*dt) list -> dt AMap.t option **)
  
  let fixpoint bound successors transf entrypoints =
    PrimIter.iterate (step bound successors transf)
      (start_state bound successors entrypoints)
  
  type dt1 = L.t
  
  type dt2 = L.t
 end

