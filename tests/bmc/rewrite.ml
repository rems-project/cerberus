type sym =
  | Symbol of string

type pexpr =
  | PEval of int
  | PEtuple of pexpr list

type expr =
  | Epure of pexpr
  | Esym of sym
  | Eskip
  | Eunseq of expr list
  | Ewseq of sym option * expr * expr

(* --- *)

module type Monad = sig
  type 'a t
  val return: 'a -> 'a t
  val bind: 'a t -> ('a -> 'b t) -> 'b t
  val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  val mapM: ('a -> 'b t) -> 'a list -> ('b list) t
  val foldlM: ('a -> 'b -> 'b t) -> 'a list -> 'b -> 'b t
end


module State(St : sig type t end) = struct
  type 'a t =
    | State of (St.t -> 'a * St.t)

  let return x =
    State (fun st -> (x, st))
  let bind (State m) f =
    State (fun st ->
      let (a, st') = m st in
      let State mb = f a in
      mb st'
    )
  let (>>=) = bind
  
  let sequence ms =
    List.fold_right
      (fun m m' ->
        m  >>= fun x  ->
        m' >>= fun xs ->
        return (x::xs)
      ) ms (return [])
  
  let listM t xs = sequence (t xs)
  
  let mapM f xs =
     listM (List.map f) xs
  
  let rec foldlM f xs a =
    match xs with
      | [] ->
          return a
      | (x::xs') ->
          f x a >>= foldlM f xs'
  
  let initial_state =
    0
  
  let runState (State m) st0 : ('a * 'st) =
    m st0
end


module CounterState = struct
  include State(struct type t = int end)
  let fresh : int t =
    State (fun st -> (st, st+1))
end


module Identity : Monad = struct
  type 'a t = 'a
  let return x = x
  let bind x f = f x
  let (>>=) = bind
  let mapM = List.map
  let foldlM f a xs = List.fold_left (fun acc x -> f x acc) xs a
end











(* --- *)

module Rewriter = functor (Eff: Monad) -> struct
  include Eff
  type 'a action =
    | Unchanged
    | Update of 'a Eff.t
    | Traverse
    | ChangeDoChildrenPost of ('a Eff.t) * ('a -> 'a Eff.t) (* NOTE: the name comes from CIL *)
  
  type rewriter =
    Rewriter of (expr -> expr action)
  
  let doRewrite ((Rewriter start as rw): rewriter) (children: rewriter -> 'a -> 'a Eff.t) (node: 'a) : 'a Eff.t =
    match start node with
      | Unchanged ->
          return node
      | Update node' ->
          node'
      | Traverse ->
          children rw node
      | ChangeDoChildrenPost (m_node', post) ->
          m_node' >>= fun node' ->
          children rw node' >>= fun ch ->
          post ch
  
  let rec rewriteExpr (rw: rewriter) (e: expr) : expr Eff.t =
    doRewrite rw childrenExpr e
  
  and childrenExpr (rw: rewriter) (expr: expr) = 
    let aux = rewriteExpr rw in
    match expr with
      | Epure _
      | Esym _
      | Eskip ->
          return expr
      | Eunseq es ->
          mapM aux es >>= fun es' ->
          return (Eunseq es')
      | Ewseq (pat, e1, e2) ->
          aux e1 >>= fun e1' ->
          aux e2 >>= fun e2' ->
          return (Ewseq (pat, e1', e2'))
    end







module RW = Rewriter(CounterState)

(* left to right *)
let sequentialise: RW.rewriter =
  RW.(Rewriter begin function
    | Epure _
    | Esym _
    | Eskip ->
        Unchanged (* Traverse *)
    | Eunseq es ->
        let node' =
          match List.rev es with
            | [] ->
                return Eskip
            | [e] ->
                return e
            | e::es ->
                foldlM (fun acc e ->
                  CounterState.fresh >>= fun n ->
                  let sym = Symbol ("sym_" ^ string_of_int n) in
                  return (Ewseq (Some sym, e, acc))
                ) es e in
        ChangeDoChildrenPost (node', return)
    | Ewseq _ ->
        Traverse
  end)
