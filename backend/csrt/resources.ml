open Option
open List
open PPrint
open Pp_tools
module Loc=Locations


type t = 
  | Block of IndexTerms.t * IndexTerms.t (* size *)
  (* | Uninitialised of IndexTerms.t * Ctype.ctype *)
  | Points of IndexTerms.t * IndexTerms.t

let pp = function
  | Block (it1,it2) -> 
     parens (!^"block" ^^^ IndexTerms.pp it1 ^^^ IndexTerms.pp it2)
  (* | Uninitialised (it, ct) ->
   *    parens (!^"uninit" ^^^ IndexTerms.pp it ^^^ squotes (Pp_core_ctype.pp_ctype ct) *)
  | Points (it1,it2) -> 
     parens (!^"points" ^^^ IndexTerms.pp it1 ^^^ IndexTerms.pp it2)




let subst sym with_it t = 
  match t with
  | Block (it, it') -> 
     Block (IndexTerms.subst sym with_it it, 
             IndexTerms.subst sym with_it it')
  (* | Uninitialised (it,ct) ->
   *    Uninitialised (IndexTerms.subst sym with_it it, ct) *)
  | Points (it, it') -> 
     Points (IndexTerms.subst sym with_it it, 
             IndexTerms.subst sym with_it it')

let type_equal env t1 t2 = 
  t1 = t2                       (* todo: maybe up to variable
                                   instantiation, etc. *)

let types_equal env ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)

let unify r1 r2 res = 
  match r1, r2 with
  (* | Uninitialised (it1, ct), Uninitialised (it1', ct') ->
   *    IndexTerms.unify it1 it1' res *)
  | Points (it1, it2), Points (it1', it2') ->
     IndexTerms.unify it1 it1' res >>= fun res ->
     IndexTerms.unify it2 it2' res
  | Block (it1, it2), Block (it1', it2') ->
     IndexTerms.unify it1 it1' res >>= fun res ->
     IndexTerms.unify it2 it2' res
  | _ -> fail


let owner = function
  | Points (S (v,_), _) -> Some v
  | Block (S (v,_), _) -> Some v
  (* | Uninitialised (S v, _) -> v *)
  | _ -> None

let owned = function
  | Points (_, S (v,_)) -> [v]
  | Points (_, _) -> []
  | Block _ -> []
  (* | Uninitialised _ -> [] *)


