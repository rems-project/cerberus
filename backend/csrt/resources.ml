open List
open PPrint
open Pp_tools
open Except
module Loc=Location


type t = 
  (* | Block of IndexTerms.t * IndexTerms.t
   * | Int of IndexTerms.t * IndexTerms.t (\* location and value *\)
   * | Array of IndexTerms.t * IndexTerms.t
   * | Pred of string * IndexTerms.t list *)
  | Points of IndexTerms.t * IndexTerms.t

let pp = function
  (* | Block (it1,it2) -> 
   *    sprintf "(block %s %s)" 
   *      (IndexTerms.pp it1)
   *      (IndexTerms.pp it2) *)
  (* | Bool (it1,it2) -> 
   *    sprintf "(bool %s %s)" 
   *      (IndexTerms.pp it1) 
   *      (IndexTerms.pp it2)
   * | Int (it1,it2) -> 
   *    sprintf "(int %s %s)" 
   *      (IndexTerms.pp it1) 
   *      (IndexTerms.pp it2)
   * | Array (it1,it2) -> 
   *    sprintf "(array %s %s)" 
   *      (IndexTerms.pp it1)
   *      (IndexTerms.pp it2) *)
  | Points (it1,it2) -> 
     parens (!^ "points" ^^^ IndexTerms.pp it1 ^^^ IndexTerms.pp it2)
  (* | Pred (p,its) ->
   *    sprintf "(%s %s)" 
   *      p
   *      (String.concat " " (map IndexTerms.pp its)) *)



let subst sym with_it t = 
  match t with
  (* | Block (it, it') -> 
   *    Block (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it') *)
  (* | Bool (it, it') -> 
   *    Bool (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it')
   * | Int (it, it') -> 
   *    Int (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it')
   * | Points (it, it') -> 
   *    Points (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it')
   * | Array (it, it') -> 
   *    Array (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it') *)
  | Points (it, it') -> 
     Points (IndexTerms.subst sym with_it it, 
             IndexTerms.subst sym with_it it')
  (* | Pred (p, its) ->
   *    Pred (p, map (IndexTerms.subst sym with_it) its) *)

let type_equal env t1 t2 = 
  t1 = t2                       (* todo: maybe up to variable
                                   instantiation, etc. *)

let types_equal env ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)

let unify r1 r2 res = 
  match r1, r2 with
  (* | Block (it1, it2), Block (it1', it2') ->
   *    IndexTerms.unify it1 it1' res >>= fun res ->
   *    IndexTerms.unify it2 it2' res *)
  (* | Bool (it1, it2), Bool (it1', it2') -> 
   *    IndexTerms.unify it1 it1' res >>= fun res ->
   *    IndexTerms.unify it2 it2' res
   * | Int (it1, it2), Int (it1', it2') -> 
   *    IndexTerms.unify it1 it1' res >>= fun res ->
   *    IndexTerms.unify it2 it2' res *)
  (* | Array (it1, it2), Array (it1', it2') -> 
   *    IndexTerms.unify it1 it1' res >>= fun res ->
   *    IndexTerms.unify it2 it2' res *)
  | Points (it1, it2), Points (it1', it2') ->
     IndexTerms.unify it1 it1' res >>= fun res ->
     IndexTerms.unify it2 it2' res
  (* | Pred (p, its), Pred (p', its') when p = p' ->
   *    IndexTerms.unify_list its its' res *)
  (* | _, _ -> fail () *)

let owner = function
  | Points (S v, _) -> v
  | Points (_, _) -> failwith "no owner"

let owned = function
  | Points (_, S v) -> [v]
  | Points (_, _) -> failwith "nothing owned"

