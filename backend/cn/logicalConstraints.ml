module IT = IndexTerms
module BT = BaseTypes
module SymSet = Set.Make(Sym)
open Pp


type trigger = 
  | T_Term of IT.t
  | T_App of trigger * trigger
  | T_Member of trigger * BT.member

type t = 
  | T of IT.t
  | Forall of  (Sym.t * BT.t) * trigger option * IT.t

let pp = function
  | T it -> 
     Pp.dquotes (IT.pp it)
  | Forall ((s, bt), trigger, it) ->
     Pp.dquotes (Pp.c_app !^"forall" [Sym.pp s; BT.pp bt] ^^ dot ^^^ IT.pp it)


let json c : Yojson.Safe.t = 
  `String (Pp.plain (pp c))


let rec subst_var_trigger substitution t = 
  match t with
  | T_Term it ->
     let it = IT.subst_var substitution it in
     T_Term it
  | T_App (t, t') -> 
     let t = subst_var_trigger substitution t in
     let t' = subst_var_trigger substitution t' in
     T_App (t, t')
  | T_Member (t, member) ->
     let t = subst_var_trigger substitution t in
     T_Member (t, member)

let rec subst_it_trigger substitution t = 
  match t with
  | T_Term it ->
     let it = IT.subst_it substitution it in
     T_Term it
  | T_App (t, t') -> 
     let t = subst_it_trigger substitution t in
     let t' = subst_it_trigger substitution t' in
     T_App (t, t')
  | T_Member (t, member) ->
     let t = subst_it_trigger substitution t in
     T_Member (t, member)


let subst_var substitution c = 
  match c with
  | T it -> 
     T (IT.subst_var substitution it)
  | Forall ((s, bt), trigger, body) ->
     let s' = Sym.fresh_same s in 
     let substitution' = Subst.{before = s; after = s'} in
     let trigger = Option.map (subst_var_trigger substitution') trigger in
     let trigger = Option.map (subst_var_trigger substitution) trigger in
     let body = IT.subst_var substitution' body in
     let body = IT.subst_var substitution body in
     Forall ((s', bt), trigger, body)

let subst_it substitution c = 
  match c with
  | T it -> 
     T (IT.subst_it substitution it)
  | Forall ((s, bt), trigger, body) ->
     let s' = Sym.fresh_same s in 
     let substitution' = Subst.{before = s; after = s'} in
     let trigger = Option.map (subst_var_trigger substitution') trigger in
     let trigger = Option.map (subst_it_trigger substitution) trigger in
     let body = IT.subst_var substitution' body in
     let body = IT.subst_it substitution body in
     Forall ((s', bt), trigger, body)



let subst_vars c = Subst.make_substs subst_var c
let subst_its c = Subst.make_substs subst_it c

let rec free_vars_trigger = function
  | T_Term it ->
     IT.free_vars it
  | T_App (t, t') -> 
     SymSet.union (free_vars_trigger t) (free_vars_trigger t')
  | T_Member (t, member) -> 
     free_vars_trigger t

let free_vars = function
  | T c -> 
     IT.free_vars c
  | Forall ((s,_), trigger, body) -> 
     SymSet.remove s
       (SymSet.union
          (Option.value SymSet.empty (Option.map free_vars_trigger trigger))
          (IT.free_vars body))



let rec equal_trigger t t' = 
  match t, t' with
  | T_Term it, T_Term it' ->
     IT.equal it it'
  | T_App (t1, t2), T_App (t1', t2') ->
     equal_trigger t1 t1' && equal_trigger t2 t2'
  | T_Member (t, member), T_Member (t', member') ->
     equal_trigger t t' && Id.equal member member'
  | T_Term _, _ ->
     false
  | T_App _, _ -> 
     false
  | T_Member _, _ ->
     false

let equal c c' = 
  match c, c' with
  | T it, T it' -> 
     IT.equal it it'
  | Forall ((s,bt), trigger, body), Forall ((s',bt'), trigger', body') ->
     Sym.equal s s' && 
       BT.equal bt bt' && 
         Option.equal equal_trigger trigger trigger' && 
           IT.equal body body'
  | T _, _ -> 
     false
  | Forall _, _ ->
     false


let t_ it = T it

let forall_ (s,bt) trigger it = 
  Forall ((s, bt), None, it)
(* let forall_sth_ (s, bt) cond it = 
 *   Forall ((s, bt), None, IT.impl_ (cond, it))
 * let forall_trigger_ (s,bt) trigger it = 
 *   Forall ((s, bt), trigger, it) *)

