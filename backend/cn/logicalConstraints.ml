module IT = IndexTerms
module BT = BaseTypes
module SymSet = Set.Make(Sym)
open Pp


module Pred = struct

  type t = { name : string; args : IT.t list }
  type pred = t


  let pp {name; args} = 
    Pp.c_app !^name (List.map IT.pp args)

  let equal pred pred' =
    String.equal pred.name pred'.name &&
      List.equal IT.equal pred.args pred'.args

  let subst su pred = 
    {pred with args = List.map (IT.subst su) pred.args }

  let free_vars pred = 
    IT.free_vars_list pred.args

end

open Pred


type qpred = { q : Sym.t * BT.t; condition: IT.t; pred : pred }

type t = 
  | T of IT.t
  | Forall of (Sym.t * BT.t) * IT.t
  | Pred of pred
  | QPred of qpred

let pp lc = 
  let aux = function
    | T it -> 
       IT.pp it
    | Forall ((s, bt), it) ->
       Pp.c_app !^"forall" [Sym.pp s; BT.pp bt] ^^ dot ^^^ IT.pp it
    | Pred pred -> 
       Pred.pp pred
    | QPred {q; condition; pred} ->
       Pp.c_app !^"forall" [Sym.pp (fst q); BT.pp (snd q); IT.pp condition]
       ^^ dot ^^^ (Pred.pp pred)
  in
  squotes (aux lc)


let json c : Yojson.Safe.t = 
  `String (Pp.plain (pp c))



let alpha_rename_forall s' ((s, bt), body) = 
  let body = IT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) body in
  ((s, bt), body)

let alpha_rename_qpred s' { q = (s, bt); condition; pred } = 
  let su = IT.make_subst [(s, IT.sym_ (s', bt))] in
  let condition = IT.subst su condition in
  let pred = Pred.subst su pred in
  { q = (s', bt); condition; pred }
  


let subst su c = 
  match c with
  | T it -> 
     T (IT.subst su it)
  | Forall ((s, bt), body) ->
     let ((s, bt), body) = 
       if SymSet.mem s su.relevant 
       then alpha_rename_forall (Sym.fresh_same s) ((s, bt), body)
       else ((s, bt), body)
     in
     let body = IT.subst su body in
     Forall ((s, bt), body)
  | Pred pred ->
     Pred (Pred.subst su pred)
  | QPred qpred ->
     let { q; condition; pred } = 
       if SymSet.mem (fst qpred.q) su.relevant
       then alpha_rename_qpred (Sym.fresh_same (fst qpred.q)) qpred
       else qpred
     in
     let condition = IT.subst su condition in
     let pred = Pred.subst su pred in
     QPred { q; condition; pred }





let free_vars = function
  | T c -> 
     IT.free_vars c
  | Forall ((s,_), body) -> 
     SymSet.remove s (IT.free_vars body)
  | Pred pred ->
     Pred.free_vars pred
  | QPred qpred ->
     SymSet.remove (fst qpred.q)
       (SymSet.union (IT.free_vars qpred.condition)
          (Pred.free_vars qpred.pred))





let equal c c' = 
  match c, c' with
  | T it, 
    T it' -> 
     IT.equal it it'
  | Forall ((s,bt), body), 
    Forall ((s',bt'), body') ->
     Sym.equal s s' && 
       BT.equal bt bt' && IT.equal body body'
  | Pred pred, 
    Pred pred' ->
     Pred.equal pred pred'
  | QPred {q = (s, bt); condition = c; pred = p}, 
    QPred {q = (s', bt'); condition = c'; pred = p'} ->
     Sym.equal s s' && BT.equal bt bt' && IT.equal c c' && Pred.equal p p'
  | T _, _ -> 
     false
  | Forall _, _ ->
     false
  | Pred _, _ -> 
     false
  | QPred _, _ ->
     false


let t_ it = T it

let forall_ (s,bt) it = 
  Forall ((s, bt), it)










let is_sym_equality = function
  | T (IT (Bool_op (EQ (a, b)), _)) ->
     begin match IT.is_sym a, IT.is_sym b with
     | Some (s, bt), Some (s', bt') ->
        Some (s, s')
     | _ -> None
     end
  | _ -> None
 
 
