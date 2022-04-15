module IT = IndexTerms
module BT = BaseTypes
module SymSet = Set.Make(Sym)
open Pp


type logical_constraint = 
  | T of IT.t
  | Forall of (Sym.t * BT.t) * IT.t
[@@deriving eq, ord]

type t = logical_constraint

let equal = equal_logical_constraint
let compare = compare_logical_constraint



let pp = function
  | T it -> 
     IT.pp it
  | Forall ((s, bt), it) ->
     Pp.c_app !^"forall" [Sym.pp s; BT.pp bt] ^^ dot ^^^ IT.pp it

let json c : Yojson.Safe.t = 
  `String (Pp.plain (pp c))



let alpha_rename_forall s' ((s, bt), body) = 
  let body = IT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) body in
  ((s', bt), body)

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


let free_vars = function
  | T c -> 
     IT.free_vars c
  | Forall ((s,_), body) -> 
     SymSet.remove s (IT.free_vars body)





let t_ it = T it
let forall_ (s,bt) it = Forall ((s, bt), it)



let is_sym_lhs_equality = function
  | T t ->
      begin match IT.is_eq t with
      | Some (lhs, rhs) ->
          begin match IT.is_sym lhs with
          | Some (s, _) -> Some (s, rhs)
          | _ -> None
          end
      | _ -> None
      end
  | _ -> None

let is_sym_equality t = match is_sym_lhs_equality t with
  | Some (s, rhs) -> begin match IT.is_sym rhs with
      | Some (s', _) -> Some (s, s')
      | _ -> None
      end
  | _ -> None

