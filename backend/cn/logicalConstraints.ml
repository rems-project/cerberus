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



let subst su c = 
  match c with
  | T it -> 
     T (IT.subst su it)
  | Forall ((s, bt), body) ->
     let s, body = IT.suitably_alpha_rename su (s, bt) body in
     Forall ((s, bt), IT.subst su body)

let subst_ su c = 
  subst (IT.make_subst su) c


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



let is_equality = function
  | T it ->
     begin match it with
     | IT (Bool_op (EQ (a, b)), _) -> Some ((a, b), true)
     | IT (Bool_op (Not (IT (Bool_op (EQ (a, b)), _))), _) -> Some ((a, b), false)
     | _ -> None
     end
  | _ -> 
     None

