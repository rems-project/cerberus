module Loc = Locations
module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints

open Pp

open Kind

type solver_constraint = Z3.Expr.expr

type bound =
  | Computational of Sym.t * BT.t
  | Logical of LS.t
  | Resource of RE.t
  | UsedResource of RE.t * Loc.t list
  | Constraint of LC.t * solver_constraint

type binding = Sym.t * bound


let kind = function
  | Computational _ -> KComputational
  | Logical _ -> KLogical
  | Resource _ -> KResource
  | Constraint _ -> KConstraint
  | UsedResource _ -> KUsedResource 




let pp ?(print_all_names = false) ?(print_used = false) (sym,binding) =
  let btyp sym pped = format [Bold] (Sym.pp_string sym) ^^ colon ^^ pped in
  match binding with
  | Computational (lname,bt) -> 
     btyp sym (BT.pp bt ^^ tilde ^^ Sym.pp lname)
  | Logical ls -> 
     btyp sym (LS.pp ls)
  | Resource re -> 
     if print_all_names 
     then btyp sym (squotes (RE.pp re))
     else squotes (RE.pp re)
  | UsedResource (re,_locs) -> 
     if not print_used then underscore 
     else if print_all_names 
     then btyp sym (!^"used" ^^^ (squotes (RE.pp re)))
     else !^"used" ^^^ squotes (RE.pp re)
  | Constraint (lc, _) -> 
     if print_all_names 
     then btyp sym (LC.pp lc)
     else LC.pp lc



let agree vb1 vb2 = 
  match vb1, vb2 with
  | Computational (l1,bt1), Computational (l2,bt2)
       when Sym.equal l1 l2 && BT.equal bt1 bt2 -> 
     Some (Computational (l1,bt1))
  | Logical ls1, Logical ls2 
       when LS.equal ls1 ls2 -> 
     Some (Logical ls1)
  | Constraint (lc1,sc), Constraint (lc2, _)
         when LC.equal lc1 lc2 ->
     Some (Constraint (lc1, sc))
  | Resource re1, Resource re2 
       when RE.equal re1 re2 ->
     Some (Resource re1)
  | UsedResource (re1,locs1), UsedResource (re2,locs2)
         when RE.equal re1 re2 ->
     Some (UsedResource (re1, locs1 @ locs2))
  | _, _ ->
     None



