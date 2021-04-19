module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RE = Resources
open Pp




type clause = 
  Clause of {
      condition: LRT.t;
      outputs: Assignment.t;
    }

type predicate_definition = 
  { iargs : (Sym.t * LS.t) list;
    oargs : (Sym.t * LS.t) list;
    clauses : clause list;
  }
  

let pp_clause (Clause {condition; outputs}) =
  item "condition" (LRT.pp condition) ^/^
  item "fixes" (Assignment.pp outputs)
     

let subst_it_clause subst (Clause {condition; outputs}) =
  let condition = LRT.subst_it subst condition in
  let outputs = Assignment.subst_it subst outputs in
  Clause {condition; outputs}

let subst_var_clause subst (Clause {condition; outputs}) =
  let condition = LRT.subst_var subst condition in
  let outputs = Assignment.subst_var subst outputs in
  Clause {condition; outputs}

let subst_its_clause substs = 
  Subst.make_substs subst_it_clause substs

let subst_vars_clause substs = 
  Subst.make_substs subst_var_clause substs
  



type stored_struct_predicate =
  { pointer : Sym.t;
    value : Sym.t;
    clause: LRT.t * IT.t; 
  }


let stored_struct_predicate_to_predicate tag pred = 
  let iargs = [(pred.pointer, BT.Loc)] in
  let oargs = [(pred.value, BT.Option (BT.Struct tag))] in
  let condition = fst pred.clause in
  let outputs = [snd pred.clause] in
  {iargs; oargs; clauses = [Clause {condition; outputs}]}








