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
  { pointer: Sym.t;
    iargs : (Sym.t * LS.t) list;
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
  



type ctype_predicate =
  { pointer : Sym.t;
    value : Sym.t;
    clause: LRT.t * IT.t; 
  }


let ctype_predicate_to_predicate ct pred = 
  let iargs = [] in
  let oargs = [(pred.value, BT.Option (BT.of_sct ct))] in
  let condition = fst pred.clause in
  let outputs = [snd pred.clause] in
  {pointer = pred.pointer; 
   iargs; 
   oargs; 
   clauses = [Clause {condition; outputs}]}






let ctype_predicate struct_layouts ct = 
  let open ReturnTypes in
  let open LRT in
  let open IndexTerms in
  let open BaseTypes in
  let open Memory in
  let open Resources in
  let open Option in
  let open Sctypes in
  let pointer_s = Sym.fresh_named "p" in
  let pointer_t = sym_ (pointer_s, Loc) in
  let (Sctypes.Sctype (_, ct_)) = ct in
  match ct_ with
  | Void ->
     Debug_ocaml.error "ctype_predicate void"
  | Integer it ->
     let size = size_of_ctype ct in
     let ovalue_s = Sym.fresh_named "v" in
     let ovalue_t = sym_ (ovalue_s, BT.Option BT.Integer) in
     let is_some = is_some_ ovalue_t in
     let lrt = 
       Logical ((ovalue_s, BT.Option BT.Integer), 
       Resource (point (pointer_t, size) (q_ (1,1)) ovalue_t, 
       Constraint (impl_ (is_some, IT.representable_ (ct, value_of_some_ ovalue_t)), LRT.I)))
     in
     let clause = (lrt, ovalue_t) in
     return { pointer = pointer_s; value = ovalue_s; clause }
  | Pointer (_, ct') ->
     let size = size_of_ctype ct in
     let ovalue_s = Sym.fresh_named "v" in
     let ovalue_t = sym_ (ovalue_s, BT.Option BT.Loc) in
     let is_some = is_some_ ovalue_t in
     let lrt = 
       Logical ((ovalue_s, BT.Option BT.Loc), 
       Resource (point (pointer_t, size) (q_ (1,1)) ovalue_t, 
       Constraint (impl_ (is_some, IT.good_pointer (value_of_some_ ovalue_t) ct'), LRT.I)))
     in
     let clause = (lrt, ovalue_t) in
     return { pointer = pointer_s; value = ovalue_s; clause }     
  | Array (t, None) ->
     (* todo: connect with user-annotation *)
     Debug_ocaml.error "representation: array of unknown length"
  | Array (ct', Some length) ->
     let start = pointer_t in
     let step = z_ (size_of_ctype ct') in
     let stop = addPointer_ (start, mul_ (step, int_ length)) in
     let qp_s = Sym.fresh () in 
     let qp_t = sym_ (qp_s, BT.Loc) in
     let ovalue_s = Sym.fresh_named "v" in
     let ov'_s = Sym.fresh_named "v'" in
     let ov'_bt = BT.Param ([BT.Integer], BT.Option (BT.of_sct ct')) in
     let ov'_t = sym_ (ov'_s, ov'_bt) in
     let i = 
       div_ (sub_ (pointerToIntegerCast_ qp_t ,
                   pointerToIntegerCast_ start),
             step)
     in
     let pred = predicateP (Ctype ct') qp_t [] [app_ ov'_t [i]] in
     let qpredicate = {
         start;
         step;
         stop;
         moved = [];
         unused = true;
         name = pred.name;
         pointer = qp_s;
         iargs = pred.iargs;
         oargs = pred.oargs;
       }
     in
     let lrt = 
       Logical ((ov'_s, ov'_bt), 
       Resource (QPredicate qpredicate, LRT.I))
     in
     let ovalue_t = 
       let j = Sym.fresh () in
       let all_init = 
         forall_ (qp_s, BT.Loc) 
           (impl_ (is_qpredicate_instance qpredicate qp_t,
                   is_some_ (app_ ov'_t [i])))
       in
       let init_case_map = 
         param_ [(j, BT.Integer)]
           (value_of_some_ (app_ ov'_t [sym_ (j, BT.Integer)]))
       in
       ite_ (all_init,
             init_case_map,
             nothing_ (BT.of_sct ct))
     in
     let clause = (lrt, ovalue_t) in
     return { pointer = pointer_s; value = ovalue_s; clause }
  | Struct tag ->
     let ostruct_value_s = Sym.fresh_named "v" in
     let@ layout = struct_layouts tag in
     let clause = 
       let (lrt, lcs, values) = 
         List.fold_right (fun {offset; size; member_or_padding} (lrt, lcs, values) ->
             let member_p = addPointer_ (pointer_t, z_ offset) in
             match member_or_padding with
             | Some (member, sct) ->
                let omember_v = Sym.fresh () in
                let omember_t = sym_ (omember_v, BT.Option (BT.of_sct sct)) in
                let (Sctypes.Sctype (annots, sct_)) = sct in
                let resource = predicate (Ctype sct) member_p [] [omember_t] in
                let lrt = 
                  LRT.Logical ((omember_v, BT.Option (BT.of_sct sct)),
                               LRT.Resource (resource, lrt)) in
                let lcs = is_some_ omember_t :: lcs in
                let value = (member, value_of_some_ omember_t) :: values in
                (lrt, lcs, value)
             | None ->
                let resource = point (member_p, size) (q_ (1,1)) (nothing_ BT.Integer) in
                let lrt = LRT.Resource (resource, lrt) in
                (lrt, lcs, values)
           ) layout (LRT.I, [], [])
       in
       let ovalue_t = ite_ (and_ lcs, something_ (IT.struct_ (tag, values)), nothing_ (BT.Struct tag)) in
       let lrt = lrt @@ Constraint (impl_ (and_ lcs, IT.representable_ (ct, value_of_some_ ovalue_t)), LRT.I) in
       (lrt, ovalue_t)
    in
    return { pointer = pointer_s; value = ostruct_value_s; clause }
  | Function _ -> 
     Debug_ocaml.error "todo: function ctype predicate"

