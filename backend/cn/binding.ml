module LRT=LogicalReturnTypes
module RT=ReturnTypes
module IT=IndexTerms
module LC=LogicalConstraints

open Typing
open WellTyped
open IT




(* This essentially pattern-matches a logical return type against a
   record pattern. `record_it` is the index term for the record,
   `members` the pattern for its members. *)
let bind_logical_return loc record_it = 
  let rec aux members lrt = 
    match members, lrt with
    | (member_s, member_bt) :: members, 
      LRT.Define ((s, it), _, lrt) ->
       let@ () = ensure_base_type loc ~expect:(IT.bt it) member_bt in
       let inst_it = recordMember_ ~member_bt (record_it, member_s) in
       let@ () = add_c (LC.t_ (eq__ inst_it it)) in
       aux members (LRT.subst (IT.make_subst [(s, inst_it)]) lrt)
    | (member_s, member_bt) :: members,
      LRT.Resource ((s, (re, bt)), _, lrt) -> 
       let@ () = ensure_base_type loc ~expect:bt member_bt in
       let inst_it = recordMember_ ~member_bt (record_it, member_s) in
       let@ () = add_r (re, O inst_it) in
       aux members (LRT.subst (IT.make_subst [(s, inst_it)]) lrt)
    | members,
      LRT.Constraint (lc, _, lrt) -> 
       let@ () = add_c lc in
       aux members lrt
    | [],
      I -> 
       return ()
    | _ ->
       assert false
  in
  fun members lrt -> aux members lrt


(* Same for return types *)
let bind_return loc record_it members (rt : RT.t) =
  match members, rt with
  | (member_s, member_bt) :: members,
    Computational ((s, bt), _, lrt) ->
     let@ () = ensure_base_type loc ~expect:bt member_bt in
     let inst_it = recordMember_ ~member_bt (record_it, member_s) in
     let@ () = bind_logical_return loc record_it members 
                 (LRT.subst (IT.make_subst [(s, inst_it)]) lrt) in
     return inst_it
  | _ ->
     assert false


let make_return_record loc call_situation record_members = 
  let record_s = Sym.fresh_make_uniq (TypeErrors.call_prefix call_situation) in
  let record_bt = BT.Record record_members in
  let@ () = add_l record_s record_bt (loc, lazy (Sym.pp record_s)) in
  return (sym_ (record_s, record_bt))
