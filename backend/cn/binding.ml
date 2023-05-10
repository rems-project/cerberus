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
let bind_logical_return loc = 
  let rec aux members lrt = 
    match members, lrt with
    | member :: members, 
      LRT.Define ((s, it), _, lrt) ->
       let@ () = ensure_base_type loc ~expect:(IT.bt it) (IT.bt member) in
       let@ () = add_c (LC.t_ (eq__ member it)) in
       aux members (LRT.subst (IT.make_subst [(s, member)]) lrt)
    | member :: members,
      LRT.Resource ((s, (re, bt)), _, lrt) -> 
       let@ () = ensure_base_type loc ~expect:bt (IT.bt member) in
       let@ () = add_r loc (re, O member) in
       aux members (LRT.subst (IT.make_subst [(s, member)]) lrt)
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
let bind_return loc members (rt : RT.t) =
  match members, rt with
  | member :: members,
    Computational ((s, bt), _, lrt) ->
     let@ () = ensure_base_type loc ~expect:bt (IT.bt member) in
     let@ () = bind_logical_return loc members 
                 (LRT.subst (IT.make_subst [(s, member)]) lrt) in
     return member
  | _ ->
     assert false


let make_return_record loc call_situation record_members = 
  let record_s = Sym.fresh_make_uniq (TypeErrors.call_prefix call_situation) in
  let record_bt = BT.Record record_members in
  let@ () = add_l record_s record_bt (loc, lazy (Sym.pp record_s)) in
  let record_it = sym_ (record_s, record_bt) in
  let member_its = 
    List.map (fun (s, member_bt) -> 
        IT.recordMember_ ~member_bt (record_it, s)
      ) record_members 
  in
  return (record_it, member_its)
