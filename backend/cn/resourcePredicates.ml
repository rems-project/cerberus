module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RE = Resources
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module StringMap = Map.Make(String)
module Loc = Locations
open Pp

module LP = LogicalPredicates

type clause = {
    loc : Loc.t;
    guard : IT.t;
    packing_ft : LAT.packing_ft
  }

let pp_clause {loc; guard; packing_ft} = 
  item "condition" (IT.pp guard) ^^ comma ^^^
  item "return type" (LAT.pp OutputDef.pp packing_ft)

let subst_clause subst {loc; guard; packing_ft} = 
  { loc = loc;
    guard = IT.subst subst guard; 
    packing_ft = LAT.subst OutputDef.subst subst packing_ft }


let clause_lrt pred_oargs clause_packing_ft = 
  let rec aux = function
    | LAT.Define (bound, info, lat) -> LRT.Define (bound, info, aux lat)
    | LAT.Resource (bound, info, lat) -> LRT.Resource (bound, info, aux lat)
    | LAT.Constraint (lc, info, lat) -> LRT.Constraint (lc, info, aux lat)
    | I outputs ->
       let lc = LC.t_ (IT.eq_ (pred_oargs, OutputDef.to_record outputs)) in
       LRT.Constraint (lc, (Loc.unknown, None), LRT.I)
  in
  aux clause_packing_ft



type definition = {
    loc : Loc.t;
    pointer: Sym.t;
    iargs : (Sym.t * LS.t) list;
    oargs : (Sym.t * LS.t) list;
    clauses : (clause list) option;
  }


let alpha_rename_definition def = 
  let iargs, subst = 
    List.fold_right (fun (s, ls) (iargs, subst) ->
        let s' = Sym.fresh_same s in
        ((s', ls) :: iargs, (s, IT.sym_ (s', ls)) :: subst)
      ) def.iargs ([],[])
  in
  let pointer = Sym.fresh_same def.pointer in
  let subst = IT.make_subst ((def.pointer, IT.sym_ (pointer, BT.Loc)) :: subst) in
  let clauses = Option.map (List.map (subst_clause subst)) def.clauses in
  { loc = def.loc; pointer; iargs; oargs = def.oargs; clauses }
  



let pp_definition def = 
  item "pointer" (Sym.pp def.pointer) ^/^
  item "iargs" (Pp.list (fun (s,_) -> Sym.pp s) def.iargs) ^/^
  item "oargs" (Pp.list (fun (s,_) -> Sym.pp s) def.oargs) ^/^
  item "clauses" (match def.clauses with
                  | Some clauses -> Pp.list pp_clause clauses
                  | None -> !^"(uninterpreted)")


let instantiate_clauses def ptr_arg iargs = match def.clauses with
  | Some clauses ->
    let subst = IT.make_subst (
        (def.pointer, ptr_arg) ::
        List.map2 (fun (def_ia, _) ia -> (def_ia, ia)) def.iargs iargs
      )
    in
    Some (List.map (subst_clause subst) clauses)
  | None -> None
  

(* let byte_sym = Sym.fresh_named "Legacy_Internal_Byte" *)
(* let char_sym = Sym.fresh_named "Legacy_Internal_Char" *)
(* let bytev_sym = Sym.fresh_named "Legacy_Internal_ByteV" *)
(* let early_alloc_sym = Sym.fresh_named "EarlyAlloc" *)


(* let byte () =  *)
(*   let loc = Loc.other "internal (Byte)" in *)
(*   let pointer_s, pointer = IT.fresh Loc in *)
(*   let resource_s, resource = IT.fresh (owned_oargs (Integer Char)) in *)
(*   let point = (P { *)
(*       name = Owned (Integer Char);  *)
(*       pointer = pointer; *)
(*       iargs = []; *)
(*       permission = bool_ true; *)
(*     }, *)
(*     owned_oargs (Integer Char)) *)
(*   in *)
(*   let lrt = *)
(*     LRT.Resource ((resource_s, point), (loc, None), *)
(*     LRT.I) *)
(*   in *)
(*   let clause = { *)
(*       loc = loc; *)
(*       guard = bool_ true; *)
(*       packing_ft = LAT.of_lrt lrt (LAT.I [])  *)
(*     } *)
(*   in *)
(*   let predicate = { *)
(*       loc = loc; *)
(*       pointer = pointer_s; *)
(*       iargs = [];  *)
(*       oargs = [];  *)
(*       clauses = Some [clause];  *)
(*     }  *)
(*   in *)
(*   (byte_sym, predicate) *)


(* let char () =  *)
(*   let id = char_sym in *)
(*   let loc = Loc.other "internal (Char)" in *)
(*   let pointer_s, pointer = IT.fresh Loc in *)


(*   let point = (P { *)
(*       name = Owned (Integer Char);  *)
(*       pointer = pointer; *)
(*       iargs = []; *)
(*       permission = bool_ true; *)
(*     }, *)
(*     owned_oargs (Integer Char)) *)
(*   in *)

(*   let resource_s, resource = IT.fresh (snd point) in *)

(*   let lrt = *)
(*     LRT.Resource ((resource_s, point), (loc, None), *)
(*     LRT.I) *)
(*   in *)
(*   let value_s_o = Sym.fresh_named "value" in   *)
(*   let clause = { *)
(*       loc = loc; *)
(*       guard = bool_ true; *)
(*       packing_ft = LAT.of_lrt lrt (LAT.I [OutputDef.{loc; name = value_s_o; value = recordMember_ ~member_bt:Integer (resource, value_sym)}])  *)
(*     } *)
(*   in *)
(*   let predicate = { *)
(*       loc = loc; *)
(*       pointer = pointer_s; *)
(*       iargs = [];  *)
(*       oargs = [(value_s_o, Integer)];  *)
(*       clauses = Some [clause];  *)
(*     }  *)
(*   in *)
(*   (id, predicate) *)





(* let bytev () =  *)
(*   let id = bytev_sym in *)
(*   let loc = Loc.other "internal (ByteV)" in *)
(*   let pointer_s, pointer = IT.fresh Loc in *)
(*   let the_value_s, the_value = IT.fresh Integer in *)
(*   let point = (P { *)
(*       name = Owned (Integer Char);  *)
(*       pointer = pointer; *)
(*       iargs = []; *)
(*       permission = bool_ true; *)
(*     },  *)
(*     owned_oargs (Integer Char)) *)
(*   in *)
(*   let resource_s, resource = IT.fresh (snd point) in *)

(*   let has_value =  *)
(*     eq_ (recordMember_ ~member_bt:BT.Integer (resource, value_sym),  *)
(*          the_value) *)
(*   in *)

(*   let lrt = *)
(*     LRT.Resource ((resource_s, point), (loc, None), *)
(*     LRT.Constraint (t_ has_value, (loc, None),  *)
(*     LRT.I)) *)
(*   in *)
(*   let clause = { *)
(*       loc = loc; *)
(*       guard = bool_ true; *)
(*       packing_ft = LAT.of_lrt lrt (LAT.I [])  *)
(*     } *)
(*   in *)
(*   let predicate = { *)
(*       loc = loc; *)
(*       pointer = pointer_s; *)
(*       iargs = [(the_value_s, IT.bt the_value)];  *)
(*       oargs = [];  *)
(*       clauses = Some [clause];  *)
(*     }  *)
(*   in *)
(*   (id, predicate) *)






let predicate_list struct_decls logical_pred_syms =
  (* char () :: *)
  (* byte () :: *)
  (* bytev () :: *)
  (* early_alloc () :: *)
  []

    




