open Sctypes
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RE = Resources
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module StringMap = Map.Make(String)
module Loc = Locations
open Pp
open ResourceTypes
open Resources
open BT
open IT
open LC

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





type definition = {
    loc : Loc.t;
    pointer: Sym.t;
    iargs : (Sym.t * LS.t) list;
    oargs : (Sym.t * LS.t) list;
    clauses : (clause list) option;
  }

let pp_definition def = 
  item "pointer" (Sym.pp def.pointer) ^/^
  item "iargs" (Pp.list (fun (s,_) -> Sym.pp s) def.iargs) ^/^
  item "oargs" (Pp.list (fun (s,_) -> Sym.pp s) def.oargs) ^/^
  item "clauses" (match def.clauses with
                  | Some clauses -> Pp.list pp_clause clauses
                  | None -> !^"(uninterpreted)")
  

let byte_sym = Sym.fresh_named "Byte"
let char_sym = Sym.fresh_named "Char"
let bytev_sym = Sym.fresh_named "ByteV"
let early_alloc_sym = Sym.fresh_named "EarlyAlloc"


let byte () = 
  let loc = Loc.other "internal (Byte)" in
  let pointer_s, pointer = IT.fresh Loc in
  let resource_s, resource = IT.fresh (owned_oargs (Integer Char)) in
  let point = (P {
      name = Owned (Integer Char); 
      pointer = pointer;
      iargs = [];
      permission = bool_ true;
    },
    owned_oargs (Integer Char))
  in
  let lrt =
    LRT.Resource ((resource_s, point), (loc, None),
    LRT.I)
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = LAT.of_lrt lrt (LAT.I []) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = []; 
      oargs = []; 
      clauses = Some [clause]; 
    } 
  in
  (byte_sym, predicate)


let char () = 
  let id = char_sym in
  let loc = Loc.other "internal (Char)" in
  let pointer_s, pointer = IT.fresh Loc in


  let point = (P {
      name = Owned (Integer Char); 
      pointer = pointer;
      iargs = [];
      permission = bool_ true;
    },
    owned_oargs (Integer Char))
  in

  let resource_s, resource = IT.fresh (snd point) in

  let lrt =
    LRT.Resource ((resource_s, point), (loc, None),
    LRT.I)
  in
  let value_s_o = Sym.fresh_named "value" in  
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = LAT.of_lrt lrt (LAT.I [OutputDef.{loc; name = value_s_o; value = recordMember_ ~member_bt:Integer (resource, value_sym)}]) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = []; 
      oargs = [(value_s_o, Integer)]; 
      clauses = Some [clause]; 
    } 
  in
  (id, predicate)





let bytev () = 
  let id = bytev_sym in
  let loc = Loc.other "internal (ByteV)" in
  let pointer_s, pointer = IT.fresh Loc in
  let the_value_s, the_value = IT.fresh Integer in
  let point = (P {
      name = Owned (Integer Char); 
      pointer = pointer;
      iargs = [];
      permission = bool_ true;
    }, 
    owned_oargs (Integer Char))
  in
  let resource_s, resource = IT.fresh (snd point) in

  let has_value = 
    eq_ (recordMember_ ~member_bt:BT.Integer (resource, value_sym), 
         the_value)
  in

  let lrt =
    LRT.Resource ((resource_s, point), (loc, None),
    LRT.Constraint (t_ has_value, (loc, None), 
    LRT.I))
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = LAT.of_lrt lrt (LAT.I []) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = [(the_value_s, IT.bt the_value)]; 
      oargs = []; 
      clauses = Some [clause]; 
    } 
  in
  (id, predicate)











let early_alloc () = 
  let id = early_alloc_sym in
  let loc = Loc.other "internal (EarlyAlloc)" in
  let cur_s, cur = IT.fresh Loc in
  let end_s, end_t = IT.fresh Integer in
  let resource_s = Sym.fresh () in
  let region = 
    let q_s, q = IT.fresh Integer in 
    (ResourceTypes.Q {
        name = PName byte_sym;
        pointer = pointer_ Z.zero;
        q = q_s;
        step = IT.int_ (Memory.size_of_ctype char_ct);
        permission = and_ [pointerToIntegerCast_ cur %<= q; q %<= (sub_ (end_t, int_ 1))];
        iargs = [];
      },
     BT.Record [])
  in
  let lrt =
    LRT.Resource ((resource_s, region), (loc, None),
    LRT.Constraint (t_ (IT.good_ (pointer_ct char_ct, cur)), (loc, None),
    LRT.Constraint (t_ (IT.good_ (pointer_ct char_ct, integerToPointerCast_ end_t)), (loc, None),
    LRT.Constraint (t_ ((pointerToIntegerCast_ cur) %<= end_t), (loc, None),
    LRT.I))))
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = LAT.of_lrt lrt (LAT.I [])
    }
  in
  let predicate = {
      loc = loc;
      pointer = cur_s;
      iargs = [
          (end_s, IT.bt end_t);
        ]; 
      oargs = []; 
      clauses = Some [clause]; 
    } 
  in
  (id, predicate)




let predicate_list struct_decls logical_pred_syms =
  char () ::
  byte () ::
  bytev () ::
  (* region () ::
   * zero_region () :: *)
  (* part_zero_region () :: *)
  early_alloc () ::
  []

    




