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
let page_sym = Sym.fresh_named "Page"
let zeropage_sym = Sym.fresh_named "ZeroPage"
let hyp_pool_sym = Sym.fresh_named "Hyp_pool"



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
        step = Memory.size_of_ctype char_ct;
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




let page_alloc_predicates struct_decls = 

  let module Aux = LogicalPredicates.PageAlloc.Aux(struct let struct_decls = struct_decls end) in
  let open Aux in


  let page = 
    let id = page_sym in
    let loc = Loc.other "internal (Page)" in
    let guardv_s, guardv = IT.fresh BT.Integer in
    let pbase_s, pbase = IT.fresh Loc in
    let pbaseI = pointerToIntegerCast_ pbase in
    let order_s, order = IT.fresh Integer in
    let resource_s = Sym.fresh () in
    let clause1 = 
      let qp = 
        let length = pred_ LP.page_size_of_order_sym [order] Integer in
        let q_s, q = IT.fresh Integer in 
        (ResourceTypes.Q {
          name = PName byte_sym; 
          pointer = pointer_ Z.zero;
          q = q_s;
          step = Memory.size_of_ctype char_ct;
          permission = 
            and_ [pbaseI %<= q; q %<= (sub_ (pbaseI %+ length, int_ 1))];
          iargs = [];
        }, BT.Record [])
      in
      let lrt =
        LRT.Resource ((resource_s, qp), (loc, None),
        LRT.Constraint (t_ (ne_ (order, int_ hHYP_NO_ORDER)), (loc, None),
        LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct pbase), (loc, None),
        LRT.I)))
      in
      {
        loc = loc;
        guard = ne_ (guardv, int_ 0);
          (* and_ [ne_ (vbase, null_); *)
          (*       int_ 0 %<= order; order %<= int_ (mMAX_ORDER - 1)]; *)
        packing_ft = LAT.of_lrt lrt (LAT.I []) 
      }
    in
    let clause2 = 
      {
        loc = loc;
        guard = bool_ true;
        packing_ft = LAT.I []
      }
    in
    let predicate = {
        loc = loc;
        pointer = pbase_s;
        iargs = [(guardv_s, IT.bt guardv);
                 (order_s, IT.bt order);
                ]; 
        oargs = []; 
        clauses = Some [clause1; clause2]; 
      } 
    in
    (id, predicate)
  in

  
  let zeropage = 
    let id = zeropage_sym in
    let loc = Loc.other "internal (ZeroPage)" in
    let guardv_s, guardv = IT.fresh BT.Integer in
    let pbase_s, pbase = IT.fresh Loc in
    let pbaseI = pointerToIntegerCast_ pbase in
    let order_s, order = IT.fresh Integer in
    let resource_s = Sym.fresh () in
    let clause1 = 
      let qp = 
        let length = pred_ LP.page_size_of_order_sym [order] Integer in
        let q_s, q = IT.fresh Integer in 
        (ResourceTypes.Q {
          name = PName bytev_sym; 
          pointer = pointer_ Z.zero;
          q = q_s;
          step = Memory.size_of_ctype char_ct;
          permission = 
            and_ [pbaseI %<= q; q %<= (sub_ (pbaseI %+ length, int_ 1))];
          iargs = [int_ 0];
        }, BT.Record [])
      in
      let lrt =
        LRT.Resource ((resource_s, qp), (loc, None),
        LRT.Constraint (t_ (ne_ (order, int_ hHYP_NO_ORDER)), (loc, None),
        LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct pbase), (loc, None),
        LRT.I)))
      in
      {
        loc = loc;
        guard = ne_ (guardv, int_ 0);
          (* and_ [ne_ (vbase, null_); *)
          (*       int_ 0 %<= order; order %<= int_ (mMAX_ORDER - 1)]; *)
        packing_ft = LAT.of_lrt lrt (LAT.I []) 
      }
    in
    let clause2 = 
      {
        loc = loc;
        guard = bool_ true;
        packing_ft = LAT.I []
      }
    in
    let predicate = {
        loc = loc;
        pointer = pbase_s;
        iargs = [(guardv_s, IT.bt guardv);
                 (order_s, IT.bt order);
                ]; 
        oargs = []; 
        clauses = Some [clause1; clause2]; 
      } 
    in
    (id, predicate)
  in


  let hyp_pool =  
    let id = hyp_pool_sym in
    let loc = Loc.other ("internal (Hyp_pool)") in
    let pool_pointer_s, pool_pointer = IT.fresh Loc in
    (* iargs *)
    let vmemmap_pointer_s, vmemmap_pointer = IT.fresh Loc in
    let hyp_physvirt_offset_s, hyp_physvirt_offset = 
      IT.fresh BT.Integer in
    (* (\* oargs *\) *)
    (* let pool_s, pool = IT.fresh (BT.Struct hyp_pool_tag) in *)
    (* let vmemmap_s, vmemmap =  *)
    (*   IT.fresh (BT.Map (Integer, (BT.Struct hyp_page_tag))) in *)

    let pool_resource = 
      (P {
           name = Owned (Struct hyp_pool_tag);
           pointer = pool_pointer;
           iargs = [];
             permission = bool_ true;
         },
       owned_oargs (Struct hyp_pool_tag))
    in

    let pool_oarg_s, pool_oarg = IT.fresh (snd pool_resource) in


    let pool_value = (recordMember_ ~member_bt:(BT.Struct hyp_pool_tag) (pool_oarg, value_sym)) in

    let good_pool = t_ (good_ (Struct hyp_pool_tag, pool_value)) in

    let metadata_owned = 
      LRT.Resource ((pool_oarg_s, pool_resource), (loc, None), 
      LRT.Constraint (good_pool, (loc, None),
      LRT.I))
    in



    let vmemmap_resource, ((vmemmap_qs, vmemmap_q), vmemmap_permission) = 
      Aux.vmemmap_resource ~vmemmap_pointer
        ~range_start:(pool_value %. "range_start")
        ~range_end:(pool_value %. "range_end")
    in

    let vmemmap_oarg_s, vmemmap_oarg = 
      IT.fresh (snd vmemmap_resource) in

    let good_vmemmap = 
      let value_it = 
        recordMember_
          ~member_bt:(Map (Integer, Struct hyp_page_tag))
          (vmemmap_oarg, Resources.value_sym)
      in
      let q_s = vmemmap_qs in
      let q = vmemmap_q in
      forall_ (q_s, IT.bt q) (
          impl_ (and_ [le_ (int_ 0, q); vmemmap_permission],
                 good_ (Struct hyp_page_tag, map_get_ value_it q))
        )
    in

    let vmemmap_metadata_owned =
      LRT.Resource ((vmemmap_oarg_s, vmemmap_resource), (loc, None), 
      LRT.Constraint (good_vmemmap, (loc, None),
      LRT.I))
    in

    let vmemmap_value = (recordMember_ ~member_bt:(Map (Integer, BT.Struct hyp_page_tag)) (vmemmap_oarg, value_sym)) in

    let start_i = (pool_value %. "range_start") %/ (int_ pPAGE_SIZE) in
    let end_i = (pool_value %. "range_end") %/ (int_ pPAGE_SIZE) in
  
    let vmemmap_wf = 
      let i_s, i = IT.fresh Integer in
      let condition = and_ [start_i %<= i; i %<= (sub_ (end_i, int_ 1))] in
      let args = [
          i;
          vmemmap_pointer;
          vmemmap_value;
          pool_pointer;
          pool_value;
        ]
      in
      forall_ (i_s, IT.bt i) (
          impl_ (condition, pred_ LP.vmemmap_wf_sym args BT.Bool);
        )
    in
  
    let vmemmap_l_wf = 
      let i_s, i = IT.fresh Integer in
      let condition = and_ [start_i %<= i; i %<= (sub_ (end_i, int_ 1))] in
      let args = [
          i;
          vmemmap_pointer;
          vmemmap_value;
          pool_pointer;
          pool_value;
        ]
      in
      forall_ (i_s, IT.bt i) (
          impl_ (condition,
                 pred_ LP.vmemmap_l_wf_sym args BT.Bool )
        )
    in

  let free_area_wf = 
      let i_s, i = IT.fresh Integer in
      let condition = and_ [int_ 0 %<= i; i %<= int_ (mMAX_ORDER - 1)] in
      let args = [
          i;
          vmemmap_pointer;
          vmemmap_value;
          pool_pointer;
          pool_value;
        ]
      in
      forall_ (i_s, IT.bt i) (
          impl_ (condition,
                 pred_ LP.freeArea_cell_wf_sym args BT.Bool)
        )
    in

    let hyp_pool_wf = 
      let args = [
          pool_pointer;
          pool_value;
          vmemmap_pointer;
          hyp_physvirt_offset;
        ]        
      in
      LC.t_ (pred_ LP.hyp_pool_wf_sym args BT.Bool)
    in

    let wellformedness = 
      LRT.Constraint (vmemmap_wf, (loc, Some "vmemmap_wf"),
      LRT.Constraint (vmemmap_l_wf, (loc, Some "vmemmap_wf_list"),
      LRT.Constraint (free_area_wf, (loc, Some "free_area_wf"),
      LRT.Constraint (hyp_pool_wf, (loc, Some "hyp_pool_wf"),
      LRT.I))))
    in

    let page_group_ownership = 
      let q_s, q = IT.fresh Integer in
      let condition = 
        and_ [start_i %<= q; q %<= (sub_ (end_i, int_ 1));
              (((map_get_ vmemmap_value q)) %. "refcount") %== int_ 0;
              (((map_get_ vmemmap_value q)) %. "order") %!= int_ hHYP_NO_ORDER;
          ]
      in
      let qp = 
        (ResourceTypes.Q {
            name = PName zeropage_sym;
            pointer = pointer_ Z.zero;
            q = q_s;
            step = pPAGE_SIZE;
            permission = condition;
            iargs = [int_ 1; (((map_get_ vmemmap_value q)) %. "order")];
          },
         BT.Record [])
      in
      LRT.Resource ((Sym.fresh (), qp), (loc, None), 
      LRT.I)
    in



    let lrt = 
      let open LRT in
      metadata_owned
      @@ vmemmap_metadata_owned
      @@ wellformedness
      (* @@ free_area_well_formedness (\* possibly inconsistent *\)
       * @@ vmemmap_well_formedness2 *)
      @@ page_group_ownership
    in
  
    let pool_s_o = Sym.fresh_named "pool" in
    let vmemmap_s_o = Sym.fresh_named "vmemmap" in

    let assignment = OutputDef.[
          {loc; name = pool_s_o; value = pool_value};
          {loc; name = vmemmap_s_o; value = vmemmap_value};
      ]
    in
    let clause = {
        loc = loc;
        guard = bool_ true;
        packing_ft = LAT.of_lrt lrt (LAT.I assignment)
      }
    in

    let oargs = [
        (pool_s_o, IT.bt pool_value); 
        (vmemmap_s_o, IT.bt vmemmap_value);
      ]
    in

  
    let clauses = Some [clause] in

    let predicate = {
        loc = loc;
        pointer = pool_pointer_s;
        iargs = [
            (vmemmap_pointer_s, IT.bt vmemmap_pointer);
            (hyp_physvirt_offset_s, IT.bt hyp_physvirt_offset);
          ]
        ;
        oargs = oargs;
        clauses = clauses; 
      } 
    in
    (id, predicate)
  in


  



  [page; zeropage; hyp_pool;]








    


let predicate_list struct_decls = 
  char () ::
  byte () ::
  bytev () ::
  (* region () ::
   * zero_region () :: *)
  (* part_zero_region () :: *)
  early_alloc () ::
  (* for now: *)
  try page_alloc_predicates struct_decls with
  | LogicalPredicates.Struct_not_found -> []


    




