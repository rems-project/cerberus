open Sctypes
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RE = Resources.RE
module AT = ArgumentTypes
module StringMap = Map.Make(String)
module Loc = Locations
open Pp
open Resources.RE
open BT
open IT
open LC

type clause = {
    loc : Loc.t;
    guard : IT.t;
    packing_ft : AT.packing_ft
  }

let pp_clause {loc; guard; packing_ft} = 
  item "condition" (IT.pp guard) ^^ comma ^^^
  item "return type" (AT.pp OutputDef.pp packing_ft)

let subst_clause subst {loc; guard; packing_ft} = 
  { loc = loc;
    guard = IT.subst subst guard; 
    packing_ft = AT.subst OutputDef.subst subst packing_ft }





type definition = {
    loc : Loc.t;
    pointer: Sym.t;
    iargs : (Sym.t * LS.t) list;
    oargs : (Sym.t * LS.t) list;
    clauses : clause list;
  }

let pp_definition def = 
  item "pointer" (Sym.pp def.pointer) ^/^
  item "iargs" (Pp.list (fun (s,_) -> Sym.pp s) def.iargs) ^/^
  item "oargs" (Pp.list (fun (s,_) -> Sym.pp s) def.oargs) ^/^
  item "clauses" (Pp.list pp_clause def.clauses)
  


let byte () = 
  let id = "Byte" in
  let loc = Loc.other "internal (Byte)" in
  let pointer_s, pointer = IT.fresh Loc in
  let value_s, value = IT.fresh BT.Integer in
  let init_s, init = IT.fresh BT.Bool in
  let point = {
      ct = char_ct; 
      pointer = pointer;
      permission = bool_ true;
      value = value;
      init = init;
    }
  in
  let lrt =
    LRT.Logical ((value_s, IT.bt value), (loc, None),
    LRT.Logical ((init_s, IT.bt init), (loc, None),
    LRT.Resource (Point point, (loc, None),
    LRT.I)))
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = AT.of_lrt lrt (AT.I []) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = []; 
      oargs = []; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)


let char () = 
  let id = "Char" in
  let loc = Loc.other "internal (Char)" in
  let pointer_s, pointer = IT.fresh Loc in
  let value_s, value = IT.fresh BT.Integer in
  let point = {
      ct = char_ct; 
      pointer = pointer;
      permission = bool_ true;
      value = value;
      init = bool_ true;
    }
  in
  let lrt =
    LRT.Logical ((value_s, IT.bt value), (loc, None),
    LRT.Resource (Point point, (loc, None),
    LRT.I))
  in
  let value_s_o = Sym.fresh_named "value" in  
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = AT.of_lrt lrt (AT.I [OutputDef.{loc; name = value_s_o; value}]) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = []; 
      oargs = [(value_s_o, IT.bt value)]; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)





let zerobyte () = 
  let id = "ZeroByte" in
  let loc = Loc.other "internal (ZeroByte)" in
  let pointer_s, pointer = IT.fresh Loc in
  let point = {
      ct = char_ct; 
      pointer = pointer;
      permission = bool_ true;
      value = int_ 0;
      init = bool_ true;
    }
  in
  let lrt =
    LRT.Resource (Point point, (loc, None),
    LRT.I)
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = AT.of_lrt lrt (AT.I []) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = []; 
      oargs = []; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)











let early_alloc () = 
  let id = "EarlyAlloc" in
  let loc = Loc.other "internal (EarlyAlloc)" in
  let cur_s, cur = IT.fresh Loc in
  let end_s, end_t = IT.fresh Integer in
  let region = 
    let q_s, q = IT.fresh Integer in 
    QPredicate {
        name = "Byte";
        pointer = pointer_ Z.zero;
        q = q_s;
        step = Memory.size_of_ctype char_ct;
        permission = and_ [pointerToIntegerCast_ cur %<= q; q %<= (sub_ (end_t, int_ 1))];
        iargs = [];
        oargs = [];
      }
  in
  let lrt =
    LRT.Resource (region, (loc, None),
    LRT.Constraint (t_ (IT.good_ (pointer_ct char_ct, cur)), (loc, None),
    LRT.Constraint (t_ (IT.good_ (pointer_ct char_ct, integerToPointerCast_ end_t)), (loc, None),
    LRT.Constraint (t_ ((pointerToIntegerCast_ cur) %<= end_t), (loc, None),
    LRT.I))))
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = AT.of_lrt lrt (AT.I [])
    }
  in
  let predicate = {
      loc = loc;
      pointer = cur_s;
      iargs = [
          (end_s, IT.bt end_t);
        ]; 
      oargs = []; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)




let page_alloc_predicates struct_decls = 

  let module Aux = LogicalPredicates.PageAlloc.Aux(struct let struct_decls = struct_decls end) in
  let open Aux in


  let page = 
    let id = "Page" in
    let loc = Loc.other "internal (Page)" in
    let guardv_s, guardv = IT.fresh BT.Integer in
    let pbase_s, pbase = IT.fresh Loc in
    let pbaseI = pointerToIntegerCast_ pbase in
    let order_s, order = IT.fresh Integer in
    let clause1 = 
      let qp = 
        let length = pred_ "page_size_of_order" [order] Integer in
        let q_s, q = IT.fresh Integer in {
          name = "Byte"; 
          pointer = pointer_ Z.zero;
          q = q_s;
          step = Memory.size_of_ctype char_ct;
          permission = 
            and_ [pbaseI %<= q; q %<= (sub_ (pbaseI %+ length, int_ 1))];
          iargs = [];
          oargs = [];
        }
      in
      let lrt =
        LRT.Resource (QPredicate qp, (loc, None),
        LRT.Constraint (t_ (ne_ (order, int_ hHYP_NO_ORDER)), (loc, None),
        LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct pbase), (loc, None),
        LRT.I)))
      in
      {
        loc = loc;
        guard = ne_ (guardv, int_ 0);
          (* and_ [ne_ (vbase, null_); *)
          (*       int_ 0 %<= order; order %<= int_ (mMAX_ORDER - 1)]; *)
        packing_ft = AT.of_lrt lrt (AT.I []) 
      }
    in
    let clause2 = 
      {
        loc = loc;
        guard = bool_ true;
        packing_ft = AT.I []
      }
    in
    let predicate = {
        loc = loc;
        pointer = pbase_s;
        iargs = [(guardv_s, IT.bt guardv);
                 (order_s, IT.bt order);
                ]; 
        oargs = []; 
        clauses = [clause1; clause2]; 
      } 
    in
    (id, predicate)
  in


  let hyp_pool =  
    let id = "Hyp_pool" in
    let loc = Loc.other "internal (Hyp_pool)" in
    let pool_pointer_s, pool_pointer = IT.fresh Loc in
    (* iargs *)
    let vmemmap_pointer_s, vmemmap_pointer = IT.fresh Loc in
    let hyp_physvirt_offset_s, hyp_physvirt_offset = 
      IT.fresh BT.Integer in
    (* oargs *)
    let pool_s, pool = IT.fresh (BT.Struct hyp_pool_tag) in
    let vmemmap_s, vmemmap = 
      IT.fresh (BT.Map (Integer, (BT.Struct hyp_page_tag))) in


    let metadata_owned = 
      let resource = 
        Point {
            ct = struct_ct hyp_pool_tag;
            pointer = pool_pointer;
            permission = bool_ true;
            init = bool_ true;
            value = pool;
          }
      in
      LRT.Logical ((pool_s, IT.bt pool), (loc, None), 
      LRT.Resource (resource, (loc, None), 
      LRT.I))
    in


    let vmemmap_metadata_owned =
      let resource = 
        Aux.vmemmap_resource ~vmemmap_pointer ~vmemmap
          ~range_start:(pool %. "range_start")
          ~range_end:(pool %. "range_end")
      in
      LRT.Logical ((vmemmap_s, IT.bt vmemmap), (loc, None),
      LRT.Resource (resource, (loc, None), 
      LRT.I))
    in

    let start_i = (pool %. "range_start") %/ (int_ pPAGE_SIZE) in
    let end_i = (pool %. "range_end") %/ (int_ pPAGE_SIZE) in
  
    let vmemmap_wf = 
      let i_s, i = IT.fresh Integer in
      let condition = and_ [start_i %<= i; i %<= (sub_ (end_i, int_ 1))] in
      let args = [
          i;
          vmemmap_pointer;
          vmemmap;
          pool_pointer;
          pool
        ]
      in
      forall_ (i_s, IT.bt i) (
          impl_ (condition, pred_ "vmemmap_page_wf" args BT.Bool);
        )
    in
  
    let vmemmap_wf_list = 
      let i_s, i = IT.fresh Integer in
      let condition = and_ [start_i %<= i; i %<= (sub_ (end_i, int_ 1))] in
      let args = [
          i;
          vmemmap_pointer;
          vmemmap;
          pool_pointer;
          pool
        ]
      in
      forall_ (i_s, IT.bt i) (
          impl_ (condition,
                 pred_ "vmemmap_page_wf_list" args BT.Bool )
        )
    in

  let free_area_wf = 
      let i_s, i = IT.fresh Integer in
      let condition = and_ [int_ 0 %<= i; i %<= int_ (mMAX_ORDER - 1)] in
      let args = [
          i;
          vmemmap_pointer;
          vmemmap;
          pool_pointer;
          pool;
        ]
      in
      forall_ (i_s, IT.bt i) (
          impl_ (condition,
                 pred_ "freeArea_cell_wf" args BT.Bool)
        )
    in

    let hyp_pool_wf = 
      let args = [
          pool_pointer;
          pool;
          vmemmap_pointer;
          hyp_physvirt_offset;
        ]        
      in
      LC.t_ (pred_ "hyp_pool_wf" args BT.Bool)
    in

    let wellformedness = 
      LRT.Constraint (vmemmap_wf, (loc, Some "vmemmap_wf"),
      LRT.Constraint (vmemmap_wf_list, (loc, Some "vmemmap_wf_list"),
      LRT.Constraint (free_area_wf, (loc, Some "free_area_wf"),
      LRT.Constraint (hyp_pool_wf, (loc, Some "hyp_pool_wf"),
      LRT.I))))
    in

    let page_group_ownership = 
      let q_s, q = IT.fresh Integer in
      let condition = 
        and_ [start_i %<= q; q %<= (sub_ (end_i, int_ 1));
              (((map_get_ vmemmap q)) %. "refcount") %== int_ 0;
              (((map_get_ vmemmap q)) %. "order") %!= int_ hHYP_NO_ORDER;
          ]
      in
      let qp = 
        QPredicate {
            name = "Page";
            pointer = pointer_ Z.zero;
            q = q_s;
            step = pPAGE_SIZE;
            permission = condition;
            iargs = [int_ 1; (((map_get_ vmemmap q)) %. "order")];
            oargs = [];
          }
      in
      LRT.Resource (qp, (loc, None), 
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
          {loc; name = pool_s_o; value = pool};
          {loc; name = vmemmap_s_o; value = vmemmap};
      ]
    in
    let clause = {
        loc = loc;
        guard = bool_ true;
        packing_ft = AT.of_lrt lrt (AT.I assignment)
      }
    in
  
    let predicate = {
        loc = loc;
        pointer = pool_pointer_s;
        iargs = [
            (vmemmap_pointer_s, IT.bt vmemmap_pointer);
            (hyp_physvirt_offset_s, IT.bt hyp_physvirt_offset);
          ]
        ;
        oargs = [
            (pool_s_o, IT.bt pool); 
            (vmemmap_s_o, IT.bt vmemmap);
          ];
        clauses = [clause;]; 
      } 
    in
    (id, predicate)
  in

  [page; hyp_pool;]








    


let predicate_list struct_decls = 
  char () ::
  byte () ::
  zerobyte () ::
  (* region () ::
   * zero_region () :: *)
  (* part_zero_region () :: *)
  early_alloc () ::
  (* for now: *)
  try page_alloc_predicates struct_decls with
  | LogicalPredicates.Struct_not_found -> []


    




