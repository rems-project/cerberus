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
    oargs : (string * LS.t) list;
    permission: Sym.t;
    clauses : clause list;
  }

let pp_definition def = 
  item "pointer" (Sym.pp def.pointer) ^/^
  item "iargs" (Pp.list (fun (s,_) -> Sym.pp s) def.iargs) ^/^
  item "oargs" (Pp.list (fun (s,_) -> Pp.string s) def.oargs) ^/^
  item "permission" (Sym.pp def.permission) ^/^
  item "clauses" (Pp.list pp_clause def.clauses)
  


let byte () = 
  let id = "Byte" in
  let loc = Loc.other "internal (Byte)" in
  let pointer_s, pointer = IT.fresh_named Loc "pointer" in
  let permission_s, permission = IT.fresh_named BT.Bool "permission" in
  let value_s, value = IT.fresh_named BT.Integer "value" in
  let init_s, init = IT.fresh_named BT.Bool "init" in
  let point = {
      ct = char_ct; 
      pointer = pointer;
      permission = permission;
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
      permission = permission_s;
      iargs = []; 
      oargs = []; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)


let char () = 
  let id = "Char" in
  let loc = Loc.other "internal (Char)" in
  let pointer_s, pointer = IT.fresh_named Loc "pointer" in
  let permission_s, permission = IT.fresh_named BT.Bool "permission" in
  let value_s, value = IT.fresh_named BT.Integer "value" in
  let point = {
      ct = char_ct; 
      pointer = pointer;
      permission = permission;
      value = value;
      init = bool_ true;
    }
  in
  let lrt =
    LRT.Logical ((value_s, IT.bt value), (loc, None),
    LRT.Resource (Point point, (loc, None),
    LRT.I))
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = AT.of_lrt lrt (AT.I [OutputDef.{loc; name = "value"; value}]) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      permission = permission_s;
      iargs = []; 
      oargs = [("value", IT.bt value)]; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)





let zerobyte () = 
  let id = "ZeroByte" in
  let loc = Loc.other "internal (ZeroByte)" in
  let pointer_s, pointer = IT.fresh_named Loc "pointer" in
  let permission_s, permission = IT.fresh_named BT.Bool "permission" in
  let point = {
      ct = char_ct; 
      pointer = pointer;
      permission = permission;
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
      permission = permission_s;
      iargs = []; 
      oargs = []; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)


let page () = 
  let id = "Page" in
  let loc = Loc.other "internal (Page)" in
  let guardv_s, guardv = IT.fresh_named BT.Integer "guardv" in
  let pbase_s, pbase = IT.fresh_named Loc "pbase" in
  let pbaseI = pointerToIntegerCast_ pbase in
  let order_s, order = IT.fresh_named Integer "order" in
  let permission_s, permission = IT.fresh_named BT.Bool "permission" in
  let clause1 = 
    let qp = 
      let length = 
        let rec aux i = 
          if i >= 11 then default_ BT.Integer else 
            ite_ (eq_ (order, int_ i), 
                  z_ (Z.pow (Z.of_int 2) (12 + i)), 
                  aux (i + 1))

        in
        aux 0
      in
      let q_s, q = IT.fresh Integer in {
        name = "Byte"; 
        pointer = pointer_ Z.zero;
        q = q_s;
        step = Memory.size_of_ctype char_ct;
        permission = 
          and_ [permission; pbaseI %<= q; q %<= (sub_ (pbaseI %+ length, int_ 1))];
        iargs = [];
        oargs = [];
      }
    in
    let lrt =
      LRT.Resource (QPredicate qp, (loc, None),
      LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct pbase), (loc, None),
      LRT.I))
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
      permission = permission_s;
      iargs = [(guardv_s, IT.bt guardv);
               (order_s, IT.bt order);
              ]; 
      oargs = []; 
      clauses = [clause1; clause2]; 
    } 
  in
  (id, predicate)








let early_alloc () = 
  let id = "EarlyAlloc" in
  let loc = Loc.other "internal (EarlyAlloc)" in
  let cur_s, cur = IT.fresh_named Loc "cur" in
  let end_s, end_t = IT.fresh_named Integer "end" in
  let permission_s, permission = IT.fresh_named BT.Bool "permission" in
  let region = 
    let q_s, q = IT.fresh Integer in 
    QPredicate {
        name = "Byte";
        pointer = pointer_ Z.zero;
        q = q_s;
        step = Memory.size_of_ctype char_ct;
        permission = and_ [permission; pointerToIntegerCast_ cur %<= q; q %<= (sub_ (end_t, int_ 1))];
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
      permission = permission_s;
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


  let hyp_pool =  
    let id = "Hyp_pool" in
    let loc = Loc.other "internal (Hyp_pool)" in
    let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
    let permission_s, permission = IT.fresh_named BT.Bool "permission" in
    (* iargs *)
    let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
    let hyp_physvirt_offset_s, hyp_physvirt_offset = 
      IT.fresh_named BT.Integer "hyp_physvirt_offset" in
    (* oargs *)
    let pool_s, pool = IT.fresh_named (BT.Struct hyp_pool_tag) "pool" in
    let vmemmap_s, vmemmap = 
      IT.fresh_named (BT.Map (Integer, (BT.Struct hyp_page_tag))) "vmemmap" in


    let metadata_owned = 
      let resource = 
        Point {
            ct = struct_ct hyp_pool_tag;
            pointer = pool_pointer;
            permission = permission;
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
          permission
      in
      LRT.Logical ((vmemmap_s, IT.bt vmemmap), (loc, None),
      LRT.Resource (resource, (loc, None), 
      LRT.I))
    in

    let start_i = (pool %. "range_start") %/ (int_ pPAGE_SIZE) in
    let end_i = (pool %. "range_end") %/ (int_ pPAGE_SIZE) in
  
    let vmemmap_wf = 
      let i_s, i = IT.fresh_named Integer "i" in
      let condition = and_ [start_i %<= i; i %<= (sub_ (end_i, int_ 1))] in
      let args = [
          i;
          vmemmap_pointer;
          vmemmap;
          pool_pointer;
          pool
        ]
      in
      QPred {
          q = (i_s, IT.bt i); 
          condition = condition;
          pred = { name = "Vmemmap_page_wf"; args };
        }
    in

  let free_area_wf = 
      let i_s, i = IT.fresh_named Integer "i" in
      let condition = and_ [int_ 0 %<= i; i %<= int_ (mMAX_ORDER - 1)] in
      let args = [
          i;
          vmemmap_pointer;
          vmemmap;
          pool_pointer;
          pool;
        ]
      in
      QPred {
          q = (i_s, IT.bt i); 
          condition = condition;
          pred = { name = "FreeArea_cell_wf"; args };
        }
    in

    let hyp_pool_wf = 
      let args = [
          pool_pointer;
          pool;
          vmemmap_pointer;
          hyp_physvirt_offset;
        ]        
      in
      Pred { name = "Hyp_pool_wf"; args }
    in

    let wellformedness = 
      LRT.Constraint (vmemmap_wf, (loc, Some "vmemmap_wf"),
      LRT.Constraint (free_area_wf, (loc, Some "free_area_wf"),
      LRT.Constraint (hyp_pool_wf, (loc, Some "hyp_pool_wf"),
      LRT.I)))
    in

    let page_group_ownership = 
      let q_s, q = IT.fresh_named Integer "q" in
      let condition = 
        and_ [permission; start_i %<= q; q %<= (sub_ (end_i, int_ 1));
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
  
    let assignment = OutputDef.[
          {loc; name = "pool"; value = pool};
          {loc; name = "vmemmap"; value = vmemmap};
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
        permission = permission_s;
        iargs = [
            (vmemmap_pointer_s, IT.bt vmemmap_pointer);
            (hyp_physvirt_offset_s, IT.bt hyp_physvirt_offset);
          ]
        ;
        oargs = [
            ("pool", IT.bt pool); 
            ("vmemmap", IT.bt vmemmap);
          ];
        clauses = [clause;]; 
      } 
    in
    (id, predicate)
  in












  [hyp_pool;]








    


let predicate_list struct_decls = 
  char () ::
  byte () ::
  zerobyte () ::
  (* region () ::
   * zero_region () :: *)
  (* part_zero_region () :: *)
  early_alloc () ::
  page () ::
  (* for now: *)
  try page_alloc_predicates struct_decls with
  | LogicalPredicates.Struct_not_found -> []


    




