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
          and_ [permission; pbaseI %<= q; q %< (pbaseI %+ length)];
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
        (*       int_ 0 %<= order; order %< int_ mMAX_ORDER]; *)
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







(* let early_alloc () = 
 *   let id = "EarlyAlloc" in
 *   let loc = Loc.other "internal (EarlyAlloc)" in
 *   let base_s, base = IT.fresh_named Loc "base" in
 *   let cur_s, cur = IT.fresh_named Integer "cur" in
 *   let end_s, end_t = IT.fresh_named Integer "end" in
 *   let permission_s, permission = IT.fresh_named BT.Bool "permission" in
 *   let region = 
 *     let q_s, q = IT.fresh Integer in 
 *     QPredicate {
 *         name = "Byte";
 *         pointer = base;
 *         q = q_s;
 *         step = Memory.size_of_ctype char_ct;
 *         permission = and_ [permission; cur %<= q; q %< end_t];
 *         iargs = [];
 *         oargs = [];
 *       }
 *   in
 *   let lrt =
 *     LRT.Resource (region, (loc, None),
 *     LRT.Constraint (t_ (IT.good_ (pointer_ct char_ct, base)), (loc, None),
 *     LRT.Constraint (t_ (IT.good_ (pointer_ct char_ct, integerToPointerCast_ cur)), (loc, None),
 *     LRT.Constraint (t_ (IT.good_ (pointer_ct char_ct, integerToPointerCast_ end_t)), (loc, None),
 *     LRT.Constraint (t_ (and_ [pointerToIntegerCast_ base %<= cur; cur %<= end_t]), (loc, None),
 *     LRT.I)))))
 *   in
 *   let clause = {
 *       loc = loc;
 *       guard = bool_ true;
 *       packing_ft = AT.of_lrt lrt (AT.I [])
 *     }
 *   in
 *   let predicate = {
 *       loc = loc;
 *       pointer = base_s;
 *       permission = permission_s;
 *       iargs = [
 *           (cur_s, IT.bt cur);
 *           (end_s, IT.bt end_t);
 *         ]; 
 *       oargs = []; 
 *       clauses = [clause]; 
 *     } 
 *   in
 *   (id, predicate) *)





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
        permission = and_ [permission; pointerToIntegerCast_ cur %<= q; q %< end_t];
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

  let list_node = 
    let id = "ListNode" in
    let loc = Loc.other "internal (ListNode)" in
    let pointer_s, pointer = IT.fresh_named Loc "pointer" in
    let permission_s, permission = IT.fresh_named BT.Bool "permission" in
    let value_s, value = IT.fresh_named (BT.Struct list_head_tag) "value" in
    let point = {
        ct = struct_ct list_head_tag; 
        pointer = pointer;
        permission = permission;
        value = value;
        init = bool_ true;
      }
    in
    let lrt =
      LRT.Logical ((value_s, IT.bt value), (loc, None),
      LRT.Constraint (t_ (good_ (struct_ct list_head_tag, value)), (loc, None),
      LRT.Resource (Point point, (loc, None),
      LRT.I)))
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
  in

  (* let o_list_node = 
   *   let id = "OListNode" in
   *   let loc = Loc.other "internal (OListNode)" in
   *   let pointer_s, pointer = IT.fresh_named Loc "pointer" in
   *   let permission_s, permission = IT.fresh_named BT.Bool "permission" in
   *   let oalias_s, oalias = IT.fresh_named BT.Loc "oalias" in
   *   let value_s, value = IT.fresh_named (BT.Struct list_head_tag) "value" in
   *   let clause1 = 
   *     let point = {
   *         ct = struct_ct list_head_tag; 
   *         pointer = pointer;
   *         permission = permission;
   *         value = value;
   *         init = bool_ true;
   *       }
   *     in
   *     let lrt =
   *       LRT.Logical ((value_s, IT.bt value), (loc, None),
   *       LRT.Constraint (t_ (good_ (struct_ct list_head_tag, value)), (loc, None),
   *       LRT.Resource (Point point, (loc, None),
   *       LRT.I)))
   *     in
   *     {
   *       loc = loc;
   *       guard = ne_ (pointer, oalias);
   *       packing_ft = AT.of_lrt lrt (AT.I [OutputDef.{loc; name = "value"; value}]) 
   *     }
   *   in
   *   let clause2 = {
   *       loc = loc;
   *       guard = bool_ true;
   *       packing_ft = AT.I [OutputDef.{loc; name = "value"; value = IT.default_ (IT.bt value)}]
   *     }
   *   in
   *   let predicate = {
   *       loc = loc;
   *       pointer = pointer_s;
   *       permission = permission_s;
   *       iargs = [(oalias_s, IT.bt oalias)]; 
   *       oargs = [("value", IT.bt value)]; 
   *       clauses = [clause1; clause2]; 
   *     } 
   *   in
   *   (id, predicate)
   * in *)


  let vmemmap_page =
    let id = "Vmemmap_page" in
    let loc = Loc.other "internal (Vmemmap_page)" in
    let page_pointer_s, page_pointer = IT.fresh_named Loc "page_pointer" in
    let permission_s, permission = IT.fresh_named BT.Bool "permission" in
    let page_s, page = IT.fresh_named (BT.Struct hyp_page_tag) "page" in
    let resource = 
      Point {
          ct = struct_ct hyp_page_tag;
          pointer = page_pointer;
          permission = permission;
          value = page; 
          init = bool_ true;
        }
    in
    let lrt = 
      AT.of_lrt (
        LRT.Logical ((page_s, IT.bt page), (loc, None),
        LRT.Resource (resource, (loc, None),
        LRT.Constraint (t_ (good_ (struct_ct hyp_page_tag, page)), (loc, None), 
        LRT.I))))
        (AT.I OutputDef.[{loc; name = "page"; value= page}])
    in
    let clause = { loc; guard = bool_ true; packing_ft = lrt } in    
    let predicate = {
        loc = loc;
        pointer = page_pointer_s;
        iargs = [];
        oargs = [("page", IT.bt page)];
        permission = permission_s;
        clauses = [clause]; 
      } 
    in
    (id, predicate)
  in



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
      LRT.Constraint (t_ (good_ (struct_ct hyp_pool_tag, pool)), (loc, None), 
      LRT.I)))
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
      let condition = and_ [start_i %<= i; i %< end_i] in
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
      let condition = and_ [int_ 0 %<= i; i %< int_ mMAX_ORDER] in
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

    (* let page_group_ownership =  *)
    (*   let q_s, q = IT.fresh_named Integer "q" in *)
    (*   let condition =  *)
    (*     and_ [permission; *)
    (*           (pool %. "range_start") %<= q; *)
    (*           q %< (pool %. "range_end"); *)
    (*           (((map_get_ vmemmap (q %/ (int_ pPAGE_SIZE)))) %. "refcount") %== int_ 0; *)
    (*       ] *)
    (*   in *)
    (*   let qp =  *)
    (*     QPredicate { *)
    (*         name = "Byte"; *)
    (*         pointer = pointer_ Z.zero; *)
    (*         q = q_s; *)
    (*         step = Memory.size_of_ctype char_ct; *)
    (*         permission = condition; *)
    (*         iargs = []; *)
    (*         oargs = []; *)
    (*       } *)
    (*   in *)
    (*   LRT.Resource (qp, (loc, None),  *)
    (*   LRT.I) *)
    (* in *)

    let page_group_ownership = 
      let q_s, q = IT.fresh_named Integer "q" in
      let condition = 
        and_ [permission; start_i %<= q; q %< end_i;
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












  [list_node;
   (* o_list_node; *)
   vmemmap_page;
   hyp_pool;]








    
    (* let vmemmap_well_formedness2 = 
     *   let constr prev_next =
     *     (\* let i_s, i_t = IT.fresh_named Integer "i" in *\)
     *     (\* let trigger = 
     *      *   T_Member (T_Member (T_App (T_Term vmemmap_t, T_Term i_t), Id.id "node"), Id.id prev_next)
     *      * in *\)
     *     T (bool_ true)
     *     (\* forall_trigger_ (i_s, IT.bt i_t) (Some trigger)
     *      *   begin
     *      *     let prev_next_t = ((vmemmap_t %@ i_t) %. "node") %.prev_next in
     *      *     impl_ (
     *      *         vmemmap_good_node_pointer vmemmap_pointer_t prev_next_t
     *      *       ,
     *      *         let j_t = vmemmap_node_pointer_to_index vmemmap_pointer_t prev_next_t in
     *      *         and_
     *      *           [
     *      *             (\\* (((vmemmap_t %@ j_t) %. "node") %.(if prev_next = "next" then "prev" else "next")) %== 
     *      *              *   (vmemmap_cell_node_address vmemmap_pointer_t i_t); *\\)
     *      *             ((vmemmap_t %@ i_t) %. "order") %== ((vmemmap_t %@ j_t) %. "order");
     *      *         (\\* forall_sth_ (k_s, IT.bt k_t)
     *      *          *   (and_ [(i_t %+ int_ 1) %<= k_t; 
     *      *          *          k_t %< (i_t %+ (exp_ (int_ 2, (vmemmap_t %@ i_t) %. "order")))])
     *      *          *   (and_ [
     *      *          *       ((vmemmap_t %@ k_t) %. "order") %== hHYP_NO_ORDER_t;
     *      *          *       ((vmemmap_t %@ k_t) %. "refcount") %== int_ 0;
     *      *          *     ])
     *      *          * ] *\\)
     *      *           ]
     *      *       )
     *      *   end *\)
     *   in
     *   LRT.Constraint (constr "prev", (loc, None), 
     *   LRT.Constraint (constr "next", (loc, None), 
     *   LRT.I))
     * in *)










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
  | Not_found -> []


    




