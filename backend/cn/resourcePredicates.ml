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





(* let region () = 
 *   let id = "Region" in
 *   let loc = Loc.other "internal (Region)" in
 *   let base_s, base = IT.fresh_named Loc "base" in
 *   let length_s, length = IT.fresh_named Integer "length" in
 *   let permission_s, permission = IT.fresh_named BT.Bool "permission" in
 *   let value_s, value = IT.fresh_named (BT.Array (Loc, Integer)) "value" in
 *   let init_s, init = IT.fresh_named (BT.Array (Loc, Bool)) "init" in
 *   let qpoint = 
 *     let qpointer_s, qpointer = IT.fresh Loc in {
 *       ct = char_ct; 
 *       qpointer = qpointer_s;
 *       permission = 
 *         RE.array_permission ~base ~item_ct:char_ct
 *           ~length ~qpointer ~permission;
 *       value = get_ value qpointer;
 *       init = get_ init qpointer;
 *     }
 *   in
 *   let lrt =
 *     LRT.Logical ((value_s, IT.bt value), (loc, None),
 *     LRT.Logical ((init_s, IT.bt init), (loc, None),
 *     LRT.Resource (QPoint qpoint, (loc, None),
 *     LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct base), (loc, None),
 *     LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct (subPointer_ (addPointer_ (base, length), int_ 1))), (loc, None),
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
 *       iargs = [(length_s, IT.bt length)]; 
 *       oargs = []; 
 *       clauses = [clause]; 
 *     } 
 *   in
 *   (id, predicate) *)



(* let part_zero_region () = 
 *   let id = "PartZeroRegion" in
 *   let loc = Loc.other "internal (PartZeroRegion)" in
 *   let base_s, base = IT.fresh_named Loc "base" in
 *   let permission_s, permission = IT.fresh_named BT.Bool "permission" in
 *   let length_s, length = IT.fresh_named Integer "length" in
 *   let value_s, value = IT.fresh_named (BT.Array (Loc, Integer)) "value" in
 *   let init_s, init = IT.fresh_named (BT.Array (Loc, Bool)) "init" in
 *   let up_to_s, up_to = IT.fresh_named Integer "up_to" in
 *   let qp_s, qp = IT.fresh Loc in 
 *   let qpoint = {
 *       ct = char_ct; 
 *       qpointer = qp_s;
 *       permission = array_permission ~item_ct:char_ct ~base
 *                      ~length ~qpointer:qp ~permission;
 *       value = get_ value qp;
 *       init = get_ init qp;
 *     }
 *   in
 *   let constr = 
 *     forall_ (qp_s, IT.bt qp)
 *       (impl_ (and_ [lePointer_ (base, qp); 
 *                     ltPointer_ (qp, addPointer_ (base, up_to))],
 *               and_ [eq_ (get_ value qp, int_ 0);
 *                     get_ init qp]))
 *   in
 *   let lrt =
 *     LRT.Logical ((value_s, IT.bt value), (loc, None), 
 *     LRT.Logical ((init_s, IT.bt init), (loc, None), 
 *     LRT.Resource (QPoint qpoint, (loc, None),
 *     LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct base), (loc, None),
 *     LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct (subPointer_ (addPointer_ (base, length), int_ 1))), (loc, None),
 *     LRT.Constraint (constr, (loc, None),
 *     LRT.I))))))
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
 *       iargs = [(length_s, IT.bt length); 
 *                (up_to_s, IT.bt up_to);]; 
 *       oargs = []; 
 *       clauses = [clause]; 
 *     } 
 *   in
 *   (id, predicate) *)




(* let zero_region () = 
 *   let id = "ZeroRegion" in
 *   let loc = Loc.other "internal (ZeroRegion)" in
 *   let base_s, base = IT.fresh_named Loc "base" in
 *   let length_s, length = IT.fresh_named Integer "length" in
 *   let permission_s, permission = IT.fresh_named BT.Bool "permission" in
 *   let qp_s, qp = IT.fresh_named Loc "p" in
 *   let qpoint = {
 *       ct = char_ct; 
 *       qpointer = qp_s;
 *       permission = array_permission ~item_ct:char_ct ~base ~length
 *                      ~qpointer:qp ~permission;
 *       value = int_ 0;
 *       init = bool_ true;
 *     }
 *   in
 *   let lrt =
 *     LRT.Resource (QPoint qpoint, (loc, None),
 *     LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct base), (loc, None),
 *     LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct (subPointer_ (addPointer_ (base, 
 * length), int_ 1))), (loc, None),
 *     LRT.I)))
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
 *       iargs = [(length_s, IT.bt length)]; 
 *       oargs = []; 
 *       clauses = [clause]; 
 *     } 
 *   in
 *   (id, predicate) *)



let early_alloc () = 
  let id = "EarlyAlloc" in
  let loc = Loc.other "internal (EarlyAlloc)" in
  let start_s, start = IT.fresh_named Loc "start" in
  let permission_s, permission = IT.fresh_named BT.Bool "permission" in
  let end_s, end_t = IT.fresh_named Loc "end" in
  let length = 
    sub_ (pointerToIntegerCast_ end_t,
          pointerToIntegerCast_ start)
  in
  let region = 
    let item_size = int_ (Memory.size_of_ctype char_ct) in
    let qpointer_s, qpointer = IT.fresh Loc in {
        name = "Byte";
        qpointer = qpointer_s;
        permission = 
          RE.array_permission ~base:start ~item_size
            ~length ~qpointer ~permission;
        iargs = [];
        oargs = [];
      }
  in
  let lrt =
    LRT.Resource (QPredicate region, (loc, None),
    LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct start), (loc, None),
    LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct end_t), (loc, None),
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
      pointer = start_s;
      permission = permission_s;
      iargs = [(end_s, IT.bt end_t)]; 
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
      IT.fresh_named (BT.Array (Loc, BT.Struct hyp_page_tag)) "vmemmap" in


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
  
    let vmemmap_wf = 
      let p_s, p = IT.fresh_named Loc "ptr" in

      let condition =
        vmemmap_good_pointer ~vmemmap_pointer p
          (pool %. "range_start") (pool %. "range_end");
      in
      let args = [
          p;
          (* get_ vmemmap p; *)
          vmemmap_pointer;
          vmemmap;
          pool_pointer;
          pool
        ]
      in
      QPred {
          q = (p_s, IT.bt p); 
          condition = condition;
          pred = { name = "Vmemmap_page_wf"; args };
        }
    in

  let free_area_wf = 
      let i_s, i = IT.fresh_named Integer "i" in
      let condition = and_ [int_ 0 %<= i; i %< int_ mMAX_ORDER] in
      let args = [
          i;
          get_ (pool %. "free_area") i;
          vmemmap_pointer;
          vmemmap;
          pool_pointer;
          pool %. "range_start";
          pool %. "range_end"
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
      let qp_s, qp = IT.fresh_named Loc "qp" in
      let qp_int = pointerToIntegerCast_ qp in
      let i = 
        arrayShift_ 
          (vmemmap_pointer,
           struct_ct hyp_page_tag,
           (qp_int %/ (z_ pPAGE_SIZE)))
      in
      let condition = 
        and_ [
            (pool %. "range_start") %<= qp_int; 
            qp_int %< (pool %. "range_end");
            ((vmemmap %@ i) %. "refcount") %== int_ 0;
          ]
      in
      let qpoint = 
        QPredicate {
            name = "Byte";
            qpointer = qp_s;
            permission = condition;
            iargs = [];
            oargs = [];
          }
      in
      LRT.Resource (qpoint, (loc, None), 
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
      (* @@ Tools.skip (LRT.I) page_group_ownership *)
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

  let vpage = 
    let id = "VPage" in
    let loc = Loc.other "internal (VPage)" in
    let vbase_s, vbase = IT.fresh_named Loc "vbase" in
    let order_s, order = IT.fresh_named Integer "order" in
    let permission_s, permission = IT.fresh_named BT.Bool "permission" in
    let hyp_physvirt_offset_s, hyp_physvirt_offset = 
      IT.fresh_named BT.Integer "hyp_physvirt_offset" in
    let pbase = 
      integerToPointerCast_ 
        (add_ (pointerToIntegerCast_ vbase, 
               hyp_physvirt_offset)) 
    in
    let clause1 = 
      let value_s, value = IT.fresh_named (BT.Array (Loc, Integer)) "value" in
      let init_s, init = IT.fresh_named (BT.Array (Loc, Bool)) "init" in
      let qpoint = 
        let item_size = int_ (Memory.size_of_ctype char_ct) in
        let qpointer_s, qpointer = IT.fresh Loc in {
          ct = char_ct; 
          qpointer = qpointer_s;
          permission = 
            RE.array_permission ~base:pbase ~item_size 
              ~length:(mul_ (z_ pPAGE_SIZE, exp_ (int_ 2, order))) ~qpointer ~permission;
          value = get_ value qpointer;
          init = get_ init qpointer;
        }
      in
      let lrt =
        LRT.Logical ((value_s, IT.bt value), (loc, None),
        LRT.Logical ((init_s, IT.bt init), (loc, None),
        LRT.Resource (QPoint qpoint, (loc, None),
        LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct pbase), (loc, None),
        (* LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct (subPointer_ (addPointer_ (base, length), int_ 1))), (loc, None), *)
        (* LRT.Constraint (t_ (eq_ (rem_ (pointerToIntegerCast_ base, pPAGE_SIZE), int_ 0)), (loc, None), *)
        LRT.I))))
      in
      {
        loc = loc;
        guard = ne_ (vbase, null_);
        packing_ft = AT.of_lrt lrt (AT.I []) 
      }
    in
    let clause2 = 
      {
        loc = loc;
        guard = eq_ (vbase, null_);
        packing_ft = AT.I []
      }
    in
    let predicate = {
        loc = loc;
        pointer = vbase_s;
        permission = permission_s;
        iargs = [(order_s, IT.bt order);
                 (hyp_physvirt_offset_s, IT.bt hyp_physvirt_offset)]; 
        oargs = []; 
        clauses = [clause1; clause2]; 
      } 
    in
    (id, predicate)
  in




  [list_node;
   vmemmap_page;
   hyp_pool;
   vpage]








    
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
  byte () ::
  zerobyte () ::
  (* region () ::
   * zero_region () :: *)
  (* part_zero_region () :: *)
  early_alloc () ::
  (* for now: *)
  try page_alloc_predicates struct_decls with
  | Not_found -> []


    




