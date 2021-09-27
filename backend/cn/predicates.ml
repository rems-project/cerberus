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





type predicate_definition = {
    loc : Loc.t;
    pointer: Sym.t;
    iargs : (Sym.t * LS.t) list;
    oargs : (string * LS.t) list;
    permission: Sym.t;
    clauses : clause list;
  }
  
let pp_predicate_definition def = 
  item "pointer" (Sym.pp def.pointer) ^/^
  item "iargs" (Pp.list (fun (s,_) -> Sym.pp s) def.iargs) ^/^
  item "oargs" (Pp.list (fun (s,_) -> Pp.string s) def.oargs) ^/^
  item "permission" (Sym.pp def.permission) ^/^
  item "clauses" (Pp.list pp_clause def.clauses)
  






let region () = 
  let id = "Region" in
  let loc = Loc.other "internal (Region)" in
  let base_s, base = IT.fresh_named Loc "base" in
  let length_s, length = IT.fresh_named Integer "length" in
  let permission_s, permission = IT.fresh_named BT.Real "permission" in
  let value_s, value = IT.fresh_named (BT.Array (Loc, Integer)) "value" in
  let init_s, init = IT.fresh_named (BT.Array (Loc, Bool)) "init" in
  let qpoint = 
    let qpointer_s, qpointer = IT.fresh Loc in {
      ct = char_ct; 
      qpointer = qpointer_s;
      permission = 
        RE.array_permission ~base ~item_ct:char_ct
          ~length ~qpointer ~permission;
      value = get_ value qpointer;
      init = get_ init qpointer;
    }
  in
  let lrt =
    LRT.Logical ((value_s, IT.bt value), (loc, None),
    LRT.Logical ((init_s, IT.bt init), (loc, None),
    LRT.Resource (QPoint qpoint, (loc, None),
    LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct base), (loc, None),
    LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct (subPointer_ (addPointer_ (base, length), int_ 1))), (loc, None),
    LRT.I)))))
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = AT.of_lrt lrt (AT.I []) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = base_s;
      permission = permission_s;
      iargs = [(length_s, IT.bt length)]; 
      oargs = []; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)



let part_zero_region () = 
  let id = "PartZeroRegion" in
  let loc = Loc.other "internal (PartZeroRegion)" in
  let base_s, base = IT.fresh_named Loc "base" in
  let permission_s, permission = IT.fresh_named BT.Real "permission" in
  let length_s, length = IT.fresh_named Integer "length" in
  let value_s, value = IT.fresh_named (BT.Array (Loc, Integer)) "value" in
  let init_s, init = IT.fresh_named (BT.Array (Loc, Bool)) "init" in
  let up_to_s, up_to = IT.fresh_named Integer "up_to" in
  let qp_s, qp = IT.fresh Loc in 
  let qpoint = {
      ct = char_ct; 
      qpointer = qp_s;
      permission = array_permission ~item_ct:char_ct ~base
                     ~length ~qpointer:qp ~permission;
      value = get_ value qp;
      init = get_ init qp;
    }
  in
  let constr = 
    forall_ (qp_s, IT.bt qp)
      (impl_ (and_ [lePointer_ (base, qp); 
                    ltPointer_ (qp, addPointer_ (base, up_to))],
              and_ [eq_ (get_ value qp, int_ 0);
                    get_ init qp]))
  in
  let lrt =
    LRT.Logical ((value_s, IT.bt value), (loc, None), 
    LRT.Logical ((init_s, IT.bt init), (loc, None), 
    LRT.Resource (QPoint qpoint, (loc, None),
    LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct base), (loc, None),
    LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct (subPointer_ (addPointer_ (base, length), int_ 1))), (loc, None),
    LRT.Constraint (constr, (loc, None),
    LRT.I))))))
  in
  let clause = {
      loc = loc;
      guard = bool_ true;
      packing_ft = AT.of_lrt lrt (AT.I []) 
    }
  in
  let predicate = {
      loc = loc;
      pointer = base_s;
      permission = permission_s;
      iargs = [(length_s, IT.bt length); 
               (up_to_s, IT.bt up_to);]; 
      oargs = []; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)




let zero_region () = 
  let id = "ZeroRegion" in
  let loc = Loc.other "internal (ZeroRegion)" in
  let base_s, base = IT.fresh_named Loc "base" in
  let length_s, length = IT.fresh_named Integer "length" in
  let permission_s, permission = IT.fresh_named BT.Real "permission" in
  let qp_s, qp = IT.fresh_named Loc "p" in
  let qpoint = {
      ct = char_ct; 
      qpointer = qp_s;
      permission = array_permission ~item_ct:char_ct ~base ~length
                     ~qpointer:qp ~permission;
      value = int_ 0;
      init = bool_ true;
    }
  in
  let lrt =
    LRT.Resource (QPoint qpoint, (loc, None),
    LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct base), (loc, None),
    LRT.Constraint (t_ (IT.good_pointer ~pointee_ct:char_ct (subPointer_ (addPointer_ (base, 
length), int_ 1))), (loc, None),
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
      pointer = base_s;
      permission = permission_s;
      iargs = [(length_s, IT.bt length)]; 
      oargs = []; 
      clauses = [clause]; 
    } 
  in
  (id, predicate)



let early_alloc () = 
  let id = "EarlyAlloc" in
  let loc = Loc.other "internal (EarlyAlloc)" in
  let start_s, start = IT.fresh_named Loc "start" in
  let permission_s, permission = IT.fresh_named BT.Real "permission" in
  let end_s, end_t = IT.fresh_named Loc "end" in
  let length = 
    add_ (sub_ (pointerToIntegerCast_ end_t,
                pointerToIntegerCast_ start), 
          int_ 1)
  in
  let region = {
      name = "Region";
      pointer = start; 
      iargs = [length];
      oargs = [];
      permission = permission;
    }
  in
  let lrt =
    LRT.Resource (Predicate region, (loc, None),
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

  let pPAGE_SHIFT = int_ 12 in
  let pPAGE_SIZE = exp_ (int_ 2, pPAGE_SHIFT) in
  let mMAX_ORDER = int_ 11 in
  let _hHYP_NO_ORDER = int_ (-1) in

  let find_tag tag = 
    SymMap.choose
      (SymMap.filter (fun s _ ->
           match Sym.description s with
           | Sym.SD_Id tag' when String.equal tag tag' -> true
           | _ -> false
         ) struct_decls
      )
  in

  let list_head_tag, _ = find_tag "list_head" in
  let hyp_pool_tag, _ = find_tag "hyp_pool" in
  let hyp_page_tag, _ = find_tag "hyp_page" in

  let (%.) t member = IT.(%.) struct_decls t (Id.id member) in

  let hyp_page_size = int_ (Memory.size_of_struct hyp_page_tag) in

  let vmemmap_offset_of_pointer ~vmemmap_pointer pointer = 
    pointerToIntegerCast_ pointer %-
      pointerToIntegerCast_ vmemmap_pointer
  in
  
  let vmemmap_good_pointer ~vmemmap_pointer pointer range_start range_end = 
    let offset = vmemmap_offset_of_pointer ~vmemmap_pointer pointer in
    let index = offset %/ hyp_page_size in
    let phys = index %* pPAGE_SIZE in
    and_ [ lePointer_ (vmemmap_pointer, pointer);
           eq_ (rem_ (offset, hyp_page_size), int_ 0);
           range_start %<= phys; phys %< range_end; ]
  in


  let vmemmap_page =

    let id = "Vmemmap_page" in
    let loc = Loc.other "internal (Vmemmap_page)" in

    let page_pointer_s, page_pointer = IT.fresh_named Loc "page_pointer" in
    let permission_s, permission = IT.fresh_named BT.Real "permission" in
    (* iargs *)
    let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
    let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
    let range_start_s, range_start = IT.fresh_named Integer "range_start" in
    let range_end_s, range_end = IT.fresh_named Integer "range_end" in
    (* oargs *)
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

    let wellformedness = 

      let self_node_pointer = 
        memberShift_ (page_pointer, hyp_page_tag, Id.id "node") in

      let pool_free_area_pointer = 
        arrayShift_
          (memberShift_ (pool_pointer, hyp_pool_tag, Id.id "free_area"),
           struct_ct list_head_tag,
           page %. "order");
      in

      let _prev_next_well_formed prev_next = 
        let prev_next = (page %. "node") %.prev_next in
        or_ [
            (* either empty list (pointer to itself) *)
            prev_next %== self_node_pointer;
            (* or pointer to free_area cell *)
            prev_next %== pool_free_area_pointer;
            (* or pointer to other vmemmap cell, within the same range*)
            vmemmap_good_pointer ~vmemmap_pointer 
              (container_of_ (prev_next, hyp_page_tag, Id.id "node"))
              range_start range_end
          ]
      in

      let constrs = [
          (* representable, including that refcount is natural number *)
          representable_ (struct_ct hyp_page_tag, page);
          (* refcount is also valid signed int: for hyp_page_count *)
          representable_ (integer_ct (Signed Int_), page %. "refcount");
          (* order is HYP_NO_ORDER or between 0 and MAX_ORDER *)
          (* (or_ [(page_t %. "order") %== int_ hHYP_NO_ORDER; 
           *       and_ [int_ 0 %<= (page_t %. "order"); (page_t %. "order") %<= int_ mMAX_ORDER]]);              
           * (\* points back to the pool *\)
           * ((page_t %. "pool") %== pool_pointer_t);              
           * (\* list emptiness via next and prev is equivalent ("prev/next" points back at node for index i_t) *\)
           * eq_ (((page_t %. "node") %. "next") %== self_node_pointer_t,
           *      ((page_t %. "node") %. "prev") %== self_node_pointer_t);
           * (\* list non-empty in the above sense if and only if refcount 0 and order != NYP_NO_ORDER *\)
           * (eq_ (
           *      ((page_t %. "node") %. "next") %!= self_node_pointer_t,
           *      and_ [(page_t %. "refcount") %== int_ 0;
           *            (page_t %. "order") %!= int_ hHYP_NO_ORDER;
           *        ]
           * ));
           * prev_next_well_formed "prev";
           * prev_next_well_formed "next"; *)
        ]
      in
      List.map (fun lc -> (t_ lc, (loc, None))) constrs
    in

    let lrt = 
      AT.of_lrt (
        LRT.Logical ((page_s, IT.bt page), (loc, None),
        LRT.Resource (resource, (loc, None),
        LRT.mConstraints wellformedness
        LRT.I)))
        (AT.I 
        OutputDef.[{loc; name = "page"; value= page}])
    in

    let clause = { loc; guard = bool_ true; packing_ft = lrt } in
    
    let predicate = {
        loc = loc;
        pointer = page_pointer_s;
        iargs = [
            (vmemmap_pointer_s, IT.bt vmemmap_pointer);
            (pool_pointer_s, IT.bt pool_pointer);
            (range_start_s, IT.bt range_start);
            (range_end_s, IT.bt range_end);
          ];
        oargs = [("page", IT.bt page)];
        permission = permission_s;
        clauses = [clause]; 
      } 
    in
    (id, predicate)
  in



  (* let vmemmap_cell_address hyp_vmemmap_t i_t =
   *   arrayShift_ (hyp_vmemmap_t, 
   *                Sctype ([], Struct hyp_page_tag), 
   *                i_t)
   * in *)

  (* let _vmemmap_cell_node_address hyp_vmemmap_t i_t =
   *   memberShift_ (vmemmap_cell_address hyp_vmemmap_t i_t,
   *                 hyp_page_tag,
   *                 Id.id "node")
   * in *)



  
  (* let _vmemmap_node_pointer_to_index hyp_vmemmap_t pointer = 
   *   vmemmap_offset_of_node_pointer hyp_vmemmap_t pointer %/
   *     int_ (Memory.size_of_struct hyp_page_tag)
   * in *)
  
  (* let _vmemmap_node_pointer_to_cell_pointer hyp_vmemmap_t pointer = 
   *   vmemmap_offset_of_node_pointer hyp_vmemmap_t pointer
   * in *)




  (* let free_area_cell = 
   * 
   *   let id = "Free_area_cell" in
   *   let loc = Loc.other "internal (Free_area_cell)" in
   *   
   *   let vmemmap_pointer_s, vmemmap_pointer_t = IT.fresh_named Loc "vmemmap_pointer" in
   *   let vmemmap_s, vmemmap_t = IT.fresh_named (BT.Array (Integer, Struct hyp_page_tag)) "vmemmap" in
   *   let range_start_s, range_start_t = IT.fresh_named Integer "range_start" in
   *   let range_end_s, range_end_t = IT.fresh_named Integer "range_end" in
   *   let order_s, order_t = IT.fresh_named Integer "order" in
   * 
   *   let cell_pointer_s, cell_pointer_t = IT.fresh_named Loc "cell_pointer" in
   *   let cell_s, cell_t = IT.fresh_named (BT.Struct list_head_tag) "cell" in
   * 
   *   let constr prev_next = 
   *     let prev_next_t = cell_t %. prev_next in
   *     or_ [
   *         prev_next_t %== cell_pointer_t;
   *         and_ (
   *             vmemmap_good_node_pointer vmemmap_pointer_t prev_next_t ::
   *               (let i_t = vmemmap_node_pointer_to_index vmemmap_pointer_t prev_next_t in
   *                [range_start_t %<= i_t; i_t %< range_end_t;
   *                 ((vmemmap_t %@ i_t) %. "order") %== order_t;
   *                 ((vmemmap_t %@ i_t) %. "refcount") %== int_ 0]
   *               )
   *           )
   *       ]
   *   in
   *   
   *   let lrt = 
   *     let points = 
   *       point (cell_pointer_t, Memory.size_of_struct list_head_tag) 
   *         (q_ (1, 1)) cell_t (bool_ true)
   *     in
   *     LRT.Logical ((cell_s, IT.bt cell_t),
   *     LRT.Resource (points,
   *     LRT.Constraint (t_ (constr "prev"),
   *     LRT.Constraint (t_ (constr "next"),
   *     LRT.I))))
   *   in
   * 
   *   let predicate = 
   *     {
   *       loc = loc;
   *       pointer = cell_pointer_s;
   *       iargs = [
   *           (vmemmap_pointer_s, IT.bt vmemmap_pointer_t);
   *           (vmemmap_s, IT.bt vmemmap_t);
   *           (range_start_s, IT.bt range_start_t);
   *           (range_end_s, IT.bt range_end_t);
   *           (order_s, IT.bt order_t);
   *         ];
   *       oargs = [("cell", IT.bt cell_t)];
   *       clauses = 
   *         [(loc, PackingFT.of_lrt lrt 
   *                (PackingFT.I [("cell", cell_t)]));]; 
   *     } 
   *   in
   *   (id, predicate)
   * in *)







  let hyp_pool =

    let id = "Hyp_pool" in
    let loc = Loc.other "internal (Hyp_pool)" in
    let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
    let permission_s, permission = IT.fresh_named BT.Real "permission" in
    (* iargs *)
    let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
    (* oargs *)
    let pool_s, pool = IT.fresh_named (BT.Struct hyp_pool_tag) "pool" in


    let vmemmap_s, vmemmap = 
      IT.fresh_named (BT.Array (Loc, BT.Struct hyp_page_tag)) "vmemmap" in
    let range_start = pool %. "range_start" in
    let range_end = pool %. "range_end" in
    let max_order_t = pool %. "max_order" in
    let _free_area_t = pool %. "free_area" in

    let metadata_ownership = 
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

    let beyond_range_end_cell_pointer = 
      addPointer_ (vmemmap_pointer, (range_end %/ pPAGE_SIZE) %* hyp_page_size) in
    let metadata_well_formedness =
      let constrs = [
          representable_ (pointer_ct void_ct, integerToPointerCast_ range_start);
          representable_ (pointer_ct void_ct, integerToPointerCast_ range_end);
          range_start %< range_end;
          rem_ (range_start, pPAGE_SIZE) %== int_ 0;
          rem_ (range_end, pPAGE_SIZE) %== int_ 0;
          representable_ (pointer_ct void_ct, beyond_range_end_cell_pointer);
          max_order_t %> int_ 0;
          max_order_t %<= mMAX_ORDER;
        ]
      in
      LRT.mConstraints (List.map (fun lc -> (t_ lc, (loc, None))) constrs) LRT.I
    in

    let vmemmap_metadata_owned =
      let p_s, p = IT.fresh_named Loc "p" in
      let point_permission = 
        let condition = 
          vmemmap_good_pointer ~vmemmap_pointer p
            range_start range_end
        in
        ite_ (condition, permission, q_ (0, 1))
      in
      let vmemmap_array = 
        QPredicate {
            qpointer = p_s;
            name = "Vmemmap_page";
            iargs = [
                vmemmap_pointer;
                pool_pointer;
                range_start;
                range_end;
              ];
            oargs = [get_ vmemmap p];
            permission = point_permission;
          }
      in
      let aligned = 
        aligned_ (vmemmap_pointer,
                  array_ct (struct_ct hyp_page_tag) None)
      in

      LRT.Logical ((vmemmap_s, IT.bt vmemmap), (loc, None),
      LRT.Resource (vmemmap_array, (loc, None), 
      LRT.Constraint (t_ aligned, (loc, None), 
      LRT.I)))
    in

    let free_area_well_formedness = 
      (* let constr prev_next = 
       *   let o_s, o_t = IT.fresh_named Integer "o" in
       *   let prev_next_t = (free_area_t %@ o_t) %. prev_next in
       *   let cell_pointer_t = 
       *     arrayShift_ (memberShift_ (pool_pointer_t, hyp_pool_tag, Id.id "free_area"),
       *                  Sctype ([], Struct hyp_pool_tag),
       *                  o_t) 
       *   in
       *   forall_ (o_s, IT.bt o_t) 
       *     (\* (Some (T_Member (T_Get (T_Term free_area_t, T_Term o_t), Id.id prev_next))) *\)
       *     begin
       *       and_ []
       *           good_pointer prev_next_t (Sctype ([], Struct list_head_tag));
       *           or_ [
       *               prev_next_t %== cell_pointer_t;
       *               and_ (
       *                   vmemmap_good_node_pointer vmemmap_pointer_t prev_next_t :: []
       * 
       *                 (\* (let p_t = vmemmap_node_pointer_to_cell_pointer vmemmap_pointer_t prev_next_t in
       *                  *  [range_start_t %<= p_t; p_t %< range_end_t;
       *                  *   ((get_ vmemmap_t p_t) %. "order") %== o_t;
       *                  *   ((get_ vmemmap_t p_t) %. "refcount") %== int_ 0] *\)
       *                 )
       *             ]
       *         ]
       *     end
       * in
       * LRT.Constraint (constr "prev", (loc, None), 
       * LRT.Constraint (constr "next", (loc, None), 
       * LRT.I)) *)
      LRT.I
    in

    let vmemmap_well_formedness2 = 
      let constr prev_next =
        (* let i_s, i_t = IT.fresh_named Integer "i" in *)
        (* let trigger = 
         *   T_Member (T_Member (T_App (T_Term vmemmap_t, T_Term i_t), Id.id "node"), Id.id prev_next)
         * in *)
        T (bool_ true)
        (* forall_trigger_ (i_s, IT.bt i_t) (Some trigger)
         *   begin
         *     let prev_next_t = ((vmemmap_t %@ i_t) %. "node") %.prev_next in
         *     impl_ (
         *         vmemmap_good_node_pointer vmemmap_pointer_t prev_next_t
         *       ,
         *         let j_t = vmemmap_node_pointer_to_index vmemmap_pointer_t prev_next_t in
         *         and_
         *           [
         *             (\* (((vmemmap_t %@ j_t) %. "node") %.(if prev_next = "next" then "prev" else "next")) %== 
         *              *   (vmemmap_cell_node_address vmemmap_pointer_t i_t); *\)
         *             ((vmemmap_t %@ i_t) %. "order") %== ((vmemmap_t %@ j_t) %. "order");
         *         (\* forall_sth_ (k_s, IT.bt k_t)
         *          *   (and_ [(i_t %+ int_ 1) %<= k_t; 
         *          *          k_t %< (i_t %+ (exp_ (int_ 2, (vmemmap_t %@ i_t) %. "order")))])
         *          *   (and_ [
         *          *       ((vmemmap_t %@ k_t) %. "order") %== hHYP_NO_ORDER_t;
         *          *       ((vmemmap_t %@ k_t) %. "refcount") %== int_ 0;
         *          *     ])
         *          * ] *\)
         *           ]
         *       )
         *   end *)
      in
      LRT.Constraint (constr "prev", (loc, None), 
      LRT.Constraint (constr "next", (loc, None), 
      LRT.I))
    in

    (* let page_group_ownership = 
     *   let qp_s, qp_t = IT.fresh_named Loc "qp" in
     *   let bytes_s, bytes_t = IT.fresh_named (BT.Array (Loc, Integer)) "bytes" in
     *   let condition = 
     *     let i_t = (pointerToIntegerCast_ qp_t) %/ pPAGE_SIZE_t in
     *     and_ [
     *         gtPointer_ (qp_t, pointer_ (Z.of_int 0));
     *           (and_ (
     *              [range_start_t %<= pointerToIntegerCast_ qp_t; 
     *               pointerToIntegerCast_ qp_t %< range_end_t;
     *               or_ [
     *                   and_ [((vmemmap_t %@ i_t) %. "order") %!= int_ hHYP_NO_ORDER;
     *                         ((vmemmap_t %@ i_t) %. "refcount") %== int_ 0];
     *                   and_ [((vmemmap_t %@ i_t) %. "order") %== int_ hHYP_NO_ORDER;
     *                         ((vmemmap_t %@ i_t) %. "refcount") %== int_ 0]
     *                 ]
     *              ]
     *           ))
     *       ]
     *   in
     *   let qpoint = 
     *     QPoint {
     *         qpointer = qp_s;
     *         size = Z.of_int 1;
     *         permission = ite_ (condition, q_ (1, 1), q_ (0, 1));
     *         value = get_ bytes_t qp_t;
     *         init = bool_ false;
     *       }
     *   in
     *   LRT.Logical ((bytes_s, IT.bt bytes_t),
     *   LRT.Resource (qpoint, LRT.I))
     * in *)

    let lrt = 
      let open LRT in
      metadata_ownership
      @@ metadata_well_formedness
      @@ vmemmap_metadata_owned
      @@ free_area_well_formedness (* possibly inconsistent *)
      @@ vmemmap_well_formedness2
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
          ]
        ;
        oargs = [
            ("pool", IT.bt pool); 
            ("vmemmap", IT.bt vmemmap)
          ];
        clauses = [clause;]; 
      } 
    in
    (id, predicate)


  in
  [vmemmap_page;
   hyp_pool]



let predicate_list struct_decls = 
  region () ::
  zero_region () ::
  part_zero_region () ::
  early_alloc () ::
  (* for now: *)
  try page_alloc_predicates struct_decls with
  | Not_found -> []


    
