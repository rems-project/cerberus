module Loc = Locations
module IT = IndexTerms
module BT = BaseTypes

open IndexTerms
open Sctypes
open BaseTypes


type definition = {
    loc : Locations.t;
    args : (Sym.t * LogicalSorts.t) list;
    (* If the predicate is supposed to get used in a quantified form,
       one of the arguments has to be the index/quantified
       variable. For now at least. *)
    qarg : int option;
    body : IndexTerms.t
  }


module PageAlloc = struct

  module Aux(SD : sig val struct_decls : Memory.struct_decls end) = struct
    open SD

    let pPAGE_SHIFT = int_ 12
    let pPAGE_SIZE = exp_ (int_ 2, pPAGE_SHIFT)
    let mMAX_ORDER = int_ 11
    let _hHYP_NO_ORDER = int_ (-1)

    let list_head_tag, _ = Memory.find_tag struct_decls "list_head"
    let hyp_pool_tag, _ = Memory.find_tag struct_decls "hyp_pool"
    let hyp_page_tag, _ = Memory.find_tag struct_decls "hyp_page"

    let (%.) t member = IT.(%.) struct_decls t (Id.id member)

    let hyp_page_size = int_ (Memory.size_of_struct hyp_page_tag)

    let vmemmap_offset_of_pointer ~vmemmap_pointer pointer = 
      pointerToIntegerCast_ pointer %-
        pointerToIntegerCast_ vmemmap_pointer

    let vmemmap_good_pointer ~vmemmap_pointer pointer range_start range_end = 
      let offset = vmemmap_offset_of_pointer ~vmemmap_pointer pointer in
      let index = offset %/ hyp_page_size in
      let phys = index %* pPAGE_SIZE in
      and_ [ lePointer_ (vmemmap_pointer, pointer);
             eq_ (rem_ (offset, hyp_page_size), int_ 0);
             range_start %<= phys; phys %< range_end; ]

  end


  let predicates struct_decls = 

    let module Aux = Aux(struct let struct_decls = struct_decls end) in
    let open Aux in


    let vmemmap_page_wf =

      let id = "Vmemmap_page_wf" in
      let loc = Loc.other "internal (Vmemmap_page_wf)" in

      let page_pointer_s, page_pointer = IT.fresh_named Loc "page_pointer" in
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let range_start_s, range_start = IT.fresh_named BT.Integer "range_start" in
      let range_end_s, range_end = IT.fresh_named BT.Integer "range_end" in
      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Array (Loc, BT.Struct hyp_page_tag)) "vmemmap" 
      in

      let page = get_ vmemmap page_pointer in


      let args = [
          (page_pointer_s, IT.bt page_pointer);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
          (pool_pointer_s, IT.bt pool_pointer);
          (range_start_s, IT.bt range_start);
          (range_end_s, IT.bt range_end);
        ]
      in
      let qarg = Some 0 in

      let self_node_pointer = 
        memberShift_ (page_pointer, hyp_page_tag, Id.id "node") in

      let pool_free_area_pointer = 
        arrayShift_
          (memberShift_ (pool_pointer, hyp_pool_tag, Id.id "free_area"),
           struct_ct list_head_tag,
           page %. "order");
      in

      (* wrong, have to fix *)
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


      let body = and_ constrs in

      (id, {loc; args; body; qarg} )
    in




    (* check: possibly inconsistent *)
    let free_area_cell_wf =

      let id = "FreeArea_cell_ef" in
      let loc = Loc.other "internal (FreeArea_cell_wf)" in

      let cell_pointer_s, cell_pointer = IT.fresh_named Loc "cell_pointer" in
      let cell_s, cell = IT.fresh_named (BT.Struct list_head_tag) "cell" in
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Array (Loc, BT.Struct hyp_page_tag)) "vmemmap" in
      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let range_start_s, range_start = IT.fresh_named Integer "range_start" in
      let range_end_s, range_end = IT.fresh_named Integer "range_end" in

      let args = [
          (cell_pointer_s, IT.bt cell_pointer);
          (cell_s, IT.bt cell);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
          (pool_pointer_s, IT.bt pool_pointer);
          (range_start_s, IT.bt range_start);
          (range_end_s, IT.bt range_end);
        ]
      in
      let qarg = Some 0 in


      let free_area_base_pointer = 
        addPointer_ (pool_pointer, memberOffset_ (hyp_pool_tag, Id.id "free_area")) in

      let offset_within_free_area =
        (pointerToIntegerCast_ cell_pointer) %-
          (pointerToIntegerCast_ free_area_base_pointer)
      in

      let index_in_free_area = 
        offset_within_free_area %/ (int_ (Memory.size_of_struct list_head_tag))
      in

      let order = index_in_free_area in


      let body = 
        let prev = cell %. "prev" in
        let prev_pointer = addPointer_ (cell_pointer, memberOffset_ (list_head_tag, Id.id "prev")) in
        let next = cell %. "next" in
        let next_pointer = addPointer_ (cell_pointer, memberOffset_ (list_head_tag, Id.id "next")) in
        or_ [and_ [prev %== cell_pointer; next %== cell_pointer];
             and_ begin
                 let prev_vmemmap = container_of_ (prev, hyp_page_tag, Id.id "node") in
                 let next_vmemmap = container_of_ (next, hyp_page_tag, Id.id "node") in
                 [(*prev*)
                   vmemmap_good_pointer ~vmemmap_pointer prev_vmemmap range_start range_end;
                   ((get_ vmemmap prev_vmemmap) %. "order") %== order;
                   ((get_ vmemmap prev_vmemmap) %. "refcount") %== (int_ 0);
                   (((get_ vmemmap prev_vmemmap) %. "node") %. "next") %== prev_pointer;
                   (*next*)
                   vmemmap_good_pointer ~vmemmap_pointer next_vmemmap range_start range_end;
                   ((get_ vmemmap next_vmemmap) %. "order") %== order;
                   ((get_ vmemmap next_vmemmap) %. "refcount") %== (int_ 0);
                   (((get_ vmemmap next_vmemmap) %. "node") %. "prev") %== next_pointer;
                 ]
               end
          ]
      in

      (id, {loc; args; body; qarg} )
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




    let hyp_pool_wf =
      let id = "Hyp_pool_wf" in
      let loc = Loc.other "internal (Hyp_pool_wf)" in
      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let pool_s, pool = IT.fresh_named (Struct hyp_pool_tag) "pool" in
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Array (Loc, BT.Struct hyp_page_tag)) "vmemmap" in

      let args = [
          (pool_pointer_s, IT.bt pool_pointer);
          (pool_s, IT.bt pool);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
        ]
      in
      let qarg = None in

      let range_start = pool %. "range_start" in
      let range_end = pool %. "range_end" in
      let max_order = pool %. "max_order" in

      let beyond_range_end_cell_pointer = 
        addPointer_ (vmemmap_pointer, (range_end %/ pPAGE_SIZE) %* hyp_page_size) in
      let metadata_well_formedness =
        and_ [
            good_ (pointer_ct void_ct, integerToPointerCast_ range_start);
            good_ (pointer_ct void_ct, integerToPointerCast_ range_end);
            range_start %< range_end;
            rem_ (range_start, pPAGE_SIZE) %== int_ 0;
            rem_ (range_end, pPAGE_SIZE) %== int_ 0;
            good_ (pointer_ct void_ct, beyond_range_end_cell_pointer);
            max_order %> int_ 0;
            max_order %<= mMAX_ORDER;
          ]
      in
      let vmemmap_pointer_aligned = 
        aligned_ (vmemmap_pointer,
                  array_ct (struct_ct hyp_page_tag) None)
      in

      let body = and_ [metadata_well_formedness; vmemmap_pointer_aligned] in

      (id, { loc; args; qarg; body; })
      
    in
    [vmemmap_page_wf;
     free_area_cell_wf;
     hyp_pool_wf]








      (* let vmemmap_metadata_owned =
       *   let p_s, p = IT.fresh_named Loc "p" in
       *   let point_permission = 
       *     let condition = 
       *       vmemmap_good_pointer ~vmemmap_pointer p
       *         range_start range_end
       *     in
       *     ite_ (condition, permission, q_ (0, 1))
       *   in
       *   let vmemmap_array = 
       *     QPredicate {
       *         qpointer = p_s;
       *         name = "Vmemmap_page";
       *         iargs = [
       *             vmemmap_pointer;
       *             pool_pointer;
       *             range_start;
       *             range_end;
       *           ];
       *         oargs = [get_ vmemmap p];
       *         permission = point_permission;
       *       }
       *   in
       *   let aligned = 
       *     aligned_ (vmemmap_pointer,
       *               array_ct (struct_ct hyp_page_tag) None)
       *   in
       *   LRT.Logical ((vmemmap_s, IT.bt vmemmap), (loc, None),
       *   LRT.Resource (vmemmap_array, (loc, None), 
       *   LRT.Constraint (t_ aligned, (loc, None), 
       *   LRT.I)))
       * in *)



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


end


let predicate_list struct_decls = 
  try PageAlloc.predicates struct_decls with
  | Not_found -> []


    
