module Loc = Locations
module IT = IndexTerms
module BT = BaseTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes

open IndexTerms
open Sctypes
open BaseTypes


type def_or_uninterp = 
  | Def of IndexTerms.t
  | Uninterp

type definition = {
    loc : Locations.t;
    args : (Sym.t * LogicalSorts.t) list;
    (* If the predicate is supposed to get used in a quantified form,
       one of the arguments has to be the index/quantified
       variable. For now at least. *)
    return_bt: BT.t;
    definition : def_or_uninterp;
  }



let open_pred def_args def_body args =
  let su = make_subst (List.map2 (fun (s, _) arg -> (s, arg)) def_args args) in
  IT.subst su def_body


exception Struct_not_found



let order_aligned_sym = Sym.fresh_named "order_aligned"
let order_align_sym = Sym.fresh_named "order_align"
let pfn_buddy_sym = Sym.fresh_named "pfn_buddy"
let buddy_sym = Sym.fresh_named "buddy"
let page_size_of_order_sym = Sym.fresh_named "page_size_of_order"
let page_group_ok_sym = Sym.fresh_named "page_group_ok"
let vmemmap_wf_sym = Sym.fresh_named "vmemmap_wf"
let init_vmemmap_page_sym = Sym.fresh_named "init_vmemmap_page"
let vmemmap_l_wf_sym = Sym.fresh_named "vmemmap_l_wf"
let vmemmap_b_wf_sym = Sym.fresh_named "vmemmap_b_wf"
let freeArea_cell_wf_sym = Sym.fresh_named "freeArea_cell_wf"
let hyp_pool_wf_sym = Sym.fresh_named "hyp_pool_wf"




let make_uninterp (fname : Sym.t) arg_spec return_bt = 

  let id = fname in
  let loc = Loc.other ("internal ("^ Sym.pp_string fname^")") in
  (id, {loc; args = arg_spec; return_bt; definition = Uninterp})



let exp_sym = Sym.fresh_named "exp"

let exp_fun = make_uninterp exp_sym
        [(Sym.fresh_named "n", Integer); (Sym.fresh_named "exponent", Integer);]
        Integer

let mk_exp (x, y) = pred_ exp_sym [x; y] Integer


module PageAlloc = struct

  module Aux(SD : sig val struct_decls : Memory.struct_decls end) = struct
    open SD

    let pPAGE_SHIFT = 12
    let pPAGE_SIZE = 4096
    let mMAX_ORDER = 11
    let hHYP_NO_ORDER = 4294967295

    let list_head_tag, _ = 
      try Memory.find_tag struct_decls "list_head" with
      | Not_found -> raise Struct_not_found
    let hyp_pool_tag, _ = 
      try Memory.find_tag struct_decls "hyp_pool" with
      | Not_found -> raise Struct_not_found
    let hyp_page_tag, _ = 
      try Memory.find_tag struct_decls "hyp_page" with
      | Not_found -> raise Struct_not_found

    let (%.) t member = IT.(%.) struct_decls t (Id.id member)

    let hyp_page_size = int_ (Memory.size_of_struct hyp_page_tag)

    let vmemmap_offset_of_pointer ~vmemmap_pointer pointer = 
      IT.array_offset_of_pointer ~base:vmemmap_pointer ~pointer

    let vmemmap_index_of_pointer ~vmemmap_pointer pointer = 
      array_pointer_to_index ~base:vmemmap_pointer ~item_size:hyp_page_size
        ~pointer

    let vmemmap_good_pointer ~vmemmap_pointer pointer range_start range_end = 
      cellPointer_ ~base:vmemmap_pointer ~step:hyp_page_size
        ~starti:(range_start %/ int_ pPAGE_SIZE)
        ~endi:(range_end %/ int_ pPAGE_SIZE)
        ~p:pointer


    let vmemmap_resource ~vmemmap_pointer ~range_start ~range_end =
      let range_start_i = range_start %/ (int_ pPAGE_SIZE) in
      let range_end_i = range_end %/ (int_ pPAGE_SIZE) in
      let q_s, q = IT.fresh_named Integer "q" in
      let resource =
        ResourceTypes.Q {
            name = Owned (Struct hyp_page_tag);
            q = q_s;
            pointer = vmemmap_pointer;
            iargs = [];
            step = Memory.size_of_ctype (Struct hyp_page_tag);
            permission = and_ [range_start_i %<= q; q %<= (sub_ (range_end_i, int_ 1))];
           }
      in
      let oargs_spec = Resources.q_owned_oargs (Struct hyp_page_tag) in
      (resource, oargs_spec)


  end


  let predicates struct_decls = 

    let module Aux = Aux(struct let struct_decls = struct_decls end) in
    let open Aux in


    let order_aligned = 
      (* let _body = divisible_ (page_index, exp_ (int_ 2, sym_ (order, Integer))) in *)
      make_uninterp order_aligned_sym
        [(Sym.fresh_named "page_index", Integer);
         (Sym.fresh_named "order", Integer);]
        Bool
    in

    let order_align = 
      make_uninterp order_align_sym
        [(Sym.fresh_named "page_index", Integer);
         (Sym.fresh_named "order", Integer);]
        Integer
    in

    let pfn_buddy =
      make_uninterp pfn_buddy_sym
        [(Sym.fresh_named "p", Integer);
         (Sym.fresh_named "order", Integer);]
        Integer
    in

    let buddy = 
      make_uninterp buddy_sym
        [(Sym.fresh_named "p", Loc);
         (Sym.fresh_named "order", Integer);]
        Loc
    in

    let page_size_of_order = 
      make_uninterp page_size_of_order_sym
        [(Sym.fresh_named "order", Integer)]
        Integer
    in


    let page_group_ok =
      let id = page_group_ok_sym in
      let loc = Loc.other ("internal ("^(Sym.pp_string id)^")") in
      let page_index_s, page_index = IT.fresh_named Integer "page_index" in
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Map (Integer, BT.Struct hyp_page_tag)) "vmemmap" in
      let pool_s, pool = IT.fresh_named (BT.Struct hyp_pool_tag) "pool" in

      let page = map_get_ vmemmap page_index in

      let args = [
          (page_index_s, IT.bt page_index);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
          (pool_s, IT.bt pool);
        ]
      in

      let body = 
        let o_s, o = IT.fresh Integer in
        let oa_i = pred_ order_align_sym [page_index; o] Integer in
        let in_page_group =
          and_ [oa_i %< page_index; 
                ((pool %. "range_start") %/ int_ pPAGE_SIZE) %<= oa_i;
                o %<= ((map_get_ vmemmap oa_i) %. "order");
                not_ (((map_get_ vmemmap oa_i) %. "order") %== int_ hHYP_NO_ORDER)]
        in
        
        or_ [
            eachI_ (1, o_s, mMAX_ORDER - 1) (not_ in_page_group);
	    (page %. "order") %== int_ hHYP_NO_ORDER;
          ]
      in
      
      (id, {loc; args; definition = Def body; return_bt = Bool})
    in


    let vmemmap_wf =

      let id = vmemmap_wf_sym in
      let loc = Loc.other "internal (vmemmap_wf)" in

      let page_index_s, page_index = IT.fresh_named Integer "page_index" in

      (* let page_pointer_s, page_pointer = IT.fresh_named Loc "page_pointer" in *)
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let pool_s, pool = IT.fresh_named (BT.Struct hyp_pool_tag) "pool" in

      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Map (Integer, BT.Struct hyp_page_tag)) "vmemmap" 
      in

      let page = map_get_ vmemmap page_index in

      let args = [
          (page_index_s, IT.bt page_index);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
          (pool_pointer_s, IT.bt pool_pointer);
          (pool_s, IT.bt pool);
        ]
      in

      let body = 
        let page_pointer = arrayShift_ (vmemmap_pointer, struct_ct hyp_page_tag, page_index) in
        let self_node_pointer = memberShift_ (page_pointer, hyp_page_tag, Id.id "node") in
        let prev = (page %. "node") %. "prev" in
        let next = (page %. "node") %. "next" in
        and_ [
            (* refcount is also valid signed int: for hyp_page_count *)
            representable_ (integer_ct (Signed Int_), page %. "refcount");
            (* order is HYP_NO_ORDER or between 0 and max_order *)
            (or_ [(page %. "order") %== int_ hHYP_NO_ORDER; 
                  and_ [int_ 0 %<= (page %. "order"); 
                        (page %. "order") %< (pool %. "max_order");
                        (page %. "order") %< int_ mMAX_ORDER;
            ]]);              
            (* points back to the pool *)
            ((page %. "pool") %== pool_pointer);
            (impl_ (
                 (page %. "order") %!= int_ hHYP_NO_ORDER,
                 pred_ order_aligned_sym [page_index; page%."order"] BT.Bool));
            (impl_ (
                 (page %. "order") %!= int_ hHYP_NO_ORDER,
                 (page_index %* int_ pPAGE_SIZE) %+ 
                   (pred_ page_size_of_order_sym [page%."order"] Integer) %<= 
                     (pool %. "range_end")));
            (impl_ (
                 (page %. "order") %== int_ hHYP_NO_ORDER,
                 (page %. "refcount") %== (int_ 0))
            );
            (* list emptiness via next and prev is equivalent ("prev/next" points back at node for index i_t) *)
            eq_ (next %== self_node_pointer, prev %== self_node_pointer);
            (* list non-empty in the above sense implies refcount 0 and order != NYP_NO_ORDER *)
            (impl_ (
                 next %!= self_node_pointer,
                 and_ [(page %. "refcount") %== int_ 0;
                       (page %. "order") %!= int_ hHYP_NO_ORDER;
                   ]
               )
            );

            pred_ page_group_ok_sym [page_index; vmemmap_pointer; vmemmap; pool] Bool
          ]
      in

      (id, {loc; args; definition = Def body; return_bt = Bool} )
    in



    let init_vmemmap_page =

      let id = init_vmemmap_page_sym in
      let loc = Loc.other "internal (init_vmemmap_page)" in

      let page_index_s, page_index = IT.fresh_named Integer "page_index" in

      (* let page_pointer_s, page_pointer = IT.fresh_named Loc "page_pointer" in *)
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let pool_s, pool = IT.fresh_named (BT.Struct hyp_pool_tag) "pool" in

      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Map (Integer, BT.Struct hyp_page_tag)) "vmemmap" 
      in

      let page = map_get_ vmemmap page_index in

      let args = [
          (page_index_s, IT.bt page_index);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
          (pool_pointer_s, IT.bt pool_pointer);
          (pool_s, IT.bt pool);
        ]
      in

      let body = 
        let page_pointer = arrayShift_ (vmemmap_pointer, struct_ct hyp_page_tag, page_index) in
        let self_node_pointer = memberShift_ (page_pointer, hyp_page_tag, Id.id "node") in
        let prev = (page %. "node") %. "prev" in
        let next = (page %. "node") %. "next" in
        and_ [

            (page %. "order") %== int_ 0;
            (page %. "refcount") %== int_ 1;
            ((page %. "pool") %== pool_pointer);
            (next %== self_node_pointer);
            (prev %== self_node_pointer);
            pred_ order_aligned_sym [page_index; int_ 0] BT.Bool;
            (page_index %* int_ pPAGE_SIZE) %+ 
              (pred_ page_size_of_order_sym [page%."order"] Integer) %<= 
                (pool %. "range_end");
            (* pred_ "page_group_ok" [page_index; vmemmap_pointer; vmemmap; pool] Bool *)
          ]
      in



      (id, {loc; args; definition = Def body; return_bt = Bool} )
    in




    let vmemmap_l_wf =

      let id = vmemmap_l_wf_sym in
      let loc = Loc.other "internal (vmemmap_l_wf)" in

      let page_index_s, page_index = IT.fresh_named Integer "page_index" in

      (* let page_pointer_s, page_pointer = IT.fresh_named Loc "page_pointer" in *)
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let pool_s, pool = IT.fresh_named (BT.Struct hyp_pool_tag) "pool" in

      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Map (Integer, BT.Struct hyp_page_tag)) "vmemmap" 
      in

      let args = [
          (page_index_s, IT.bt page_index);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
          (pool_pointer_s, IT.bt pool_pointer);
          (pool_s, IT.bt pool);
        ]
      in

      let body = 
        let page_pointer = arrayShift_ (vmemmap_pointer, struct_ct hyp_page_tag, page_index) in
        let page = map_get_ vmemmap page_index in
        let self_node_pointer = memberShift_ (page_pointer, hyp_page_tag, Id.id "node") in
        let pool_free_area_pointer =
          arrayShift_
            (memberShift_ (pool_pointer, hyp_pool_tag, Id.id "free_area"),
             struct_ct list_head_tag,
             page %. "order")
        in
        let prev = (page %. "node") %. "prev" in
        let next = (page %. "node") %. "next" in
        and_ [
            or_ [
                (* either empty list (pointer to itself) *)
                prev %== self_node_pointer;
                (* or pointer to free_area cell *)
                and_ (
                    let free_area_entry = map_get_ (pool %. "free_area") (page %. "order") in
                    [prev %== pool_free_area_pointer;
                     (free_area_entry %. "next") %== self_node_pointer]
                  );
                (* or pointer to other vmemmap cell, within the same range*)
                and_ (
                    let prev_page_pointer = 
                      container_of_ (prev, hyp_page_tag, Id.id "node") in
                    let prev_page_index = 
                      vmemmap_index_of_pointer ~vmemmap_pointer prev_page_pointer in
                    let prev_page = 
                      map_get_ vmemmap prev_page_index in
                    [vmemmap_good_pointer ~vmemmap_pointer prev_page_pointer
                       (pool %. "range_start") (pool %. "range_end");
                     (((prev_page %. "node") %. "next") %== self_node_pointer);
                     ((prev_page %. "order") %== (page %. "order"))
                    ]
                  )
              ];
            or_ [
                (* either empty list (pointer to itself) *)
                next %== self_node_pointer;
                (* or pointer to free_area cell *)
                and_ (
                    let free_area_entry = map_get_ (pool %. "free_area") (page %. "order") in
                    [next %== pool_free_area_pointer;
                     (free_area_entry %. "prev") %== self_node_pointer]
                  );
                (* or pointer to other vmemmap cell, within the same range*)
                and_ (
                    let next_page_pointer = 
                      container_of_ (next, hyp_page_tag, Id.id "node") in
                    let next_page_index = 
                      vmemmap_index_of_pointer ~vmemmap_pointer next_page_pointer in
                    let next_page = 
                      map_get_ vmemmap next_page_index in
                    [vmemmap_good_pointer ~vmemmap_pointer next_page_pointer
                       (pool %. "range_start") (pool %. "range_end");
                     (((next_page %. "node") %. "prev") %== self_node_pointer);
                     ((next_page %. "order") %== (page %. "order"))
                    ]
                  )
              ]
          ]
      in

      (id, {loc; args; definition = Def body; return_bt = Bool} )
    in












    let vmemmap_b_wf =

      let id = vmemmap_b_wf_sym in
      let loc = Loc.other "internal (vmemmap_b_wf)" in

      let page_index_s, page_index = IT.fresh_named Integer "page_index" in

      (* let page_pointer_s, page_pointer = IT.fresh_named Loc "page_pointer" in *)
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let pool_s, pool = IT.fresh_named (BT.Struct hyp_pool_tag) "pool" in

      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Map (Integer, BT.Struct hyp_page_tag)) "vmemmap" 
      in

      let args = [
          (page_index_s, IT.bt page_index);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
          (pool_pointer_s, IT.bt pool_pointer);
          (pool_s, IT.bt pool);
        ]
      in

      let body = 
        and_ [
            pred_ vmemmap_wf_sym [page_index; vmemmap_pointer; vmemmap; pool_pointer; pool] BT.Bool;
            pred_ vmemmap_l_wf_sym [page_index; vmemmap_pointer; vmemmap; pool_pointer; pool] BT.Bool;
          ]
      in

      (id, {loc; args; definition = Def body; return_bt = Bool} )
    in







    (* check: possibly inconsistent *)
    let free_area_cell_wf =

      let id = freeArea_cell_wf_sym in
      let loc = Loc.other "internal (freeArea_cell_wf)" in

      let cell_index_s, cell_index = IT.fresh_named Integer "cell_index" in
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let vmemmap_s, vmemmap = 
        IT.fresh_named (BT.Map (Integer, BT.Struct hyp_page_tag)) "vmemmap" in
      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let pool_s, pool = IT.fresh_named (Struct hyp_pool_tag) "pool" in

      let args = [
          (cell_index_s, IT.bt cell_index);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (vmemmap_s, IT.bt vmemmap);
          (pool_pointer_s, IT.bt pool_pointer);
          (pool_s, IT.bt pool);
        ]
      in

      let body = 
        let cell = (map_get_ (pool %. "free_area") cell_index) in
        let order = cell_index in
        let free_area_pointer = memberShift_ (pool_pointer, hyp_pool_tag, Id.id "free_area") in
        let cell_pointer = arrayShift_ (free_area_pointer, struct_ct list_head_tag, cell_index) in

        let prev = cell %. "prev" in
        let next = cell %. "next" in
        and_ [
            (prev %== cell_pointer) %== (next %== cell_pointer);
            or_ [prev %== cell_pointer;
                 and_ begin
                     let prev_vmemmap = container_of_ (prev, hyp_page_tag, Id.id "node") in
                     let next_vmemmap = container_of_ (next, hyp_page_tag, Id.id "node") in
                     let prev_index = vmemmap_index_of_pointer ~vmemmap_pointer prev_vmemmap in
                     let next_index = vmemmap_index_of_pointer ~vmemmap_pointer next_vmemmap in
                     let prev_page = (map_get_ vmemmap prev_index) in
                     let next_page = (map_get_ vmemmap next_index) in
                     [(*prev*)
                       vmemmap_good_pointer ~vmemmap_pointer prev_vmemmap (pool %. "range_start") (pool %. "range_end");
                       (prev_page %. "order") %== order;
                       (prev_page %. "refcount") %== (int_ 0);
                       ((prev_page %. "node") %. "next") %== cell_pointer;
                       (*next*)
                       vmemmap_good_pointer ~vmemmap_pointer next_vmemmap (pool %. "range_start") (pool %. "range_end");
                       (next_page %. "order") %== order;
                       (next_page %. "refcount") %== (int_ 0);
                       ((next_page %. "node") %. "prev") %== cell_pointer;
                     ]
                   end
              ];
          ]
      in

      (id, {loc; args; definition = Def body; return_bt = Bool} )
    in






    let hyp_pool_wf =
      let id = hyp_pool_wf_sym in
      let loc = Loc.other "internal (hyp_pool_wf)" in

      let pool_pointer_s, pool_pointer = IT.fresh_named Loc "pool_pointer" in
      let pool_s, pool = IT.fresh_named (Struct hyp_pool_tag) "pool" in
      let vmemmap_pointer_s, vmemmap_pointer = IT.fresh_named Loc "vmemmap_pointer" in
      let hyp_physvirt_offset_s, hyp_physvirt_offset = 
        IT.fresh_named BT.Integer "hyp_physvirt_offset" in

      let args = [
          (pool_pointer_s, IT.bt pool_pointer);
          (pool_s, IT.bt pool);
          (vmemmap_pointer_s, IT.bt vmemmap_pointer);
          (hyp_physvirt_offset_s, IT.bt hyp_physvirt_offset);
        ]
      in

      let body = 
        let range_start = pool %. "range_start" in
        let range_end = pool %. "range_end" in
        let max_order = pool %. "max_order" in
        let beyond_range_end_cell_pointer =
          (arrayShift_ 
             (vmemmap_pointer, struct_ct hyp_page_tag,
              range_end %/ (int_ pPAGE_SIZE))) in
        (* (for the final disjointness condition) the vmemamp can be
           bigger than just the part managed by this allocator *)
        let start_i = (pool %. "range_start") %/ (int_ pPAGE_SIZE) in
        let end_i = (pool %. "range_end") %/ (int_ pPAGE_SIZE) in
        let vmemmap_start_pointer =
          arrayShift_ (vmemmap_pointer, struct_ct hyp_page_tag, start_i) in
        (* end_i is the first index outside the vmemmap *)
        let vmemmap_length =
          (end_i %- start_i) %* 
            (int_ (Memory.size_of_struct hyp_page_tag)) in
        and_ [
            (* metadata well formedness *)
            good_ (pointer_ct void_ct, integerToPointerCast_ range_start);
            good_ (pointer_ct void_ct, integerToPointerCast_ range_end);
            (* TODO: the following three have to go *)
            good_ (pointer_ct void_ct, integerToPointerCast_ (range_start %- hyp_physvirt_offset));
            good_ (pointer_ct void_ct, integerToPointerCast_ (range_end %- hyp_physvirt_offset));
            good_ (pointer_ct void_ct, integerToPointerCast_ (pointerToIntegerCast_ (null_) %+ hyp_physvirt_offset));
            range_start %< range_end;
            divisible_ (range_start, int_ pPAGE_SIZE);
            divisible_ (range_end, int_ pPAGE_SIZE);
            (* for hyp_page_to_phys conversion *)
            representable_ (integer_ct Ptrdiff_t, range_end);
            good_ (pointer_ct void_ct, beyond_range_end_cell_pointer);
            max_order %>= int_ 0;
            max_order %<= int_ mMAX_ORDER;
            (* vmemmap pointer aligned *)
            aligned_ (vmemmap_pointer,
                      array_ct (struct_ct hyp_page_tag) None);
            (* hyp pool vmemmap disjoint *)
            IT.disjoint_ 
              (pool_pointer, int_ (Memory.size_of_struct hyp_pool_tag))
              (vmemmap_start_pointer, vmemmap_length);
            IT.disjoint_int_ 
              (hyp_physvirt_offset, int_ 1)
              (range_start, range_end);
            IT.disjoint_int_ 
              (hyp_physvirt_offset %+ z_ (Z.of_string "18446744073709551616"), int_ 1)
              (range_start, range_end);
          ] 
      in

      (id, { loc; args; return_bt = Bool; definition = Def body})
      
    in



    [order_aligned;
     order_align;
     page_size_of_order;
     page_group_ok;
     vmemmap_wf;
     init_vmemmap_page;
     vmemmap_l_wf;
     vmemmap_b_wf;
     free_area_cell_wf;
     hyp_pool_wf;
     pfn_buddy;
     buddy;
    ]








end


let predicate_list struct_decls = 
  (
  try PageAlloc.predicates struct_decls with
  | Struct_not_found -> []
  ) @
  [exp_fun]


    
