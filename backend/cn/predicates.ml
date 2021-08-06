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

type clause = Loc.t * AT.packing_ft

let pp_clause c = AT.pp OutputDef.pp c

let subst_it_clause subst c = AT.subst_it OutputDef.subst_it subst c
let subst_var_clause subst c = AT.subst_var OutputDef.subst_var subst c

let subst_its_clause substs = 
  Subst.make_substs subst_it_clause substs

let subst_vars_clause substs = 
  Subst.make_substs subst_var_clause substs



type predicate_definition = {
    loc : Loc.t;
    pointer: Sym.t;
    iargs : (Sym.t * LS.t) list;
    oargs : (string * LS.t) list;
    clauses : clause list;
  }
  
let pp_predicate_definition def = 
  item "pointer" (Sym.pp def.pointer) ^/^
  item "iargs" (Pp.list (fun (s,_) -> Sym.pp s) def.iargs) ^/^
  item "oargs" (Pp.list (fun (s,_) -> Pp.string s) def.oargs) ^/^
  item "clauses" (Pp.list (fun (_, clause) -> pp_clause clause) def.clauses)
  



(* let rec init_bt (Sctype (_, ct_)) =
 *   match ct_ with
 *   | Array (t, _) -> BT.Param (Integer, init_bt t)
 *   | t -> Bool *)




type ctype_predicate =
  { pointer_iarg : Sym.t;
    value_oarg : string * IT.t;
    init_oarg : string * IT.t;
    lrt: LRT.t;
  }


let ctype_predicate_to_predicate ct pred = 
  let loc = Loc.other "internal (Ctype)" in
  let clause = AT.of_lrt pred.lrt (AT.I [pred.value_oarg; pred.init_oarg]) in
  let def = {
      loc = loc;
      pointer = pred.pointer_iarg; 
      iargs = []; 
      oargs = [(fst pred.value_oarg, IT.bt (snd pred.value_oarg));
               (fst pred.init_oarg, IT.bt (snd pred.init_oarg))];
      clauses = [(loc, clause)]
    }
  in
  def






let ctype_predicate struct_layouts ct = 
  let open ReturnTypes in
  let open LRT in
  let open Memory in
  let open Resources in
  let open Option in
  let open Sctypes in
  let pointer_s, pointer_t = IT.fresh_named BT.Loc "?pointer" in
  let init_s, init_t = IT.fresh_named BT.Bool "?init" in
  let v_s, v_t = IT.fresh_named (BT.of_sct ct) "?value" in
  let size = size_of_ctype ct in
  let (Sctypes.Sctype (_, ct_)) = ct in
  let@ lrt, value_def = match ct_ with
  | Void ->
     Debug_ocaml.error "ctype_predicate void"
  | Integer it ->
     let lrt = 
       Logical ((v_s, IT.bt v_t), 
       Logical ((init_s, IT.bt init_t), 
       Resource (point (pointer_t, size) (q_ (1,1)) v_t init_t, LRT.I)))
     in
     return (lrt, v_t)
  | Pointer (_, ct') ->
     let lrt = 
       Logical ((v_s, IT.bt v_t), 
       Logical ((init_s, IT.bt init_t), 
       Resource (point (pointer_t, size) (q_ (1,1)) v_t init_t, LRT.I)))
     in
     return (lrt, v_t)
  | Array (t, None) ->
     (* todo: connect with user-annotation *)
     Debug_ocaml.error "representation: array of unknown length"
  | Array (ct', Some length) ->
     let i_s, i_t = IT.fresh_named BT.Integer "?i" in
     let qpredicate = {
         pointer = pointer_t; 
         element_size = z_ (size_of_ctype ct'); 
         istart = int_ 0;
         iend = int_ length;
         moved = []; 
         unused = true;
         name = Ctype ct';
         i = i_s;
         iargs = [];
         oargs = [app_ v_t i_t; init_t];
       }
     in
     let lrt = 
       Logical ((v_s, IT.bt v_t), 
       Logical ((init_s, IT.bt init_t), 
       Resource (QPredicate qpredicate, LRT.I)))
     in
     return (lrt, v_t)
  | Struct tag ->
     let@ layout = struct_layouts tag in
     let (lrt, values) = 
       List.fold_right (fun {offset; size; member_or_padding} (lrt, values) ->
           let member_p = addPointer_ (pointer_t, z_ offset) in
           match member_or_padding with
           | Some (member, sct) ->
              let member_s, member_t = IT.fresh_named (BT.of_sct sct) "?member" in
              let resource = predicate (Ctype sct) member_p [] [member_t; init_t] in
              let lrt = 
                LRT.Logical ((member_s, IT.bt member_t),
                LRT.Resource (resource, lrt))
              in
              let values = (member, member_t) :: values in
              (lrt, values)
           | None ->
              let padding_s, padding_t = IT.fresh_named BT.Integer "?padding" in
              let resource = point (member_p, size) (q_ (1,1)) padding_t (bool_ false) in
              let lrt = 
                LRT.Logical ((padding_s, IT.bt padding_t),
                LRT.Resource (resource, lrt)) 
              in
              (lrt, values)
         ) layout (LRT.I, [])
     in
     let value_t = IT.struct_ (tag, values) in
     let lrt = 
       Logical ((init_s, IT.bt init_t), lrt) @@ LRT.I
     in
    return (lrt, value_t)
  | Function _ -> 
     Debug_ocaml.error "todo: function ctype predicate"
  in
  let def = { 
      pointer_iarg = pointer_s; 
      value_oarg = ("value", value_def); 
      init_oarg = ("init", init_t);
      lrt; 
    }
  in
  return def









let char_ct = Sctypes.Sctype ([], Integer Char)


let region = 
  let id = "Region" in
  let loc = Loc.other "internal (Region)" in
  let pointer_s, pointer_t = IT.fresh_named Loc "?pointer" in
  let length_s, length_t = IT.fresh_named Integer "?length" in
  let v_s, v_t = IT.fresh_named (BT.Array (Loc, Integer)) "?value" in
  let init_s, init_t = IT.fresh_named (BT.Array (Loc, Bool)) "?init" in
  let p_s, p_t = IT.fresh_named Loc "?p" in
  let qpoint = {
      qpointer = p_s;
      size = Z.of_int 1; 
      permission = 
        ite_ (
            and_ [lePointer_ (pointer_t, p_t); 
                  ltPointer_ (p_t, addPointer_ (pointer_t, length_t));], 
            q_ (1, 1), 
            q_ (0, 1)
          );
      value = app_ v_t p_t;
      init = app_ init_t p_t;
    }
  in
  let lrt =
    LRT.Logical ((v_s, IT.bt v_t),
    LRT.Logical ((init_s, IT.bt init_t),
    LRT.Resource (QPoint qpoint, 
    LRT.Constraint (t_ (IT.good_pointer pointer_t char_ct),
    LRT.I))))
  in
  let clause = AT.of_lrt lrt (AT.I [("value",v_t); ("init", init_t)]) in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t)]; 
      oargs = [("value", IT.bt v_t); ("init", IT.bt init_t)]; 
      clauses = [(loc, clause)]; 
    } 
  in
  (id, predicate)




let part_zero_region = 
  let id = "PartZeroRegion" in
  let loc = Loc.other "internal (PartZeroRegion)" in
  let pointer_s, pointer_t = IT.fresh_named Loc "?pointer" in
  let length_s, length_t = IT.fresh_named Integer "?length" in
  let v_s, v_t = IT.fresh_named (BT.Array (Loc, Integer)) "?v" in
  let init_s, init_t = IT.fresh_named (BT.Array (Loc, Bool)) "?init" in
  let up_to_s, up_to_t = IT.fresh_named Loc "?up_to" in
  let p_s, p_t = IT.fresh_named Loc "?p" in
  let region = {
      name = Id "Region";
      pointer = pointer_t; 
      unused = true;
      iargs = [length_t];
      oargs = [v_t; init_t];
    }
  in
  let v_constr = 
    forall_ (p_s, IT.bt p_t) 
      (Some (T_App (T_Term v_t, T_Term p_t)))
      (impl_ (and_ [lePointer_ (pointer_t, p_t); 
                   ltPointer_ (p_t, up_to_t)],
              and_ [eq_ (app_ v_t p_t, int_ 0)]))
  in
  let init_constr = 
    forall_ (p_s, IT.bt p_t)
      (Some (T_App (T_Term init_t, T_Term p_t)))
      (impl_ (and_ [lePointer_ (pointer_t, p_t); 
                    ltPointer_ (p_t, up_to_t)],
              and_ [app_ init_t p_t]))
  in
  let lrt =
    LRT.Logical ((v_s, IT.bt v_t),
    LRT.Logical ((init_s, IT.bt init_t),
    LRT.Resource (Predicate region, 
    LRT.Constraint (v_constr,
    LRT.Constraint (init_constr,
    LRT.I)))))
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t); (up_to_s, IT.bt up_to_t)];
      oargs = [];
      clauses = [(loc, AT.of_lrt lrt (AT.I []))]; 
    } 
  in
  (id, predicate)




let zero_region = 
  let id = "ZeroRegion" in
  let loc = Loc.other "internal (ZeroRegion)" in
  let pointer_s, pointer_t = IT.fresh_named Loc "?pointer" in
  let length_s, length_t = IT.fresh_named Integer "?length" in
  let lrt = 
    let p = {
        name = Id "PartZeroRegion";
        pointer = pointer_t; 
        unused = true;
        iargs = [length_t; addPointer_ (pointer_t, length_t)];
        oargs = [];
      }
    in
    LRT.Resource (Predicate p, LRT.I) 
  in
  let predicate = {
      loc = loc;
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t)];
      oargs = [];
      clauses = [(loc, AT.of_lrt lrt (AT.I []))]; 
    } 
  in
  (id, predicate)



let early = 
  let id = "EarlyAlloc" in
  let loc = Loc.other "internal (EarlyAlloc)" in
  let start_s, start_t = IT.fresh_named Loc "?start" in
  let end_s, end_t = IT.fresh_named Loc "?end" in
  let length_t = 
    add_ (sub_ (pointerToIntegerCast_ end_t,
                pointerToIntegerCast_ start_t), 
          int_ 1)
  in
  let v_s, v_t = IT.fresh_named (BT.Array (Loc, Integer)) "?v" in
  let init_s, init_t = IT.fresh_named (BT.Array (Loc, Bool)) "?init" in
  let region = {
      name = Id "Region";
      pointer = start_t; 
      unused = true;
      iargs = [length_t];
      oargs = [v_t; init_t];
    }
  in
  let lrt =
    LRT.Logical ((v_s, IT.bt v_t),
    LRT.Logical ((init_s, IT.bt init_t),
    LRT.Resource (Predicate region, 
    LRT.Constraint (t_ (IT.good_pointer start_t char_ct),
    LRT.Constraint (t_ (IT.good_pointer end_t char_ct),
    LRT.I)))))
  in
  let predicate = {
      loc = loc;
      pointer = start_s;
      iargs = [(end_s, IT.bt end_t)]; 
      oargs = []; 
      clauses = [(loc, AT.of_lrt lrt (AT.I []))]; 
    } 
  in
  (id, predicate)






let page_alloc_predicates struct_decls = 

  let pPAGE_SHIFT = 12 in
  let mMAX_ORDER = 11 in
  let _hHYP_NO_ORDER = 0 - 1 in

  let find_tag tag = 
    SymMap.find_first (fun tag' ->
        Option.equal String.equal (Sym.name tag') (Some tag)
      ) struct_decls
  in

  let list_head_tag, _ = find_tag "list_head" in
  let hyp_pool_tag, _ = find_tag "hyp_pool" in
  let hyp_page_tag, _ = find_tag "hyp_page" in

  let (%.) t member = IT.(%.) struct_decls t (Id.id member) in



  let vmemmap_cell_address hyp_vmemmap_t i_t =
    arrayShift_ (hyp_vmemmap_t, 
                 Sctype ([], Struct hyp_page_tag), 
                 i_t)
  in

  let _vmemmap_cell_node_address hyp_vmemmap_t i_t =
    memberShift_ (vmemmap_cell_address hyp_vmemmap_t i_t,
                  hyp_page_tag,
                  Id.id "node")
  in


  let vmemmap_offset_of_node_pointer hyp_vmemmap_t pointer = 
    (pointerToIntegerCast_
       (container_of_ (pointer, hyp_page_tag, Id.id "node"))) %-
      pointerToIntegerCast_ hyp_vmemmap_t
  in
  
  let vmemmap_good_node_pointer hyp_vmemmap_t pointer = 
    alignedI_ 
      ~t:(integerToPointerCast_ (vmemmap_offset_of_node_pointer hyp_vmemmap_t pointer))
      ~align:(z_ (Memory.size_of_struct hyp_page_tag))
  in
  
  let _vmemmap_node_pointer_to_index hyp_vmemmap_t pointer = 
    vmemmap_offset_of_node_pointer hyp_vmemmap_t pointer %/
      z_ (Memory.size_of_struct hyp_page_tag)
  in




  (* let free_area_cell = 
   * 
   *   let id = "Free_area_cell" in
   *   let loc = Loc.other "internal (Free_area_cell)" in
   *   
   *   let vmemmap_pointer_s, vmemmap_pointer_t = IT.fresh_named Loc "?vmemmap_pointer" in
   *   let vmemmap_s, vmemmap_t = IT.fresh_named (BT.Array (Integer, Struct hyp_page_tag)) "?vmemmap" in
   *   let range_start_s, range_start_t = IT.fresh_named Integer "?range_start" in
   *   let range_end_s, range_end_t = IT.fresh_named Integer "?range_end" in
   *   let order_s, order_t = IT.fresh_named Integer "?order" in
   * 
   *   let cell_pointer_s, cell_pointer_t = IT.fresh_named Loc "?cell_pointer" in
   *   let cell_s, cell_t = IT.fresh_named (BT.Struct list_head_tag) "?cell" in
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



  let vmemmap_page =

    let id = "Vmemmap_page" in
    let loc = Loc.other "internal (Vmemmap_page)" in
    let pool_pointer_s, pool_pointer_t = IT.fresh_named Loc "?pool_pointer" in
    let page_pointer_s, page_pointer_t = IT.fresh_named Loc "?page_pointer" in
    let range_start_s, range_start_t = IT.fresh_named Integer "?range_start" in
    let range_end_s, range_end_t = IT.fresh_named Integer "?range_end" in
    let page_s, page_t = IT.fresh_named (BT.Struct hyp_page_tag) "?page" in
    let vmemmap_pointer_s, vmemmap_pointer_t = IT.fresh_named Loc "?vmemmap_pointer" in

    let resource = 
      Predicate {
          pointer = page_pointer_t;
          name = Ctype (Sctypes.Sctype ([], Struct hyp_page_tag));
          iargs = [];
          oargs = [page_t; bool_ true];
          unused = true;
        }
    in

    let wellformedness = 
      let self_node_pointer_t = memberShift_ (page_pointer_t, hyp_page_tag, Id.id "node" )in
      let _prev_next_well_formed prev_next = 
        let prev_next_t = (page_t %. "node") %.prev_next in
        or_ [
            (* either empty list (pointer to itself) *)
            prev_next_t %== self_node_pointer_t;
            (* or pointer to free_area cell *)
            prev_next_t %==
              arrayShift_
                (memberShift_ (pool_pointer_t, hyp_pool_tag, Id.id "free_area"),
                 Sctype ([], Struct list_head_tag),
                 page_t %. "order");
            (* or pointer to other vmemmap cell, within the same range*)
            and_ (
                vmemmap_good_node_pointer vmemmap_pointer_t prev_next_t :: 
                let cell_pointer_t = 
                  container_of_ (prev_next_t, hyp_page_tag, Id.id "node") in
              [ range_start_t %<= (pointerToIntegerCast_ cell_pointer_t);
                (pointerToIntegerCast_ cell_pointer_t) %< range_end_t ]
              );              
          ]
      in

      let constrs = [
          (* representable *)
          (representable_ (Sctype ([], Struct hyp_page_tag), page_t));
          (* refcount is natural number *)
          ((page_t %. "refcount") %>= int_ 0);
          (* refcount is also valid signed int: for hyp_page_count *)
          ((representable_ (Sctype ([], Integer (Signed Int_)), page_t %. "refcount")));
          (* order is HYP_NO_ORDER or between 0 and MAX_ORDER *)
          (* (let order = page_t %. "order" in
           *  or_ [order %== int_ hHYP_NO_ORDER; 
           *       and_ [int_ 0 %<= order; order %<= int_ mMAX_ORDER]]);              
           * (\* points back to the pool *\)
           * ((page_t %. "pool") %== pool_pointer_t);              
           * (\* list emptiness via next and prev is equivalent ("prev/next" points back at node for index i_t) *\)
           * eq_ (((page_t %. "node") %. "next") %== self_node_pointer_t,
           *      ((page_t %. "node") %. "prev") %== self_node_pointer_t);
           * (\* list empty in the above sense if and only if refcount 0 and order != NYP_NO_ORDER *\)
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
      List.map t_ constrs
    in

    let clause = 
      AT.of_lrt (
        LRT.Logical ((page_s, IT.bt page_t),
        LRT.Resource (resource, 
        LRT.mConstraints wellformedness
        LRT.I)))
        (AT.I [("page", page_t)])
    in

    let predicate = 
      {
        loc = loc;
        pointer = page_pointer_s;
        iargs = [
            (vmemmap_pointer_s, IT.bt vmemmap_pointer_t);
            (pool_pointer_s, IT.bt pool_pointer_t);
            (range_start_s, IT.bt range_start_t);
            (range_end_s, IT.bt range_end_t);
          ];
        oargs = [("page", IT.bt page_t)];
        clauses = [(loc, clause)]; 
      } 
    in
    (id, predicate)
  in




  let hyp_pool =

    let id = "Hyp_pool" in
    let loc = Loc.other "internal (Hyp_pool)" in

    let pool_pointer_s, pool_pointer_t = IT.fresh_named Loc "?pool_pointer" in
    let pool_s, pool_t = IT.fresh_named (BT.Struct hyp_pool_tag) "?pool" in

    let hyp_pool_metadata_owned =
      let predicate : RE.predicate = {
          name = Ctype (Sctype ([], Struct hyp_pool_tag));
          pointer = pool_pointer_t;
          iargs = [];
          oargs = [pool_t; bool_ true];
          unused = true;
        }
      in
      let pointer_good = 
        let beyond_end_of_pool_struct = 
          addPointer_ (pool_pointer_t, 
                       z_ (Memory.size_of_struct hyp_pool_tag))
        in
        representable_ (pointer_sct (Sctype ([], Void)),
                        beyond_end_of_pool_struct)
      in

      LRT.Logical ((pool_s, IT.bt pool_t), 
      LRT.Constraint (T pointer_good,
      LRT.Resource (Predicate predicate,
      LRT.I)))
    in

    let vmemmap_pointer_s, vmemmap_pointer_t = IT.fresh_named Loc "?vmemmap_pointer" in
    (* let pool_s, pool_t = IT.fresh_named (BT.Struct hyp_pool_tag) "?pool" in *)
    let vmemmap_s, vmemmap_t = 
      IT.fresh_named (BT.Array (Integer, BT.Struct hyp_page_tag)) "?vmemmap" in
    let range_start_t = pool_t %. "range_start" in
    let range_end_t = pool_t %. "range_end" in
    let max_order_t = pool_t %. "max_order" in
    let free_area_t = pool_t %. "free_area" in
    let pPAGE_SIZE_t = exp_ (int_ 2, int_ pPAGE_SHIFT) in
    let start_t = range_start_t %/ pPAGE_SIZE_t in
    let end_t = range_end_t %/ pPAGE_SIZE_t in

    let metadata_well_formedness =
      let constrs = [
          int_ 0 %<= range_start_t;
          range_start_t %< range_end_t;
          range_end_t %< exp_ (int_ 2, int_ 64);
          rem_ (range_start_t, pPAGE_SIZE_t) %== int_ 0;
          rem_ (range_end_t, pPAGE_SIZE_t) %== int_ 0;
          ((pointerToIntegerCast_ vmemmap_pointer_t) %+ ((end_t %* z_ (Memory.size_of_struct hyp_page_tag)))) %< exp_ (int_ 2, int_ 64);
          max_order_t %> int_ 0;
          max_order_t %<= int_ mMAX_ORDER;
        ]
      in
      LRT.mConstraints (List.map t_ constrs) LRT.I
    in

    let vmemmap_metadata_owned =
      let element_size = Memory.size_of_struct hyp_page_tag in
      let i_s, i_t = IT.fresh_named Integer "?i" in
      let vmemmap_array = 
        QPredicate {
            pointer = vmemmap_pointer_t;
            element_size = z_ element_size;
            istart = start_t;
            iend = end_t;
            name = Id "Vmemmap_page";
            i = i_s;
            iargs = [
                vmemmap_pointer_t;
                pool_pointer_t;
                range_start_t;
                range_end_t;
              ];
            oargs = [app_ vmemmap_t i_t];
            moved = [];
            unused = true;
          }
      in
      let aligned = 
        aligned_ (vmemmap_pointer_t,
                  Sctype ([], Array (Sctype ([], Struct hyp_page_tag), None)))
      in

      LRT.Logical ((vmemmap_s, IT.bt vmemmap_t),
      LRT.Resource (vmemmap_array, 
      LRT.Constraint (t_ aligned,
      LRT.I)))
    in

    let free_area_well_formedness = 
      let constr prev_next = 
        let o_s, o_t = IT.fresh_named Integer "?o" in
        let prev_next_t = (free_area_t %@ o_t) %. prev_next in
        let cell_pointer_t = 
          arrayShift_ (memberShift_ (pool_pointer_t, hyp_pool_tag, Id.id "free_area"),
                       Sctype ([], Struct hyp_pool_tag),
                       o_t) 
        in
        forall_ (o_s, IT.bt o_t) 
          (Some (T_Member (T_App (T_Term free_area_t, T_Term o_t), Id.id prev_next)))
          begin
            and_ [
                good_pointer prev_next_t (Sctype ([], Struct list_head_tag));
                or_ [
                    prev_next_t %== cell_pointer_t;
                    and_ (
                        vmemmap_good_node_pointer vmemmap_pointer_t prev_next_t :: []
                      (* (let i_t = vmemmap_node_pointer_to_index vmemmap_pointer_t prev_next_t in
                       *  [range_start_t %<= i_t; i_t %< range_end_t;
                       *   ((vmemmap_t %@ i_t) %. "order") %== o_t;
                       *   ((vmemmap_t %@ i_t) %. "refcount") %== int_ 0] *)
                      )
                  ]
              ]
          end
      in
      LRT.Constraint (constr "prev",
      LRT.Constraint (constr "next",
      LRT.I))
    in

    let vmemmap_well_formedness2 = 
      let constr prev_next =
        (* let i_s, i_t = IT.fresh_named Integer "?i" in *)
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
      LRT.Constraint (constr "prev",
      LRT.Constraint (constr "next",
      LRT.I))
    in

    (* let page_group_ownership = 
     *   let qp_s, qp_t = IT.fresh_named Loc "?qp" in
     *   let bytes_s, bytes_t = IT.fresh_named (BT.Array (Loc, Integer)) "?bytes" in
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
     *         value = app_ bytes_t qp_t;
     *         init = bool_ false;
     *       }
     *   in
     *   LRT.Logical ((bytes_s, IT.bt bytes_t),
     *   LRT.Resource (qpoint, LRT.I))
     * in *)

    let lrt = 
      let open LRT in
      hyp_pool_metadata_owned 
      @@ metadata_well_formedness
      @@ vmemmap_metadata_owned
      @@ free_area_well_formedness (* possibly inconsistent *)
      @@ vmemmap_well_formedness2
      (* @@ Tools.skip (LRT.I) page_group_ownership *)
    in

    let predicate = 
      {
        loc = loc;
        pointer = 
          pool_pointer_s;
        iargs = [
            (vmemmap_pointer_s, IT.bt vmemmap_pointer_t);
          ];
        oargs = [
            ("pool", IT.bt pool_t);
            ("vmemmap", IT.bt vmemmap_t);
          ];
        clauses = 
          [(loc, AT.of_lrt lrt 
                   (AT.I [("pool", pool_t);
                          ("vmemmap", vmemmap_t)]));]; 
      } 
    in
    (id, predicate)


  in
  [vmemmap_page;
   hyp_pool]



let predicate_list struct_decls = 
  region ::
  part_zero_region ::
  zero_region ::
  early ::
  (* for now: *)
  try page_alloc_predicates struct_decls with
  | Not_found -> []


    
