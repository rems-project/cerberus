open Sctypes
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RE = Resources.RE
module PackingFT = ArgumentTypes.Make(OutputDef)
module StringMap = Map.Make(String)
module Loc = Locations
open Pp


open Resources.RE
open BT
open IT

type clause = PackingFT.t

let pp_clause c = PackingFT.pp c

let subst_it_clause subst c = PackingFT.subst_it subst c
let subst_var_clause subst c = PackingFT.subst_var subst c

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
  item "clauses" (Pp.list pp_clause def.clauses)
  



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
  let clause = 
    PackingFT.of_lrt pred.lrt 
      (PackingFT.I [pred.value_oarg; pred.init_oarg]) in
  let def = {
      loc = Loc.other "internal (Ctype)";
      pointer = pred.pointer_iarg; 
      iargs = []; 
      oargs = [(fst pred.value_oarg, IT.bt (snd pred.value_oarg));
               (fst pred.init_oarg, IT.bt (snd pred.init_oarg))];
      clauses = [clause]
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
         length = int_ length;
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
  let pointer_s, pointer_t = IT.fresh_named Loc "?pointer" in
  let length_s, length_t = IT.fresh_named Integer "?length" in
  let v_s, v_t = IT.fresh_named (BT.Param (Integer, Integer)) "?value" in
  let init_s, init_t = IT.fresh_named (BT.Param (Integer, Bool)) "?init" in
  let i_s, i_t = IT.fresh_named Integer "?i" in
  let qpredicate = {
      name = Ctype char_ct;
      element_size = int_ 1; 
      pointer = pointer_t; 
      length = length_t;
      moved = []; 
      unused = true;
      i = i_s;
      iargs = [];
      oargs = [app_ v_t i_t; app_ init_t i_t];
    }
  in
  let lrt =
    LRT.Logical ((v_s, IT.bt v_t),
    LRT.Logical ((init_s, IT.bt init_t),
    LRT.Resource (QPredicate qpredicate, 
    LRT.Constraint (IT.good_pointer pointer_t char_ct,
    LRT.I))))
  in
  let predicate = {
      loc = Loc.other "internal (Region)";
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t)]; 
      oargs = [("value", IT.bt v_t); ("init", IT.bt init_t)]; 
      clauses = [PackingFT.of_lrt lrt 
                   (PackingFT.I [("value",v_t); ("init", init_t)])]; 
    } 
  in
  (id, predicate)




let part_zero_region = 
  let id = "PartZeroRegion" in
  let pointer_s, pointer_t = IT.fresh_named Loc "?pointer" in
  let length_s, length_t = IT.fresh_named Integer "?length" in
  let v_s, v_t = IT.fresh_named (BT.Param (Integer, Integer)) "?v" in
  let init_s, init_t = IT.fresh_named (BT.Param (Integer, Bool)) "?init" in
  let j_s, j_t = IT.fresh_named Integer "?j" in
  let i_s, i_t = IT.fresh_named Integer "?i" in
  let region = {
      name = Id "Region";
      pointer = pointer_t; 
      unused = true;
      iargs = [length_t];
      oargs = [v_t; init_t];
    }
  in
  let v_constr = 
    forall_sth_ (i_s, IT.bt i_t) 
      (and_ [le_ (int_ 0, i_t); lt_ (i_t, j_t)])
      (and_ [eq_ (app_ v_t i_t, int_ 0)])
  in
  let init_constr = 
    forall_sth_ (i_s, IT.bt i_t)
      (and_ [le_ (int_ 0, i_t); lt_ (i_t, j_t)])
      (and_ [app_ init_t i_t])
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
      loc = Loc.other "internal (PartZeroRegion)";
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t); (j_s, IT.bt j_t)];
      oargs = [];
      clauses = [PackingFT.of_lrt lrt (PackingFT.I [])]; 
    } 
  in
  (id, predicate)




let zero_region = 
  let id = "ZeroRegion" in
  let pointer_s, pointer_t = IT.fresh_named Loc "?pointer" in
  let length_s, length_t = IT.fresh_named Integer "?length" in
  let lrt = 
    let p = {
        name = Id "PartZeroRegion";
        pointer = pointer_t; 
        unused = true;
        iargs = [length_t; length_t];
        oargs = [];
      }
    in
    LRT.Resource (Predicate p, LRT.I) 
  in
  let predicate = {
      loc = Loc.other "internal (ZeroRegion)";
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t)];
      oargs = [];
      clauses = [PackingFT.of_lrt lrt (PackingFT.I [])]; 
    } 
  in
  (id, predicate)



let early = 
  let id = "EarlyAlloc" in
  let start_s, start_t = IT.fresh_named Loc "?start" in
  let end_s, end_t = IT.fresh_named Loc "?end" in
  let length_t = 
    add_ (sub_ (pointerToIntegerCast_ end_t,
                pointerToIntegerCast_ start_t), 
          int_ 1)
  in
  let v_s, v_t = IT.fresh_named (BT.Param (Integer, Integer)) "?v" in
  let init_s, init_t = IT.fresh_named (BT.Param (Integer, Bool)) "?init" in
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
    LRT.Constraint (IT.good_pointer start_t char_ct,
    LRT.Constraint (IT.good_pointer end_t char_ct,
    LRT.I)))))
  in
  let predicate = {
      loc = Loc.other "internal (EarlyAlloc)";
      pointer = start_s;
      iargs = [(end_s, IT.bt end_t)]; 
      oargs = []; 
      clauses = [PackingFT.of_lrt lrt (PackingFT.I [])]; 
    } 
  in
  (id, predicate)



let hyp_pool (struct_decls : Memory.struct_decls) =


  let list_head_tag, _ = 
    SymMap.find_first (fun tag ->
        Option.equal String.equal (Sym.name tag) (Some "list_head")
      ) struct_decls
  in

  let hyp_pool_tag, _ = 
    SymMap.find_first (fun tag ->
        Option.equal String.equal (Sym.name tag) (Some "hyp_pool")
      ) struct_decls
  in

  let hyp_page_tag, _ = 
    SymMap.find_first (fun tag ->
        Option.equal String.equal (Sym.name tag) (Some "hyp_page")
      ) struct_decls
  in

  let id = "Hyp_pool" in
  let p_s, p_t = IT.fresh_named Loc "?p" in
  let hyp_vmemmap_s, hyp_vmemmap_t = IT.fresh_named Loc "?hyp_vmemmap" in
  let pPAGE_SHIFT_s, pPAGE_SHIFT_t = IT.fresh_named Integer "?PAGE_SHIFT" in
  let mMAX_ORDER_s, mMAX_ORDER_t = IT.fresh_named Integer "?MAX_ORDER" in
  let hHYP_NO_ORDER_s, hHYP_NO_ORDER_t = IT.fresh_named Integer "?HYP_NO_ORDER" in
  let pool_s, pool_t = IT.fresh_named (BT.Struct hyp_pool_tag) "?pool" in
  let poolmap_s, poolmap_t = 
    IT.fresh_named (BT.Param (Integer, BT.Struct hyp_page_tag)) "?poolmap" in
  let poolmap_i_s, poolmap_i_t = 
    IT.fresh_named (BT.Param (Integer, Bool)) "?poolmap_i" in

  
  let (%.) t member = 
    let tag = match IT.bt t with
      | Struct tag -> tag
      | _ -> Debug_ocaml.error "illtyped index term. not a struct"
    in
    let member = Id.id member in
    let member_bt = 
      BT.of_sct
        (List.assoc Id.equal member 
           (Memory.member_types (SymMap.find tag struct_decls)))
    in
    member_ ~member_bt (tag, t, member)
  in


  let hyp_vmemmap_offset_of_node_pointer pointer = 
    pointerToIntegerCast_
      (container_of_ (pointer, hyp_page_tag, Id.id "node")) %-
      pointerToIntegerCast_ hyp_vmemmap_t
  in

  let hyp_vmemmap_good_node_pointer pointer = 
    (rem_t_ (hyp_vmemmap_offset_of_node_pointer pointer, 
             z_ (Memory.size_of_struct hyp_page_tag)))
    %==
      (int_ 0)
  in
  
  let hyp_vmemmap_node_pointer_to_index pointer = 
    hyp_vmemmap_offset_of_node_pointer pointer %/
      z_ (Memory.size_of_struct hyp_page_tag)
  in


  let hyp_pool_metadata_owned =
    let points = 
      point (p_t, Memory.size_of_struct hyp_pool_tag) 
        (q_ (1, 1)) pool_t (bool_ true)
    in
    LRT.Logical ((pool_s, IT.bt pool_t),
    LRT.Resource (points,
    LRT.I))
  in
  
  let pPAGE_SIZE_t = exp_ (int_ 2, pPAGE_SHIFT_t) in

  let hyp_pool_metadata_well_formedness =
    let constr = 
      and_ [
          int_ 0 %<= (pool_t %. "range_start");
          (pool_t %. "range_start") %< (pool_t %. "range_end");
          nat_divides_ (pool_t %. "range_start", pPAGE_SIZE_t);
          nat_divides_ (pool_t %. "range_end", pPAGE_SIZE_t);
          (pool_t %. "max_order") %<= mMAX_ORDER_t;
        ]
    in
    LRT.Constraint (constr, LRT.I)
  in

  let start_t = (pool_t %. "range_start") %/ pPAGE_SIZE_t in
  let end_t = (pool_t %. "range_end") %/ pPAGE_SIZE_t in

  let vmmemmap_metadata_owned =
    let element_size = Memory.size_of_struct hyp_page_tag in
    let i_s, i_t = IT.fresh_named Integer "?i" in
    let qpredicate = 
      QPredicate {
          pointer = hyp_vmemmap_t %+. (start_t %* z_ element_size);
          element_size = z_ element_size;
          length = sub_ (end_t, start_t);
          name = Ctype (Sctypes.Sctype ([], Struct hyp_page_tag));
          i = i_s;
          iargs = [];
          oargs = [app_ poolmap_t i_t; app_ poolmap_i_t i_t];
          moved = [];
          unused = true;
        }
    in
    LRT.Logical ((poolmap_s, IT.bt poolmap_t),
    LRT.Logical ((poolmap_i_s, IT.bt poolmap_i_t),
    LRT.Resource (qpredicate, LRT.I)))
  in

  let vmemmap_cell_address i_t =
    arrayShift_ (hyp_vmemmap_t, 
                 Sctype ([], Struct hyp_page_tag), 
                 i_t)
  in

  let vmemmap_cell_node_address i_t =
    memberShift_ (vmemmap_cell_address i_t,
                  hyp_page_tag,
                  Id.id "node")
  in

  let free_list_well_formedness = 
    let o_s, o_t = IT.fresh_named Integer "?o" in
    let constr = 
      forall_ (o_s, IT.bt o_t) 
        (and_ (
          let condition prev_next = 
            let prev_next_t = ((pool_t %. "free_area") %@ o_t) %. prev_next in
            hyp_vmemmap_good_node_pointer prev_next_t ::
              (let i_t = hyp_vmemmap_node_pointer_to_index prev_next_t in
               [start_t %<= i_t; i_t %< end_t;
                ((poolmap_t %@ (i_t %- start_t)) %. "order") %== o_t;
                ((poolmap_t %@ (i_t %- start_t)) %. "refcount") %== int_ 0
              ])
          in
          condition "prev" @ condition "next"
        ))
    in
    LRT.Constraint (constr, LRT.I)
  in

  let hyp_page_well_formedness = 
    let constr =  
      let i_s, i_t = IT.fresh_named Integer "?i" in
      let first = 
        forall_sth_ (i_s, IT.bt i_t) 
          (and_ [start_t %<= i_t; i_t %< end_t]) 
          (and_ [
              (* initialised *)
              poolmap_i_t %@ (i_t %- start_t);
              (* refcount is natural number *)
              ((poolmap_t %@ (i_t %- start_t)) %. "refcount") %>= int_ 0;
              (* order is HYP_NO_ORDER or between 0 and MAX_ORDER *)
              (let order = (poolmap_t %@ (i_t %- start_t)) %. "order" in
               impl_ (order %!= hHYP_NO_ORDER_t,
                      and_ [int_ 0 %<= order; order %<= mMAX_ORDER_t]));
              (* points back to the pool *)
              ((poolmap_t %@ (i_t %- start_t)) %. "pool") %== p_t;
              (* list emptiness via next and prev is equivalent ("prev/next" points back at node for index i_t) *)
              eq_ ((((poolmap_t %@ (i_t %- start_t)) %. "node") %. "next") %== vmemmap_cell_node_address i_t,
                   (((poolmap_t %@ (i_t %- start_t)) %. "node") %. "prev") %== vmemmap_cell_node_address i_t);
              (* list empty in the above sense if and only if refcount 0 and order != NYP_NO_ORDER *)
              eq_ (
                  (((poolmap_t %@ (i_t %- start_t)) %. "node") %. "next") %!= vmemmap_cell_node_address i_t,
                  and_ [((poolmap_t %@ (sub_ (i_t, start_t))) %. "refcount") %== int_ 0;
                        ((poolmap_t %@ (sub_ (i_t, start_t))) %. "order") %!= hHYP_NO_ORDER_t;
                     ]
                )
          ])
      in
      let linked_list_well_formed prev_next = 
        forall_sth_ (i_s, IT.bt i_t) 
          (and_ [start_t %<= i_t; i_t %< end_t]) 
          (let prev_next_t = ((poolmap_t %@ (i_t %- start_t)) %. "node") %.prev_next in
           or_ [
               
               prev_next_t %== vmemmap_cell_node_address i_t; (* points to itself *)
               
               prev_next_t %==
                 arrayShift_
                   (memberShift_ (p_t, hyp_pool_tag, Id.id "free_area"),
                    Sctype ([], Struct list_head_tag),
                    (poolmap_t %@ (i_t %- start_t)) %. "order");
               
               and_ (
                   hyp_vmemmap_good_node_pointer prev_next_t ::
                   let j_t = hyp_vmemmap_node_pointer_to_index prev_next_t in
                   let k_s, k_t = IT.fresh_named Integer "?k" in
                   [start_t %<= j_t; j_t %< end_t;
                    (((poolmap_t %@ (j_t %- start_t)) %. "node") %.(if prev_next = "next" then "prev" else "next")) %== vmemmap_cell_node_address i_t;
                    ((poolmap_t %@ (i_t %- start_t)) %. "order") %== ((poolmap_t %@ (j_t %- start_t)) %. "order");
                    forall_sth_ (k_s, IT.bt k_t)
                      (and_ [(i_t %+ int_ 1) %<= k_t; 
                             k_t %< (i_t %+ (exp_ (int_ 2, (poolmap_t %@ (i_t %- start_t)) %. "order")))])
                      (and_ [
                          ((poolmap_t %@ (k_t %- start_t)) %. "order") %== hHYP_NO_ORDER_t;
                          ((poolmap_t %@ (k_t %- start_t)) %. "refcount") %== int_ 0;
                        ])
                   ]);
               
          ])
      in
      and_ [first; linked_list_well_formed "prev"; linked_list_well_formed "next"]
    in
    LRT.Constraint (constr, LRT.I)
  in

  let page_group_ownership = 
    let qp_s, qp_t = IT.fresh_named Loc "?qp" in
    let bytes_s, bytes_t = IT.fresh_named (BT.Param (Loc, Integer)) "?bytes" in
    let condition = 
      let i_s, i_t = IT.fresh_named Integer "?i" in
      and_ [
          gtPointer_ (qp_t, pointer_ (Z.of_int 0));
          exists_ (i_s, IT.bt i_t)
            (and_ (
               [start_t %<= i_t; i_t %< end_t;
                ((poolmap_t %@ (i_t %- start_t)) %. "order") %!= hHYP_NO_ORDER_t;
                ((poolmap_t %@ (i_t %- start_t)) %. "refcount") %== int_ 0] @
                 let page_group_start_addr = mul_ (i_t, pPAGE_SIZE_t) in
                 let number_pages = exp_ (int_ 2, (poolmap_t %@ (i_t %- start_t)) %. "order") in
                 let page_group_end_addr = 
                   page_group_start_addr %+ (number_pages %* pPAGE_SIZE_t)
                 in
                 [lePointer_ (integerToPointerCast_ (page_group_start_addr), qp_t);
                  ltPointer_ (qp_t, integerToPointerCast_ (page_group_end_addr));]
            ))
        ]
    in
    let qpoint = 
      QPoint {
          qpointer = qp_s;
          size = Z.of_int 1;
          permission = ite_ (condition, q_ (1, 1), q_ (0, 1));
          value = app_ bytes_t qp_t;
          init = bool_ false;
        }
    in
    LRT.Logical ((bytes_s, IT.bt bytes_t),
    LRT.Resource (qpoint, LRT.I))
  in

  
  let lrt = 
    let open LRT in
    hyp_pool_metadata_owned 
    @@ hyp_pool_metadata_well_formedness
    @@ vmmemmap_metadata_owned
    @@ free_list_well_formedness
    @@ hyp_page_well_formedness
    @@ page_group_ownership
  in

  let predicate = 
    {
      loc = Loc.other "internal (Hyp_pool)";
      pointer = 
        p_s;
      iargs = [
          (hyp_vmemmap_s, IT.bt hyp_vmemmap_t);
          (pPAGE_SHIFT_s, IT.bt pPAGE_SHIFT_t);
          (mMAX_ORDER_s, IT.bt mMAX_ORDER_t);
          (hHYP_NO_ORDER_s, IT.bt hHYP_NO_ORDER_t);
        ];
      oargs = [
          ("pool", IT.bt pool_t);
        ];
      clauses = 
        [PackingFT.of_lrt lrt (PackingFT.I [("pool", pool_t);])]; 
    } 
  in
  (id, predicate)







let predicate_list struct_decls = 
  region ::
  part_zero_region ::
  zero_region ::
  early ::
  (* for now: *)
  try [hyp_pool struct_decls] with
  | Not_found -> []


    
