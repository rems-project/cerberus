module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RE = Resources.RE
module PackingFT = ArgumentTypes.Make(Assignment)
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
    pointer: Sym.t;
    iargs : (Sym.t * LS.t) list;
    oargs : (Sym.t * LS.t) list;
    clauses : clause list;
  }
  
let pp_predicate_definition def = 
  item "pointer" (Sym.pp def.pointer) ^/^
  item "iargs" (Pp.list (fun (s,_) -> Sym.pp s) def.iargs) ^/^
  item "oargs" (Pp.list (fun (s,_) -> Sym.pp s) def.oargs) ^/^
  item "clauses" (Pp.list pp_clause def.clauses)
  



(* let rec init_bt (Sctype (_, ct_)) =
 *   match ct_ with
 *   | Array (t, _) -> BT.Param (Integer, init_bt t)
 *   | t -> Bool *)




type ctype_predicate =
  { pointer_arg : Sym.t;
    value_arg : Sym.t;
    init_arg : Sym.t;
    lrt: LRT.t;
    value_def: IT.t; 
    init_def: IT.t; 
  }


let ctype_predicate_to_predicate ct pred = 
  let clause = 
    PackingFT.of_lrt pred.lrt 
      (PackingFT.I [pred.value_def; pred.init_def]) in
  let def = {
      pointer = pred.pointer_arg; 
      iargs = []; 
      oargs = [(pred.value_arg, IT.bt pred.value_def);
               (pred.init_arg, IT.bt pred.init_def)];
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
  let pointer_s, pointer_t = IT.fresh BT.Loc in
  let init_s, init_t = IT.fresh BT.Bool in
  let v_s, v_t = IT.fresh (BT.of_sct ct) in
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
              let member_v, member_t = IT.fresh (BT.of_sct sct) in
              let resource = predicate (Ctype sct) member_p [] [member_t; init_t] in
              let lrt = 
                LRT.Logical ((member_v, IT.bt member_t),
                LRT.Resource (resource, lrt))
              in
              let values = (member, member_t) :: values in
              (lrt, values)
           | None ->
              let padding_s, padding_t = IT.fresh BT.Integer in
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
      pointer_arg = pointer_s; 
      value_arg = v_s; 
      init_arg = init_s;
      lrt; 
      value_def = value_def; 
      init_def = init_t 
    }
  in
  return def









let char_ct = Sctypes.Sctype ([], Integer Char)


let region = 
  let id = "Region" in
  let pointer_s, pointer_t = IT.fresh Loc in
  let length_s, length_t = IT.fresh Integer in
  let v_s, v_t = IT.fresh (BT.Param (Integer, Integer)) in
  let init_s, init_t = IT.fresh (BT.Param (Integer, Bool)) in
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
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t)]; 
      oargs = [(v_s, IT.bt v_t); (init_s, IT.bt init_t)]; 
      clauses = [PackingFT.of_lrt lrt (PackingFT.I [v_t; init_t])]; 
    } 
  in
  (id, predicate)



let early = 
  let id = "EarlyAlloc" in
  let start_s, start_t = IT.fresh Loc in
  let end_s, end_t = IT.fresh Loc in
  let length_t = 
    add_ (sub_ (pointerToIntegerCast_ end_t,
                pointerToIntegerCast_ start_t), 
          int_ 1)
  in
  let v_s, v_t = IT.fresh (BT.Param (Integer, Integer)) in
  let init_s, init_t = IT.fresh (BT.Param (Integer, Bool)) in
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
      pointer = start_s;
      iargs = [(end_s, IT.bt end_t)]; 
      oargs = []; 
      clauses = [PackingFT.of_lrt lrt (PackingFT.I [])]; 
    } 
  in
  (id, predicate)




let part_zero_region = 
  let id = "PartZeroRegion" in
  let pointer_s, pointer_t = IT.fresh Loc in
  let length_s, length_t = IT.fresh Integer in
  let v_s, v_t = IT.fresh (BT.Param (Integer, Integer)) in
  let init_s, init_t = IT.fresh (BT.Param (Integer, Bool)) in
  let j_s, j_t = IT.fresh Integer in
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
    forall_ (i_s, IT.bt i_t)
      (impl_ (and_ [le_ (int_ 0, i_t); lt_ (i_t, j_t)], 
              eq_ (app_ v_t i_t, int_ 0)))
  in
  let init_constr = 
    forall_ (i_s, IT.bt i_t)
      (impl_ (and_ [le_ (int_ 0, i_t); lt_ (i_t, j_t)], 
              app_ init_t i_t))
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
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t); (j_s, IT.bt j_t)];
      oargs = [];
      clauses = [PackingFT.of_lrt lrt (PackingFT.I [])]; 
    } 
  in
  (id, predicate)




let zero_region = 
  let id = "ZeroRegion" in
  let pointer_s, pointer_t = IT.fresh Loc in
  let length_s, length_t = IT.fresh Integer in
  let predicate = {
      name = Id "PartZeroRegion";
      pointer = pointer_t; 
      unused = true;
      iargs = [length_t; length_t];
      oargs = [];
    }
  in
  let lrt = LRT.Resource (Predicate predicate, LRT.I) in
  let predicate = {
      pointer = pointer_s;
      iargs = [(length_s, IT.bt length_t)];
      oargs = [];
      clauses = [PackingFT.of_lrt lrt (PackingFT.I [])]; 
    } 
  in
  (id, predicate)





