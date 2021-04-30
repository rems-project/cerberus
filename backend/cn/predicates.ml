module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RE = Resources
module PackingFT = ArgumentTypes.Make(Assignment)
open Pp



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
  {
    pointer = pred.pointer_arg; 
    iargs = []; 
    oargs = [(pred.value_arg, BT.of_sct ct);
             (pred.init_arg, BT.Bool)];
    clauses = [clause]
  }






let ctype_predicate struct_layouts ct = 
  let open ReturnTypes in
  let open LRT in
  let open IndexTerms in
  let open BaseTypes in
  let open Memory in
  let open Resources in
  let open Option in
  let open Sctypes in
  let pointer_s = Sym.fresh_named "p" in
  let pointer_t = sym_ (pointer_s, Loc) in
  let init_s = Sym.fresh_named "init" in
  let init_bt = BT.Bool in
  let init_t = sym_ (init_s, init_bt) in
  let v_s = Sym.fresh_named "v" in
  let v_bt = BT.of_sct ct in
  let v_t = sym_ (v_s, v_bt) in
  let size = size_of_ctype ct in
  let (Sctypes.Sctype (_, ct_)) = ct in
  let@ lrt, value_def = match ct_ with
  | Void ->
     Debug_ocaml.error "ctype_predicate void"
  | Integer it ->
     let lrt = 
       Logical ((v_s, v_bt), 
       Logical ((init_s, init_bt), 
       Resource (point (pointer_t, size) (q_ (1,1)) v_t init_t, LRT.I)))
     in
     return (lrt, v_t)
  | Pointer (_, ct') ->
     let lrt = 
       Logical ((v_s, v_bt), 
       Logical ((init_s, init_bt), 
       Resource (point (pointer_t, size) (q_ (1,1)) v_t init_t, LRT.I)))
     in
     return (lrt, v_t)
  | Array (t, None) ->
     (* todo: connect with user-annotation *)
     Debug_ocaml.error "representation: array of unknown length"
  | Array (ct', Some length) ->
     let i = Sym.fresh () in
     let i_t = sym_ (i, BT.Integer) in
     let qpredicate = {
         pointer = pointer_t; 
         element_size = z_ (size_of_ctype ct'); 
         length = int_ length;
         moved = []; 
         unused = true;
         name = Ctype ct';
         i;
         iargs = [];
         oargs = [app_ v_t i_t; init_t];
       }
     in
     let lrt = 
       Logical ((v_s, v_bt), 
       Logical ((init_s, init_bt), 
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
              let member_v = Sym.fresh () in
              let member_t = sym_ (member_v, BT.of_sct sct) in
              let resource = predicate (Ctype sct) member_p [] [member_t; init_t] in
              let lrt = 
                LRT.Logical ((member_v, BT.of_sct sct),
                LRT.Resource (resource, lrt))
              in
              let values = (member, member_t) :: values in
              (lrt, values)
           | None ->
              let padding_s = Sym.fresh () in
              let padding_t = sym_ (padding_s, BT.Integer) in
              let resource = point (member_p, size) (q_ (1,1)) padding_t init_t in
              let lrt = 
                LRT.Logical ((padding_s, BT.Integer),
                LRT.Resource (resource, lrt)) 
              in
              (lrt, values)
         ) layout (LRT.I, [])
     in
     let value_t = IT.struct_ (tag, values) in
     let lrt = 
       Logical ((init_s, BT.Bool), lrt) @@ LRT.I
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
      value_def = v_t; 
      init_def = init_t 
    }
  in
  return def










let early = 
  let open Resources in
  let open BT in
  let open IT in
  let id = "EarlyAlloc" in
  let start_s = Sym.fresh () in
  let start_t = sym_ (start_s, Loc) in
  let end_s = Sym.fresh () in
  let end_t = sym_ (end_s, Loc) in
  let v_s = Sym.fresh () in
  let v_bt = BT.Param (Loc, Integer) in
  let v_t = sym_ (v_s, v_bt) in
  let init_s = Sym.fresh () in
  let init_bt = BT.Param (Loc, Bool) in
  let init_t = sym_ (init_s, init_bt) in
  let iargs = [(end_s, BT.Loc)] in
  let oargs = [] in
  let q = Sym.fresh () in 
  let block = 
    Resources.array
      q
      (start_t)
      (add_ (sub_ (pointerToIntegerCast_ end_t, pointerToIntegerCast_ start_t), int_ 1))
      (Z.of_int 1)
      (app_ v_t (sym_ (q, Loc)))
      (app_ init_t (sym_ (q, Loc)))
      (q_ (1, 1))
  in
  let lrt =
    LRT.Logical ((v_s, v_bt),
    LRT.Logical ((init_s, init_bt),
    LRT.Resource (block, 
    LRT.Constraint (IT.good_pointer start_t (Sctypes.Sctype ([], Void)),
    LRT.Constraint (IT.good_pointer end_t (Sctypes.Sctype ([], Void)),
    LRT.I)))))
  in
  let outputs = [] in
  let predicate = {
      pointer = start_s;
      iargs; 
      oargs; 
      clauses = [PackingFT.of_lrt lrt (PackingFT.I outputs)]; 
    } 
  in
  (id, predicate)



let zero_region = 
  let open Resources in
  let open BT in
  let open IT in
  let id = "ZeroRegion" in
  let pointer_s = Sym.fresh () in
  let pointer_t = sym_ (pointer_s, Loc) in
  let length_s = Sym.fresh () in
  let length_t = sym_ (length_s, Integer) in
  let iargs = [(length_s, BT.Integer)] in
  let oargs = [] in
  let array = 
    RE.array (Sym.fresh ()) pointer_t length_t (Z.of_int 1)
      (int_ 0) 
      (bool_ true)
      (q_ (1,1))
  in
  let lrt =
    LRT.Resource (array, 
    LRT.Constraint (IT.good_pointer pointer_t (Sctypes.Sctype ([], Void)),
    LRT.I))
  in
  let outputs = [] in
  let predicate = {
      pointer = pointer_s;
      iargs; 
      oargs; 
      clauses = [PackingFT.of_lrt lrt (PackingFT.I outputs)]; 
    } 
  in
  (id, predicate)
