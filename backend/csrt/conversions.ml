module CF=Cerb_frontend
open List
(* open Sym *)
open Resultat
open Pp
(* open Tools *)
module BT = BaseTypes
module RT = ReturnTypes
module FT = ArgumentTypes.Make(ReturnTypes)
module LT = ArgumentTypes.Make(False)
open TypeErrors
open IndexTerms
open BaseTypes
open LogicalConstraints
open Resources


module StringMap = Map.Make(String)
module SymSet = Set.Make(Sym)




let annot_of_ct (CF.Ctype.Ctype (annot,_)) = annot


(* base types *)

let bt_of_core_object_type loc ot =
  let open CF.Core in
  match ot with
  | OTy_integer -> return BT.Integer
  | OTy_pointer -> return BT.Loc
  | OTy_array cbt -> return BT.Array
  | OTy_struct sym -> return (BT.Struct (Tag sym))
  | OTy_union _sym -> fail loc (Unsupported !^"todo: unions")
  | OTy_floating -> fail loc (Unsupported !^"todo: float")

let rec bt_of_core_base_type loc cbt =
  let open CF.Core in
  match cbt with
  | BTy_unit -> return BT.Unit
  | BTy_boolean -> return BT.Bool
  | BTy_object ot -> bt_of_core_object_type loc ot
  | BTy_loaded ot -> bt_of_core_object_type loc ot
  | BTy_list bt -> 
     let* bt = bt_of_core_base_type loc bt in
     return (BT.List bt)
  | BTy_tuple bts -> 
     let* bts = ListM.mapM (bt_of_core_base_type loc) bts in
     return (BT.Tuple bts)
  | BTy_storable -> fail loc (Unsupported !^"BTy_storable")
  | BTy_ctype -> fail loc (Unsupported !^"ctype")

let rec bt_of_ctype loc (CF.Ctype.Ctype (_,ct_)) =
  let open CF.Ctype in
  match ct_ with
  | Void -> return BT.Unit
  | Basic (Integer _) -> return BT.Integer
  | Basic (Floating _) -> fail loc (Unsupported !^"floats")
  | Array _ -> fail loc (Unsupported !^"arrays")
  | Function _ -> fail loc (Unsupported !^"todo: function pointers")
  | Pointer _ -> return BT.Loc
  | Atomic ct -> bt_of_ctype loc ct  (* check? *)
  | Struct tag -> return (BT.Struct (BT.Tag tag))
  | Union _ -> fail loc (Unsupported !^"union types")

let rec st_of_ctype loc (CF.Ctype.Ctype (_,ct_)) =
  let open CF.Ctype in
  match ct_ with
  | Void -> 
     fail loc (Unsupported !^"todo: void*")
  | Basic (Integer it) -> 
     return (ST_Integer it)
  | Basic (Floating _) -> 
     fail loc (Unsupported !^"floats")
  | Array _ -> 
     fail loc (Unsupported !^"arrays")
  | Function _ -> 
     fail loc (Unsupported !^"todo: function pointers")
  | Pointer _ -> 
     return ST_Pointer
  | Atomic ct -> 
     st_of_ctype loc ct  (* check? *)
  | Struct tag -> 
     return (ST_Struct (BT.Tag tag))
  | Union _ -> 
fail loc (Unsupported !^"union types")

let integerType_constraint loc it =
  let* (min,max) = match it with
    | CF.Ctype.Bool -> return (Z.of_int 0, Z.of_int 1)
    | _ -> Memory.integer_range loc it 
  in
  let lc about = LC (IT.in_range (Num min) (Num max) about) in
  return lc

let lookup_struct_in_tagDefs loc (BT.Tag tag) =
  match Pmap.lookup tag (CF.Tags.tagDefs ()) with
  | Some (CF.Ctype.StructDef (fields,flexible_array_member)) -> 
     return (fields,flexible_array_member)
  | Some (UnionDef _) -> fail loc (Generic !^"expected struct")
  | None -> 
     fail loc (Generic (!^"struct" ^^^ (BT.pp_tag (BT.Tag tag)) ^^^ !^"not defined"))


let pointer_range_constraint loc = 
  let* pointer_byte_size = Memory.size_of_pointer loc in
  let pointer_size = Z.mult_big_int pointer_byte_size (Z.of_int 8) in
  let max = Z.power_int_positive_big_int 2 (Z.sub_big_int pointer_size (Z.of_int 1)) in
  let rangef about = 
    LC (IT.And [IT.LocLE (Pointer Z.zero, about); 
                IT.LocLE (about, Pointer max)])
  in
  return rangef


let rec in_range_of_ctype loc (CF.Ctype.Ctype (_,ct_)) =
  let open CF.Ctype in
  match ct_ with
  | Void -> return (fun it -> LC (EQ (it , Unit)))
  | Basic (Integer it) -> integerType_constraint loc it
  | Basic (Floating _) -> fail loc (Unsupported !^"floats")
  | Array _ -> fail loc (Unsupported !^"arrays")
  | Function _ -> fail loc (Unsupported !^"todo: function pointers")
  | Pointer _ -> pointer_range_constraint loc
  | Atomic ct -> in_range_of_ctype loc ct
  | Struct tag -> in_range_of_struct_type loc (Tag tag)
  | Union _ -> fail loc (Unsupported !^"union types")

and in_range_of_struct_type loc (Tag tag) = 
  let* (fields,_) = lookup_struct_in_tagDefs loc (BT.Tag tag) in
  let* member_rangefs =
    ListM.mapM (fun (id, (_, _, ct)) ->
        let loc = Loc.update_a loc (annot_of_ct ct) in
        let* rangef = in_range_of_ctype loc ct in
        return (Member (Id.s id),rangef)
      ) fields
  in
  let rangef about = 
    let lcs = 
      List.map (fun (member, rangef) ->
          let (LC c) = rangef (IT.Member (Tag tag, about, member)) in
          c
        ) member_rangefs
    in
    (LC (And lcs))
  in
  return rangef





(* structs *)
let struct_decl_raw loc tag = 
  let* (fields,_) = lookup_struct_in_tagDefs loc tag in
  ListM.mapM (fun (id, (_,_, ct)) ->
      let loc = Loc.update_a loc (annot_of_ct ct) in
      let* bt = bt_of_ctype loc ct in
      return (Member (Id.s id), bt)
  ) fields


let struct_decl_sizes loc tag = 
  let* (fields,_) = lookup_struct_in_tagDefs loc tag in
  ListM.mapM (fun (id, (_, _, ct)) ->
      let loc = Loc.update_a loc (annot_of_ct ct) in
      let* size = Memory.size_of_ctype loc ct in
      return (Member (Id.s id),size)
    ) fields

let struct_decl_ranges loc tag = 
  in_range_of_struct_type loc tag

let struct_decl_offsets loc tag = 
  let* (fields,_) = lookup_struct_in_tagDefs loc tag in
  ListM.mapM (fun (id, (_, _, ct)) ->
      let loc = Loc.update_a loc (annot_of_ct ct) in
      let* offset = Memory.offset loc tag (BT.Member (Id.s id)) in
      return (Member (Id.s id),offset)
    ) fields


let struct_decl_closed loc tag = 
  let this = Sym.fresh () in
  let* lc = in_range_of_struct_type loc tag in
  return (RT.Computational ((this, BT.Struct tag), Constraint (lc (S this), I)))


let struct_decl_closed_stored loc tag = 
  let open RT in
  let rec aux loc tag struct_p = 
    let* (fields,_) = lookup_struct_in_tagDefs loc tag in
    let* members = 
      ListM.mapM (fun (id, (_, _, ct)) ->
          let loc = Loc.update_a loc (annot_of_ct ct) in
          let member = Member (Id.s id) in
          let member_p = IT.MemberOffset (tag,struct_p,member) in
          let (CF.Ctype.Ctype (_,ct_)) = ct in
          match ct_ with
          | Struct tag -> 
             let* (components, s_value) = aux loc (BT.Tag tag) member_p in
             return (components, (member, s_value))
          | _ ->
             let v = Sym.fresh () in
             let* bt = bt_of_ctype loc ct in
             let* size = Memory.size_of_ctype loc ct in
             return ([(member_p, v, size, bt)], (member, S v))
          ) fields
    in
    let (components, values) = List.split members in
    return (List.flatten components, IT.Struct (tag, values))
  in
  let struct_pointer = Sym.fresh () in
  let* components, struct_value = aux loc tag (S struct_pointer) in
  let pointer_constr about = LC (InRange (ST_Pointer, about)) in
  let lrt = 
    List.fold_right (fun (member_p, member_v, size, bt) lrt ->
        let points = RE.Points {pointer = member_p; pointee = member_v; size} in
        RT.Logical ((member_v, Base bt), 
        RT.Resource (points, 
        RT.Constraint (pointer_constr member_p, lrt)))
      ) components RT.I
  in
  let range_constraint = LC (IT.InRange (ST_Struct tag, struct_value)) in
  let lrt = lrt @@ Constraint (range_constraint, RT.I) in
  return (Computational ((struct_pointer, BT.Loc), lrt))
  
  

let struct_decl loc (tag : BT.tag) = 
  let* raw = struct_decl_raw loc tag in
  let* sizes = struct_decl_sizes loc tag in
  let* range = struct_decl_ranges loc tag in
  let* offsets = struct_decl_offsets loc tag in
  let* closed = struct_decl_closed loc tag in
  let* closed_stored = struct_decl_closed_stored loc tag in
  return Global.{ raw; sizes; range; offsets; closed; closed_stored }


(* return types *)

let rec rt_of_pointer_ctype loc struct_decls (pointer : Sym.t) ct = 
  let open RT in
  let CF.Ctype.Ctype (_, ct_) = ct in
  begin match ct_ with
  | CF.Ctype.Struct tag ->
     let open Global in
     let* decl = Global.get_struct_decl loc struct_decls (Tag tag) in
     let Computational ((s',bt), lrt) = RT.freshify decl.closed_stored in
     let* align = Memory.align_of_ctype loc ct in
     let lrt' = RT.subst_var_l {before = s'; after = pointer} lrt in
     let lrt' = Constraint (LC (IT.Aligned (ST_Struct (BT.Tag tag), S pointer)), lrt') in
     return (Computational ((pointer, bt), lrt'))
  | CF.Ctype.Void -> 
     fail loc (Unsupported !^"todo: void*")
  | _ ->
     let s2 = Sym.fresh () in
     let* (Computational ((s2,bt),lrt)) = 
       rt_of_ctype loc struct_decls s2 ct in
     (* fix *)
     let* size = Memory.size_of_ctype loc ct in
     let* align = Memory.align_of_ctype loc ct in
     let points = RE.Points {pointer = S pointer; pointee = s2; size} in
     let* st = st_of_ctype loc ct in
     let lrt = 
       Logical ((s2, Base bt), 
       Resource ((points, 
       Constraint (LC (IT.Aligned (st, S pointer)),
       lrt))))
     in
     return (Computational ((pointer,Loc), lrt))
  end

and rt_of_ctype loc struct_decls (s : Sym.t) (CF.Ctype.Ctype (annots, ct_)) =
  let open RT in
  match ct_ with
  | Void -> return (Computational ((s, BT.Unit), I))
  | Basic (Integer it) -> 
     let* constr = integerType_constraint loc it in
     return (Computational ((s, Integer), Constraint (constr (S s),I)))
  | Array (ct, _maybe_integer) ->
     return (Computational ((s, Array), I))
  | Pointer (_qualifiers, ct) ->
     rt_of_pointer_ctype loc struct_decls s ct
  (* fix *)
  | Atomic ct -> 
     rt_of_ctype loc struct_decls s ct
  | Struct tag -> 
     let* decl = Global.get_struct_decl loc struct_decls (Tag tag) in
     let Computational ((s',bt),lrt) = RT.freshify decl.Global.closed in
     return (Computational ((s, bt), RT.subst_var_l {before=s; after=s} lrt))
  | Basic (Floating _) -> 
     fail loc (Unsupported !^"floats")
  | Union sym -> 
     fail loc (Unsupported !^"todo: union types")
  | Function _ -> 
     fail loc (Unsupported !^"function pointers")



(* function types *)


let update_values_lrt lrt =
  let subst_non_pointer = RT.subst_var_l ~re_subst_var:RE.subst_non_pointer in
  let rec aux = function
    | RT.Logical ((s,ls),lrt) ->
       let s' = Sym.fresh () in
       let lrt' = subst_non_pointer {before=s;after=s'} lrt in
       RT.Logical ((s',ls), aux lrt')
    | RT.Resource (re,lrt) -> RT.Resource (re,aux lrt)
    | RT.Constraint (lc,lrt) -> RT.Constraint (lc,aux lrt)
    | RT.I -> RT.I
  in
  aux lrt

let make_fun_spec loc struct_decls args ret_ctype = 
  let open FT in
  let open RT in
  let* (names, arg_rts, args, rets) = 
    ListM.fold_rightM (fun (msym, ct) (names, arg_rts, args, rets) ->
        let oname = Option.bind msym Sym.name in
        let sl = Sym.fresh_onamed oname in
        let names = match oname with
          | Some ident -> StringMap.add ident sl names
          | None -> names
        in
        let* arg_rt = rt_of_pointer_ctype loc struct_decls sl ct in
        let arg_rts = (oname, arg_rt) :: arg_rts in
        let arg = FT.of_rt arg_rt in
        let args = Tools.comp arg args in
        let ret = update_values_lrt (RT.lrt arg_rt) in
        return (names, arg_rts, args, ret @@ rets)
      ) 
      args (StringMap.empty, [], (fun ft -> ft), I)
  in
  let* (Computational ((ret_name,bound),ret)) = 
    rt_of_ctype loc struct_decls (Sym.fresh ()) ret_ctype in
  let ftyp = args (I (RT.Computational ((ret_name,bound), RT.(@@) ret rets))) in
  return (names, ftyp, arg_rts)





(* unused currently: picking some default types for labels *)
let make_label_spec (loc : Loc.t) (ftyp : FT.t) 
                    (struct_decls : Global.struct_decls) 
                    (args : (Sym.t option * CF.Ctype.ctype) list) : LT.t m =
  let subst_non_pointer = FT.subst_var ~re_subst_var:RE.subst_non_pointer in
  let rec aux = function
    | FT.Computational (_,lt) -> aux lt
    | FT.Logical ((s,ls),lt) ->
       let s' = Sym.fresh () in
       let lt' = subst_non_pointer {before=s;after=s'} lt in
       let* lt' = aux lt' in
       return (LT.Logical ((s',ls), lt'))
    | FT.Resource (re,lrt) -> 
       let* lrt = aux lrt in
       return (LT.Resource (re,lrt))
    | FT.Constraint (lc,lrt) -> 
       let* lrt = aux lrt in
       return (LT.Constraint (lc,lrt))
    | FT.I _ -> 
       let* arguments = 
         ListM.fold_leftM (fun args (msym, ct) ->
             let s = Sym.fresh_onamed (Option.bind msym Sym.name) in
             let* arg_rt = rt_of_pointer_ctype loc struct_decls s ct in
             let arg = LT.of_rt arg_rt in
             let args = Tools.comp args arg in
             return args
           ) 
           (fun ft -> ft) args
       in
       let ftyp = arguments (LT.I False.False) in
       return ftyp
  in
  aux ftyp




