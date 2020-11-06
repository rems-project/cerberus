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

let integerType_constraint loc it =
  let* (min,max) = match it with
    | CF.Ctype.Bool -> return (Z.of_int 0, Z.of_int 1)
    | _ -> Memory.integer_range loc it 
  in
  let lc about = LC (IT.in_range (Num min) (Num max) about) in
  return lc

let rec in_range_of_ctype loc struct_decls (CF.Ctype.Ctype (_,ct_)) =
  let open CF.Ctype in
  match ct_ with
  | Void -> 
     return (fun it -> LC (EQ (it , Unit)))
  | Basic (Integer it) -> 
     let* rangef = integerType_constraint loc it in
     return rangef
  | Basic (Floating _) -> 
     fail loc (Unsupported !^"floats")
  | Array _ -> 
     fail loc (Unsupported !^"arrays")
  | Function _ -> 
     fail loc (Unsupported !^"todo: function pointers")
  | Pointer _ ->
     let* pointer_size = Memory.size_of_pointer loc in
     let rangef about = LC (in_range (Num Z.zero) (Num pointer_size) about) in
     return rangef
  | Atomic ct -> 
     (* check *)
     in_range_of_ctype loc struct_decls ct
  | Struct tag -> 
     let* decl = Global.get_struct_decl loc struct_decls (Tag tag) in
     let rangef about = 
       let lcs = 
         List.map (fun (member, rangef) ->
             let (LC c) = rangef (IT.Member (Tag tag, about, member)) in
             c
           ) decl.Global.ranges
       in
       (LC (And lcs))
     in
     return rangef
  | Union _ -> 
     fail loc (Unsupported !^"union types")




(* structs *)

let struct_decl_raw loc fields = 
  let rec aux id ct = 
    let member = Member (Id.s id) in
    let (CF.Ctype.Ctype (annots, ct_)) = ct in
    let loc = Loc.update_a loc annots in
    match ct_ with
    | Void -> return (member,Unit)
    | Basic (Integer it) -> return (member,Integer)
    | Array (ct, _maybe_integer) -> return (member,Array)
    | Pointer (_qualifiers, ct) -> return (member,Loc)
    | Atomic ct -> aux id ct
    | Struct tag -> return (member, Struct (Tag tag))
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in
  ListM.mapM (fun (id, (_,_,ct)) -> aux id ct) fields


let struct_decl_sizes loc fields = 
  ListM.mapM (fun (id, (_, _, ct)) ->
      let member = Member (Id.s id) in
      let* size = Memory.size_of_ctype loc ct in
      return (member,size)
    ) fields

let struct_decl_ranges loc struct_decls fields = 
  ListM.mapM (fun (id, (_, _, ct)) ->
      let member = Member (Id.s id) in
      let* rangef = in_range_of_ctype loc struct_decls ct in
      return (member,rangef)
    ) fields



let struct_decl_closed loc tag fields struct_decls = 
  let open Sym in
  let rec aux loc acc the_struct member ct =
    let (CF.Ctype.Ctype (annots, ct_)) = ct in
    let loc = Loc.update_a loc annots in
    let this = IT.Member (tag, S the_struct, member) in
    match ct_ with
    | Void -> 
       return acc
    | Basic (Integer it) -> 
       let* lc1 = integerType_constraint loc it in
       return (RT.Constraint (lc1 this,acc))
    | Array (ct, _maybe_integer) -> 
       return acc
    | Pointer (_qualifiers, ct) -> 
       return acc
    (* fix *)
    | Atomic ct -> 
       aux loc acc the_struct member ct
    | Struct tag2 -> 
       let open RT in
       let open Global in
       let* decl = Global.get_struct_decl loc struct_decls (Tag tag2) in
       let s' = Sym.fresh () in 
       let Computational ((s,_struct),tag2_bindings) = decl.closed in
       return (RT.subst_var_l (Subst.{before=s;after=s'}) tag2_bindings @@ 
                 Constraint (LC (EQ (S s', this)), acc))
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in
  let thisstruct = fresh () in
  let* bindings = 
    ListM.fold_rightM (fun (id, (_attributes, _qualifier, ct)) acc ->
        aux loc acc thisstruct (BT.Member (Id.s id)) ct
      ) fields I
  in
  return (RT.Computational ((thisstruct, BT.Struct tag), bindings))


let struct_decl_closed_stored loc tag fields (struct_decls: Global.struct_decls) = 
  let open Sym in
  let rec aux loc member ct =
    let open RT in
    let* size = Memory.size_of_ctype loc ct in
    let (CF.Ctype.Ctype (annots, ct_)) = ct in
    let loc = Loc.update_a loc annots in
    let this_v = Sym.fresh () in
    match ct_ with
    | Void -> 
       fail loc (Generic !^"void member of struct")
    | Basic (Integer it) -> 
       let* lc = integerType_constraint loc it in
       let make struct_p = 
         let this_p = IT.MemberOffset (tag,struct_p,member) in
         let points struct_p = RE.Points {pointer=this_p;pointee=this_v; size} in
         RT.Logical ((this_v, Base Integer), 
           RT.Resource (points struct_p, 
             RT.Constraint (lc (S this_v), I)))
       in
       return make
    | Array (ct, _maybe_integer) -> 
       let make struct_p = 
         let this_p = IT.MemberOffset (tag,struct_p,member) in
         let points struct_p = RE.Points {pointer=this_p;pointee=this_v; size} in
         RT.Logical ((this_v, Base Array), 
           RT.Resource (points struct_p, I))
       in
       return make
    | Pointer (_qualifiers, ct) -> 
       let make struct_p = 
         let this_p = IT.MemberOffset (tag,struct_p,member) in
         let points struct_p = RE.Points {pointer=this_p;pointee=this_v; size} in
         RT.Logical ((this_v, Base Loc), 
           RT.Resource (points struct_p, I))
       in
       return make
    | Atomic ct -> 
       (* fix *)
       aux loc member ct
    | Struct tag2 -> 
       (* let open RT in
        * let open Global in *)
       let* decl = Global.get_struct_decl loc struct_decls (Tag tag2) in
       let make struct_p = 
         RT.freshify_l (decl.closed_stored_aux 
                          (IT.MemberOffset (tag,struct_p,member)))
       in
       return make
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in
  let* make = 
    ListM.fold_rightM (fun (id, (_attributes, _qualifier, ct)) acc_make ->
        let* make = aux loc (BT.Member (Id.s id)) ct in
        return 
          (fun struct_p -> RT.(@@) (make struct_p) (acc_make struct_p))
      ) fields (fun struct_p -> RT.I)
  in
  return make


let struct_decl loc tag fields struct_decls = 
  let* raw = struct_decl_raw loc fields in
  let* sizes = struct_decl_sizes loc fields in
  let* ranges = struct_decl_ranges loc struct_decls fields in
  let* closed = struct_decl_closed loc tag fields struct_decls in
  let* closed_stored_aux = struct_decl_closed_stored loc tag fields struct_decls in
  let closed_stored = 
    let s = Sym.fresh () in 
    RT.Computational ((s, BT.Loc), closed_stored_aux (S s))
  in
  return Global.{ raw; sizes; ranges; closed; closed_stored; closed_stored_aux }


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
     let lrt' = Constraint (LC (IT.Aligned (S pointer, Num align)), lrt') in
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
     let lrt = 
       Logical ((s2, Base bt), 
       Resource ((points, 
       Constraint (LC (IT.Aligned (S pointer, Num align)),
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

(* fix *)
(* let lift ct = 
 *   let q = CF.Ctype.{const = false; restrict = false; volatile = false} in
 *   CF.Ctype.Ctype ([], Pointer (q, ct)) *)

(* let do_name (msym : Sym.t option) : Sym.t =  *)
  


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




