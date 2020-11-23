module CF=Cerb_frontend
open List
(* open Sym *)
open Resultat
open Pp
(* open Tools *)
module BT = BaseTypes
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module LFT = ArgumentTypes.Make(LogicalReturnTypes)
module FT = ArgumentTypes.Make(ReturnTypes)
module LT = ArgumentTypes.Make(False)
open TypeErrors
open IndexTerms
open BaseTypes
open LogicalConstraints
open Resources


module StringMap = Map.Make(String)
module SymSet = Set.Make(Sym)




let get_loc_ annots = Cerb_frontend.Annot.get_loc_ annots


let struct_predicates = true




let annot_of_ct (CF.Ctype.Ctype (annot,_)) = annot


(* base types *)

let sct_of_ct loc ct = 
  match Sctypes.of_ctype ct with
  | Some ct -> return ct
  | None -> fail loc (Unsupported (!^"ctype" ^^^ CF.Pp_core_ctype.pp_ctype ct))

let bt_of_core_object_type loc ot =
  let open CF.Core in
  match ot with
  | OTy_integer -> return BT.Integer
  | OTy_pointer -> return BT.Loc
  | OTy_array cbt -> Debug_ocaml.error "arrays"
  | OTy_struct tag -> return (BT.Struct tag)
  | OTy_union _tag -> Debug_ocaml.error "union types"
  | OTy_floating -> fail loc (Unsupported !^"floats")

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
  | BTy_storable -> Debug_ocaml.error "BTy_storageble"
  | BTy_ctype -> Debug_ocaml.error "BTy_ctype"










let struct_layout loc members tag = 
  let rec aux members position =
    match members with
    | [] -> 
       return []
    | (member, (attrs, qualifiers, ct)) :: members ->
       let* sct = sct_of_ct loc ct in
       let offset = Memory.member_offset tag member in
       let size = Memory.size_of_ctype sct in
       let to_pad = Z.sub offset position in
       let padding = 
         if Z.gt_big_int to_pad Z.zero 
         then [(position, to_pad, None)] 
         else [] 
       in
       let member = [(offset, size, Some (member, sct))] in
       let* rest = aux members (Z.add_big_int to_pad size) in
       return (padding @ member @ rest)
  in
  (aux members Z.zero)



module CA = CF.Core_anormalise

let struct_decl loc (tagDefs : (CA.st, CA.ut) CF.Mucore.mu_tag_definitions) fields (tag : BT.tag) = 

  let get_struct_members tag = 
    match Pmap.lookup tag tagDefs with
    | None -> fail loc (Missing_struct tag)
    | Some (M_UnionDef _) -> fail loc (Generic !^"expected struct")
    | Some (M_StructDef (fields, _)) -> return fields
  in

  let* members = 
    ListM.mapM (fun (member, (_,_, ct)) ->
        let loc = Loc.update loc (get_loc_ (annot_of_ct ct)) in
        let* sct = sct_of_ct loc ct in
        let bt = BT.of_sct sct in
        return (member, (sct, bt))
    ) fields
  in

  let* closed_stored =
    let open RT in
    let open LRT in
    let rec aux loc tag struct_p = 
      let* def_members = get_struct_members tag in
      let* layout = struct_layout loc def_members tag in
      let* members = 
        ListM.mapM (fun (offset, size, member_or_padding) ->
            let pointer = IT.Offset (struct_p, Num offset) in
            match member_or_padding with
            | None -> return ([(pointer, size, None)], [])
            | Some (member, sct) -> 
               match sct with
               | Sctypes.Struct tag -> 
                  let* (components, s_value) = aux loc tag pointer in
                  return (components, [(member, s_value)])
               | _ ->
                  let v = Sym.fresh () in
                  let bt = BT.of_sct sct in
                  return ([(pointer, size, Some (v, bt))], [(member, S v)])
            ) layout
      in
      let (components, values) = List.split members in
      return (List.flatten components, IT.Struct (tag, List.flatten values))
    in
    let struct_pointer = Sym.fresh () in
    let* components, struct_value = aux loc tag (S struct_pointer) in
    let lrt = 
      List.fold_right (fun (member_p, size, member_or_padding) lrt ->
          match member_or_padding with
          | Some (member_v, bt) ->
             LRT.Logical ((member_v, Base bt), 
             LRT.Resource (RE.Points {pointer = member_p; pointee = member_v; size}, lrt))
          | None ->
             LRT.Resource (RE.Padding {pointer = member_p; size}, lrt)           
        ) components LRT.I
    in
    let st = ST.ST_Ctype (Sctypes.Struct tag) in
    let rt = 
      Computational ((struct_pointer, BT.Loc), 
      Constraint (LC (IT.Representable (ST_Pointer, S struct_pointer)),
      Constraint (LC (Aligned (st, S struct_pointer)),
      (* Constraint (LC (EQ (AllocationSize (S struct_pointer), Num size)), *)
      lrt @@ 
      Constraint (LC (IT.Representable (st, struct_value)), LRT.I))))
    in
    return rt
  in


  let* closed_stored_predicate_definition = 
    let open RT in
    let open LRT in
    let struct_value_s = Sym.fresh () in
    (* let size = Memory.size_of_struct loc tag in *)
    let* def_members = get_struct_members tag in
    let* layout = struct_layout loc def_members tag in
    let clause struct_pointer = 
      let (lrt, values) = 
        List.fold_right (fun (offset, size, member_or_padding) (lrt, values) ->
            let member_p = Offset (struct_pointer, Num offset) in
            match member_or_padding with
            | Some (member, sct) ->
               let member_v = Sym.fresh () in
               let resource = match sct with
                 | Sctypes.Struct tag ->
                    RE.Predicate {pointer = member_p; name = Tag tag; args = [member_v]}
                 | _ -> 
                    RE.Points {pointer = member_p; pointee = member_v; size}
               in
               let lrt = 
                 LRT.Logical ((member_v, LS.Base (BT.of_sct sct)), 
                 LRT.Resource (resource, lrt))
               in
               let value = (member, S member_v) :: values in
               (lrt, value)
            | None ->
               let lrt = LRT.Resource (RE.Padding {pointer = member_p; size}, lrt) in
               (lrt, values)
          ) layout (LRT.I, [])
      in
      let value = IT.Struct (tag, values) in
      let st = ST.ST_Ctype (Sctypes.Struct tag) in
      let lrt = 
        Constraint (LC (IT.Representable (ST_Pointer, struct_pointer)),
        Constraint (LC (Aligned (st, struct_pointer)),
        lrt @@ Constraint (LC (IT.Representable (st, value)), LRT.I)))
      in
      let constr = LC (IT.EQ (S struct_value_s, value)) in
      (lrt, constr)
    in
    let predicate struct_pointer = 
      Predicate {pointer = struct_pointer; 
                 name = Tag tag; 
                 args = [struct_value_s]} 
    in
    let unpack_function struct_pointer = 
      let (lrt, constr) = clause struct_pointer in
      LFT.Logical ((struct_value_s, LS.Base (Struct tag)), 
      LFT.Resource (predicate struct_pointer,
      LFT.I (LRT.concat lrt (LRT.Constraint (constr, LRT.I)))))
    in
    let pack_function struct_pointer = 
      let (arg_lrt, constr) = clause struct_pointer in
      LFT.of_lrt arg_lrt
      (LFT.I
        (LRT.Logical ((struct_value_s, LS.Base (Struct tag)), 
         LRT.Resource (predicate struct_pointer,
         LRT.Constraint (constr, LRT.I)))))
    in
    return (Global.{pack_function; unpack_function})
  in


  let open Global in
  let decl = { members; closed_stored; closed_stored_predicate_definition } in
  return decl











let make_owned_pointer struct_decls pointer stored_type rt = 
  let open RT in
  let (Computational ((pointee,bt),lrt)) = rt in
  let size = Memory.size_of_stored_type stored_type in
  let points = RE.Points {pointer = S pointer; pointee; size} in
  Computational ((pointer,Loc),
  Logical ((pointee, Base bt), 
  Resource ((points, 
  Constraint (LC (IT.Representable (ST_Pointer, S pointer)),
  Constraint (LC (IT.Aligned (stored_type, S pointer)),
  (* Constraint (LC (EQ (AllocationSize (S pointer), Num size)), *)
  lrt))))))



let rec rt_of_pointer_sct loc struct_decls (pointer : Sym.t) sct = 
  let open RT in
  begin match sct with
  | Sctypes.Struct tag when struct_predicates ->
     let pointee = Sym.fresh () in
     let predicate = 
       Predicate {pointer = S pointer; name = Tag tag; args = [pointee]} in
     let rt = 
       Computational ((pointer, BT.Loc), 
       Logical ((pointee, Base (BT.Struct tag)), 
       Resource (predicate, I)))
     in
     return rt
  | Sctypes.Struct tag ->
     let open Global in
     let* decl = match SymMap.find_opt tag struct_decls with
       | Some decl -> return decl
       | None -> fail loc (Missing_struct tag)
     in
     let rt = RT.freshify decl.closed_stored in
     let Computational ((s',_), _) = rt in
     let rt = RT.subst_var {before = s'; after = pointer} rt in
     return rt
  | Sctypes.Void -> 
     Debug_ocaml.error "todo: void*"
  | _ ->
     let st = ST.of_ctype sct in
     let* rt = rt_of_sct loc struct_decls (Sym.fresh ()) sct in
     return (make_owned_pointer struct_decls pointer st rt)
  end

and rt_of_sct loc struct_decls (s : Sym.t) sct =
  let open RT in
  let open Sctypes in
  match sct with
  | Pointer (_qualifiers, ct) ->
     rt_of_pointer_sct loc struct_decls s ct
  | _ ->
     let bt = BT.of_sct sct in
     let rt = 
       Computational ((s, bt), 
       Constraint (LC (IT.Representable (ST_Ctype sct, S s)),I))
     in
     return rt



(* function types *)


let update_values_lrt lrt =
  let subst_non_pointer = LRT.subst_var_fancy ~re_subst_var:RE.subst_non_pointer in
  let rec aux = function
    | LRT.Logical ((s,ls),lrt) ->
       let s' = Sym.fresh () in
       let lrt' = subst_non_pointer {before=s;after=s'} lrt in
       LRT.Logical ((s',ls), aux lrt')
    | LRT.Resource (re,lrt) -> LRT.Resource (re,aux lrt)
    | LRT.Constraint (lc,lrt) -> LRT.Constraint (lc,aux lrt)
    | LRT.I -> LRT.I
  in
  aux lrt

let make_fun_spec loc struct_decls args ret_sct = 
  let open FT in
  let open RT in
  let* (names, arg_rts, args, rets) = 
    ListM.fold_rightM (fun (msym, sct) (names, arg_rts, args, rets) ->
        let oname = Option.bind msym Sym.name in
        let sl = Sym.fresh_onamed oname in
        let names = match oname with
          | Some ident -> StringMap.add ident sl names
          | None -> names
        in
        let* arg_rt = rt_of_pointer_sct loc struct_decls sl sct in
        let arg_rts = (oname, arg_rt) :: arg_rts in
        let arg = FT.of_rt arg_rt in
        let args = Tools.comp arg args in
        let ret = update_values_lrt (RT.lrt arg_rt) in
        return (names, arg_rts, args, LRT.concat ret rets)
      ) 
      args (StringMap.empty, [], (fun ft -> ft), I)
  in
  let* (Computational ((ret_name,bound),ret)) = 
    rt_of_sct loc struct_decls (Sym.fresh ()) ret_sct in
  let ftyp = args (I (RT.Computational ((ret_name,bound), LRT.concat ret rets))) in
  return (names, ftyp, arg_rts)





(* unused currently: picking some default types for labels *)
let make_label_spec (loc : Loc.t) (ftyp : FT.t) 
                    (struct_decls : Global.struct_decls) 
                    (args : (Sym.t option * Sctypes.t) list) : (LT.t, type_error) m =
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
         ListM.fold_leftM (fun args (msym, sct) ->
             let s = Sym.fresh_onamed (Option.bind msym Sym.name) in
             let* arg_rt = rt_of_pointer_sct loc struct_decls s sct in
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




