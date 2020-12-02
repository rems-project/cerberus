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
         then [Global.{offset = position; size = to_pad; member_or_padding = None}] 
         else [] 
       in
       let member = [Global.{offset; size; member_or_padding = Some (member, sct)}] in
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

  let* layout = 
    struct_layout loc fields tag
  in

  let* closed_stored =
    let open RT in
    let open LRT in
    let rec aux loc tag struct_p = 
      let* def_members = get_struct_members tag in
      let* layout = struct_layout loc def_members tag in
      let* members = 
        ListM.mapM (fun Global.{offset; size; member_or_padding} ->
            let pointer = IT.Offset (struct_p, Num offset) in
            match member_or_padding with
            | None -> return ([(pointer, size, None)], [])
            | Some (member, sct) -> 
               let (Sctypes.Sctype (annots, sct_)) = sct in
               match sct_ with
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
             LRT.Resource (RE.Block {pointer = member_p; size; block_type = Padding}, lrt)           
        ) components LRT.I
    in
    let st = ST.ST_Ctype (Sctypes.Sctype ([], Struct tag)) in
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
        List.fold_right (fun Global.{offset; size; member_or_padding} (lrt, values) ->
            let member_p = Offset (struct_pointer, Num offset) in
            match member_or_padding with
            | Some (member, sct) ->
               let member_v = Sym.fresh () in
               let (Sctypes.Sctype (annots, sct_)) = sct in
               let resource = match sct_ with
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
               let lrt = LRT.Resource (RE.Block {pointer = member_p; size; block_type = Padding}, lrt) in
               (lrt, values)
          ) layout (LRT.I, [])
      in
      let value = IT.Struct (tag, values) in
      let st = ST.ST_Ctype (Sctypes.Sctype ([], Sctypes.Struct tag)) in
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
  let decl = { layout; closed_stored; closed_stored_predicate_definition } in
  return decl










let make_unowned_pointer pointer stored_type = 
  let open RT in
  Computational ((pointer,Loc),
  Constraint (LC (IT.Representable (ST_Pointer, S pointer)),
  Constraint (LC (IT.Aligned (stored_type, S pointer)),
  (* Constraint (LC (EQ (AllocationSize (S pointer), Num size)), *)
  LRT.I)))

let make_uninit_pointer pointer stored_type = 
  let open RT in
  let size = Memory.size_of_stored_type stored_type in
  let uninit = RE.Block {pointer = S pointer; size; block_type = Uninit} in
  Computational ((pointer,Loc),
  Resource ((uninit, 
  Constraint (LC (IT.Representable (ST_Pointer, S pointer)),
  Constraint (LC (IT.Aligned (stored_type, S pointer)),
  (* Constraint (LC (EQ (AllocationSize (S pointer), Num size)), *)
  LRT.I)))))

let make_owned_pointer pointer stored_type rt = 
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




module AST = Parse_ast

let ownership_of_obj ownership obj = 
  let found = 
    List.find_opt (fun (obj',o) -> 
        AST.compare_obj_ String.compare obj obj' = 0
      ) ownership 
  in
  Option.map snd found


let rec rt_of_sct loc ownership obj struct_decls (sym : Sym.t) sct =
  let (Sctypes.Sctype (annots, sct_)) = sct in
  let loc = Loc.update loc (get_loc_ annots) in
  let open RT in
  let open Sctypes in
  match sct_ with
  | Pointer (_qualifiers, sct2) ->
     let (Sctypes.Sctype (annots, sct2_)) = sct2 in
     let open RT in
     let loc = Loc.update loc (get_loc_ annots) in
     let pointee = Sym.fresh () in
     begin match sct2_, ownership_of_obj ownership (AST.pointee_obj_ obj) with
     | Sctypes.Void, _ -> 
        Debug_ocaml.error "todo: void*"
     | _, Some (AST.Unowned) ->
        (make_unowned_pointer sym (ST.of_ctype sct2), [])
     | _, Some (AST.Block) ->
        (make_uninit_pointer sym (ST.of_ctype sct2), [])
     | Sctypes.Struct tag, None ->
        let predicate = 
          Predicate {pointer = S sym; name = Tag tag; args = [pointee]} in
        let rt = 
          Computational ((sym, BT.Loc), 
          Logical ((pointee, Base (BT.Struct tag)), 
          Resource (predicate, I)))
        in
        (rt, [(AST.pointee obj, pointee)])
     | _, None ->
        let (rt, objs) = 
          rt_of_sct loc ownership (AST.pointee obj) struct_decls pointee sct2 in
        let objs = (AST.pointee obj, pointee) :: objs in
        let rt = make_owned_pointer sym (ST.of_ctype sct2) rt in
        (rt,objs)
     end
  | _ ->
     let bt = BT.of_sct sct in
     let rt = 
       Computational ((sym, bt), 
       Constraint (LC (IT.Representable (ST_Ctype sct, S sym)),I))
     in
     let objs = [] in
     (rt, objs)



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



let plain_pointer_sct sct = 
  let qualifiers = 
    CF.Ctype.{const = false; restrict = false; volatile = false} 
  in
  Sctypes.Sctype ([], (Pointer (qualifiers, sct)))




let make_fun_spec loc struct_decls args ret_sct attrs 
    : (FT.t * (AST.obj_map * (AST.obj_map * AST.obj_map)), type_error) m = 
  let open FT in
  let open RT in
  let* (pre_ownership, pre_constraints) = Assertions.requires loc attrs in
  let* (post_ownership, post_constraints) = Assertions.ensures loc attrs in
  let aux (sym, sct) (acc_global_objs, (acc_pre_objs, acc_post_objs), args, rets) =
    let name = Option.value (Sym.pp_string sym) (Sym.name sym) in
    let obj = AST.VariableLocation name in
    (* let sl = Sym.fresh_named name in *)
    let sct_lifted = plain_pointer_sct sct in
    let (arg_rt, pre_objs) = rt_of_sct loc pre_ownership obj struct_decls sym sct_lifted in
    let (ret_rt, post_objs) = rt_of_sct loc post_ownership obj struct_decls sym sct_lifted in
    ((obj, sym) :: acc_global_objs,
     (pre_objs @ acc_pre_objs, post_objs @ acc_post_objs), 
     Tools.comp (FT.of_rt arg_rt) args, 
     LRT.concat (RT.lrt ret_rt) rets)
  in
  let (everywhere_objs, (pre_objs, post_objs), args, rets) = 
    List.fold_right aux args ([], ([], []), (fun ft -> ft), I)
  in
  let ret_name = "ret" in
  let ret_sym = Sym.fresh_named ret_name in
  let (ret_rt, post_objs') = 
    rt_of_sct loc post_ownership (AST.Obj_ (Id ret_name)) struct_decls ret_sym ret_sct
  in
  let post_objs = (AST.Obj_ (AST.Id ret_name), ret_sym) :: post_objs @ post_objs' in
  let* definition_objs = Assertions.definitions loc attrs pre_objs in
  let* requires = Assertions.resolve_constraints loc pre_objs pre_constraints in
  print stderr (item "pre_ownership" (Pp.list (fun (obj_,_) -> AST.pp_obj_ obj_) pre_ownership ));
  print stderr (item "pre_objs" (Pp.list (fun (obj_,_) -> AST.pp_obj obj_) pre_objs ));
  print stderr (item "post_ownership" (Pp.list (fun (obj_,_) -> AST.pp_obj_ obj_) post_ownership ));
  print stderr (item "post_objs" (Pp.list (fun (obj_,_) -> AST.pp_obj obj_) post_objs ));
  let* ensures = Assertions.resolve_constraints loc (definition_objs @ post_objs) post_constraints in
  let rt = RT.concat ret_rt (LRT.concat rets (LRT.mConstraints ensures LRT.I)) in
  let ftyp = args (FT.mConstraints requires (I rt)) in
  return (ftyp, (everywhere_objs @ definition_objs, (pre_objs,post_objs)))



let make_label_spec 
      (loc : Loc.t)
      fglobal_objs
      struct_decls
      (fargs : (Sym.t * Sctypes.t) list) 
      (args : (Sym.t option * Sctypes.t) list) 
      attrs = 
  let* (pre_ownership, pre_constraints) = Assertions.requires loc attrs in
  let aux1 (sym, sct) (acc_pre_objs, args) =
    let name = Option.value (Sym.pp_string sym) (Sym.name sym) in
    let obj = AST.VariableLocation name in
    let sct_lifted = plain_pointer_sct sct in
    let (arg_rt, pre_objs) = rt_of_sct loc pre_ownership obj struct_decls sym sct_lifted in
    (pre_objs @ acc_pre_objs, Tools.comp (LT.of_lrt (RT.lrt arg_rt)) args)
  in
  let (pre_objs, fargs_ftt) = List.fold_right aux1 fargs ([], (fun ft -> ft)) in
  let aux2 (msym, sct) (acc_pre_objs, args) =
    let sym = Option.value (Sym.fresh ()) msym in
    let name = Option.value (Sym.pp_string sym) (Sym.name sym) in
    let obj = AST.Obj_ (AST.Id name) in
    let (arg_rt, pre_objs) = rt_of_sct loc pre_ownership obj struct_decls sym sct in
    (pre_objs @ acc_pre_objs, Tools.comp (LT.of_rt arg_rt) args)
  in
  let (pre_objs, args_ftt) = List.fold_right aux2 args (pre_objs, fargs_ftt) in
  let* requires = Assertions.resolve_constraints loc (fglobal_objs @ pre_objs) pre_constraints in
  let ltyp = args_ftt (LT.mConstraints requires (I False.False)) in
  return ltyp
