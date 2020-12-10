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
open Parse_ast
open Sctypes
open Mapping
open BaseName


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

  (* let* closed_stored =
   *   let open RT in
   *   let open LRT in
   *   let rec aux loc tag struct_p = 
   *     let* def_members = get_struct_members tag in
   *     let* layout = struct_layout loc def_members tag in
   *     let* members = 
   *       ListM.mapM (fun Global.{offset; size; member_or_padding} ->
   *           let pointer = IT.Offset (struct_p, Num offset) in
   *           match member_or_padding with
   *           | None -> return ([(pointer, size, None)], [])
   *           | Some (member, sct) -> 
   *              let (Sctypes.Sctype (annots, sct_)) = sct in
   *              match sct_ with
   *              | Sctypes.Struct tag -> 
   *                 let* (components, s_value) = aux loc tag pointer in
   *                 return (components, [(member, s_value)])
   *              | _ ->
   *                 let v = Sym.fresh () in
   *                 let bt = BT.of_sct sct in
   *                 return ([(pointer, size, Some (v, bt))], [(member, S (bt, v))])
   *           ) layout
   *     in
   *     let (components, values) = List.split members in
   *     return (List.flatten components, IT.Struct (tag, List.flatten values))
   *   in
   *   let struct_pointer = Sym.fresh () in
   *   let* components, struct_value = aux loc tag (S (BT.Loc, struct_pointer)) in
   *   let lrt = 
   *     List.fold_right (fun (member_p, size, member_or_padding) lrt ->
   *         match member_or_padding with
   *         | Some (member_v, bt) ->
   *            LRT.Logical ((member_v, Base bt), 
   *            LRT.Resource (RE.Points {pointer = member_p; pointee = member_v; size}, lrt))
   *         | None ->
   *            LRT.Resource (RE.Block {pointer = member_p; size = Num size; block_type = Padding}, lrt)           
   *       ) components LRT.I
   *   in
   *   let st = ST.ST_Ctype (Sctypes.Sctype ([], Struct tag)) in
   *   let rt = 
   *     Computational ((struct_pointer, BT.Loc), 
   *     Constraint (LC (IT.Representable (ST_Pointer, S (BT.Loc, struct_pointer))),
   *     Constraint (LC (Aligned (st, S (BT.Loc, struct_pointer))),
   *     (\* Constraint (LC (EQ (AllocationSize (S struct_pointer), Num size)), *\)
   *     lrt @@ 
   *     Constraint (LC (IT.Representable (st, struct_value)), LRT.I))))
   *   in
   *   return rt
   * in *)


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
               let bt = BT.of_sct sct in
               let lrt = 
                 LRT.Logical ((member_v, LS.Base bt), 
                 LRT.Resource (resource, lrt))
               in
               let value = (member, S (bt, member_v)) :: values in
               (lrt, value)
            | None ->
               let lrt = LRT.Resource (RE.Block {pointer = member_p; size = Num size; block_type = Padding}, lrt) in
               (lrt, values)
          ) layout (LRT.I, [])
      in
      let value = IT.Struct (tag, values) in
      let st = ST.ST_Ctype (Sctypes.Sctype ([], Sctypes.Struct tag)) in
      let lrt = lrt @@ Constraint (LC (IT.Representable (st, value)), LRT.I) in
      let constr = LC (IT.EQ (S (BT.Struct tag, struct_value_s), value)) in
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
  let decl = { layout; closed_stored_predicate_definition } in
  return decl







let make_owned pointer path sct =
  let open Pred in
  let open Sctypes in
  let pointer_it = S (BT.Loc, pointer) in
  match sct with
  | Sctype (_, Void) ->
     let size = Sym.fresh () in
     let r = 
       [RE.Block {pointer = pointer_it; 
                  size = S (Integer, size); 
                  block_type = Nothing}]
     in
     let l = [(size, LS.Base Integer)] in
     let mapping = 
       [{path = Path.predarg Block path "size"; sym = size; bt = Integer}] in
     let c = [
         LC (IT.Representable (ST_Pointer, pointer_it));
         LC (IT.Aligned (ST_Ctype sct, pointer_it));
       ]
     in
     (l, r, c, mapping)
  | Sctype (_, Struct tag) ->
     let pointee = Sym.fresh () in
     let r = 
       [RE.Predicate {pointer = S (BT.Loc, pointer); 
                      name = Tag tag; 
                      args = [pointee]}]
     in
     let l = [(pointee, LS.Base (Struct tag))] in
     let c = [
         LC (IT.Representable (ST_Pointer, pointer_it));
         LC (IT.Aligned (ST_Ctype sct, pointer_it));
       ]
     in
     let mapping = 
       [{path = Path.pointee path; sym = pointee; bt = Struct tag}] in
     (l, r, c, mapping)
  | _ -> 
     let pointee = Sym.fresh () in
     let r = 
       [RE.Points {pointer = S (BT.Loc, pointer); 
                   pointee; 
                   size = Memory.size_of_ctype sct}]
     in
     let bt = BT.of_sct sct in
     let l = [(pointee, LS.Base bt)] in
     let c = [
         LC (IT.Representable (ST_Pointer, pointer_it));
         LC (IT.Aligned (ST_Ctype sct, pointer_it));
         LC (IT.Representable (ST_Ctype sct, S (bt, pointee)));
       ]
     in
     let mapping = 
       [{path = Path.pointee path; sym = pointee; bt}] in
     (l, r, c, mapping)


let make_block pointer path sct =
  let open Pred in
  let open Sctypes in
  let pointer_it = S (BT.Loc, pointer) in
  match sct with
  | Sctype (_, Void) ->
     let size = Sym.fresh () in
     let r = 
       [RE.Block {pointer = pointer_it; 
                  size = S (Integer, size); 
                  block_type = Nothing}]
     in
     let l = [(size, LS.Base Integer)] in
     let mapping = 
       [{path = Path.predarg Block path "size"; sym = size; bt = Integer}] in
     let c = [
         LC (IT.Representable (ST_Pointer, pointer_it));
         LC (IT.Aligned (ST_Ctype sct, pointer_it));
       ]
     in
     (l, r, c, mapping)
  | _ -> 
     let pointee = Sym.fresh () in
     let r = 
       [RE.Block {pointer = pointer_it; 
                  size = Num (Memory.size_of_ctype sct); 
                  block_type = Nothing}]
     in
     let bt = BT.of_sct sct in
     let l = [(pointee, LS.Base bt)] in
     let c = [
         LC (IT.Representable (ST_Pointer, pointer_it));
         LC (IT.Aligned (ST_Ctype sct, pointer_it));
       ]
     in
     let mapping = 
       [{path = Path.pointee path; sym = pointee; bt}] in
     (l, r, c, mapping)

let make_pred loc pointer pred path stored_type = 
  let* def = match Global.IdMap.find_opt pred Global.builtin_predicates with
    | Some def -> return def
    | None -> fail loc (Missing_predicate pred)
  in
  let pointer_it = S (BT.Loc, pointer) in
  let* (mapping, l) = 
    ListM.fold_rightM (fun (name, LS.Base bt) (mapping, l) ->
        let s = Sym.fresh_named name in
        let l = (s, LS.Base bt) :: l in
        let mapping = {path = Path.predarg (Pred pred) path name; sym = s; bt = bt} :: mapping in
        return (mapping, l)
      ) def.Global.arguments ([], [])
  in
  let args = List.map fst l in
  let r = [RE.Predicate {pointer = pointer_it; name = Id pred; args}] in
  return (l, r, [], mapping)





type funinfo_extra = 
  {mapping : mapping;
   globs : Parse_ast.aarg list;
   fargs : Parse_ast.aarg list}


let rec deref_path_pp name deref = 
  match deref with
  | 0 -> !^name
  | n -> star ^^ deref_path_pp name (n - 1)

let rec type_of__var loc typ name derefs = 
  match derefs with
  | 0 -> return typ
  | n ->
     let* (Sctype (_, typ2_)) = type_of__var loc typ name (n - 1) in
     match typ2_ with
     | Pointer (_qualifiers, typ3) -> return typ3
     | _ -> fail loc (Generic (deref_path_pp name n ^^^ !^"is not a pointer"))

let type_of__vars loc var_typs name derefs = 
  match List.assoc_opt String.equal name var_typs with
  | None -> fail loc (Unbound_name (String name))
  | Some typ -> type_of__var loc typ name derefs
  


let apply_ownership_spec var_typs mapping (loc, (pred,path)) =
  print stderr (item "path" (Path.pp path));
  match Path.deref_path path with
  | None ->
     fail loc (Generic (!^"cannot assign ownership of" ^^^ (Path.pp path)))
  | Some (bn, derefs) -> 
     let* sct = type_of__vars loc var_typs bn.v derefs in
     let* (_, sym) = Assertions.resolve_path loc mapping path in
     match sct with
     | Sctype (_, Pointer (_, sct2)) ->
        begin match pred with
        | Pred.Owned -> return (make_owned sym (Path.var bn) sct2)
        | Pred.Block -> return (make_owned sym (Path.var bn) sct2)
        | Pred.Pred id -> make_pred loc sym id (Path.var bn) sct2 
        end
     | _ -> 
        fail loc (Generic (Path.pp path ^^^ !^"is not a pointer"))


let aarg_item l (aarg : aarg) =
  let bn = {v = aarg.name; label = Assertions.label_name l} in
  let path = Path.addr bn in
  {path; sym = aarg.asym; bt = BT.Loc}


let varg_item l (varg : varg) =
  let bn = {v = varg.name; label = Assertions.label_name l} in
  let path = Path.var bn in
  {path; sym = varg.vsym; bt = BT.of_sct varg.typ}

let arg_item l arg =
  match arg with
  | Aarg aarg -> aarg_item l aarg
  | Varg varg -> varg_item l varg


let make_fun_spec loc struct_decls globals arguments ret_sct attrs 
    : (FT.t * funinfo_extra, type_error) m = 
  let open FT in
  let open RT in
  let* typ = Assertions.parse_function_type loc attrs globals (ret_sct, arguments) in

  let (FT (FA {globs; fargs}, pre, FRet ret, post)) = typ in

  let var_typs = 
    List.map (fun aarg -> (aarg.name, aarg.typ)) globs @
    List.map (fun aarg -> (aarg.name, aarg.typ)) fargs @
    [(ret.name, ret.typ)]
  in

  let iL, iR, iC = [], [], [] in
  let oL, oR, oC = [], [], [] in
  let mapping = [] in

  let iA = List.map (fun aarg -> (aarg.asym, BT.Loc)) fargs in
  (* globs and fargs *)
  let (iL, iR, iC, mapping) = 
    List.fold_left (fun (iL, iR, iC, mapping) aarg ->
        let item = aarg_item Pre aarg in
        let (l, r, c, mapping') = make_owned aarg.asym item.path aarg.typ in
        (iL @ l, iR @ r, iC @ c, mapping @ (item :: mapping'))
      )
      (iL, iR, iC, mapping) (globs @ fargs)
  in

  let (FPre (pre_resources, pre_constraints)) = pre in

  let* (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) spec ->
        let* (l, r, c, mapping') = apply_ownership_spec var_typs mapping spec in
        return (iL @ l, iR @ r, iC @ c, mapping @ mapping')
      )
      (iL, iR, iC, mapping) pre_resources
  in
  let* iC = 
    let* lcs = Assertions.resolve_constraints mapping pre_constraints in
    return (lcs @ iC)
  in

  let init_mapping = mapping in

  (* ret *)
  let (oA, mapping) = 
    let item = varg_item Post ret in
    ((ret.vsym, item.bt), item :: mapping)
  in

  (* defaults *)
  let (oL, oR, oC, mapping) = 
    List.fold_left (fun (oL, oR, oC, mapping) aarg ->
        let item = aarg_item Post aarg in
        let (l, r, c, mapping') = make_owned aarg.asym item.path aarg.typ in
        (oL @ l, oR @ r, oC @ c, mapping @ mapping')
      )
      (oL, oR, oC, mapping) (globs @ fargs)
  in

  let (FPost (post_resources, post_constraints)) = post in

  let* (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) spec ->
        let* (l, r, c, mapping') = apply_ownership_spec var_typs mapping spec in
        return (oL @ l, oR @ r, oC @ c, mapping @ mapping')
      )
      (oL, oR, oC, mapping) post_resources
  in


  print stderr (item "mapping" (Mapping.pp mapping));

  let* oC = 
    let* lcs = Assertions.resolve_constraints mapping post_constraints in
    return (lcs @ oC)
  in


  let lrt = LRT.mLogicals oL (LRT.mResources oR (LRT.mConstraints oC LRT.I)) in
  let rt = RT.mComputational oA lrt in
  let lft = FT.mLogicals iL (FT.mResources iR (FT.mConstraints iC (FT.I rt))) in
  let ft = FT.mComputationals iA lft in
  return (ft, {mapping = init_mapping; globs; fargs})


  
let make_label_spec
      (loc : Loc.t) 
      (lsym: Sym.t)
      (extra: funinfo_extra)
      (largs : (Sym.t option * Sctypes.t) list) 
      attrs = 

  let lname = match Sym.name lsym with
    | Some lname -> lname
    | None -> Sym.pp_string lsym (* check *)
  in
  let largs = List.map (fun (os, t) -> (Option.value (Sym.fresh ()) os, t)) largs in
  let* ltyp = Assertions.parse_label_type loc lname attrs extra.globs extra.fargs largs in

  let (LT (LA {globs; fargs; largs}, inv)) = ltyp in

  let var_typs = 
    List.map (fun (aarg : aarg) -> (aarg.name, aarg.typ)) globs @
    List.map (fun (aarg : aarg) -> (aarg.name, aarg.typ)) fargs @
    List.map (fun (varg : varg) -> (varg.name, varg.typ)) largs
  in

  let iA, iL, iR, iC = [], [], [], [] in
  let mapping = extra.mapping in


  (* globs and fargs *)
  let (iL, iR, iC, mapping) = 
    List.fold_left (fun (iL, iR, iC, mapping) aarg ->
        let item = aarg_item (Inv lname) aarg in
        let (l, r, c, mapping') = make_owned aarg.asym item.path aarg.typ in
        (iL @ l, iR @ r, iC @ c, mapping @ mapping')
      )
      (iL, iR, iC, mapping) (globs @ fargs)
  in
  (* largs *)
  let (iA, mapping) = 
    List.fold_left (fun (iA, mapping) varg ->
        let item = varg_item (Inv lname) varg in
        let a = (varg.vsym, item.bt) in
        (iA @ [a], mapping @ [item])
      )
      (iA, mapping) largs
  in

  let (LInv (pre_resources, pre_constraints)) = inv in
  let* (iL, iR, iC, mapping) = 
    ListM.fold_rightM (fun spec (iL, iR, iC, mapping) ->
        let* (l, r, c, mapping') = apply_ownership_spec var_typs mapping spec in
        return (l @ iL, r @ iR, c @ iC, mapping' @ mapping)
      )
      pre_resources (iL, iR, iC, mapping)
  in
  let* iC = 
    let* lcs = Assertions.resolve_constraints mapping pre_constraints in
    return (lcs @ iC)
  in

  let llt = LT.mLogicals iL (LT.mResources iR (LT.mConstraints iC (LT.I False.False))) in
  let lt = LT.mComputationals iA llt in
  return (lt, mapping)




