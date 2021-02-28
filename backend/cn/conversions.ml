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
open Path.LabeledName
open Assertions


module StringMap = Map.Make(String)
module SymSet = Set.Make(Sym)




let get_loc_ annots = Cerb_frontend.Annot.get_loc_ annots





let annot_of_ct (CF.Ctype.Ctype (annot,_)) = annot



let sct_of_ct loc ct = 
  match Sctypes.of_ctype ct with
  | Some ct -> return ct
  | None -> fail loc (Unsupported (!^"ctype" ^^^ CF.Pp_core_ctype.pp_ctype ct))





(* base types *)

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
       let* rest = aux members (Z.add_big_int offset size) in
       return (padding @ member @ rest)
  in
  (aux members Z.zero)



module CA = CF.Core_anormalise

let struct_decl loc (tagDefs : (CA.st, CA.ut) CF.Mucore.mu_tag_definitions) fields (tag : BT.tag) = 
  let open Global in

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


  let* stored_struct_predicate = 
    let open RT in
    let open LRT in
    let struct_value_s = Sym.fresh () in
    let struct_pointer_s = Sym.fresh () in
    let struct_pointer_t = sym_ (Loc, struct_pointer_s) in
    (* let size = Memory.size_of_struct loc tag in *)
    let* def_members = get_struct_members tag in
    let* layout = struct_layout loc def_members tag in
    let clause = 
      let (lrt, values) = 
        List.fold_right (fun {offset; size; member_or_padding} (lrt, values) ->
            let member_p = addPointer_ (struct_pointer_t, num_ offset) in
            match member_or_padding with
            | Some (member, sct) ->
               let member_v = Sym.fresh () in
               let (Sctypes.Sctype (annots, sct_)) = sct in
               let resource = match sct_ with
                 | Sctypes.Struct tag ->
                    RE.Predicate {name = Tag tag; iargs = [member_p]; oargs = [member_v]}
                 | _ -> 
                    RE.Points {pointer = member_p; pointee = member_v; size}
               in
               let bt = BT.of_sct sct in
               let lrt = 
                 LRT.Logical ((member_v, LS.Base bt), 
                 LRT.Resource (resource, lrt))
               in
               let value = (member, sym_ (bt, member_v)) :: values in
               (lrt, value)
            | None ->
               let lrt = 
                 LRT.Resource (RE.Block {pointer = member_p; size; block_type = Padding}, lrt)
               in
               (lrt, values)
          ) layout (LRT.I, [])
      in
      let value = IT.struct_ (tag, values) in
      let ct = Sctypes.Sctype ([], Sctypes.Struct tag) in
      let lrt = lrt @@ Constraint (LC (IT.representable_ (ct, value)), LRT.I) in
      let constr = LC (IT.eq_ (sym_ (BT.Struct tag, struct_value_s), value)) in
      (lrt, constr)
    in
    let predicate = 
      Predicate {name = Tag tag; 
                 iargs = [struct_pointer_t];
                 oargs = [struct_value_s]} 
    in
    let unpack_function = 
      let (lrt, constr) = clause in
      LFT.Logical ((struct_value_s, LS.Base (Struct tag)), 
      LFT.Resource (predicate,
      LFT.I (LRT.concat lrt (LRT.Constraint (constr, LRT.I)))))
    in
    let pack_function = 
      let (arg_lrt, constr) = clause in
      LFT.of_lrt arg_lrt
      (LFT.I
        (LRT.Logical ((struct_value_s, LS.Base (Struct tag)), 
         LRT.Resource (predicate,
         LRT.Constraint (constr, LRT.I)))))
    in
    let def = 
      {pack_function; 
       unpack_function;
       pointer = struct_pointer_s;
       value = struct_value_s
      }
    in
    return def
  in

  let decl = { layout; stored_struct_predicate } in
  return decl








let make_owned loc label pointer path sct =
  let open Sctypes in
  let label = Assertions.label_name label in
  match sct with
  | Sctype (_, Void) ->
     fail loc (Generic !^"cannot make owned void* pointer")
     (* let size = Sym.fresh () in
      * let r = 
      *   [RE.Block {pointer = pointer_it; 
      *              size;
      *              block_type = Nothing}]
      * in
      * let l = [(size, LS.Base Integer)] in
      * let mapping = 
      *   [{path = Path.predarg Block path "size"; sym = size; bt = Integer}] in
      * return (l, r, [], mapping) *)
  | Sctype (_, Struct tag) ->
     let pointee = Sym.fresh () in
     let r = 
       [RE.Predicate {name = Tag tag; 
                      iargs = [sym_ (BT.Loc, pointer)];
                      oargs = [pointee]}]
     in
     let l = [(pointee, LS.Base (Struct tag))] in
     let mapping = 
       [{path = Path.pointee (Some label) path; sym = pointee; bt = Struct tag}] in
     return (l, r, [], mapping)
  | sct -> 
     let pointee = Sym.fresh () in
     let r = 
       [RE.Points {pointer = sym_ (BT.Loc, pointer); 
                   pointee; 
                   size = Memory.size_of_ctype sct}]
     in
     let bt = BT.of_sct sct in
     let l = [(pointee, LS.Base bt)] in
     let c = [LC (good_value pointee sct)] in
     let mapping = 
       [{path = Path.pointee (Some label) path; sym = pointee; bt}] in
     return(l, r, c, mapping)


let make_region loc pointer_it size =
  (* let open Sctypes in *)
  let r = [RE.Region {pointer = pointer_it; size}] in
  return ([], r, [], [])


let make_block loc pointer path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     fail loc (Generic !^"cannot make void* pointer a block")
  | _ -> 
     let r = 
       [RE.Block {pointer = sym_ (BT.Loc, pointer); 
                  size = Memory.size_of_ctype sct;
                  block_type = Nothing}]
     in
     return ([], r, [], [])

let make_pred loc pred (predargs : Path.predarg list) iargs = 
  let* def = match Global.StringMap.find_opt pred Global.builtin_predicates with
    | Some def -> return def
    | None -> fail loc (Missing_predicate pred)
  in
  let* (mapping, l) = 
    ListM.fold_rightM (fun (oarg, LS.Base bt) (mapping, l) ->
        let s = Sym.fresh () in
        let l = (s, LS.Base bt) :: l in
        let mapping = match Sym.name oarg with
          | Some name -> 
             let item = 
               {path = Path.predarg pred predargs name; 
                sym = s; bt = bt} 
             in
             item :: mapping 
          | None -> []
        in
        return (mapping, l)
      ) def.oargs ([], [])
  in
  let oargs = List.map fst l in
  let r = [RE.Predicate {name = Id pred; iargs; oargs}] in
  return (l, r, [], mapping)





type funinfo_extra = {
    init_mapping : mapping;
    globs : Parse_ast.gargs;
    fargs : Parse_ast.aargs;
  }


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
  


let apply_ownership_spec label var_typs mapping (loc, (pred,predargs)) =
  let open Path in
  match pred, predargs with
  | "Owned", [PathArg path] ->
     begin match Path.deref_path path with
     | None -> fail loc (Generic (!^"cannot assign ownership of" ^^^ (Path.pp path)))
     | Some (bn, derefs) -> 
        let* sct = type_of__vars loc var_typs bn.v derefs in
        let* (_, sym) = Assertions.resolve_path loc mapping path in
        match sct with
        | Sctype (_, Pointer (_, sct2)) ->
           make_owned loc label sym (Path.var bn) sct2
        | _ ->
          fail loc (Generic (Path.pp path ^^^ !^"is not a pointer"))       
     end
  | "Owned", _ ->
     fail loc (Generic !^"Owned predicate takes 1 argument, which has to be a path")

  | "Block", [PathArg path] ->
     begin match Path.deref_path path with
     | None -> fail loc (Generic (!^"cannot assign ownership of" ^^^ (Path.pp path)))
     | Some (bn, derefs) -> 
        let* sct = type_of__vars loc var_typs bn.v derefs in
        let* (_, sym) = Assertions.resolve_path loc mapping path in
        match sct with
        | Sctype (_, Pointer (_, sct2)) ->
           make_block loc sym (Path.var bn) sct2
        | _ ->
          fail loc (Generic (Path.pp path ^^^ !^"is not a pointer"))       
     end
  | "Block", _ ->
     fail loc (Generic !^"Block predicate takes 1 argument, which has to be a path")

  | "Region", [pointer_arg; size_arg] ->
     let* pointer_it = Assertions.resolve_predarg loc mapping pointer_arg in
     let* size_it = Assertions.resolve_predarg loc mapping size_arg in
     make_region loc pointer_it size_it
  | "Region", _ ->
     fail loc (Generic !^"Region predicate takes 2 arguments, a path and a size")

  | _, _ ->
     let* iargs_resolved = 
       ListM.mapM (Assertions.resolve_predarg loc mapping) predargs
     in
     make_pred loc pred predargs iargs_resolved


let aarg_item l (aarg : aarg) =
  let path = Path.addr aarg.name in
  {path; sym = aarg.asym; bt = BT.Loc}

let varg_item l (varg : varg) =
  let bn = {v = varg.name; label = Some (Assertions.label_name l)} in
  let path = Path.var bn in
  {path; sym = varg.vsym; bt = BT.of_sct varg.typ} 

let garg_item l (garg : garg) =
  let path = Path.addr garg.name in
  {path; sym = garg.lsym; bt = BT.of_sct garg.typ} 


let make_fun_spec loc struct_decls globals arguments ret_sct attrs 
    : (FT.t * funinfo_extra, type_error) m = 
  let open FT in
  let open RT in
  let* typ = Assertions.parse_function_type attrs globals (ret_sct, arguments) in

  let (FT (FA {globs; fargs}, pre, FRet ret, post)) = typ in

  let var_typs = 
    List.map (fun (garg : garg) -> (garg.name, garg.typ)) globs @
    List.map (fun (aarg : aarg) -> (aarg.name, aarg.typ)) fargs @
    [(ret.name, ret.typ)]
  in

  let iA, iL, iR, iC = [], [], [], [] in
  let oL, oR, oC = [], [], [] in
  let mapping = [] in


  (* globs *)
  let* (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) garg ->
        let item = garg_item Pre garg in
        let* (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> make_owned loc Pre garg.lsym item.path garg.typ 
          | None -> return ([], [], [], [])
        in
        return (iL @ l, iR @ r, iC @ c, (item :: mapping') @ mapping)
      )
      (iL, iR, iC, mapping) globs
  in

  (* fargs *)
  let* (iA, iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iA, iL, iR, iC, mapping) aarg ->
        let a = [(aarg.asym, BT.Loc)] in
        let item = aarg_item Pre aarg in
        let* (l, r, c, mapping') = make_owned loc Pre aarg.asym item.path aarg.typ in
        let c = LC (good_value aarg.asym (pointer_sct aarg.typ)) :: c in
        return (iA @ a, iL @ l, iR @ r, iC @ c, (item :: mapping') @ mapping)
      )
      (iA, iL, iR, iC, mapping) fargs
  in

  let (FPre (pre_resources, pre_constraints)) = pre in

  let* (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) spec ->
        let* (l, r, c, mapping') = apply_ownership_spec Pre var_typs mapping spec in
        return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
      )
      (iL, iR, iC, mapping) pre_resources
  in
  let* iC = 
    let* lcs = Assertions.resolve_constraints mapping pre_constraints in
    return (lcs @ iC)
  in

  let init_mapping = mapping in

  (* ret *)
  let (oA, oC, mapping) = 
    let item = varg_item Post ret in
    let c = [LC (good_value ret.vsym ret.typ)] in
    ((ret.vsym, item.bt), c, item :: mapping)
  in

  (* globs *)
  let* (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) garg ->
        let item = garg_item Post garg in
        let* (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> make_owned loc Post garg.lsym item.path garg.typ 
          | None -> return ([], [], [], [])
        in
        return (oL @ l, oR @ r, oC @ c, (item :: mapping') @ mapping)
      )
      (oL, oR, oC, mapping) globs
  in

  (* fargs *)
  let* (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) aarg ->
        let item = aarg_item Post aarg in
        let* (l, r, c, mapping') = make_owned loc Post aarg.asym item.path aarg.typ in
        let c = LC (good_value aarg.asym (pointer_sct aarg.typ) ):: c in
        return (oL @ l, oR @ r, oC @ c, (item :: mapping') @ mapping)
      )
      (oL, oR, oC, mapping) fargs
  in

  let (FPost (post_resources, post_constraints)) = post in

  let* (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) spec ->
        let* (l, r, c, mapping') = apply_ownership_spec Post var_typs mapping spec in
        return (oL @ l, oR @ r, oC @ c, mapping' @ mapping)
      )
      (oL, oR, oC, mapping) post_resources
  in

  let* oC = 
    let* lcs = Assertions.resolve_constraints mapping post_constraints in
    return (lcs @ oC)
  in

  let lrt = LRT.mLogicals oL (LRT.mResources oR (LRT.mConstraints oC LRT.I)) in
  let rt = RT.mComputational oA lrt in
  let lft = FT.mLogicals iL (FT.mResources iR (FT.mConstraints iC (FT.I rt))) in
  let ft = FT.mComputationals iA lft in
  return (ft, {init_mapping; globs; fargs})


  
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
    List.map (fun (garg : garg) -> (garg.name, garg.typ)) globs @
    List.map (fun (aarg : aarg) -> (aarg.name, aarg.typ)) fargs @
    List.map (fun (aarg : aarg) -> (aarg.name, aarg.typ)) largs
  in

  let iA, iL, iR, iC = [], [], [], [] in
  let mapping = extra.init_mapping in

  (* globs *)
  let* (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) garg ->
        let item = garg_item (Inv lname) garg in
        let* (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> make_owned loc (Inv lname) garg.lsym item.path garg.typ 
          | None ->  return ([], [], [], [])
        in
        return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
      )
      (iL, iR, iC, mapping) globs
  in

  (* fargs *)
  let* (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) aarg ->
        let item = aarg_item (Inv lname) aarg in
        let* (l, r, c, mapping') = make_owned loc (Inv lname) aarg.asym item.path aarg.typ in
        return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
      )
      (iL, iR, iC, mapping) fargs
  in

  (* largs *)
  let* (iA, iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iA, iL, iR, iC, mapping) aarg ->
        let a = [(aarg.asym, BT.Loc)] in
        let item = aarg_item (Inv lname) aarg in
        let* (l, r, c, mapping') = make_owned loc (Inv lname) aarg.asym item.path aarg.typ in
        let c = LC (good_value aarg.asym (pointer_sct aarg.typ)) :: c in
        return (iA @ a, iL @ l, iR @ r, iC @ c, (item :: mapping') @ mapping)
      )
      (iA, iL, iR, iC, mapping) largs
  in


  let (LInv (pre_resources, pre_constraints)) = inv in
  let* (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) spec ->
        let* (l, r, c, mapping') = apply_ownership_spec (Inv lname) var_typs mapping spec in
        return (iL @ l, iR @ r, iC @ c, mapping @ mapping')
      )
      (iL, iR, iC, mapping) pre_resources
  in
  let* iC = 
    let* lcs = Assertions.resolve_constraints mapping pre_constraints in
    return (iC @ lcs)
  in

  let llt = LT.mLogicals iL (LT.mResources iR (LT.mConstraints iC (LT.I False.False))) in
  let lt = LT.mComputationals iA llt in
  return (lt, mapping)




