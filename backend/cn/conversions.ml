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
open Sctypes
open Mapping
open Path.LabeledName
open Ast
open Predicates


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
     let@ bt = bt_of_core_base_type loc bt in
     return (BT.List bt)
  | BTy_tuple bts -> 
     let@ bts = ListM.mapM (bt_of_core_base_type loc) bts in
     return (BT.Tuple bts)
  | BTy_storable -> Debug_ocaml.error "BTy_storageble"
  | BTy_ctype -> Debug_ocaml.error "BTy_ctype"













module CA = CF.Core_anormalise

let struct_decl loc fields (tag : BT.tag) = 
  let open Global in

  let member_offset tag member = 
    let iv = CF.Impl_mem.offsetof_ival (CF.Tags.tagDefs ()) tag member in
    Memory.integer_value_to_num iv
  in

  let struct_layout loc members tag = 
    let rec aux members position =
      match members with
      | [] -> 
         return []
      | (member, (attrs, qualifiers, ct)) :: members ->
         let@ sct = sct_of_ct loc ct in
         let offset = member_offset tag member in
         let size = Memory.size_of_ctype sct in
         let to_pad = Z.sub offset position in
         let padding = 
           if Z.gt_big_int to_pad Z.zero 
           then [Global.{offset = position; size = to_pad; member_or_padding = None}] 
           else [] 
         in
         let member = [Global.{offset; size; member_or_padding = Some (member, sct)}] in
         let@ rest = aux members (Z.add_big_int offset size) in
         return (padding @ member @ rest)
    in
    (aux members Z.zero)
  in


  let@ layout = struct_layout loc fields tag in

  let@ stored_struct_predicate = 
    let open RT in
    let open LRT in
    let struct_pointer_s = Sym.fresh_named "p" in
    let struct_pointer_t = sym_ (Loc, struct_pointer_s) in
    let struct_value_s = Sym.fresh_named "v" in
    (* let size = Memory.size_of_struct loc tag in *)
    let clause = 
      let (lrt, values) = 
        List.fold_right (fun {offset; size; member_or_padding} (lrt, values) ->
            let member_p = addPointer_ (struct_pointer_t, z_ offset) in
            match member_or_padding with
            | Some (member, sct) ->
               let bt = BT.of_sct sct in
               let member_v = Sym.fresh () in
               let member_t = sym_ (bt, member_v) in
               let (Sctypes.Sctype (annots, sct_)) = sct in
               let resource = match sct_ with
                 | Sctypes.Struct tag ->
                    RE.Predicate {
                        name = Tag tag; 
                        iargs = [member_p]; 
                        oargs = [member_t];
                        unused = (* bool_ *) true;
                      }
                 | _ -> 
                    RE.Point {
                        pointer = member_p; 
                        content = Value member_t; 
                        size;
                        permission = q_ (1, 1);
                      }
               in
               let lrt = 
                 LRT.Logical ((member_v, Base bt),
                 LRT.Resource (resource, lrt)) in
               let value = (member, sym_ (bt, member_v)) :: values in
               (lrt, value)
            | None ->
               let resource = 
                 RE.Point {
                     pointer = member_p; 
                     size; 
                     content = Block Padding;
                     permission = q_ (1, 1);
                   }
               in
               let lrt = LRT.Resource (resource, lrt) in
               (lrt, values)
          ) layout (LRT.I, [])
      in
      let value = IT.struct_ (tag, values) in
      let ct = Sctypes.Sctype ([], Sctypes.Struct tag) in
      let lrt = lrt @@ Constraint (LC (IT.representable_ (ct, value)), LRT.I) in
      (lrt, value)
    in
    let def = 
      {pointer = struct_pointer_s;
       value = struct_value_s;
       clause;
      }
    in
    return def
  in

  let decl = { layout; stored_struct_predicate } in
  return decl








let make_owned loc label pointer path sct =
  let open Sctypes in
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
       [RE.Predicate {
            name = Tag tag; 
            iargs = [sym_ (BT.Loc, pointer)];
            oargs = [sym_ (BT.Struct tag, pointee)];
            unused = (* bool_ *) true;
       }]
     in
     let l = [(pointee, LS.Base (Struct tag))] in
     let mapping = 
       [{path = Path.pointee (Some label) path; sym = pointee; bt = Struct tag}] in
     return (l, r, [], mapping)
  | sct -> 
     let pointee = Sym.fresh () in
     let bt = BT.of_sct sct in
     let r = 
       [RE.Point {
            pointer = sym_ (BT.Loc, pointer); 
            content = Value (sym_ (bt, pointee)); 
            size = Memory.size_of_ctype sct;
            permission = q_ (1, 1);
       }]
     in
     let l = [(pointee, LS.Base bt)] in
     let c = [LC (good_value pointee sct)] in
     let mapping = 
       [{path = Path.pointee (Some label) path; sym = pointee; bt}] in
     return(l, r, c, mapping)


let make_region loc pointer size =
  (* let open Sctypes in *)
  let resource = Resources.region pointer size (q_ (1, 1)) in
  return ([], [resource], [], [])


let make_block loc pointer path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     fail loc (Generic !^"cannot make void* pointer a block")
  | _ -> 
     let r = 
       [RE.Point {
            pointer = sym_ (BT.Loc, pointer); 
            size = Memory.size_of_ctype sct;
            content = Block Nothing;
            permission = q_ (1, 1);
       }]
     in
     return ([], r, [], [])

let make_pred loc pred (predargs : Path.predarg list) iargs = 
  let@ def = match Global.StringMap.find_opt pred Global.builtin_predicates with
    | Some def -> return def
    | None -> fail loc (Missing_predicate pred)
  in
  let@ (mapping, l) = 
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
  let oargs = 
    List.map (fun (s, LS.Base bt) ->
        sym_ (bt, s)
      )l
  in
  let r = 
    RE.Predicate {
        name = Id pred; 
        iargs; 
        oargs;
        unused = (* bool_ *) true;
      } 
  in
  return (l, [r], [], mapping)






let rec deref_path_pp name deref = 
  match deref with
  | 0 -> !^name
  | n -> star ^^ deref_path_pp name (n - 1)

let rec type_of__var loc typ name derefs = 
  match derefs with
  | 0 -> return typ
  | n ->
     let@ (Sctype (_, typ2_)) = type_of__var loc typ name (n - 1) in
     match typ2_ with
     | Pointer (_qualifiers, typ3) -> return typ3
     | _ -> fail loc (Generic (deref_path_pp name n ^^^ !^"is not a pointer"))

let type_of__vars loc var_typs name derefs = 
  match List.assoc_opt String.equal name var_typs with
  | None -> fail loc (Unbound_name (String name))
  | Some typ -> type_of__var loc typ name derefs
  




let resolve_path loc (mapping : mapping) (o : Path.t) : (BT.t * Sym.t, type_error) m = 
  let open Mapping in
  (* let () = print stderr (item "o" (Path.pp o)) in
   * let () = print stderr (item "mapping" (Mapping.pp mapping)) in *)
  let found = List.find_opt (fun {path;_} -> Path.equal path o) mapping in
  match found with
  | Some {sym; bt; _} -> 
     return (bt, sym)
  | None -> 
     fail loc (Generic (!^"term" ^^^ Path.pp o ^^^ !^"does not apply"))


(* change this to return unit IT.term, then apply index term type
   checker *)
let rec resolve_index_term loc mapping (it: Ast.term) 
        : (BT.t IT.term, type_error) m =
  let aux = resolve_index_term loc mapping in
  match it with
  | Lit (Integer i) -> 
     return (IT.z_ i)
  | Path o -> 
     let@ (bt,s) = resolve_path loc mapping o in
     return (IT.sym_ (bt, s))
  | ArithOp (Addition (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.add_ (it, it'))
  | ArithOp (Subtraction (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.sub_ (it, it'))
  | ArithOp (Multiplication (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.mul_ (it, it'))
  | ArithOp (Division (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.div_ (it, it'))
  | ArithOp (Exponentiation (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.exp_ (it, it'))
  | CmpOp (Equality (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.eq_ (it, it'))
  | CmpOp (Inequality (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.ne_ (it, it'))
  | CmpOp (LessThan (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.lt_ (it, it'))
  | CmpOp (GreaterThan (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.gt_ (it, it'))
  | CmpOp (LessOrEqual (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.le_ (it, it'))
  | CmpOp (GreaterOrEqual (it, it')) -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT.ge_ (it, it'))


let rec resolve_predarg loc mapping = function
  | Path.NumArg z -> 
     return (IT.z_ z)
  | Add (p,a) -> 
     let@ it = resolve_predarg loc mapping p in
     let@ it' = resolve_predarg loc mapping a in
     return (IT.add_ (it, it'))
  | Sub (p,a) -> 
     let@ it = resolve_predarg loc mapping p in
     let@ it' = resolve_predarg loc mapping a in
     return (IT.sub_ (it, it'))
  | AddPointer (p,a) -> 
     let@ it = resolve_predarg loc mapping p in
     let@ it' = resolve_predarg loc mapping a in
     return (IT.addPointer_ (it, it'))
  | SubPointer (p,a) -> 
     let@ it = resolve_predarg loc mapping p in
     let@ it' = resolve_predarg loc mapping a in
     return (IT.subPointer_ (it, it'))
  | MulPointer (p,a) -> 
     let@ it = resolve_predarg loc mapping p in
     let@ it' = resolve_predarg loc mapping a in
     return (IT.mulPointer_ (it, it'))
  | PathArg p ->
     let@ (ls, s) = resolve_path loc mapping p in
     return (IT.sym_ (ls, s))



let resolve_constraint loc mapping lc =
  let@ lc = resolve_index_term loc mapping lc in
  return (LogicalConstraints.LC lc)




let apply_ownership_spec label var_typs mapping (loc, {predicate;arguments}) =
  let open Path in
  match predicate, arguments with
  | "Owned", [PathArg path] ->
     begin match Path.deref_path path with
     | None -> fail loc (Generic (!^"cannot assign ownership of" ^^^ (Path.pp path)))
     | Some (bn, derefs) -> 
        let@ sct = type_of__vars loc var_typs bn.v derefs in
        let@ (_, sym) = resolve_path loc mapping path in
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
        let@ sct = type_of__vars loc var_typs bn.v derefs in
        let@ (_, sym) = resolve_path loc mapping path in
        match sct with
        | Sctype (_, Pointer (_, sct2)) ->
           make_block loc sym (Path.var bn) sct2
        | _ ->
          fail loc (Generic (Path.pp path ^^^ !^"is not a pointer"))       
     end
  | "Block", _ ->
     fail loc (Generic !^"Block predicate takes 1 argument, which has to be a path")

  | "Region", [pointer_arg; size_arg] ->
     let@ pointer_it = resolve_predarg loc mapping pointer_arg in
     let@ size_it = resolve_predarg loc mapping size_arg in
     make_region loc pointer_it size_it
  | "Region", _ ->
     fail loc (Generic !^"Region predicate takes 2 arguments, a path and a size")

  | _, _ ->
     let@ iargs_resolved = 
       ListM.mapM (resolve_predarg loc mapping) arguments
     in
     let@ result = make_pred loc predicate arguments iargs_resolved in
     return result


let aarg_item l (aarg : aarg) =
  let path = Path.addr aarg.name in
  {path; sym = aarg.asym; bt = BT.Loc}

let varg_item l (varg : varg) =
  let bn = {v = varg.name; label = Some l} in
  let path = Path.var bn in
  {path; sym = varg.vsym; bt = BT.of_sct varg.typ} 

let garg_item l (garg : garg) =
  let path = Path.addr garg.name in
  {path; sym = garg.lsym; bt = BT.of_sct garg.typ} 


let make_fun_spec loc fsym (fspec : function_spec)
    : (FT.t * Mapping.t, type_error) m = 
  let open FT in
  let open RT in
  let var_typs = 
    List.map (fun (garg : garg) -> (garg.name, garg.typ)) fspec.global_arguments @
    List.map (fun (aarg : aarg) -> (aarg.name, aarg.typ)) fspec.function_arguments @
    [(fspec.function_return.name, 
      fspec.function_return.typ)]
  in

  let iA, iL, iR, iC = [], [], [], [] in
  let oL, oR, oC = [], [], [] in
  let mapping = [] in

  (* globs *)
  let@ (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) garg ->
        let item = garg_item "start" garg in
        let@ (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> make_owned loc "start" garg.lsym item.path garg.typ 
          | None -> return ([], [], [], [])
        in
        return (iL @ l, iR @ r, iC @ c, (item :: mapping') @ mapping)
      )
      (iL, iR, iC, mapping) fspec.global_arguments
  in

  (* fargs *)
  let@ (iA, iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iA, iL, iR, iC, mapping) (aarg : aarg) ->
        let a = [(aarg.asym, BT.Loc)] in
        let item = aarg_item "start" aarg in
        let@ (l, r, c, mapping') = make_owned loc "start" aarg.asym item.path aarg.typ in
        let c = LC (good_value aarg.asym (pointer_sct aarg.typ)) :: c in
        return (iA @ a, iL @ l, iR @ r, iC @ c, (item :: mapping') @ mapping)
      )
      (iA, iL, iR, iC, mapping) fspec.function_arguments
  in

  let@ (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
           let@ (l, r, c, mapping') = 
             apply_ownership_spec "start" var_typs mapping (loc, cond) in
           return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc mapping cond in
           return (iL, iR, iC @ [c], mapping)
      )
      (iL, iR, iC, mapping) fspec.pre_condition
  in

  let init_mapping = mapping in

  (* ret *)
  let (oA, oC, mapping) = 
    let ret = fspec.function_return in
    let item = varg_item "end" ret in
    let c = [LC (good_value ret.vsym ret.typ)] in
    ((ret.vsym, item.bt), c, item :: mapping)
  in

  (* globs *)
  let@ (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) garg ->
        let item = garg_item "end" garg in
        let@ (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> make_owned loc "end" garg.lsym item.path garg.typ 
          | None -> return ([], [], [], [])
        in
        return (oL @ l, oR @ r, oC @ c, (item :: mapping') @ mapping)
      )
      (oL, oR, oC, mapping) fspec.global_arguments
  in

  (* fargs *)
  let@ (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) aarg ->
        let item = aarg_item "end" aarg in
        let@ (l, r, c, mapping') = make_owned loc "end" aarg.asym item.path aarg.typ in
        let c = LC (good_value aarg.asym (pointer_sct aarg.typ) ):: c in
        return (oL @ l, oR @ r, oC @ c, (item :: mapping') @ mapping)
      )
      (oL, oR, oC, mapping) fspec.function_arguments
  in

  let@ (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
           let@ (l, r, c, mapping') = 
             apply_ownership_spec "end" var_typs mapping (loc, cond) in
           return (oL @ l, oR @ r, oC @ c, mapping' @ mapping)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc mapping cond in
           return (oL, oR, oC @ [c], mapping)
      )
      (oL, oR, oC, mapping) fspec.post_condition
  in

  let lrt = LRT.mLogicals oL (LRT.mResources oR (LRT.mConstraints oC LRT.I)) in
  let rt = RT.mComputational oA lrt in
  let lft = FT.mLogicals iL (FT.mResources iR (FT.mConstraints iC (FT.I rt))) in
  let ft = FT.mComputationals iA lft in
  return (ft, init_mapping)


  
let make_label_spec
      (loc : Loc.t) 
      (lname : string)
      init_mapping
      (lspec: Ast.label_spec)
  =
  (* let largs = List.map (fun (os, t) -> (Option.value (Sym.fresh ()) os, t)) largs in *)
  let var_typs = 
    List.map (fun (garg : garg) -> (garg.name, garg.typ)) lspec.global_arguments @
    List.map (fun (aarg : aarg) -> (aarg.name, aarg.typ)) lspec.function_arguments @
    List.map (fun (aarg : aarg) -> (aarg.name, aarg.typ)) lspec.label_arguments
  in

  let iA, iL, iR, iC = [], [], [], [] in
  let mapping = init_mapping in

  (* globs *)
  let@ (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) garg ->
        let item = garg_item lname garg in
        let@ (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> make_owned loc lname garg.lsym item.path garg.typ 
          | None ->  return ([], [], [], [])
        in
        return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
      )
      (iL, iR, iC, mapping) lspec.global_arguments
  in

  (* fargs *)
  let@ (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) aarg ->
        let item = aarg_item lname aarg in
        let@ (l, r, c, mapping') = make_owned loc lname aarg.asym item.path aarg.typ in
        return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
      )
      (iL, iR, iC, mapping) lspec.function_arguments
  in

  (* largs *)
  let@ (iA, iL, iR, iC, mapping) = 
    (* In the label's argument list, the left-most arguments have the
       inner-most scope. In the mapping, we also want the arguments
       that are inner-most scoped-wise to be left-most. *)
    let@ (ia, iL, iR, iC, mapping') = 
      ListM.fold_leftM (fun (iA, iL, iR, iC, mapping) (aarg : aarg) ->
          let a = [(aarg.asym, BT.Loc)] in
          let item = aarg_item lname aarg in
          let@ (l, r, c, mapping') = make_owned loc lname aarg.asym item.path aarg.typ in
          let c = LC (good_value aarg.asym (pointer_sct aarg.typ)) :: c in
          return (iA @ a, iL @ l, iR @ r, iC @ c, (item :: mapping') @ mapping)
        )
        (iA, iL, iR, iC, []) lspec.label_arguments
    in
    return (ia, iL, iR, iC, List.rev mapping' @ mapping)
  in


  let@ (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
           let@ (l, r, c, mapping') = 
             apply_ownership_spec lname var_typs mapping (loc, cond) in
           return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc mapping cond in
           return (iL, iR, iC @ [c], mapping)
      )
      (iL, iR, iC, mapping) lspec.invariant
  in

  let llt = LT.mLogicals iL (LT.mResources iR (LT.mConstraints iC (LT.I False.False))) in
  let lt = LT.mComputationals iA llt in
  return (lt, mapping)





