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
open Resources.RE
open Sctypes
open Mapping
open Ast.LabeledName
open Ast
open Predicates
open Memory


module StringMap = Map.Make(String)
module SymSet = Set.Make(Sym)




let get_loc_ annots = Cerb_frontend.Annot.get_loc_ annots





let annot_of_ct (CF.Ctype.Ctype (annot,_)) = annot



let sct_of_ct loc ct = 
  match Sctypes.of_ctype ct with
  | Some ct -> ct
  | None -> unsupported loc (!^"ctype" ^^^ CF.Pp_core_ctype.pp_ctype ct)





(* base types *)

let bt_of_core_object_type loc ot =
  let open CF.Core in
  match ot with
  | OTy_integer -> return BT.Integer
  | OTy_pointer -> return BT.Loc
  | OTy_array cbt -> Debug_ocaml.error "arrays"
  | OTy_struct tag -> return (BT.Struct tag)
  | OTy_union _tag -> Debug_ocaml.error "union types"
  | OTy_floating -> unsupported loc !^"floats"

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
         let sct = sct_of_ct loc ct in
         let offset = member_offset tag member in
         let size = Memory.size_of_ctype sct in
         let to_pad = Z.sub offset position in
         let padding = 
           if Z.gt_big_int to_pad Z.zero 
           then [{offset = position; size = to_pad; member_or_padding = None}] 
           else [] 
         in
         let member = [{offset; size; member_or_padding = Some (member, sct)}] in
         let@ rest = aux members (Z.add_big_int offset size) in
         return (padding @ member @ rest)
    in
    (aux members Z.zero)
  in

  let@ layout = struct_layout loc fields tag in

  return layout








let make_owned loc (layouts : Sym.t -> Memory.struct_layout) label (pointer : IT.t) path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     fail loc (Generic !^"cannot make owned void* pointer")
  | _ ->
     let pointee = Sym.fresh () in
     let pointee_bt = BT.of_sct sct in
     let pointee_t = sym_ (pointee, pointee_bt) in
     let l = [(pointee, pointee_bt)] in
     let mapping = [{path = Ast.pointee (Some label) path; it = pointee_t}] in
     let c = [good_value pointee_t sct] in
     let r = [predicate (Ctype sct) pointer [] [pointee_t; (bool_ true)]] in
     return (l, r, c, mapping)





let make_block loc (layouts : Sym.t -> Memory.struct_layout) (pointer : IT.t) path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     fail loc (Generic !^"cannot make owned void* pointer")
  | _ ->
     let pointee = Sym.fresh () in
     let pointee_bt = BT.of_sct sct in
     let pointee_t = sym_ (pointee, pointee_bt) in
     let l = [(pointee, pointee_bt)] in
     let mapping = [] in
     let r = [predicate (Ctype sct) pointer [] [pointee_t; (bool_ true)]] in
     return (l, r, [], mapping)

let make_pred loc pred (predargs : Ast.pred_arg list) pointer iargs = 
  let@ def = match Global.StringMap.find_opt pred Global.builtin_predicates with
    | Some def -> return def
    | None -> fail loc (Missing_predicate pred)
  in
  let@ (mapping, l) = 
    ListM.fold_rightM (fun (oarg, bt) (mapping, l) ->
        let s = Sym.fresh () in
        let l = (s, bt) :: l in
        let mapping = match Sym.name oarg with
          | Some name -> 
             let item = 
               {path = Ast.predarg pred predargs name; 
                it = sym_ (s, bt)} 
             in
             item :: mapping 
          | None -> []
        in
        return (mapping, l)
      ) def.oargs ([], [])
  in
  let oargs = List.map sym_ l in
  let r = 
    RE.Predicate {
        name = Id pred; 
        pointer = pointer;
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
  




let resolve_path loc layouts (mapping : mapping) (o : Ast.path) : (IT.typed, type_error) m = 
  let open Mapping in
  (* let () = print stderr (item "o" (Ast.pp_path false o)) in
   * let () = print stderr (item "mapping" (Mapping.pp mapping)) in *)
  let found = List.find_opt (fun {path;_} -> Ast.path_equal path o) mapping in
  match found with
  | Some {it; _} -> 
     return it
  | None -> 
     fail loc (Generic (!^"term" ^^^ Ast.pp_path false o ^^^ !^"does not apply"))



(* change this to return unit IT.term, then apply index term type
   checker *)
let rec resolve_index_term loc layouts mapping (term: Ast.term) 
        : (IT.typed, type_error) m =
  let aux = resolve_index_term loc layouts mapping in
  match term with
  | Integer i -> 
     return (IT (Lit (IT.Z i), BT.Integer))
  | Path o -> 
     resolve_path loc layouts mapping o
  | Addition (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     begin match IT.bt it with
     | Loc -> return (IT (Pointer_op (AddPointer (it, it')), Loc))
     | _ -> return (IT (Arith_op (Add (it, it')), IT.bt it))
     end
  | Subtraction (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     begin match IT.bt it with
     | Loc -> return (IT (Pointer_op (SubPointer (it, it')), Loc))
     | _ -> return (IT (Arith_op (Sub (it, it')), IT.bt it))
     end
  | Multiplication (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     begin match IT.bt it with
     | Loc -> return (IT (Pointer_op (MulPointer (it, it')), Loc))
     | _ -> return (IT (Arith_op (Mul (it, it')), IT.bt it))
     end
  | Division (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT (Arith_op (Div (it, it')), IT.bt it))
  | Exponentiation (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT (Arith_op (Exp (it, it')), IT.bt it))
  | Equality (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT (Bool_op (EQ (it, it')), Bool))
  | Inequality (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT (Bool_op (Not (IT (Bool_op (EQ (it, it')), Bool))), Bool))
  | ITE (it', it'', it''') ->
     let@ it' = aux it' in
     let@ it'' = aux it'' in
     let@ it''' = aux it''' in
     return (IT (Bool_op (ITE (it', it'', it''')), IT.bt it''))
  | LessThan (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT (Cmp_op (LT (it, it')), Bool))
  | GreaterThan (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT (Cmp_op (LT (it', it)), Bool))
  | LessOrEqual (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT (Cmp_op (LE (it, it')), Bool))
  | GreaterOrEqual (it, it') -> 
     let@ it = aux it in
     let@ it' = aux it' in
     return (IT (Cmp_op (LE (it', it)), Bool))
  | StructMember (t, member) ->
     let@ st = aux t in
     let@ tag = match IT.bt st with
       | Struct tag -> return tag
       | _ -> fail loc (Generic (Ast.pp_term false term ^^^ !^"is not a struct"))
     in
     let layout = layouts tag in
     let decl_members = Memory.member_types layout in
     let@ bt = match List.assoc_opt Id.equal member decl_members with
       | Some sct -> 
          return (BT.of_sct sct)
       | None -> 
          let err = 
            !^"Illtyped index term" ^^^ pp_term false term ^^ dot ^^^
              pp_term false t ^^^ !^"does not have member" ^^^ Id.pp member
          in
          fail loc (Generic err)
     in
     return (IT (Struct_op (StructMember (tag, st, member)), bt))
  | IntegerToPointerCast t ->
     let@ t = aux t in
     return (IT (Pointer_op (IntegerToPointerCast t), Loc))
     

let resolve_predarg loc layouts mapping p = 
  match p with
  | PathArg p -> resolve_path loc layouts mapping p
  | Term t -> resolve_index_term loc layouts mapping t




let resolve_constraint loc mapping lc = 
  resolve_index_term loc mapping lc




let apply_ownership_spec layouts label var_typs mapping (loc, {predicate;arguments}) =
  match predicate, arguments with
  | "Owned", [PathArg path] ->
     begin match Ast.deref_path path with
     | None -> fail loc (Generic (!^"cannot assign ownership of" ^^^ (Ast.pp_path false path)))
     | Some (bn, derefs) -> 
        let@ sct = type_of__vars loc var_typs bn.v derefs in
        let@ it = resolve_path loc layouts mapping path in
        match sct with
        | Sctype (_, Pointer (_, sct2)) ->
           make_owned loc layouts label it (Ast.var bn) sct2
        | _ ->
          fail loc (Generic (Ast.pp_path false path ^^^ !^"is not a pointer"))       
     end
  | "Owned", _ ->
     fail loc (Generic !^"Owned predicate takes 1 argument, which has to be a path")

  | "Block", [PathArg path] ->
     begin match Ast.deref_path path with
     | None -> fail loc (Generic (!^"cannot assign ownership of" ^^^ (Ast.pp_path false path)))
     | Some (bn, derefs) -> 
        let@ sct = type_of__vars loc var_typs bn.v derefs in
        let@ it = resolve_path loc layouts mapping path in
        match sct with
        | Sctype (_, Pointer (_, sct2)) ->
           make_block loc layouts it (Ast.var bn) sct2
        | _ ->
          fail loc (Generic (Ast.pp_path false path ^^^ !^"is not a pointer"))       
     end
  | "Block", _ ->
     fail loc (Generic !^"Block predicate takes 1 argument, which has to be a path")


  | _, pointer :: arguments ->
     let@ pointer_resolved = resolve_predarg loc layouts mapping pointer in
     let@ iargs_resolved = 
       ListM.mapM (resolve_predarg loc layouts mapping) arguments
     in
     let@ result = make_pred loc predicate arguments pointer_resolved iargs_resolved in
     return result
  | pred, _ ->
     fail loc (Generic !^("predicates take at least one (pointer) argument"))



let aarg_item l (aarg : aarg) =
  let path = Ast.addr aarg.name in
  {path; it = sym_ (aarg.asym, BT.Loc)}

let varg_item l (varg : varg) =
  let bn = {v = varg.name; label = Some l} in
  let path = Ast.var bn in
  {path; it = sym_ (varg.vsym, BT.of_sct varg.typ)} 

let garg_item l (garg : garg) =
  let path = Ast.addr garg.name in
  {path; it = sym_ (garg.lsym, BT.Loc) } 


let make_fun_spec loc layouts fsym (fspec : function_spec)
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
          | Some loc -> 
             make_owned loc layouts "start" item.it item.path garg.typ 
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
        let@ (l, r, c, mapping') = 
          make_owned loc layouts "start" item.it item.path aarg.typ in
        let c = good_value item.it (pointer_sct aarg.typ) :: c in
        return (iA @ a, iL @ l, iR @ r, iC @ c, (item :: mapping') @ mapping)
      )
      (iA, iL, iR, iC, mapping) fspec.function_arguments
  in

  let@ (iL, iR, iC, mapping) = 
    ListM.fold_leftM (fun (iL, iR, iC, mapping) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
           let@ (l, r, c, mapping') = 
             apply_ownership_spec layouts "start" var_typs mapping (loc, cond) in
           return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc layouts mapping cond in
           return (iL, iR, iC @ [c], mapping)
      )
      (iL, iR, iC, mapping) fspec.pre_condition
  in

  let init_mapping = mapping in

  (* ret *)
  let (oA, oC, mapping) = 
    let ret = fspec.function_return in
    let item = varg_item "end" ret in
    let c = [good_value item.it ret.typ] in
    ((ret.vsym, IT.bt item.it), c, item :: mapping)
  in

  (* globs *)
  let@ (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) garg ->
        let item = garg_item "end" garg in
        let@ (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> 
             make_owned loc layouts "end" item.it item.path garg.typ 
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
        let@ (l, r, c, mapping') = 
          make_owned loc layouts "end" item.it item.path aarg.typ in
        let c = good_value item.it (pointer_sct aarg.typ) :: c in
        return (oL @ l, oR @ r, oC @ c, (item :: mapping') @ mapping)
      )
      (oL, oR, oC, mapping) fspec.function_arguments
  in

  let@ (oL, oR, oC, mapping) = 
    ListM.fold_leftM (fun (oL, oR, oC, mapping) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
           let@ (l, r, c, mapping') = 
             apply_ownership_spec layouts "end" var_typs mapping (loc, cond) in
           return (oL @ l, oR @ r, oC @ c, mapping' @ mapping)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc layouts mapping cond in
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
      layouts
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
          | Some loc -> 
             make_owned loc layouts lname item.it item.path garg.typ 
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
        let@ (l, r, c, mapping') = 
          make_owned loc layouts lname item.it item.path aarg.typ in
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
          let@ (l, r, c, mapping') = 
            make_owned loc layouts lname item.it item.path aarg.typ in
          let c = good_value item.it (pointer_sct aarg.typ) :: c in
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
             apply_ownership_spec layouts lname var_typs mapping (loc, cond) in
           return (iL @ l, iR @ r, iC @ c, mapping' @ mapping)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc layouts mapping cond in
           return (iL, iR, iC @ [c], mapping)
      )
      (iL, iR, iC, mapping) lspec.invariant
  in

  let llt = LT.mLogicals iL (LT.mResources iR (LT.mConstraints iC (LT.I False.False))) in
  let lt = LT.mComputationals iA llt in
  return (lt, mapping)





