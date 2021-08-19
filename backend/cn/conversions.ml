module CF=Cerb_frontend
open List
(* open Sym *)
open Resultat
open Pp
(* open Tools *)
module BT = BaseTypes
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
open TypeErrors
open IndexTerms
open Resources.RE
open Sctypes
open Mapping
open Ast
open Predicates
open Memory
open Tools


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








let make_owned loc (layouts : Sym.t -> Memory.struct_layout) (pointer : IT.t) path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     fail loc (lazy (Generic !^"cannot make owned void* pointer"))
  | _ ->
     let pointee = Sym.fresh () in
     let pointee_bt = BT.of_sct sct in
     let pointee_t = sym_ (pointee, pointee_bt) in
     let l = [(pointee, pointee_bt)] in
     let mapping = {
         path = Ast.pointee path; 
         it = pointee_t;
         o_sct = Some sct;
       } 
     in
     let c = [good_value layouts sct pointee_t] in
     let r = [predicate (Ctype sct) pointer [] [pointee_t; (bool_ true)]] in
     return (l, r, c, [mapping])





let make_block loc (layouts : Sym.t -> Memory.struct_layout) (pointer : IT.t) path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     fail loc (lazy (Generic !^"cannot make owned void* pointer"))
  | _ ->
     let pointee = Sym.fresh () in
     let init = Sym.fresh () in
     let pointee_bt = BT.of_sct sct in
     let init_bt = BT.Bool in
     let pointee_t = sym_ (pointee, pointee_bt) in
     let init_t = sym_ (init, init_bt) in
     let l = [(pointee, pointee_bt); (init, init_bt)] in
     let mapping = [] in
     let r = [predicate (Ctype sct) pointer [] [pointee_t; init_t]] in
     return (l, r, [], mapping)

let make_pred loc (predicates : (string * Predicates.predicate_definition) list) 
      pred ~oname pointer iargs = 
  let@ def = match List.assoc_opt String.equal pred predicates with
    | Some def -> return def
    | None -> fail loc (lazy (Missing_predicate pred))
  in
  let (mapping, l) = 
    List.fold_right (fun (oarg, bt) (mapping, l) ->
        let s, it = IT.fresh bt in
        let l = (s, bt) :: l in
        let mapping = match oname with
          | Some name ->
             let item = {path = Ast.predarg name oarg; it; o_sct = None } in
             item :: mapping 
          | None ->
             mapping
        in
        (mapping, l)
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










(* change this to return unit IT.term, then apply index term type
   checker *)
let resolve_index_term loc layouts 
      (default_mapping_name : string)
      (mappings : mapping StringMap.t)
      (term: Ast.term) 
        : (IT.typed * Sctypes.t option, type_error) m =
  let lookup term mapping = 
    let found = List.find_opt (fun {path;_} -> Ast.term_equal path term) mapping in
    match found with
    | Some {it; o_sct; _} -> 
       return (it, o_sct)
    | None -> 
       fail loc (lazy (Generic (!^"term" ^^^ Ast.Terms.pp false term ^^^ !^"does not apply")))
  in
  let rec resolve (term : Ast.term) mapping 
        : (IT.typed * Sctypes.t option, type_error) m =
    match term with
    | Addr name ->
       lookup (Addr name) mapping
    | Var ln ->
       lookup (Var ln) mapping
    | Pointee it ->
       lookup (Pointee it) mapping
    | PredOutput (name, oarg) ->
       lookup (PredOutput (name, oarg)) mapping
    | Integer i -> 
       return (IT (Lit (IT.Z i), BT.Integer), None)
    | Addition (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (AddPointer (it, it')), Loc)
         | _ -> IT (Arith_op (Add (it, it')), IT.bt it)
       in
       return (t, None)
    | Subtraction (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (SubPointer (it, it')), Loc)
         | _ -> IT (Arith_op (Sub (it, it')), IT.bt it)
       in
       return (t, None)
    | Multiplication (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       let t = match IT.bt it with
       | Loc -> IT (Pointer_op (MulPointer (it, it')), Loc)
       | _ -> IT (Arith_op (Mul (it, it')), IT.bt it)
       in
       return (t, None)
    | Division (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Arith_op (Div (it, it')), IT.bt it), None)
    | Exponentiation (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Arith_op (Exp (it, it')), IT.bt it), None)
    | Equality (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Bool_op (EQ (it, it')), Bool), None)
    | Inequality (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Bool_op (Not (IT (Bool_op (EQ (it, it')), Bool))), Bool), None)
    | ITE (it', it'', it''') ->
       let@ (it', _) = resolve it' mapping in
       let@ (it'', _) = resolve it'' mapping in
       let@ (it''', _) = resolve it''' mapping in
       return (IT (Bool_op (ITE (it', it'', it''')), IT.bt it''), None)
    | Or (it', it'') ->
       let@ (it', _) = resolve it' mapping in
       let@ (it'', _) = resolve it'' mapping in
       return (IT (Bool_op (Or [it'; it'']), Bool), None)
    | And (it', it'') ->
       let@ (it', _) = resolve it' mapping in
       let@ (it'', _) = resolve it'' mapping in
       return (IT (Bool_op (And [it'; it'']), Bool), None)
    | LessThan (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Cmp_op (LT (it, it')), Bool), None)
    | GreaterThan (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Cmp_op (LT (it', it)), Bool), None)
    | LessOrEqual (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Cmp_op (LE (it, it')), Bool), None)
    | GreaterOrEqual (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Cmp_op (LE (it', it)), Bool), None)
    | Member (t, member) ->
       let@ (st, _) = resolve t mapping in
       let ppf () = Ast.Terms.pp false term in
       let@ tag = match IT.bt st with
         | Struct tag -> return tag
         | _ -> fail loc (lazy (Generic (ppf () ^^^ !^"is not a struct")))
       in
       let layout = layouts tag in
       let decl_members = Memory.member_types layout in
       let@ sct = match List.assoc_opt Id.equal member decl_members with
         | Some sct -> 
            return sct
         | None -> 
            let err = 
              !^"Illtyped index term" ^^^ ppf () ^^ dot ^^^
                ppf () ^^^ !^"does not have member" ^^^ Id.pp member
            in
            fail loc (lazy (Generic err))
       in
       return (IT (Struct_op (StructMember (st, member)), BT.of_sct sct), Some sct)
    | IntegerToPointerCast t ->
       let@ (t, _) = resolve t mapping in
       return (IT (Pointer_op (IntegerToPointerCast t), Loc), None)
    | PointerToIntegerCast t ->
       let@ (t, _) = resolve t mapping in
       return (IT (Pointer_op (PointerToIntegerCast t), Integer), None)
    | Null ->
       return (IT (Pointer_op Null, BT.Loc), None)
    | App (t1, t2) ->
       let@ (it1, _) = resolve t1 mapping in
       let@ (it2, _) = resolve t2 mapping in
       let@ result_bt = match IT.bt it1 with
         | BT.Array (_, bt) -> return bt
         | _ -> 
            let ppf () = Ast.Terms.pp false t1 in
            fail loc (lazy (Generic (ppf () ^^^ !^"is not an array")))
       in
       return (IT (Array_op (App (it1, it2)), result_bt), None)
    | Env (t, mapping_name) ->
       match StringMap.find_opt mapping_name mappings with
       | Some mapping -> 
          resolve t mapping
       | None ->
          fail loc (lazy (Generic (!^"label" ^^^ !^mapping_name ^^^ !^"does not apply")))
  in
  resolve term (StringMap.find default_mapping_name mappings)
     


let resolve_constraint loc layouts default_mapping_name mappings lc = 
  let@ (lc, _) = resolve_index_term loc layouts default_mapping_name mappings lc in
  return lc




let apply_ownership_spec layouts predicates default_mapping_name mappings (loc, {predicate; arguments; oname}) =
  match predicate, arguments with
  | "Owned", [path] ->
     let@ (it, sct) = resolve_index_term loc layouts default_mapping_name mappings path in
     begin match sct with
     | None -> 
        fail loc (lazy (Generic (!^"cannot assign ownership of" ^^^ (Ast.Terms.pp false path))))
     | Some Sctype (_, Pointer (_, sct2)) ->
        make_owned loc layouts it path sct2
     | Some _ ->
        fail loc (lazy (Generic (Ast.Terms.pp false path ^^^ !^"is not a pointer")))
     end
  | "Owned", _ ->
     fail loc (lazy (Generic !^"Owned predicate takes 1 argument, which has to be a path"))
  | "Block", [path] ->
     let@ (it, sct) = resolve_index_term loc layouts default_mapping_name mappings path in
     begin match sct with
     | None -> 
        fail loc (lazy (Generic (!^"cannot assign ownership of" ^^^ (Ast.Terms.pp false path))))
     | Some (Sctype (_, Pointer (_, sct2))) -> 
        make_block loc layouts it path sct2
     | Some _ ->
        fail loc (lazy (Generic (Ast.Terms.pp false path ^^^ !^"is not a pointer")))
     end
  | "Block", _ ->
     fail loc (lazy (Generic !^"Block predicate takes 1 argument, which has to be a path"))
  | _, pointer :: arguments ->
     let@ (pointer_resolved, _) = resolve_index_term loc layouts default_mapping_name mappings pointer in
     let@ iargs_resolved = 
       ListM.mapM (fun arg ->
           let@ (t, _) = resolve_index_term loc layouts default_mapping_name mappings arg in
           return t
         ) arguments
     in
     let@ result = make_pred loc predicates ~oname predicate pointer_resolved iargs_resolved in
     return result
  | pred, _ ->
     fail loc (lazy (Generic !^("predicates take at least one (pointer) argument")))





let error_with_loc loc msg = 
  let (head, pos) = Locations.head_pos_of_location loc in
  print stderr (format [Bold; Red] "error:" ^^^ 
                  format [Bold] head ^^^ !^msg);
  failwith "internal error"
  

(* let aarg_item loc (aarg : aarg) =
 *   match Sym.description aarg.asym with
 *     | SD_ObjectAddress name -> 
 *        {path = Ast.addr name; 
 *         it = sym_ (aarg.asym, BT.Loc); 
 *         o_sct = Some (Sctypes.pointer_sct aarg.typ) }
 *     | sd -> 
 *        error_with_loc loc
 *          ("address argument " ^ Sym.pp_string aarg.asym ^
 *             " without SD_ObjectAddress, but " ^ Sym.show_symbol_description sd)
 * 
 * let varg_item loc (varg : varg) =
 *   match Sym.description varg.vsym with
 *   | SD_ObjectValue name -> 
 *      {path = Ast.var name; 
 *       it = sym_ (varg.vsym, BT.of_sct varg.typ);
 *       o_sct = Some varg.typ} 
 *   | sd -> 
 *      error_with_loc loc
 *        ("value argument " ^ Sym.pp_string varg.vsym ^ 
 *           " without SD_ObjectValue, but " ^ Sym.show_symbol_description sd)
 * 
 * let garg_item loc (garg : garg) =
 *   match Sym.description garg.asym with
 *   | SD_ObjectAddress name -> 
 *      {path = Ast.addr name; 
 *       it = sym_ (garg.lsym, BT.Loc);
 *       o_sct = Some (Sctypes.pointer_sct garg.typ) } 
 *   | sd -> 
 *      error_with_loc loc
 *        ("global argument " ^ Sym.pp_string garg.asym ^ 
 *           " without SD_ObjectAddress, but " ^ Sym.show_symbol_description sd) *)

let aarg_item loc (aarg : aarg) =
  let path = match Sym.description aarg.asym with
    | SD_ObjectAddress name -> Ast.addr name; 
    | SD_None -> Ast.addr (Sym.pp_string aarg.asym)
    | sd ->
       error_with_loc loc
         ("address argument " ^ Sym.pp_string aarg.asym ^ 
            " without SD_ObjectAddress or SD_None, but " ^ Sym.show_symbol_description sd)
  in
  { path = path;
    it = sym_ (aarg.asym, BT.Loc); 
    o_sct = Some (Sctypes.pointer_sct aarg.typ) }

let varg_item loc (varg : varg) =
  match Sym.description varg.vsym with
  | SD_Return -> 
     {path = Ast.var "return"; 
      it = sym_ (varg.vsym, BT.of_sct varg.typ);
      o_sct = Some varg.typ} 
  | sd -> 
     error_with_loc loc
       ("value argument " ^ Sym.pp_string varg.vsym ^ 
          " without SD_ObjectValue, but " ^ Sym.show_symbol_description sd)

let garg_item loc (garg : garg) =
  match Sym.description garg.asym with
  | SD_ObjectAddress name -> 
     {path = Ast.addr name; 
      it = sym_ (garg.lsym, BT.Loc);
      o_sct = Some (Sctypes.pointer_sct garg.typ) } 
  | sd -> 
     error_with_loc loc
       ("global argument " ^ Sym.pp_string garg.asym ^ 
          " without SD_ObjectAddress, but " ^ Sym.show_symbol_description sd)


let mod_mapping 
      (mapping_name : string) 
      (mappings : mapping StringMap.t) 
      (f : mapping -> mapping)
    : mapping StringMap.t
  = 
  StringMap.add mapping_name 
    (f (StringMap.find mapping_name mappings)) 
    mappings


let make_fun_spec loc layouts predicates fsym (fspec : function_spec)
    : (AT.ft * mapping, type_error) m = 
  let open AT in
  let open RT in

  let iA, iL, iR, iC = [], [], [], [] in
  let oL, oR, oC = [], [], [] in
  let mappings = StringMap.empty in
  let mappings = StringMap.add "start" [] mappings in
  let mappings = StringMap.add "end" [] mappings in

  (* globs *)
  let@ (iL, iR, iC, mappings) = 
    ListM.fold_leftM (fun (iL, iR, iC, mappings) garg ->
        let item = garg_item loc garg in
        let@ (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> 
             make_owned loc layouts item.it item.path garg.typ 
          | None ->
             return ([], [], [], [])
        in
        let mappings = 
          mod_mapping "start" mappings
            (fun mapping -> (item :: mapping') @ mapping)
        in
        return (iL @ l, iR @ r, iC @ c, mappings)
      )
      (iL, iR, iC, mappings) fspec.global_arguments
  in

  (* fargs *)
  let@ (iA, iL, iR, iC, mappings) = 
    ListM.fold_leftM (fun (iA, iL, iR, iC, mappings) (aarg : aarg) ->
        let a = [(aarg.asym, BT.Loc)] in
        let item = aarg_item loc aarg in
        let@ (l, r, c, mapping') = 
          make_owned loc layouts item.it item.path aarg.typ in
        let c = good_value layouts (pointer_sct aarg.typ) item.it :: c in
        let mappings = 
          mod_mapping "start" mappings
            (fun mapping -> (item :: mapping') @ mapping)
        in
        return (iA @ a, iL @ l, iR @ r, iC @ c, mappings)
      )
      (iA, iL, iR, iC, mappings) fspec.function_arguments
  in

  let@ (iL, iR, iC, mappings) = 
    ListM.fold_leftM (fun (iL, iR, iC, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
           let@ (l, r, c, mapping') = 
             apply_ownership_spec layouts predicates
               "start" mappings (loc, cond) in
           let mappings = 
             mod_mapping "start" mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (iL @ l, iR @ r, iC @ c, mappings)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc layouts 
                      "start" mappings cond in
           return (iL, iR, iC @ [c], mappings)
      )
      (iL, iR, iC, mappings) fspec.pre_condition
  in

  (* ret *)
  let (oA, oC, mappings) = 
    let ret = fspec.function_return in
    let item = varg_item loc ret in
    let c = [good_value layouts ret.typ item.it] in
    let mappings =
      mod_mapping "end" mappings
        (fun mapping -> item :: mapping) 
    in
    ((ret.vsym, IT.bt item.it), c, mappings)
  in

  (* globs *)
  let@ (oL, oR, oC, mappings) = 
    ListM.fold_leftM (fun (oL, oR, oC, mappings) garg ->
        let item = garg_item loc garg in
        let@ (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> 
             make_owned loc layouts item.it item.path garg.typ 
          | None -> return ([], [], [], [])
        in
        let mappings =
          mod_mapping "end" mappings
            (fun mapping -> (item :: mapping') @ mapping)
        in
        return (oL @ l, oR @ r, oC @ c, mappings)
      )
      (oL, oR, oC, mappings) fspec.global_arguments
  in

  (* fargs *)
  let@ (oL, oR, oC, mappings) = 
    ListM.fold_leftM (fun (oL, oR, oC, mappings) aarg ->
        let item = aarg_item loc aarg in
        let@ (l, r, c, mapping') = 
          make_owned loc layouts item.it item.path aarg.typ in
        let c = good_value layouts (pointer_sct aarg.typ) item.it :: c in
        let mappings = 
          mod_mapping "end" mappings
            (fun mapping -> (item :: mapping') @ mapping)
        in
        return (oL @ l, oR @ r, oC @ c, mappings)
      )
      (oL, oR, oC, mappings) fspec.function_arguments
  in

  let@ (oL, oR, oC, mappings) = 
    ListM.fold_leftM (fun (oL, oR, oC, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
           let@ (l, r, c, mapping') = 
             apply_ownership_spec layouts predicates
               "end" mappings (loc, cond) 
           in
           let mappings = 
             mod_mapping "end" mappings 
               (fun mapping -> mapping' @ mapping)
           in
           return (oL @ l, oR @ r, oC @ c, mappings)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc layouts "end" mappings cond in
           return (oL, oR, oC @ [c], mappings)
      )
      (oL, oR, oC, mappings) fspec.post_condition
  in

  let oC = List.map LC.t_ oC in
  let iC = List.map LC.t_ iC in
  let lrt = LRT.mLogicals oL (LRT.mResources oR (LRT.mConstraints oC LRT.I)) in
  let rt = RT.mComputational oA lrt in
  let lft = AT.mLogicals iL (AT.mResources iR (AT.mConstraints iC (AT.I rt))) in
  let ft = AT.mComputationals iA lft in

  return (ft, StringMap.find "start" mappings)


  
let make_label_spec
      (loc : Loc.t)
      layouts
      predicates
      (lname : string)
      start_mapping
      (lspec: Ast.label_spec)
  =
  (* let largs = List.map (fun (os, t) -> (Option.value (Sym.fresh ()) os, t)) largs in *)
  let iA, iL, iR, iC = [], [], [], [] in
  let mappings = 
    StringMap.add lname []
      (StringMap.add "start" start_mapping 
         StringMap.empty )
  in

  (* globs *)
  let@ (iL, iR, iC, mappings) = 
    ListM.fold_leftM (fun (iL, iR, iC, mappings) garg ->
        let item = garg_item loc garg in
        let@ (l, r, c, mapping') = 
          match garg.accessed with
          | Some loc -> 
             make_owned loc layouts item.it item.path garg.typ 
          | None ->  return ([], [], [], [])
        in
        let mappings = 
          mod_mapping lname mappings
            (fun mapping -> mapping' @ mapping)
        in
        return (iL @ l, iR @ r, iC @ c, mappings)
      )
      (iL, iR, iC, mappings) lspec.global_arguments
  in

  (* fargs *)
  let@ (iL, iR, iC, mappings) = 
    ListM.fold_leftM (fun (iL, iR, iC, mappings) aarg ->
        let item = aarg_item loc aarg in
        let@ (l, r, c, mapping') = 
          make_owned loc layouts item.it item.path aarg.typ 
        in
        let mappings = 
          mod_mapping lname mappings
            (fun mapping -> mapping' @ mapping)
        in
        return (iL @ l, iR @ r, iC @ c, mappings)
      )
      (iL, iR, iC, mappings) lspec.function_arguments
  in

  (* largs *)
  let@ (iA, iL, iR, iC, mappings) = 
    (* In the label's argument list, the left-most arguments have the
       inner-most scope. In the mapping, we also want the arguments
       that are inner-most scoped-wise to be left-most. *)
    let@ (ia, iL, iR, iC, mapping') = 
      ListM.fold_leftM (fun (iA, iL, iR, iC, mapping) (aarg : aarg) ->
          let a = [(aarg.asym, BT.Loc)] in
          let item = aarg_item loc aarg in
          let@ (l, r, c, mapping') = 
            make_owned loc layouts item.it item.path aarg.typ in
          let c = good_value layouts (pointer_sct aarg.typ) item.it :: c in
          return (iA @ a, iL @ l, iR @ r, iC @ c, (item :: mapping') @ mapping)
        )
        (iA, iL, iR, iC, []) lspec.label_arguments
    in
    let mappings =
      mod_mapping lname mappings
        (fun mapping -> List.rev mapping' @ mapping)
    in
    return (ia, iL, iR, iC, mappings)
  in


  let@ (iL, iR, iC, mappings) = 
    ListM.fold_leftM (fun (iL, iR, iC, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
           let@ (l, r, c, mapping') = 
             apply_ownership_spec layouts predicates
               lname mappings (loc, cond) in
           let mappings = 
             mod_mapping lname mappings 
               (fun mapping -> mapping' @ mapping)
           in
           return (iL @ l, iR @ r, iC @ c, mappings)
        | Ast.Logical cond ->
           let@ c = resolve_constraint loc layouts lname mappings cond in
           return (iL, iR, iC @ [c], mappings)
      )
      (iL, iR, iC, mappings) lspec.invariant
  in

  let iC = List.map LC.t_ iC in
  let llt = AT.mLogicals iL (AT.mResources iR (AT.mConstraints iC (AT.I False.False))) in
  let lt = AT.mComputationals iA llt in
  return (lt, StringMap.find lname mappings)





