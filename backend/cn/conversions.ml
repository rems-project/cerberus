module CF=Cerb_frontend
open List
(* open Sym *)
open Resultat
open Effectful.Make(Resultat)
open Pp
(* open Tools *)
module BT = BaseTypes
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
open TypeErrors
open IndexTerms
open ResourceTypes
open Sctypes
open Mapping
open Ast
open ResourcePredicates
open Memory
open Tools



module StringMap = Map.Make(String)
module SymSet = Set.Make(Sym)





let sct_of_ct loc ct = 
  match Sctypes.of_ctype ct with
  | Some ct -> ct
  | None -> unsupported loc (!^"C-type" ^^^ CF.Pp_core_ctype.pp_ctype ct)





(* base types *)

let rec bt_of_core_object_type loc ot =
  let open CF.Core in
  match ot with
  | OTy_integer -> return BT.Integer
  | OTy_pointer -> return BT.Loc
  | OTy_array t -> 
     let@ t = bt_of_core_object_type loc t in
     return (BT.Map (Integer, t))
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
  | BTy_storable -> Debug_ocaml.error "BTy_storable"
  | BTy_ctype -> Debug_ocaml.error "BTy_ctype"













module CA = CF.Core_anormalise

let struct_decl loc fields (tag : BT.tag) = 

  let member_offset tag member = 
    let iv = CF.Impl_mem.offsetof_ival (CF.Tags.tagDefs ()) tag member in
    Memory.int_of_ival iv
  in

  let struct_layout loc members tag = 
    let rec aux members position =
      match members with
      | [] -> 
         let final_position = Memory.size_of_struct tag in
         if position < final_position 
         then return [{offset = position; size = final_position - position; member_or_padding = None}]
         else return []
      | (member, (attrs, qualifiers, ct)) :: members ->
         let sct = sct_of_ct loc ct in
         let offset = member_offset tag member in
         let size = Memory.size_of_ctype sct in
         let to_pad = offset - position in
         let padding = 
           if to_pad > 0
           then [{offset = position; size = to_pad; member_or_padding = None}] 
           else [] 
         in
         let member = [{offset; size; member_or_padding = Some (member, sct)}] in
         let@ rest = aux members (offset + size) in
         return (padding @ member @ rest)
    in
    (aux members 0)
  in

  let@ layout = struct_layout loc fields tag in

  return layout





let make_owned_funarg floc i (pointer : IndexTerms.t) path sct =
  let open Sctypes in
  match sct with
  | Void ->
     Debug_ocaml.error "void argument"
  | _ ->
     let descr = "ARG" ^ string_of_int i in
     let pointee, pointee_t = IT.fresh (BT.of_sct sct) in
     let l = (`Logical (pointee, IT.bt pointee_t), (floc, Some (descr ^ "value"))) in
     let mapping = [{
         path = Ast.pointee path; 
         it = pointee_t;
         o_sct = Some sct;
       }]
     in
     let r = 
       (`Resource 
          (P {
              name = Owned sct; 
              pointer; 
              permission = bool_ true; 
              iargs = [];
            },
           [(Resources.value_sym, pointee_t); 
            (Resources.init_sym, bool_ true)]),
        (floc, Some "ownership of function argument location"))
     in
     ([l;r], mapping)


let make_owned ~loc ~oname ~pointer ~path ~sct ~o_value ~o_permission =
  let open Sctypes in
  match sct with
  | Void ->
     fail {loc; msg = Generic !^"cannot make owned void* pointer"}
  | _ ->
     let l, pointee_t = match o_value with
       | None -> 
          let pointee, pointee_t = IT.fresh (BT.of_sct sct) in
          ([`Logical (pointee, IT.bt pointee_t), (loc, Some "value")], pointee_t)
       | Some pointee ->
          ([], pointee)
     in
     let mapping = [{
         path = Ast.pointee path; 
         it = pointee_t;
         o_sct = Some sct;
       }] 
     in
     let mapping = match oname with
       | Some name ->
          {path = Ast.predarg name "value"; 
           it = pointee_t; 
           o_sct = Some sct } :: mapping
       | None ->
          mapping
     in
     let r = 
       (`Resource (P {
           name = Owned sct; 
           pointer; 
           permission = Option.value o_permission ~default:(bool_ true); 
           iargs = [];
          },
          [(Resources.value_sym, pointee_t); 
           (Resources.init_sym, bool_ true)]),
        (loc, Some "ownership"))
     in
     return (l@[r], mapping)





let make_qowned ~loc ~oname ~pointer ~q:(qs,qbt) ~step ~condition ~path ~sct ~o_value =
  let open Sctypes in
  let@ () = match qbt with
    | BT.Integer -> return ()
    | _ -> fail {loc; msg = Generic (!^"Quantifier for iterated resource must be of type 'integer'")}
  in
  let@ () = 
    if Memory.size_of_ctype sct = step then return ()
    else fail {loc; msg = Generic !^"pointer increment must match size of array-cell type"}
  in
  match sct with
  | Void ->
     fail {loc; msg = Generic !^"cannot make owned void* pointer"}
  | _ ->
     let l, pointee_t = match o_value with
       | None ->
          let pointee, pointee_t = IT.fresh (BT.Map (qbt, BT.of_sct sct)) in
          ([`Logical (pointee, IT.bt pointee_t), (loc, Some "value")], pointee_t)
       | Some pointee ->
          ([], pointee)
     in
     let mapping = [] 
     in
     let mapping = match oname with
       | Some name ->
          {path = Ast.predarg name "value"; 
           it = pointee_t; 
           o_sct = Some sct } :: mapping
       | None ->
          mapping
     in
     let r = 
       (`Resource (Q {
           name = Owned sct; 
           pointer; 
           q = qs;
           permission = condition; 
           step = Memory.size_of_ctype sct;
           iargs = [];
          },
          [(Resources.value_sym, pointee_t); 
           (Resources.init_sym, const_map_ Integer (bool_ true))]),
        (loc, Some "ownership"))
     in
     return (l@[r], mapping)



let make_block ~loc ~pointer ~path ~sct ~o_permission =
  let open Sctypes in
  match sct with
  | Void ->
     fail {loc; msg = Generic !^"cannot make owned void* pointer"}
  | _ ->
     let pointee, pointee_t = IT.fresh (BT.of_sct sct) in
     let init, init_t = IT.fresh BT.Bool in
     let l = 
       [(`Logical (pointee, IT.bt pointee_t), (loc, Some "(uninitialised) value"));
        (`Logical (init, IT.bt init_t), (loc, Some "initialisedness status"))]
     in
     let mapping = [] in
     let r = 
       (`Resource (P {
            name = Owned sct; 
            pointer;
            permission = Option.value ~default:(bool_ true) o_permission;
            iargs = [];
          },
          [(Resources.value_sym, pointee_t); 
           (Resources.init_sym, init_t)]),
        (loc, Some "ownership"))
     in
     return (l@[r], mapping)

let some_oargs_map loc some_oargs = 
  ListM.fold_leftM (fun acc (name, it) ->
      if StringMap.mem name acc 
      then fail {loc; msg = Generic !^("already defined '" ^ name ^ "'")}
      else return (StringMap.add name it acc)
    ) StringMap.empty some_oargs


let ensure_some_oargs_empty loc pred some_oargs =
  match StringMap.choose_opt some_oargs with
  | None -> return ()
  | Some (name, _) -> fail {loc; msg = Generic !^("predicate '"^pred^"' does not have output argument '" ^ name ^ "'")}

let make_pred loc (pred, def) ~oname pointer iargs some_oargs ~o_permission = 
  let@ some_oargs = some_oargs_map loc some_oargs in
  let (mapping, l, some_oargs, oargs) = 
    List.fold_right (fun (oarg, bt) (mapping, l, some_oargs, oargs) ->
        let oarg_name = match Sym.description oarg with
          | SD_Id oarg_name -> oarg_name
          | _ -> assert false;
        in
        let it, l = match StringMap.find_opt oarg_name some_oargs with
          | None -> 
             let s, it = IT.fresh bt in
             let new_l = (`Logical (s, bt), (loc, Some ("output argument '"^oarg_name^"'"))) in
             (it, new_l :: l)
          | Some it -> (it, l)
        in
        let mapping = match oname with
          | Some name ->
             let item = {path = Ast.predarg name oarg_name; it; o_sct = None } in
             item :: mapping 
          | None ->
             mapping
        in
        let some_oargs = StringMap.remove oarg_name some_oargs in
        let oargs = (oarg, it) :: oargs in
        (mapping, l, some_oargs, oargs)
      ) def.oargs ([], [], some_oargs, [])
  in
  let@ () = ensure_some_oargs_empty loc pred some_oargs in
  let r = 
    (`Resource (P {
         name = PName pred; 
         pointer = pointer;
         iargs; 
         permission = Option.value ~default:(bool_ true) o_permission;
       },
       oargs),
     (loc, None))
  in
  return (l @ [r], mapping)



let make_qpred loc (pred, def) ~oname ~pointer ~q:(qs,qbt) ~step ~condition iargs some_oargs = 
  let@ () = match qbt with
    | BT.Integer -> return ()
    | _ -> fail {loc; msg = Generic (!^"Quantifier for iterated resource must be of type 'integer'")}
  in
  let@ some_oargs = some_oargs_map loc some_oargs in
  let ((mapping, l, c, oargs), some_oargs) = 
    List.fold_right (fun (oarg, bt) ((mapping, l, c, oargs), some_oargs) ->
        let oarg_name = match Sym.description oarg with
          | SD_Id name -> name
          | _ -> assert false
        in
        let it, l, c = match StringMap.find_opt oarg_name some_oargs with
          | Some it ->
             (it, l, c)
          | None ->
             let lifted_bt = BT.Map (qbt, bt) in
             let s, it = IT.fresh lifted_bt in
             let new_l = (`Logical (s, lifted_bt), (loc, Some ("output argument '"^oarg_name^"'"))) in
             (it, new_l :: l, c)
        in
        let mapping = match oname with
          | Some name ->
             let item = {path = Ast.predarg name oarg_name; it; o_sct = None } in
             item :: mapping 
          | None ->
             mapping
        in
        let some_oargs = StringMap.remove oarg_name some_oargs in
        let oargs = ((oarg, it)) :: oargs in
        ((mapping, l, c, oargs), some_oargs)
      ) def.oargs (([], [], [], []), some_oargs)
  in
  let@ () = ensure_some_oargs_empty loc pred some_oargs in
  let r = 
    (`Resource (Q {
         name = PName pred; 
         pointer;
         q = qs;
         step;
         iargs; 
         permission = condition;
       },
       oargs),
     (loc, None))
  in
  return (l @ [r] @ c, mapping)







(* copying from typing.ml *)
let get_resource_predicate_def loc id rpredicates lpredicates =
  let open TypeErrors in
  match List.assoc_opt String.equal id rpredicates with
  | Some def -> return def
  | None -> fail {loc; msg = Unknown_resource_predicate {id;
        logical = Option.is_some (List.assoc_opt String.equal id lpredicates)}}


(* copying from typing.ml *)
let get_logical_predicate_def loc id rpredicates lpredicates =
  let open TypeErrors in
  match List.assoc_opt String.equal id lpredicates with
  | Some def -> return def
  | None -> fail {loc; msg = Unknown_logical_predicate {id;
        resource = Option.is_some (List.assoc_opt String.equal id rpredicates)}}





(* change this to return unit IT.term, then apply index term type
   checker *)
let resolve_index_term loc 
      (layouts : Memory.struct_decls)
      predicates
      log_predicates
      (default_mapping_name : string)
      (mappings : mapping StringMap.t)
      (quantifiers : (string * (Sym.t * BT.t)) list)
      (term: Ast.term) 
        : (IT.typed * Sctypes.t option, type_error) m =
  let lookup term ty mapping quantifiers =
    let search () =
      let found = List.find_opt (fun {path;_} -> Ast.equal path term) mapping in
      match found with
      | Some {it; o_sct; _} -> 
         return (it, o_sct)
      | None -> 
         fail {loc; msg = Generic (!^"term" ^^^ Ast.Terms.pp false term
             ^^^ !^"is not bound as" ^^^ !^ty)}
    in
    match term with
    | Var name ->
       begin match List.assoc_opt String.equal name quantifiers with
       | Some (s, bt) -> return (sym_ (s, bt), None)
       | None -> search ()
       end
    | _ ->
       search ()
  in
  let all_rets_of name mapping =
    List.filter_map (fun {it; path; _} -> match path with
      | PredOutput (name2, oarg) when String.equal name name2 -> Some (oarg, it)
      | _ -> None) mapping
  in
  let pred_mapping name mapping =
    let match_name = function
      | PredOutput (name2, _) -> String.equal name name2
      | _ -> false
    in
    let ms_with = StringMap.bindings mappings
      |> List.map snd
      |> List.filter (List.exists (fun {path; _} -> match_name path))
    in
    match ms_with with
      | [mapping] -> mapping
      | _ -> mapping
  in
  let rec resolve (term : Ast.term) mapping quantifiers
        : (IT.typed * Sctypes.t option, type_error) m =
    match term with
    | Addr name ->
       lookup (Addr name) "an address" mapping quantifiers
    | Var ln ->
       lookup (Var ln) "a variable" mapping quantifiers
    | Pointee it ->
       lookup (Pointee it) "a pointee (i.e. not Owned)" mapping quantifiers
    | PredOutput (name, oarg) ->
       let mapping = pred_mapping name mapping in
       lookup (PredOutput (name, oarg)) "a predicate output" mapping quantifiers
    | Bool b -> 
       return (IT (Lit (IT.Bool b), BT.Bool), None)
    | Integer i -> 
       return (IT (Lit (IT.Z i), BT.Integer), None)
    | Addition (it, it') -> 
       let@ (it, oct) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let@ t = match IT.bt it with
         | Loc -> 
            let err = "pointer addition not allowed in specifications: "^
                        "please instead use pointer/integer casts"
            in
            fail {loc; msg = Generic (!^err)}
         | _ -> return (IT (Arith_op (Add (it, it')), IT.bt it))
       in
       return (t, None)
    | Subtraction (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let@ t = match IT.bt it with
         | Loc -> 
            let err = "pointer subtraction not allowed in specifications: "^
                        "please instead use pointer/integer casts"
            in
            fail {loc; msg = Generic (!^err)}
         | _ -> return (IT (Arith_op (Sub (it, it')), IT.bt it))
       in
       return (t, None)
    | Multiplication (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let t = IT (Arith_op (Mul (it, it')), IT.bt it) in
       return (t, None)
    | Division (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       return (IT (Arith_op (Div (it, it')), IT.bt it), None)
    | Exponentiation (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       return (exp_ (it, it'), None)
    | Remainder (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       return (IT (Arith_op (Rem (it, it')), IT.bt it), None)
    | Modulus (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       return (IT (Arith_op (Mod (it, it')), IT.bt it), None)
    | Equality (it, PredEqRegulator (exclude, it')) ->
       let@ (nm, nm') = begin match it, it' with
         | Var nm, Var nm' -> return (nm, nm')
         | Var _, _ -> fail {loc; msg = Generic (!^ "predicate return eq cannot handle" ^^^
             Ast.Terms.pp false it')}
         | _, _ -> fail {loc; msg = Generic (!^ "predicate return eq cannot handle" ^^^
             Ast.Terms.pp false it)}
       end in
       let rets = all_rets_of nm mapping in
       let@ () = if List.length rets == 0
           then fail {loc; msg = Generic (!^ nm ^^^ !^ "not a known resource predicate")}
           else return () in
       let@ () = ListM.iterM (fun s -> if Option.is_some (List.assoc_opt String.equal s rets)
           then return ()
           else fail {loc; msg = Generic (!^s ^^^ !^ "not a return param of" ^^^ !^ nm)})
         exclude in
       let eq_rets = List.filter (fun (nm, it) -> not (List.exists (String.equal nm) exclude))
           rets in
       let@ eqs = ListM.mapM (fun (arg_nm, it) ->
           let@ (it', _) = resolve (PredOutput (nm', arg_nm)) mapping quantifiers in
           return (eq_ (it, it'))) eq_rets in
       return (IT (Bool_op (And eqs), Bool), None)
    | PredEqRegulator (_, _) ->
       fail {loc; msg = Generic (!^ "return param limiter" ^^^ Ast.Terms.pp false term ^^^
            !^ "only permitted on right-hand-side of equalities")}
    | Equality (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       return (IT (Bool_op (EQ (it, it')), Bool), None)
    | Inequality (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       return (IT (Bool_op (Not (IT (Bool_op (EQ (it, it')), Bool))), Bool), None)
    | ITE (it', it'', it''') ->
       let@ (it', _) = resolve it' mapping quantifiers in
       let@ (it'', _) = resolve it'' mapping quantifiers in
       let@ (it''', _) = resolve it''' mapping quantifiers in
       return (IT (Bool_op (ITE (it', it'', it''')), IT.bt it''), None)
    | Or (it', it'') ->
       let@ (it', _) = resolve it' mapping quantifiers in
       let@ (it'', _) = resolve it'' mapping quantifiers in
       return (IT (Bool_op (Or [it'; it'']), Bool), None)
    | And (it', it'') ->
       let@ (it', _) = resolve it' mapping quantifiers in
       let@ (it'', _) = resolve it'' mapping quantifiers in
       return (IT (Bool_op (And [it'; it'']), Bool), None)
    | Not it' ->
       let@ (it', _) = resolve it' mapping quantifiers in
       return (IT (Bool_op (Not it'), Bool), None)
    | LessThan (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (LTPointer (it, it')), Bool)
         | _ -> IT (Arith_op (LT (it, it')), Bool)
       in
       return (t, None)
    | GreaterThan (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (LTPointer (it', it)), Bool)
         | _ -> IT (Arith_op (LT (it', it)), Bool)
       in
       return (t, None)
    | LessOrEqual (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (LEPointer (it, it')), Bool)
         | _ -> IT (Arith_op (LE (it, it')), Bool)
       in
       return (t, None)
    | GreaterOrEqual (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (LEPointer (it', it)), Bool)
         | _ -> IT (Arith_op (LE (it', it)), Bool)
       in
       return (t, None)
    | Member (t, member) ->
       let@ (st, _) = resolve t mapping quantifiers in
       let ppf () = Ast.Terms.pp false term in
       let@ tag = match IT.bt st with
         | Struct tag -> return tag
         | _ -> fail {loc; msg = Generic (ppf () ^^^ !^"is not a struct")}
       in
       let@ layout = match SymMap.find_opt tag layouts with
         | Some layout -> return layout
         | None -> fail {loc; msg = Unknown_struct tag}
       in
       let decl_members = Memory.member_types layout in
       let@ sct = match List.assoc_opt Id.equal member decl_members with
         | Some sct -> 
            return sct
         | None -> 
            let err = 
              !^"Illtyped index term" ^^^ ppf () ^^ dot ^^^
                ppf () ^^^ !^"does not have member" ^^^ Id.pp member
            in
            fail {loc; msg = Generic err}
       in
       return (IT (Struct_op (StructMember (st, member)), BT.of_sct sct), Some sct)
    | StructUpdate ((t, m), v) ->
       let@ (t, osct) = resolve t mapping quantifiers in
       let@ (v, _) = resolve v mapping quantifiers in
       return (IT (Struct_op (StructUpdate ((t, m), v)), IT.bt t), osct)
    | ArraySet ((t, i), v) ->
       let@ (t, osct) = resolve t mapping quantifiers in
       let@ (i, _) = resolve i mapping quantifiers in
       let@ (v, _) = resolve v mapping quantifiers in
       return (IT (Map_op (Set (t, i, v)), IT.bt t), osct)
    | IntegerToPointerCast t ->
       let@ (t, _) = resolve t mapping quantifiers in
       return (IT (Pointer_op (IntegerToPointerCast t), Loc), None)
    | PointerToIntegerCast t ->
       let@ (t, _) = resolve t mapping quantifiers in
       return (IT (Pointer_op (PointerToIntegerCast t), Integer), None)
    | Null ->
       return (IT (Lit Null, BT.Loc), None)
    | OffsetOf {tag; member} ->
       let (tag, layout) = 
         (* todo: fix *)
         SymMap.choose (SymMap.filter (fun sym _ -> 
             match Sym.description sym with
             | SD_Id tag' -> String.equal tag tag'
             | _ -> false
           ) layouts)
       in
       let decl_members = Memory.member_types layout in
       let member = Id.id member in
       let@ sct = match List.assoc_opt Id.equal member decl_members with
         | Some sct -> 
            return sct
         | None -> 
            let ppf () = Ast.Terms.pp false term in
            let err = 
              !^"Illtyped index term" ^^^ ppf () ^^ dot ^^^
                ppf () ^^^ !^"does not have member" ^^^ Id.pp member
            in
            fail {loc; msg = Generic err}
       in
       return (IT (Pointer_op (MemberOffset (tag, member)), BT.Integer), None)
    | MemberShift {pointer =t; member} ->
       let@ (pointer, osct) = resolve t mapping quantifiers in
       let ppf () = Ast.Terms.pp false t in
       let member = Id.parse loc member in
       let@ tag = match osct with
         | None -> 
            fail {loc; msg = Generic (!^"Cannot resolve C type of term" ^^^ 
                                        Ast.pp false t)}

         | Some (Pointer (Struct tag)) -> return tag
         | Some (Pointer _) -> 
            fail {loc; msg = Generic (ppf () ^^^ !^"is not a struct pointer")}
         | Some _ -> 
            fail {loc; msg = Generic (ppf () ^^^ !^"is not a pointer")}
       in
       let@ layout = match SymMap.find_opt tag layouts with
         | Some layout -> return layout
         | None -> fail {loc; msg = Unknown_struct tag}
       in
       let decl_members = Memory.member_types layout in
       let@ sct = match List.assoc_opt Id.equal member decl_members with
         | Some sct -> 
            return sct
         | None -> 
            let err = 
              !^"Illtyped index term" ^^^ ppf () ^^ dot ^^^
                ppf () ^^^ !^"does not have member" ^^^ Id.pp member
            in
            fail {loc; msg = Generic err}
       in
       return (memberShift_ (pointer, tag, member), Some (Sctypes.Pointer sct))
    | ArrayShift {pointer =t; index} ->
       let@ (pointer, osct) = resolve t mapping quantifiers in
       let@ (index, _) = resolve t mapping quantifiers in
       let ppf () = Ast.Terms.pp false t in
       let@ sct = match osct with
         | None -> 
            fail {loc; msg = Generic (!^"Cannot resolve C type of term" ^^^ 
                                        Ast.pp false t)}

         | Some (Pointer sct) -> return sct
         | Some _ -> 
            fail {loc; msg = Generic (ppf () ^^^ !^"is not a pointer")}
       in
       return (arrayShift_ (pointer, sct, index), Some (Sctypes.Pointer sct))
    | CellPointer ((base, step), (from_index, to_index), pointer) ->
       let@ (base, _) = resolve base mapping quantifiers in
       let@ (step, _) = resolve step mapping quantifiers in
       let@ (from_index, _) = resolve from_index mapping quantifiers in
       let@ (to_index, _) = resolve to_index mapping quantifiers in
       let@ (pointer, _) = resolve pointer mapping quantifiers in
       let t = cellPointer_ ~base ~step ~starti:from_index ~endi:to_index 
                 ~p:pointer in
       return (t, None)
    | Disjoint ((p1, sz1), (p2, sz2)) ->
       let@ (p1, _) = resolve p1 mapping quantifiers in
       let@ (sz1, _) = resolve sz1 mapping quantifiers in
       let@ (p2, _) = resolve p2 mapping quantifiers in
       let@ (sz2, _) = resolve sz2 mapping quantifiers in
       return (disjoint_ (p1, sz1) (p2, sz2), None)
    | App (t1, t2) ->
       let@ (it1, _) = resolve t1 mapping quantifiers in
       let@ (it2, _) = resolve t2 mapping quantifiers in
       begin match IT.bt it1 with
       | BT.Map (_, bt) -> 
          return ((map_get_ it1 it2), None)
       | _ -> 
          let ppf () = Ast.Terms.pp false t1 in
          fail {loc; msg = Generic (ppf () ^^^ !^"is not an array/not a map")}
       end
    | Env (t, mapping_name) ->
       let@ () = 
         if Ast.contains_env_or_unchanged_expression t 
         then fail {loc; msg = Generic !^"Cannot use '{_}@label' together with other '{_}@label' or 'unchanged' expressions."}
         else return ()
       in
       begin match StringMap.find_opt mapping_name mappings with
       | Some mapping -> 
          resolve t mapping quantifiers
       | None ->
          fail {loc; msg = Generic (!^"label" ^^^ !^mapping_name ^^^ !^"does not apply")}
       end
    | Unchanged t ->
       let@ () = 
         if Ast.contains_env_or_unchanged_expression t 
         then fail {loc; msg = Generic !^"Cannot use 'unchanged' together with '{_}@label' or other 'unchanged' expressions."}
         else return ()
       in
       let@ (t_original, _) = resolve t (StringMap.find "start" mappings) quantifiers in
       let@ (t_new, _) = resolve t mapping quantifiers in
       return (eq_ (t_new, t_original), None)
    | For ((i, s, j), t) ->
       let sym = Sym.fresh_pretty s in
       let@ (t, _) = resolve t mapping ((s, (sym, Integer)) :: quantifiers) in
       let make_int z = 
         try return (Z.to_int z) with
         | Z.Overflow -> fail {loc; msg = Generic !^"Too small/large integer"}
       in
       let@ i = make_int i in
       let@ j = make_int j in
       if j - i > 20 
       then fail {loc; msg = Generic !^"Quantifying over too large integer space using 'for'"} 
       else return (eachI_ (i, sym, j) t, None)
    | Pred (name, args) ->
       let open LogicalPredicates in
       let@ args_oscts = ListM.mapM (fun t -> resolve t mapping quantifiers) args in
       let@ def = get_logical_predicate_def loc name predicates log_predicates in
       return (pred_ name (List.map fst args_oscts) def.return_bt, None)
       
  in
  resolve term (StringMap.find default_mapping_name mappings) quantifiers



let rec resolve_typ loc 
      (layouts : Memory.struct_decls)
      predicates
      log_predicates
      (default_mapping_name : string)
      (mappings : mapping StringMap.t)
      (oquantifier : (string * (Sym.t * BT.t)) option)
      (typ: Ast.typ) =
  match typ with
  | Typeof term ->
     let@ (_, osct) = 
       resolve_index_term loc layouts 
         predicates log_predicates
         default_mapping_name
         mappings (Option.to_list oquantifier) term
     in
     begin match osct with
     | Some sct -> return sct
     | None ->
        fail {loc; msg = Generic (!^"Cannot resolve C type of term" ^^^ 
                                    Ast.pp false term)}
     end
  | Struct str ->
     let ofound = 
       SymMap.find_first_opt (fun s -> 
           match Sym.description s with
           | SD_Id str' ->
              String.equal str str'
           | _ -> false
         ) layouts
     in
     begin match ofound with
     | Some (tag, _) -> return (Sctypes.Struct tag)
     | None -> 
        fail {loc; msg = Unknown_struct (Sym.fresh_pretty str)}
     end
  | Pointer ct ->
     let@ typ = resolve_typ loc layouts predicates log_predicates default_mapping_name mappings oquantifier ct in
     return (Sctypes.Pointer typ)


     



let resolve_constraint loc layouts predicates log_predicates default_mapping_name mappings (oq, lc) = 
  match oq with
    | None -> 
       let@ (lc, _) = resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings [] lc in
       return (LC.t_ lc)
    | Some (name, bt, guard) ->
       let q_s, q = IT.fresh_named bt name in
       let qs = [(name, (q_s, bt))] in
       let@ (guard, _) = resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings qs guard in
       let@ (lc, _) = resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings qs lc in
       return (LC.forall_ (q_s, IT.bt q) (impl_ (guard, lc)))
  





let apply_ownership_spec layouts predicates log_predicates default_mapping_name mappings (loc, {oq; predicate; arguments; some_oargs; oname; o_permission; typ}) =
  let ownership_kind = match predicate with
    | "Owned" -> `Builtin `Owned
    | "Block" -> `Builtin `Block
    | str -> `Predicate str
  in
  let oq = match oq with
    | None -> None
    | Some (name, bt, condition) ->
       let s = Sym.fresh_pretty name in
       Some ((name, (s, bt)), condition)
  in
  let@ (pointer, arguments) = match arguments with
    | pointer :: arguments -> return (pointer, arguments)
    | _ -> fail {loc; msg = Generic !^("missing first (pointer) argument")}
  in
  let@ o_permission = match o_permission with
    | None -> return None
    | Some permission ->
       let@ (t, _) = 
         resolve_index_term loc layouts predicates log_predicates 
           default_mapping_name mappings 
           (Option.to_list (Option.map fst oq)) permission
       in
       return (Some t)
  in
  match ownership_kind with
  | `Builtin block_or_owned ->
     let@ () = match arguments with
       | [] -> return ()
       | _ :: _ -> fail {loc; msg = Generic !^("'"^predicate^"' takes 1 argument, which has to be a path")}
     in
     let@ o_value = match block_or_owned, some_oargs with
       | _, [] -> return None
       | `Owned, [("value", value)] -> 
          let@ (value, _) = 
            resolve_index_term loc layouts predicates log_predicates 
              default_mapping_name mappings 
              (Option.to_list (Option.map fst oq)) value
          in
          return (Some value)
       | `Block, _ -> fail {loc; msg = Generic !^(""^predicate^"' has no output arguments")}
       | `Owned, _ -> fail {loc; msg = Generic !^("'"^predicate^"' has a single output argument, named 'value'")}
     in
     begin match oq with
     | None ->
        let@ (pointer_resolved, pointer_sct) = 
          resolve_index_term loc layouts predicates log_predicates 
            default_mapping_name mappings 
            (Option.to_list (Option.map fst oq)) pointer 
        in
        let@ pointee_sct = match typ, pointer_sct with
          | Some typ, _ ->
             resolve_typ loc layouts predicates log_predicates default_mapping_name mappings 
               (Option.map fst oq) typ
          | _, Some (Pointer pointee_sct) -> 
             return pointee_sct
          | _, Some _ ->
             fail {loc; msg = Generic (Ast.Terms.pp false pointer ^^^ !^"is not a pointer")}
          | None, None ->
             fail {loc; msg = Generic (!^"cannot assign ownership of" ^^^ (Ast.Terms.pp false pointer))}
        in
        begin match block_or_owned with
        | `Owned -> 
           make_owned ~loc ~oname ~pointer:pointer_resolved ~path:pointer 
             ~sct:pointee_sct ~o_permission ~o_value
        | `Block -> 
           make_block ~loc ~pointer:pointer_resolved ~path:pointer ~sct:pointee_sct ~o_permission
        end
     | Some ((name, (qs,qbt)), condition) ->
        let@ () = match o_permission with
          | None -> return () 
          | Some _ -> 
             fail {loc; msg = Generic (!^"cannot use 'if' expression with iterated resources")}
        in
        let@ (pointer_resolved, step) = 
          match pointer with
          | Addition (pointer, Multiplication (Var name', Integer step)) 
                 when String.equal name name' ->
             let@ (pointer,_) = 
               resolve_index_term loc layouts predicates log_predicates 
                 default_mapping_name mappings 
                 [] pointer 
             in
             return (pointer, Z.to_int step)
          | _ -> 
             let msg = 
               "Iterated predicate pointer argument must be of the shape "^
                 "(pointer expression + (quantifier variable * integer constant))"
             in
             fail {loc; msg = Generic (!^msg)}
        in
        let@ (condition, _) = 
          resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings 
            [(name, (qs, qbt))] condition 
        in
        let@ pointee_sct = match typ with
          | Some typ ->
             resolve_typ loc layouts predicates log_predicates default_mapping_name mappings 
               (Option.map fst oq) typ
          | None ->
             fail {loc; msg = Generic (!^"need 'with type' annotation" ^^^ (Ast.Terms.pp false pointer))}
        in
        begin match block_or_owned with
        | `Owned -> 
           make_qowned ~loc ~oname ~pointer:pointer_resolved ~q:(qs,qbt) 
             ~step ~condition ~path:pointer ~sct:pointee_sct ~o_value
        | `Block -> 
           fail {loc; msg = Generic !^("cannot use '"^predicate^"' with quantifier")}
        end
     end
  | _ ->
     let@ () = match typ with
       | None -> return ()
       | Some _ -> fail {loc; msg = Generic !^"cannot use 'type' syntax with predicates"}
     in
     let@ def = match List.assoc_opt String.equal predicate predicates with
       | Some def -> return def
       | None -> fail {loc; msg = Unknown_resource_predicate {id = predicate;
               logical = Option.is_some (List.assoc_opt String.equal predicate log_predicates)}}
     in
     let@ iargs_resolved = 
       ListM.mapM (fun arg ->
           let@ (t, _) = 
             resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings 
               (Option.to_list (Option.map fst oq)) arg in
           return t
         ) arguments
     in
     let@ some_oargs_resolved = 
       ListM.mapM (fun (name, arg) ->
           let@ (t, _) = 
             resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings 
               [] arg in      (* quantifier not bound in some_oarg definition *)
           return (name, t)
         ) some_oargs
     in
     let@ result = match oq with
       | None ->
          let@ (pointer_resolved, pointer_sct) = 
            resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings 
              (Option.to_list (Option.map fst oq)) pointer 
          in
          make_pred loc (predicate, def) 
            ~oname pointer_resolved iargs_resolved some_oargs_resolved ~o_permission
       | Some ((name, (s, bt)), condition) -> 
          let@ () = match o_permission with
            | None -> return () 
            | Some _ -> 
               fail {loc; msg = Generic (!^"cannot use 'if' expression with iterated resources")}
          in
          let@ (pointer_resolved, step) = 
            match pointer with
            | Addition (pointer, Multiplication (Var name', Integer step)) 
                 when String.equal name name' ->
               let@ (pointer,_) = 
                 resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings 
                   [] pointer 
               in
               return (pointer, Z.to_int step)
            | _ -> 
               let msg = 
                 "Iterated predicate pointer argument must be of the shape "^
                   "(pointer expression + (quantifier variable * integer constant))"
               in
               fail {loc; msg = Generic (!^msg)}
          in
          let@ (condition, _) = 
             resolve_index_term loc layouts predicates log_predicates default_mapping_name mappings 
               [(name, (s, bt))] condition 
          in
          make_qpred 
            loc 
            (predicate, def) 
            ~oname
            ~pointer:pointer_resolved
            ~q:(s, bt) 
            ~step
            ~condition 
            iargs_resolved 
            some_oargs_resolved
     in
     return result


let apply_logical_predicate layouts predicates log_predicates default_mapping_name mappings (loc, cond) =
  let open LogicalPredicates in
  let@ def = get_logical_predicate_def loc cond.predicate predicates log_predicates in
  let@ lc = match cond.oq with
    | None ->
       let@ args_resolved = 
         ListM.mapM (fun arg ->
             let@ (t, _) = 
               resolve_index_term loc layouts predicates log_predicates 
                 default_mapping_name mappings 
                 [] arg in
             return t
           ) cond.arguments
       in
       return (LC.t_ (pred_ cond.predicate args_resolved def.return_bt))
    | Some (name, bt, condition) -> 
       let q = Sym.fresh_named name in
       let@ args_resolved = 
         ListM.mapM (fun arg ->
             let@ (t, _) = 
               resolve_index_term loc layouts 
                 predicates log_predicates default_mapping_name mappings 
                 [(name, (q, bt))] arg in
             return t
           ) cond.arguments
       in
       let@ (condition, _) = 
         resolve_index_term loc layouts
           predicates log_predicates default_mapping_name mappings 
           [(name, (q, bt))] condition
       in
       let t = pred_ cond.predicate args_resolved def.return_bt in
       return (LC.forall_ (q, bt) (impl_ (condition, t) ))
  in
  return (`Constraint lc, (loc, None))



let error_with_loc loc msg = 
  let (head, pos) = Locations.head_pos_of_location loc in
  print stderr (format [Bold; Red] "error:" ^^^ 
                  format [Bold] head ^^^ !^msg);
  failwith "internal error"
  


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
    o_sct = Some (pointer_ct aarg.typ) }

let varg_item loc (varg : varg) =
  match Sym.description varg.vsym with
  | SD_FunArgValue str ->
     {path = Ast.var str;
      it = sym_ (varg.vsym, BT.of_sct varg.typ);
      o_sct = Some varg.typ}
  | SD_Return -> 
     {path = Ast.var "return"; 
      it = sym_ (varg.vsym, BT.of_sct varg.typ);
      o_sct = Some varg.typ} 
  | sd -> 
     error_with_loc loc
       ("value argument " ^ Sym.pp_string varg.vsym ^ "\n" ^
          "description: " ^ Sym.show_symbol_description sd)

let garg_item loc (garg : garg) =
  match Sym.description garg.asym with
  | SD_ObjectAddress name -> 
     {path = Ast.addr name; 
      it = sym_ (garg.lsym, BT.Loc);
      o_sct = Some (pointer_ct garg.typ) } 
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

let mod_mappings mapping_names mappings f = 
  StringMap.mapi (fun name mapping ->
      if List.mem String.equal name mapping_names then 
        f mapping
      else 
        mapping
    ) mappings

let get_mappings_info (mappings : mapping StringMap.t) (mapping_name : string) =
  SuggestEqs.make_mappings_info (StringMap.find mapping_name mappings
    |> List.map (fun {path; it; _} -> (Pp.plain (Ast.Terms.pp true path), it)))

let make_fun_spec loc (layouts : Memory.struct_decls) rpredicates lpredicates
        calling_mode fsym (fspec : function_spec)
    : (AT.ft * CF.Mucore.trusted * mapping, type_error) m = 
  let open AT in
  let open RT in

  let i = [] in
  let o = [] in
  let mappings = StringMap.empty in
  let mappings = StringMap.add "start" [] mappings in
  let mappings = StringMap.add "end" [] mappings in

  (* globs *)
  let@ (i, mappings) = 
    ListM.fold_leftM (fun (i, mappings) garg ->
        let item = garg_item loc garg in
        match garg.accessed with
        | None ->
           return (i, mappings)
        | Some loc -> 
           let@ (i', mapping') = 
             make_owned ~loc ~oname:None ~pointer:item.it 
               ~path:item.path ~sct:garg.typ ~o_permission:None ~o_value:None 
           in
           let mappings = 
             mod_mapping "start" mappings
               (fun mapping -> (item :: mapping') @ mapping)
           in
           return (i @ i', mappings)
      )
      (i, mappings) fspec.global_arguments
  in

  (* fargs *)
  let@ (i, mappings, _) = 
    ListM.fold_leftM (fun (i, mappings, counter) (earg : earg) ->
      match calling_mode with
      | `CallByValue ->
        let descr = "ARG" ^ string_of_int counter in
        let a = (`Computational (earg.esym, BT.of_sct earg.typ), (loc, Some descr)) in
        let varg = {vsym = earg.esym; typ = earg.typ} in
        let item = varg_item loc varg in
        (* let (i', mapping') =  *)
        (*   make_owned_funarg loc counter item.it item.path aarg.typ in *)
        let c =
          (`Constraint (LC.t_ (good_ (varg.typ, item.it))),
           (loc, Some (descr ^ " constraint")))
        in
        let mappings =
          mod_mappings ["start";"end"] mappings
            (fun mapping -> item :: mapping)
        in
        return (i @ a :: [c], mappings, counter+1)
      | `CallByReference ->
        let descr = "&ARG" ^ string_of_int counter in
        let a = (`Computational (earg.esym, BT.Loc), (loc, Some descr)) in
        let aarg = {asym = earg.esym; typ = earg.typ} in
        let item = aarg_item loc aarg in
        let (i', mapping') =
          make_owned_funarg loc counter item.it item.path aarg.typ in
        let c =
          (`Constraint (LC.t_ (good_ (pointer_ct aarg.typ, item.it))),
           (loc, Some (descr ^ " constraint")))
        in
        let mappings =
          mod_mapping "start" mappings
            (fun mapping -> (item :: mapping') @ mapping)
        in
        return (i @ a :: c :: i', mappings, counter+1)
    )
    (i, mappings, 0) fspec.function_arguments
  in

  let@ (i, mappings) = 
    ListM.fold_leftM (fun (i, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
              let@ (i', mapping') = 
                apply_ownership_spec layouts rpredicates lpredicates
                  "start" mappings (loc, cond) 
              in
              let mappings = 
                mod_mapping "start" mappings
                  (fun mapping -> mapping' @ mapping)
              in
              return (i @ i', mappings)
        | Ast.Constraint (oq,lc) ->
           let@ c = resolve_constraint loc layouts rpredicates lpredicates
                      "start" mappings (oq,lc) in
           return (i @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = 
             resolve_index_term loc layouts rpredicates lpredicates
               "start" mappings [] it
           in
           let mapping' = [{path = Ast.var name; it = sym_ (s, IT.bt it); o_sct}] in
           let mappings = 
             mod_mappings ["start"; "end"] mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (i @ [(`Define (s, it), (loc, None))], mappings)
      )
      (i, mappings) fspec.pre_condition
  in

  let start_naming = SuggestEqs.make_naming "start" (get_mappings_info mappings "start") in
  let i = i @ [(`Constraint (LC.t_ start_naming), (loc, None))] in

  (* ret *)
  let (oA, o, mappings) = 
    let ret = fspec.function_return in
    let item = varg_item loc ret in
    let c = (`Constraint (LC.t_ (good_ (ret.typ, item.it))), 
             (loc, Some "return value constraint")) in
    let mappings =
      mod_mapping "end" mappings
        (fun mapping -> item :: mapping) 
    in
    ((ret.vsym, IT.bt item.it, (loc, Some "return")), o @ [c], mappings)
  in

  (* globs *)
  let@ (o, mappings) = 
    ListM.fold_leftM (fun (o, mappings) garg ->
        match garg.accessed with
        | None -> return (o, mappings)
        | Some loc -> 
           let item = garg_item loc garg in
           let@ (o', mapping') = 
             make_owned ~loc ~oname:None ~pointer:item.it 
               ~path:item.path ~sct:garg.typ ~o_permission:None ~o_value:None
           in
           let mappings =
             mod_mapping "end" mappings
               (fun mapping -> (item :: mapping') @ mapping)
           in
           return (o @ o', mappings)
      )
      (o, mappings) fspec.global_arguments
  in

  (* fargs *)
  let@ (o, mappings, _) = match calling_mode with
    | `CallByValue -> return (o, mappings, 0)
    | `CallByReference ->
    ListM.fold_leftM (fun (o, mappings, counter) earg ->
        let aarg = {asym = earg.esym; typ = earg.typ} in
        let item = aarg_item loc aarg in
        let (o', mapping') =
          make_owned_funarg loc counter item.it item.path aarg.typ in
        let c =
          (`Constraint (LC.t_ (good_ (pointer_ct aarg.typ, item.it))),
           (loc, Some ("&ARG" ^ string_of_int counter ^ " constraint")))
        in
        let mappings =
          mod_mapping "end" mappings
            (fun mapping -> (item :: mapping') @ mapping)
        in
        return (o @ [c] @ o', mappings, counter+1)
      )
      (o, mappings, 0) fspec.function_arguments
  in

  let@ (o, mappings) =
    ListM.fold_leftM (fun (o, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
              let@ (o', mapping') = 
                apply_ownership_spec layouts rpredicates lpredicates
                  "end" mappings (loc, cond) 
              in
              let mappings = 
                mod_mapping "end" mappings 
                  (fun mapping -> mapping' @ mapping)
              in
              return (o @ o', mappings)
        | Ast.Constraint (oq, cond) ->
           let@ c = resolve_constraint loc layouts rpredicates lpredicates "end" mappings (oq, cond) in
           return (o @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = resolve_index_term loc layouts rpredicates lpredicates "end" mappings [] it in
           let mapping' = [{path = Ast.var name; it = sym_ (s, IT.bt it); o_sct}] in
           let mappings = 
             mod_mapping "end" mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (o @ [(`Define (s, it), (loc, None))], mappings)
      )
      (o, mappings) fspec.post_condition
  in

  let end_naming = SuggestEqs.make_naming "end" (get_mappings_info mappings "end") in
  let o = o @ [(`Constraint (LC.t_ end_naming), (loc, None))] in

  let lrt = 
    List.fold_right (fun (oarg, info) lrt ->
        match oarg with
        | `Logical (s, bt) -> LRT.Logical ((s,bt), info, lrt)
        | `Define (s, it) -> LRT.Define ((s, it), info, lrt)
        | `Resource re -> LRT.Resource (re, info, lrt)
        | `Constraint lc -> LRT.Constraint (lc, info, lrt)
      ) o LRT.I
  in
  let rt = RT.mComputational oA lrt in
  
  let ft =
    List.fold_right (fun (iarg, info) lft ->
        match iarg with
        | `Computational (s, bt) -> AT.Computational ((s,bt), info, lft)
        | `Logical (s, bt) -> AT.Logical ((s,bt), info, lft)
        | `Define (s, it) -> AT.Define ((s, it), info, lft)
        | `Resource re -> AT.Resource (re, info, lft)
        | `Constraint lc -> AT.Constraint (lc, info, lft)
      ) i (AT.I rt)
  in

  return (ft, fspec.trusted, StringMap.find "start" mappings)


  
let make_label_spec
      (loc : Loc.t)
      layouts
      rpredicates
      lpredicates
      (lname : string)
      start_mapping
      (lspec: Ast.label_spec)
  =
  (* let largs = List.map (fun (os, t) -> (Option.value (Sym.fresh ()) os, t)) largs in *)
  let i = [] in
  let mappings = 
    StringMap.add lname []
      (StringMap.add "start" start_mapping 
         StringMap.empty )
  in

  (* globs *)
  let@ (i, mappings) = 
    ListM.fold_leftM (fun (i, mappings) garg ->
        match garg.accessed with
        | None ->  return (i, mappings)
        | Some loc -> 
           let item = garg_item loc garg in
           let@ (i', mapping') = 
             make_owned ~loc ~oname:None ~pointer:item.it 
               ~path:item.path ~sct:garg.typ ~o_permission:None ~o_value:None
           in
           let mappings = 
             mod_mapping lname mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (i @ i', mappings)
      )
      (i, mappings) lspec.global_arguments
  in

  (* fargs *)
  let@ (i, mappings, _) = 
    ListM.fold_leftM (fun (i, mappings, counter) aarg ->
        let item = aarg_item loc aarg in
        let (i', mapping') = make_owned_funarg loc counter item.it item.path aarg.typ in
        let mappings = 
          mod_mapping lname mappings
            (fun mapping -> mapping' @ mapping)
        in
        return (i @ i', mappings, counter + 1)
      )
      (i, mappings, 0) lspec.function_arguments
  in

  (* largs *)
  let@ (i, mappings) = 
    (* In the label's argument list, the left-most arguments have the
       inner-most scope. In the mapping, we also want the arguments
       that are inner-most scoped-wise to be left-most. *)
    let@ (i, mapping') = 
      ListM.fold_leftM (fun (i, mapping) (aarg : aarg) ->
          let a = (`Computational (aarg.asym, BT.Loc), (loc, None)) in
          let item = aarg_item loc aarg in
          let@ (i', mapping') = 
            make_owned ~loc ~oname:None ~pointer:item.it 
              ~path:item.path ~sct:aarg.typ ~o_permission:None ~o_value:None
          in 
          let c = 
            (`Constraint (LC.t_ (good_ (pointer_ct aarg.typ, item.it))),
             (loc, None))
          in
          return (i @ a :: c :: i', (item :: mapping') @ mapping)
        )
        (i, []) lspec.label_arguments
    in
    let mappings =
      mod_mapping lname mappings
        (fun mapping -> List.rev mapping' @ mapping)
    in
    return (i, mappings)
  in


  let@ (i, mappings) = 
    ListM.fold_leftM (fun (i, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource cond ->
              let@ (i', mapping') = 
                apply_ownership_spec layouts rpredicates lpredicates
                  lname mappings (loc, cond) in
              let mappings = 
                mod_mapping lname mappings 
                  (fun mapping -> mapping' @ mapping)
              in
              return (i @ i', mappings)
        | Ast.Constraint (oq, cond) ->
           let@ c = resolve_constraint loc layouts rpredicates lpredicates lname mappings (oq, cond) in
           return (i @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = 
             resolve_index_term loc layouts rpredicates lpredicates
               lname mappings [] it
           in
           let mapping' = [{path = Ast.var name; it = sym_ (s, IT.bt it); o_sct}] in
           let mappings = 
             mod_mapping lname mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (i @ [(`Define (s, it), (loc, None))], mappings)
      )
      (i, mappings) lspec.invariant
  in

  let inv_naming = SuggestEqs.make_naming lname (get_mappings_info mappings lname) in
  let i = i @ [(`Constraint (LC.t_ inv_naming), (loc, None))] in

  let lt =
    List.fold_right (fun (iarg, info) lt ->
        match iarg with
        | `Computational (s, bt) -> AT.Computational ((s,bt), info, lt)
        | `Logical (s, bt) -> AT.Logical ((s,bt), info, lt)
        | `Define (s, it) -> AT.Define ((s, it), info, lt)
        | `Resource re -> AT.Resource (re, info, lt)
        | `Constraint lc -> AT.Constraint (lc, info, lt)
      ) i (AT.I False.False)
  in
  return (lt, StringMap.find lname mappings)





