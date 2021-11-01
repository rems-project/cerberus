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
open Resources.RE
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

  let member_offset tag member = 
    let iv = CF.Impl_mem.offsetof_ival (CF.Tags.tagDefs ()) tag member in
    Memory.int_of_ival iv
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





let make_owned_funarg floc i (pointer : IT.t) path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     Debug_ocaml.error "void argument"
  | _ ->
     let descr = "ARG" ^ string_of_int i in
     let pointee = Sym.fresh () in
     let pointee_bt = BT.of_sct sct in
     let pointee_t = sym_ (pointee, pointee_bt) in
     let l = (`Logical (pointee, pointee_bt), (floc, Some (descr ^ "value"))) in
     let mapping = [{
         path = Ast.pointee path; 
         it = pointee_t;
         o_sct = Some sct;
       }]
     in
     let r = 
       (`Resource 
          (RE.Point {
              ct = sct; 
              pointer; 
              permission = bool_ true; 
              value = pointee_t; 
              init = bool_ true
            }),
        (floc, Some "ownership of function argument location"))
     in
     let c = 
       (`Constraint (LC.t_ (good_ (sct, pointee_t))), 
        (floc, Some (descr ^ "value constraint")))
     in
     ([l;r;c], mapping)


let make_owned loc (pointer : IT.t) path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     fail {loc; msg = Generic !^"cannot make owned void* pointer"}
  | _ ->
     let pointee = Sym.fresh () in
     let pointee_bt = BT.of_sct sct in
     let pointee_t = sym_ (pointee, pointee_bt) in
     let l = (`Logical (pointee, pointee_bt), (loc, Some "pointee")) in
     let mapping = {
         path = Ast.pointee path; 
         it = pointee_t;
         o_sct = Some sct;
       } 
     in
     let c = 
       (`Constraint (LC.t_ (good_ (sct, pointee_t))), 
        (loc, Some "value constraint"))
     in
     let r = 
       (`Resource (RE.Point {
           ct = sct; 
           pointer; 
           permission = bool_ true; 
           value = pointee_t; 
           init = bool_ true
           }),
        (loc, Some "ownership"))
     in
     return ([l;r;c], [mapping])





let make_block loc (pointer : IT.t) path sct =
  let open Sctypes in
  match sct with
  | Sctype (_, Void) ->
     fail {loc; msg = Generic !^"cannot make owned void* pointer"}
  | _ ->
     let pointee = Sym.fresh () in
     let init = Sym.fresh () in
     let pointee_bt = BT.of_sct sct in
     let init_bt = BT.Bool in
     let pointee_t = sym_ (pointee, pointee_bt) in
     let init_t = sym_ (init, init_bt) in
     let l = 
       [(`Logical (pointee, pointee_bt), (loc, Some "uninitialised value"));
        (`Logical (init, init_bt), (loc, Some "initialisedness"))]
     in
     let mapping = [] in
     let r = 
       (`Resource (RE.Point {
            ct = sct; 
            pointer;
            permission = bool_ true;
            value = pointee_t;
            init = init_t
          }),
        (loc, Some "ownership"))
     in
     return (l@[r], mapping)

let make_pred loc (predicates : (string * ResourcePredicates.definition) list) 
      (pred, def) ~oname pointer iargs = 
  let (mapping, l) = 
    List.fold_right (fun (oarg, bt) (mapping, l) ->
        let s, it = IT.fresh bt in
        let l = (`Logical (s, bt), (loc, Some ("output argument '" ^ oarg ^"'"))) :: l in
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
  let oargs = List.map (fun (`Logical (s, ls), _) -> sym_ (s, ls)) l in
  let r = 
    (`Resource (RE.Predicate {
         name = pred; 
         pointer = pointer;
         iargs; 
         oargs;
         permission = bool_ true;
       }),
     (loc, None))
  in
  return (l @ [r], mapping)



let make_qpred loc (predicates : (string * ResourcePredicates.definition) list) 
      (pred, def) ~oname ~qpointer:(qp,qbt) ~condition pointer iargs = 
  assert (BT.equal qbt BT.Loc);
  let@ () = match is_sym pointer with
    | Some (s, sbt) when Sym.equal s qp && BT.equal sbt qbt -> return ()
    | _ -> fail {loc; msg = Generic (!^"Predicate pointer argument must be the quantified variable")}
  in
  let (mapping, l) = 
    List.fold_right (fun (oarg, bt) (mapping, l) ->
        let lifted_bt = BT.Array (qbt, bt) in
        let s, it = IT.fresh lifted_bt in
        let l = (`Logical (s, lifted_bt), (loc, Some ("output argument '" ^ oarg ^"'"))) :: l in
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
  let oargs = 
    List.map (fun (`Logical (s, ls), _) -> 
        get_ (sym_ (s, ls)) (sym_ (qp, qbt))
      ) l 
  in
  let r = 
    (`Resource (RE.QPredicate {
         name = pred; 
         qpointer = qp;
         iargs; 
         oargs;
         permission = condition;
       }),
     (loc, None))
  in
  return (l @ [r], mapping)










(* change this to return unit IT.term, then apply index term type
   checker *)
let resolve_index_term loc 
      (layouts : Memory.struct_decls)
      (default_mapping_name : string)
      (mappings : mapping StringMap.t)
      (oquantifier : (string * (Sym.t * BT.t)) option)
      (term: Ast.term) 
        : (IT.typed * Sctypes.t option, type_error) m =
  let lookup term mapping = 
    match term, oquantifier with
    | Var name, Some (name', (s, bt)) when String.equal name name' -> 
       return (sym_ (s, bt), None)
    | _ ->
       let found = List.find_opt (fun {path;_} -> Ast.term_equal path term) mapping in
       match found with
       | Some {it; o_sct; _} -> 
          return (it, o_sct)
       | None -> 
          fail {loc; msg = Generic (!^"term" ^^^ Ast.Terms.pp false term ^^^ !^"does not apply")}
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
       let@ (it, oct) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
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
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
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
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       let t = IT (Arith_op (Mul (it, it')), IT.bt it) in
       return (t, None)
    | Division (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Arith_op (Div (it, it')), IT.bt it), None)
    | Exponentiation (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Arith_op (Exp (it, it')), IT.bt it), None)
    | Remainder (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       return (IT (Arith_op (Rem (it, it')), IT.bt it), None)
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
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (LTPointer (it, it')), Bool)
         | _ -> IT (Arith_op (LT (it, it')), Bool)
       in
       return (t, None)
    | GreaterThan (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (LTPointer (it', it)), Bool)
         | _ -> IT (Arith_op (LT (it', it)), Bool)
       in
       return (t, None)
    | LessOrEqual (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (LEPointer (it, it')), Bool)
         | _ -> IT (Arith_op (LE (it, it')), Bool)
       in
       return (t, None)
    | GreaterOrEqual (it, it') -> 
       let@ (it, _) = resolve it mapping in
       let@ (it', _) = resolve it' mapping in
       let t = match IT.bt it with
         | Loc -> IT (Pointer_op (LEPointer (it', it)), Bool)
         | _ -> IT (Arith_op (LE (it', it)), Bool)
       in
       return (t, None)
    | Member (t, member) ->
       let@ (st, _) = resolve t mapping in
       let ppf () = Ast.Terms.pp false term in
       let@ tag = match IT.bt st with
         | Struct tag -> return tag
         | _ -> fail {loc; msg = Generic (ppf () ^^^ !^"is not a struct")}
       in
       let layout = SymMap.find tag layouts in
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
    | IntegerToPointerCast t ->
       let@ (t, _) = resolve t mapping in
       return (IT (Pointer_op (IntegerToPointerCast t), Loc), None)
    | PointerToIntegerCast t ->
       let@ (t, _) = resolve t mapping in
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
    | App (t1, t2) ->
       let@ (it1, _) = resolve t1 mapping in
       let@ (it2, _) = resolve t2 mapping in
       let ppf () = Ast.Terms.pp false t1 in
       begin match IT.bt it1 with
       | BT.Array (_, bt) -> 
          return (IT (Array_op (Get (it1, it2)), bt), None)
       | _ -> 
          fail {loc; msg = Generic (ppf () ^^^ !^"is not an array")}
       end
    | Env (t, mapping_name) ->
       begin match StringMap.find_opt mapping_name mappings with
       | Some mapping -> 
          resolve t mapping
       | None ->
          fail {loc; msg = Generic (!^"label" ^^^ !^mapping_name ^^^ !^"does not apply")}
       end
  in
  resolve term (StringMap.find default_mapping_name mappings)
     


let resolve_constraint loc layouts default_mapping_name mappings lc = 
  let@ (lc, _) = resolve_index_term loc layouts default_mapping_name mappings None lc in
  return (LC.t_ lc)




let apply_ownership_spec layouts predicates default_mapping_name mappings (loc, {oq; predicate; arguments; oname}) =
  match predicate with
  | "Owned" ->
     if oq <> None then
       fail {loc; msg = Generic !^"cannot use 'Owned' with quantifier"}
     else
       begin match arguments with
       | [path] ->
          let@ (it, sct) = resolve_index_term loc layouts default_mapping_name mappings None path in
          begin match sct with
          | None -> 
             fail {loc; msg = Generic (!^"cannot assign ownership of" ^^^ (Ast.Terms.pp false path))}
          | Some Sctype (_, Pointer sct2) ->
             make_owned loc it path sct2
          | Some _ ->
             fail {loc; msg = Generic (Ast.Terms.pp false path ^^^ !^"is not a pointer")}
          end
       | _ ->
          fail {loc; msg = Generic !^"Owned predicate takes 1 argument, which has to be a path"}
       end
  | "Block" ->
     if oq <> None then
       fail {loc; msg = Generic !^"cannot use 'Block' with quantifier"}
     else
       begin match arguments with
       | [path] ->
          let@ (it, sct) = resolve_index_term loc layouts default_mapping_name mappings None path in
          begin match sct with
          | None -> 
             fail {loc; msg = Generic (!^"cannot assign ownership of" ^^^ (Ast.Terms.pp false path))}
          | Some (Sctype (_, Pointer sct2)) -> 
             make_block loc it path sct2
          | Some _ ->
             fail {loc; msg = Generic (Ast.Terms.pp false path ^^^ !^"is not a pointer")}
          end
       | _ ->
          fail {loc; msg = Generic !^"Block predicate takes 1 argument, which has to be a path"}
       end
  | _ ->
     let@ def = match List.assoc_opt String.equal predicate predicates with
       | Some def -> return def
       | None -> fail {loc; msg = Unknown_resource_predicate predicate}
     in
     let@ (pointer, arguments) = match arguments with
       | pointer :: arguments -> return (pointer, arguments)
       | _ ->
          fail {loc; msg = Generic !^("predicates take at least one (pointer) argument")}
     in
     let oq = 
       Option.bind oq
         (fun (name, bt, condition) -> 
           Some ((name, (Sym.fresh_pretty name, bt)), condition))
     in
     let@ (pointer_resolved, _) = 
       resolve_index_term loc layouts default_mapping_name mappings 
         (Option.map fst oq) pointer 
     in
     let@ iargs_resolved = 
       ListM.mapM (fun arg ->
           let@ (t, _) = 
             resolve_index_term loc layouts default_mapping_name mappings 
               (Option.map fst oq) arg in
           return t
         ) arguments
     in
     let@ result = match oq with
       | None ->
          make_pred loc predicates (predicate, def) 
            ~oname pointer_resolved iargs_resolved 
       | Some ((name, (s, bt)), condition) -> 
          let@ (condition, _) = 
             resolve_index_term loc layouts default_mapping_name mappings 
               (Some (name, (s, bt))) condition 
          in
          make_qpred loc predicates (predicate, def) 
            ~oname ~qpointer:(s, bt) ~condition pointer_resolved iargs_resolved 
     in
     return result


let apply_logical_predicate layouts default_mapping_name mappings (loc, cond) =
  let@ lc = match cond.oq with
    | None ->
       let@ args_resolved = 
         ListM.mapM (fun arg ->
             let@ (t, _) = 
               resolve_index_term loc layouts default_mapping_name mappings 
                 None arg in
             return t
           ) cond.arguments
       in
       return (LC.Pred { name = cond.predicate; args = args_resolved })
    | Some (name, bt, condition) -> 
       let q = Sym.fresh_named name in
       let@ args_resolved = 
         ListM.mapM (fun arg ->
             let@ (t, _) = 
               resolve_index_term loc layouts default_mapping_name mappings 
                 (Some (name, (q, bt))) arg in
             return t
           ) cond.arguments
       in
       let@ (condition, _) = 
         resolve_index_term loc layouts default_mapping_name mappings 
           (Some (name, (q, bt))) condition
       in
       let pred = LC.Pred.{ name = cond.predicate; args = args_resolved } in
       return (LC.QPred { q = (q, bt); condition; pred })
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
      if List.mem name mapping_names then 
        f mapping
      else 
        mapping
    ) mappings


let make_fun_spec loc (layouts : Memory.struct_decls) rpredicates lpredicates fsym (fspec : function_spec)
    : (AT.ft * mapping, type_error) m = 
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
           let@ (i', mapping') = make_owned loc item.it item.path garg.typ in
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
    ListM.fold_leftM (fun (i, mappings, counter) (aarg : aarg) ->
        let descr = "&ARG" ^ string_of_int counter in
        let a = (`Computational (aarg.asym, BT.Loc), (loc, Some descr)) in
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
        | Ast.Predicate cond ->
           begin match List.assoc_opt String.equal cond.predicate lpredicates with
           | Some p ->
              let@ c = apply_logical_predicate layouts "start" mappings (loc, cond) in
              return (i @ [c], mappings)
           | None ->
              let@ (i', mapping') = 
                apply_ownership_spec layouts rpredicates
                  "start" mappings (loc, cond) 
              in
              let mappings = 
                mod_mapping "start" mappings
                  (fun mapping -> mapping' @ mapping)
              in
              return (i @ i', mappings)
           end
        | Ast.Term cond ->
           let@ c = resolve_constraint loc layouts 
                      "start" mappings cond in
           return (i @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = 
             resolve_index_term loc layouts 
               "start" mappings None it
           in
           let mapping' = [{path = Ast.var name; it; o_sct}] in
           let mappings = 
             mod_mappings ["start"; "end"] mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (i @ [(`Define (s, it), (loc, None))], mappings)
      )
      (i, mappings) fspec.pre_condition
  in

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
           let@ (o', mapping') = make_owned loc item.it item.path garg.typ in
           let mappings =
             mod_mapping "end" mappings
               (fun mapping -> (item :: mapping') @ mapping)
           in
           return (o @ o', mappings)
      )
      (o, mappings) fspec.global_arguments
  in

  (* fargs *)
  let@ (o, mappings, _) = 
    ListM.fold_leftM (fun (o, mappings, counter) aarg ->
        let item = aarg_item loc aarg in
        let (o', mapping') = 
          make_owned_funarg loc counter item.it item.path aarg.typ in
        let c = 
          (`Constraint (LC.t_ (good_value layouts (pointer_ct aarg.typ) item.it)), 
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
        | Ast.Predicate cond ->
           begin match List.assoc_opt String.equal cond.predicate lpredicates with
           | Some p ->
              let@ c = apply_logical_predicate layouts "end" mappings (loc, cond) in
              return (o @ [c], mappings)
           | None ->
              let@ (o', mapping') = 
                apply_ownership_spec layouts rpredicates
                  "end" mappings (loc, cond) 
              in
              let mappings = 
                mod_mapping "end" mappings 
                  (fun mapping -> mapping' @ mapping)
              in
              return (o @ o', mappings)
           end
        | Ast.Term cond ->
           let@ c = resolve_constraint loc layouts "end" mappings cond in
           return (o @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = 
             resolve_index_term loc layouts 
               "end" mappings None it
           in
           let mapping' = [{path = Ast.var name; it; o_sct}] in
           let mappings = 
             mod_mapping "end" mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (o @ [(`Define (s, it), (loc, None))], mappings)
      )
      (o, mappings) fspec.post_condition
  in

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

  return (ft, StringMap.find "start" mappings)


  
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
           let@ (i', mapping') = make_owned loc item.it item.path garg.typ in
           let mappings = 
             mod_mapping lname mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (i @ i', mappings)
      )
      (i, mappings) lspec.global_arguments
  in

  (* fargs *)
  let@ (i, mappings) = 
    ListM.fold_leftM (fun (i, mappings) aarg ->
        let item = aarg_item loc aarg in
        let@ (i', mapping') = make_owned loc item.it item.path aarg.typ in
        let mappings = 
          mod_mapping lname mappings
            (fun mapping -> mapping' @ mapping)
        in
        return (i @ i', mappings)
      )
      (i, mappings) lspec.function_arguments
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
          let@ (i', mapping') = make_owned loc item.it item.path aarg.typ in 
          let c = 
            (`Constraint (LC.t_ (good_value layouts (pointer_ct aarg.typ) item.it)),
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
        | Ast.Predicate cond ->
           begin match List.assoc_opt String.equal cond.predicate lpredicates with
           | Some p ->
              let@ c = apply_logical_predicate layouts lname mappings (loc, cond) in
              return (i @ [c], mappings)
           | None ->
              let@ (i', mapping') = 
                apply_ownership_spec layouts rpredicates
                  lname mappings (loc, cond) in
              let mappings = 
                mod_mapping lname mappings 
                  (fun mapping -> mapping' @ mapping)
              in
              return (i @ i', mappings)
           end
        | Ast.Term cond ->
           let@ c = resolve_constraint loc layouts lname mappings cond in
           return (i @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = 
             resolve_index_term loc layouts 
               lname mappings None it
           in
           let mapping' = [{path = Ast.var name; it; o_sct}] in
           let mappings = 
             mod_mapping lname mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (i @ [(`Define (s, it), (loc, None))], mappings)
      )
      (i, mappings) lspec.invariant
  in

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





