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
module LAT = LogicalArgumentTypes
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



open Builtins








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
         let sct = Sctypes.of_ctype_unsafe loc ct in
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



let resource_counter = ref 0

let oarg_name = function
  | None ->
     let i = !resource_counter in
     resource_counter := i + 1;
     "R" ^ string_of_int i
  | Some name ->
     name



let make_owned_funarg floc i (pointer : IndexTerms.t) path sct =
  let open Sctypes in
  match sct with
  | Void ->
     Debug_ocaml.error "void argument"
  | _ ->
     let descr = "ARG" ^ string_of_int i in
     let oarg_name = oarg_name None in
     let oarg_s = Sym.fresh_named oarg_name in
     let oarg_members = Resources.owned_oargs sct in
     let oarg = sym_ (oarg_s, oarg_members) in
     let value = recordMember_ ~member_bt:(BT.of_sct sct) (oarg, Resources.value_sym) in
     let mapping = [{
         path = Ast.pointee path; 
         it = value;
         o_sct = Some sct;
       }]
     in
     let r = 
       (`Resource 
          (oarg_s, P {
              name = Owned sct; 
              pointer; 
              permission = bool_ true; 
              iargs = [];
            },
           oarg_members),
        (floc, Some (descr ^ " ownership")))
     in
     let c = 
       (`Constraint
          (LC.t_ (good_ (sct, value))),
          (floc, Some (descr ^ " good")))
     in
     ([r;c], mapping)


let make_owned ~loc ~oname ~pointer ~path ~sct ~o_permission =
  let open Sctypes in
  match sct with
  | Void ->
     fail {loc; msg = Generic !^"cannot make owned void* pointer"}
  | _ ->
     let oarg_name = oarg_name oname in
     let oarg_s = Sym.fresh_named oarg_name in
     let oarg_members = Resources.owned_oargs sct in
     let oarg = sym_ (oarg_s, oarg_members) in
     let pointee_t = recordMember_ ~member_bt:(BT.of_sct sct) (oarg, Resources.value_sym) in
     let mapping = [{
         path = Ast.pointee path; 
         it = pointee_t;
         o_sct = Some sct;
       }] 
     in
     let mapping = 
          {path = Ast.Var oarg_name; 
           it = oarg; 
           o_sct = None } :: mapping
     in
     let permission = Option.value o_permission ~default:(bool_ true) in
     let r = 
       (`Resource (oarg_s, P {
           name = Owned sct; 
           pointer; 
           permission = permission; 
           iargs = [];
          },
          oarg_members),
        (loc, None))
     in
     let c = 
       (`Constraint 
          (LC.t_ (impl_ (permission, good_ (sct, pointee_t)))),
        (loc, None))
     in
     return ([r;c], mapping)


let make_block ~loc ~oname ~pointer ~path ~sct ~o_permission =
  let open Sctypes in
  match sct with
  | Void ->
     fail {loc; msg = Generic !^"cannot create 'block' for void* pointer"}
  | _ ->
     let oarg_name = oarg_name oname in
     let oarg_s = Sym.fresh_named oarg_name in
     let oarg_members = Resources.block_oargs in
     let oarg = sym_ (oarg_s, oarg_members) in
     let mapping = 
       [{path = Ast.Var oarg_name; 
         it = oarg; 
         o_sct = None }]
     in
     let r = 
       (`Resource (oarg_s, P {
           name = Block sct; 
           pointer; 
           permission = Option.value o_permission ~default:(bool_ true); 
           iargs = [];
          },
          oarg_members),
        (loc, None))
     in
     return ([r], mapping)




let make_qowned ~loc ~oname ~pointer ~q:(qs,qbt) ~step ~condition ~path ~sct =
  let open Sctypes in
  let@ () = match qbt with
    | BT.Integer -> return ()
    | _ -> fail {loc; msg = Generic (!^"Quantifier for iterated resource must be of type 'integer'")}
  in
  let@ () = 
    if IT.equal (IT.int_ (Memory.size_of_ctype sct)) step then return ()
    else fail {loc; msg = Generic !^"pointer increment must match size of array-cell type"}
  in
  match sct with
  | Void ->
     fail {loc; msg = Generic !^"cannot make owned void* pointer"}
  | _ ->
     let oarg_name = oarg_name oname in
     let oarg_s = Sym.fresh_named oarg_name in
     let oarg_members = Resources.q_owned_oargs sct in
     let oarg = sym_ (oarg_s, oarg_members) in
     let mapping = 
       [{path = Ast.var oarg_name; 
         it = oarg; 
         o_sct = None }]
     in
     let r = 
       (`Resource (oarg_s, Q {
           name = Owned sct; 
           pointer; 
           q = qs;
           permission = condition; 
           step = IT.int_ (Memory.size_of_ctype sct);
           iargs = [];
          },
          oarg_members),
        (loc, Some "ownership"))
     in
     let c = 
       let value_t = 
         recordMember_ ~member_bt:(BT.Map (Integer, BT.of_sct sct))
           (oarg, Resources.value_sym)
       in
       let q = sym_ (qs, qbt) in
       (`Constraint 
          (LC.forall_ (qs, qbt) (
               impl_ (condition, good_ (sct, map_get_ value_t q))
          )),
        (loc, Some "good"))
     in
     return ([r;c], mapping)




let make_pred loc (pred, def) ~oname pointer iargs ~o_permission = 
  let oarg_name = oarg_name oname in
  let oarg_s = Sym.fresh_named oarg_name in
  let oarg_members = def.oargs in
  let oarg = sym_ (oarg_s, BT.Record oarg_members) in
  let mapping = 
    [{path = Ast.var oarg_name; 
      it = oarg; 
      o_sct = None }]
  in
  let r = 
    (`Resource (oarg_s, P {
         name = PName pred; 
         pointer = pointer;
         iargs; 
         permission = Option.value ~default:(bool_ true) o_permission;
       },
       BT.Record oarg_members),
     (loc, None))
  in
  return ([r], mapping)



let make_qpred loc (pred, def) ~oname ~pointer ~q:(qs,qbt) ~step ~condition iargs = 
  let@ () = match qbt with
    | BT.Integer -> return ()
    | _ -> fail {loc; msg = Generic (!^"Quantifier for iterated resource must be of type 'integer'")}
  in
  let oarg_name = oarg_name oname in
  let oarg_s = Sym.fresh_named oarg_name in
  let oarg_members = List.map_snd (BT.make_map_bt qbt) def.oargs in
  let oarg = sym_ (oarg_s, BT.Record oarg_members) in
  let mapping = 
    [{path = Ast.var oarg_name; 
      it = oarg; 
      o_sct = None }]
  in
  let r = 
    (`Resource (oarg_s, Q {
         name = PName pred; 
         pointer;
         q = qs;
         step = step;
         iargs; 
         permission = condition;
       },
       BT.Record oarg_members),
     (loc, None))
  in
  return ([r], mapping)


 


let lookup_sym_map_by_string kind id m =
  let m' = List.map (fun (s, def) -> (todo_string_of_sym s, (s, def)))
    (SymMap.bindings m) in
  let res = List.assoc_opt String.equal id m' in
  if Option.is_none res
  then Pp.debug 2 (lazy (Pp.item ("Known " ^ kind)
        (Pp.list Pp.string (List.map fst m'))))
  else ();
  res



(* copying from typing.ml *)
let get_resource_predicate_def loc id global =
  let open TypeErrors in
  let open Global in
  match lookup_sym_map_by_string "resource predicates" id global.resource_predicates with
  | Some (sym, def) -> return (sym, def)
  | None ->
     let logical = Option.is_some (lookup_sym_map_by_string "logical predicates"
             id global.logical_predicates) in
     fail {loc; msg = Unknown_resource_predicate {id = Sym.fresh_named id; logical}}


(* copying from typing.ml *)
let get_logical_predicate_def loc id global =
  let open TypeErrors in
  let open Global in
  match lookup_sym_map_by_string "logical predicates" id global.logical_predicates with
  | Some (sym, def) -> return (sym, def)
  | None ->
     let resource = Option.is_some (lookup_sym_map_by_string "resource predicates"
             id global.resource_predicates) in
     fail {loc; msg = Unknown_logical_predicate {id = Sym.fresh_named id; resource}}





(* change this to return unit IT.term, then apply index term type
   checker *)
let resolve_index_term loc 
      (global : Global.t)
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
  (* let all_rets_of name mapping = *)
  (*   List.filter_map (fun {it; path; _} -> match path with *)
  (*     | PredOutput (name2, oarg) when String.equal name name2 -> Some (oarg, it) *)
  (*     | _ -> None) mapping *)
  (* in *)
  (* let pred_mapping name mapping = *)
  (*   let match_name = function *)
  (*     | PredOutput (name2, _) -> String.equal name name2 *)
  (*     | _ -> false *)
  (*   in *)
  (*   let ms_with = StringMap.bindings mappings *)
  (*     |> List.map snd *)
  (*     |> List.filter (List.exists (fun {path; _} -> match_name path)) *)
  (*   in *)
  (*   match ms_with with *)
  (*     | [mapping] -> mapping *)
  (*     | _ -> mapping *)
  (* in *)
  let rec resolve (term : Ast.term) mapping quantifiers
        : (IT.typed * Sctypes.t option, type_error) m =
    match term with
    | Addr name ->
       lookup (Addr name) "an address" mapping quantifiers
    | Var ln ->
       lookup (Var ln) "a variable" mapping quantifiers
    | Pointee it ->
       lookup (Pointee it) "a pointee (i.e. not Owned)" mapping quantifiers
    | Bool b -> 
       return (IT (Lit (IT.Bool b), BT.Bool), None)
    | Integer i -> 
       return (IT (Lit (IT.Z i), BT.Integer), None)
    | Addition (it, it') -> 
       let@ (it, oct) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let@ t = return (IT (Arith_op (Add (it, it')), IT.bt it)) in
       return (t, None)
    | Subtraction (it, it') -> 
       let@ (it, _) = resolve it mapping quantifiers in
       let@ (it', _) = resolve it' mapping quantifiers in
       let@ t = return (IT (Arith_op (Sub (it, it')), IT.bt it)) in
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
    (* | Equality (it, PredEqRegulator (exclude, it')) -> *)
    (*    let@ (nm, nm') = begin match it, it' with *)
    (*      | Var nm, Var nm' -> return (nm, nm') *)
    (*      | Var _, _ -> fail {loc; msg = Generic (!^ "predicate return eq cannot handle" ^^^ *)
    (*          Ast.Terms.pp false it')} *)
    (*      | _, _ -> fail {loc; msg = Generic (!^ "predicate return eq cannot handle" ^^^ *)
    (*          Ast.Terms.pp false it)} *)
    (*    end in *)
    (*    let rets = all_rets_of nm mapping in *)
    (*    let@ () = if List.length rets == 0 *)
    (*        then fail {loc; msg = Generic (!^ nm ^^^ !^ "not a known resource predicate")} *)
    (*        else return () in *)
    (*    let@ () = ListM.iterM (fun s -> if Option.is_some (List.assoc_opt String.equal s rets) *)
    (*        then return () *)
    (*        else fail {loc; msg = Generic (!^s ^^^ !^ "not a return param of" ^^^ !^ nm)}) *)
    (*      exclude in *)
    (*    let eq_rets = List.filter (fun (nm, it) -> not (List.exists (String.equal nm) exclude)) *)
    (*        rets in *)
    (*    let@ eqs = ListM.mapM (fun (arg_nm, it) -> *)
    (*        let@ (it', _) = resolve (PredOutput (nm', arg_nm)) mapping quantifiers in *)
    (*        return (eq_ (it, it'))) eq_rets in *)
    (*    return (IT (Bool_op (And eqs), Bool), None) *)
    (* | PredEqRegulator (_, _) -> *)
    (*    fail {loc; msg = Generic (!^ "return param limiter" ^^^ Ast.Terms.pp false term ^^^ *)
    (*         !^ "only permitted on right-hand-side of equalities")} *)
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
       begin match IT.bt st with
       | Struct tag -> 
          let@ layout = match SymMap.find_opt tag global.Global.struct_decls with
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
       | Record members -> 
          let members' = List.map (fun (s, bt) -> (todo_string_of_sym s, (s, bt))) members in
          let@ (member,bt) = match List.assoc_opt String.equal (Id.s member) members' with
            | Some (s, bt) -> 
               return (s, bt)
            | None -> 
               let err = 
                 !^"Illtyped index term" ^^^ ppf () ^^ dot ^^^
                   ppf () ^^^ !^"does not have member" ^^^ Id.pp member
               in
               fail {loc; msg = Generic err}
          in
          return (IT (Record_op (RecordMember (st, member)), bt), None)
(* FIXME: add datatype case here *)
       | _ -> fail {loc; msg = Generic (ppf () ^^^ !^"is not a struct")}
       end
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
           ) global.Global.struct_decls)
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
       let@ layout = match SymMap.find_opt tag global.Global.struct_decls with
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
    (* | ArrayShift {pointer =t; index} -> *)
    (*    let@ (pointer, osct) = resolve t mapping quantifiers in *)
    (*    let@ (index, _) = resolve index mapping quantifiers in *)
    (*    let ppf () = Ast.Terms.pp false t in *)
    (*    let@ sct = match osct with *)
    (*      | None ->  *)
    (*         fail {loc; msg = Generic (!^"Cannot resolve C type of term" ^^^  *)
    (*                                     Ast.pp false t)} *)

    (*      | Some (Pointer sct) -> return sct *)
    (*      | Some _ ->  *)
    (*         fail {loc; msg = Generic (ppf () ^^^ !^"is not a pointer")} *)
    (*    in *)
    (*    return (arrayShift_ (pointer, sct, index), Some (Sctypes.Pointer sct)) *)
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
    | DatatypeCons (nm, mems) ->
       let@ (sym, info) = match lookup_sym_map_by_string "datatype constructors"
           nm global.Global.datatype_constrs
       with
       | None -> fail {loc; msg = Unknown_datatype_constr (Sym.fresh_named nm)}
       | Some r -> return r
       in
       let p_map = List.fold_left (fun m (nm, bt) -> StringMap.add (todo_string_of_sym nm) nm m)
           StringMap.empty info.c_params in
       let@ mems = ListM.mapM (fun (nm, t) ->
           let@ (t, _) = resolve t mapping quantifiers in
           let@ nm = match StringMap.find_opt nm p_map with
             | Some sym -> return sym
             | None -> fail {loc; msg = Generic (Pp.string ("unexpected datatype field: " ^ nm))}
           in
           return (nm, t)) mems
       in
       return (datatype_cons_ sym info.c_datatype_tag mems, None)
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
       let sym = Sym.fresh_cn s in
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
       let@ b = apply_builtin_funs loc name (List.map fst args_oscts) in
       begin match b with
         | None ->
           let@ (name, def) = get_logical_predicate_def loc name global in
           return (pred_ name (List.map fst args_oscts) def.return_bt, None)
         | Some t -> return (t, None)
       end
  in
  resolve term (StringMap.find default_mapping_name mappings) quantifiers



let rec resolve_typ loc 
      (global : Global.t)
      (default_mapping_name : string)
      (mappings : mapping StringMap.t)
      (oquantifier : (string * (Sym.t * BT.t)) option)
      (typ: Ast.typ) =
  match typ with
  | Typeof term ->
     let@ (_, osct) = 
       resolve_index_term loc global
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
         ) global.Global.struct_decls
     in
     begin match ofound with
     | Some (tag, _) -> return (Sctypes.Struct tag)
     | None -> 
        fail {loc; msg = Unknown_struct (Sym.fresh_cn str)}
     end
  | Pointer ct ->
     let@ typ = resolve_typ loc global default_mapping_name mappings oquantifier ct in
     return (Sctypes.Pointer typ)


     



let resolve_constraint loc global default_mapping_name mappings (oq, lc) =
  match oq with
    | None -> 
       let@ (lc, _) = resolve_index_term loc global default_mapping_name mappings [] lc in
       return (LC.t_ lc)
    | Some (name, bt, guard) ->
       let q_s, q = IT.fresh_named bt name in
       let qs = [(name, (q_s, bt))] in
       let@ (guard, _) = resolve_index_term loc global default_mapping_name mappings qs guard in
       let@ (lc, _) = resolve_index_term loc global default_mapping_name mappings qs lc in
       return (LC.forall_ (q_s, IT.bt q) (impl_ (guard, lc)))




let iterated_pointer_base_offset resolve loc q_name pointer =
  match pointer with
  | Addition (pointer, Multiplication (Var name', offs))
         when String.equal q_name name' ->
     let@ (pointer_r, p_osct) = resolve pointer in
     let@ (offs_r, _) = resolve offs in
     return (pointer_r, p_osct, offs_r)
  (* | ArrayShift {pointer; index = Var name'} when String.equal q_name name'-> *)
  (*    let@ (pointer, p_osct) = resolve pointer in *)
  (*    begin match p_osct with *)
  (*    | Some (Sctypes.Pointer ct) -> return (pointer, Some ct, IT.int_ (Memory.size_of_ctype ct)) *)
  (*    | None -> fail {loc; msg = Generic (!^ "array pointer type not known" ^^^ IT.pp pointer)} *)
  (*    | Some ct -> fail {loc; msg = Generic (!^ "array pointer not of pointer type:" ^^^ *)
  (*           IT.pp pointer ^^ colon ^^^ Sctypes.pp ct)} *)
  (*    end *)
  | _ ->
     let msg =
       "Iterated predicate pointer must be (ptr + (q_var * offs)) or (&(ptr[q_var]))"
     in
     fail {loc; msg = Generic (!^msg ^^ colon ^^ Ast.pp false pointer)}


let apply_ownership_spec global default_mapping_name mappings (loc, oname, {oq; predicate; arguments; o_permission; typ}) =
  let ownership_kind = match predicate with
    | "Owned" -> `Builtin `Owned
    | "Block" -> `Builtin `Block
    | str -> `Predicate str
  in
  let oq = match oq with
    | None -> None
    | Some (name, bt, condition) ->
       let s = Sym.fresh_cn name in
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
         resolve_index_term loc global default_mapping_name mappings
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
     begin match oq with
     | None ->
        let@ (pointer_resolved, pointer_sct) =
          resolve_index_term loc global default_mapping_name mappings
            (Option.to_list (Option.map fst oq)) pointer
        in
        let@ pointee_sct = match typ, pointer_sct with
          | Some typ, _ ->
             resolve_typ loc global default_mapping_name mappings (Option.map fst oq) typ
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
             ~sct:pointee_sct ~o_permission
        | `Block ->
           make_block ~loc ~oname ~pointer:pointer_resolved ~path:pointer ~sct:pointee_sct ~o_permission
        end
     | Some ((name, (qs,qbt)), condition) ->
        let@ () = match o_permission with
          | None -> return ()
          | Some _ ->
             fail {loc; msg = Generic (!^"cannot use 'if' expression with iterated resources")}
        in
        let@ (pointer_resolved, p_osct, step) = iterated_pointer_base_offset
               (resolve_index_term loc global default_mapping_name mappings [])
               loc name pointer
        in
        let@ (condition, _) =
          resolve_index_term loc global default_mapping_name mappings
            [(name, (qs, qbt))] condition
        in
        let@ pointee_sct = match typ, p_osct with
          | Some typ, _ ->
             resolve_typ loc global default_mapping_name mappings (Option.map fst oq) typ
          | _, Some ct -> return ct
          | _ ->
             fail {loc; msg = Generic (!^"need 'with type' annotation" ^^^ (Ast.Terms.pp false pointer))}
        in
        begin match block_or_owned with
        | `Owned ->
           make_qowned ~loc ~oname ~pointer:pointer_resolved ~q:(qs,qbt)
             ~step ~condition ~path:pointer ~sct:pointee_sct
        | `Block ->
           fail {loc; msg = Generic !^("cannot use '"^predicate^"' with quantifier")}
        end
     end
  | _ ->
     let@ () = match typ with
       | None -> return ()
       | Some _ -> fail {loc; msg = Generic !^"cannot use 'type' syntax with predicates"}
     in
     let@ (predicate, def) = get_resource_predicate_def loc predicate global in
     let@ iargs_resolved = 
       ListM.mapM (fun arg ->
           let@ (t, _) = 
             resolve_index_term loc global default_mapping_name mappings
               (Option.to_list (Option.map fst oq)) arg in
           return t
         ) arguments
     in
     let@ result = match oq with
       | None ->
          let@ (pointer_resolved, pointer_sct) = 
            resolve_index_term loc global default_mapping_name mappings
              (Option.to_list (Option.map fst oq)) pointer 
          in
          make_pred loc (predicate, def) 
            ~oname pointer_resolved iargs_resolved ~o_permission
       | Some ((name, (s, bt)), condition) -> 
          let@ () = match o_permission with
            | None -> return () 
            | Some _ -> 
               fail {loc; msg = Generic (!^"cannot use 'if' expression with iterated resources")}
          in
          let@ (pointer_resolved, p_osct, step) = iterated_pointer_base_offset
               (resolve_index_term loc global default_mapping_name mappings [])
               loc name pointer
          in
          let@ (condition, _) = 
             resolve_index_term loc global default_mapping_name mappings
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
     in
     return result


let apply_logical_predicate global default_mapping_name mappings (loc, cond) =
  let open LogicalPredicates in
  let@ (predicate, def) = get_logical_predicate_def loc cond.predicate global in
  let@ lc = match cond.oq with
    | None ->
       let@ args_resolved = 
         ListM.mapM (fun arg ->
             let@ (t, _) = 
               resolve_index_term loc global default_mapping_name mappings [] arg in
             return t
           ) cond.arguments
       in
       return (LC.t_ (pred_ predicate args_resolved def.return_bt))
    | Some (name, bt, condition) -> 
       let q = Sym.fresh_named name in
       let@ args_resolved = 
         ListM.mapM (fun arg ->
             let@ (t, _) = 
               resolve_index_term loc global default_mapping_name mappings
                 [(name, (q, bt))] arg in
             return t
           ) cond.arguments
       in
       let@ (condition, _) = 
         resolve_index_term loc global default_mapping_name mappings
           [(name, (q, bt))] condition
       in
       let t = pred_ predicate args_resolved def.return_bt in
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
    (* | SD_None -> Ast.addr (Sym.pp_string aarg.asym) *)
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

(* let get_mappings_info (mappings : mapping StringMap.t) (mapping_name : string) = *)
(*   SuggestEqs.make_mappings_info (StringMap.find mapping_name mappings *)
(*     |> List.map (fun {path; it; _} -> (Pp.plain (Ast.Terms.pp true path), it))) *)

let make_fun_spec loc (global : Global.t) fsym (fspec : function_spec)
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
               ~path:item.path ~sct:garg.typ ~o_permission:None
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
  let@ (iA, i, mappings, _) = 
    ListM.fold_leftM (fun (iA, i, mappings, counter) (earg : earg) ->
      (* match calling_mode with *)
      (* | `CallByValue -> *)
        let descr = "ARG" ^ string_of_int counter in
        let a = (earg.esym, BT.of_sct earg.typ, (loc, Some descr)) in
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
        return (iA @ [a], i @ [c], mappings, counter+1)
      (* | `CallByReference -> *)
      (*   let descr = "&ARG" ^ string_of_int counter in *)
      (*   let a = (earg.esym, BT.Loc, (loc, Some descr)) in *)
      (*   let aarg = {asym = earg.esym; typ = earg.typ} in *)
      (*   let item = aarg_item loc aarg in *)
      (*   let (i', mapping') = *)
      (*     make_owned_funarg loc counter item.it item.path aarg.typ in *)
      (*   let c = *)
      (*     (`Constraint (LC.t_ (good_ (pointer_ct aarg.typ, item.it))), *)
      (*      (loc, Some (descr ^ " constraint"))) *)
      (*   in *)
      (*   let mappings = *)
      (*     mod_mapping "start" mappings *)
      (*       (fun mapping -> (item :: mapping') @ mapping) *)
      (*   in *)
      (*   return (iA @ [a], i @ c :: i', mappings, counter+1) *)
    )
    ([], i, mappings, 0) fspec.function_arguments
  in

  let@ (i, mappings) = 
    ListM.fold_leftM (fun (i, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource (oroname, cond) ->
              let@ (i', mapping') = 
                apply_ownership_spec global
                  "start" mappings (loc, Some oroname, cond) 
              in
              let mappings = 
                mod_mapping "start" mappings
                  (fun mapping -> mapping' @ mapping)
              in
              return (i @ i', mappings)
        | Ast.Constraint (oq,lc) ->
           let@ c = resolve_constraint loc global
                      "start" mappings (oq,lc) in
           return (i @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = 
             resolve_index_term loc global
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
               ~path:item.path ~sct:garg.typ ~o_permission:None
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
  let@ (o, mappings, _) = 
    (* match calling_mode with *)
    (* | `CallByValue ->  *)
       return (o, mappings, 0)
    (* | `CallByReference -> *)
    (* ListM.fold_leftM (fun (o, mappings, counter) earg -> *)
    (*     let aarg = {asym = earg.esym; typ = earg.typ} in *)
    (*     let item = aarg_item loc aarg in *)
    (*     let (o', mapping') = *)
    (*       make_owned_funarg loc counter item.it item.path aarg.typ in *)
    (*     let mappings = *)
    (*       mod_mapping "end" mappings *)
    (*         (fun mapping -> (item :: mapping') @ mapping) *)
    (*     in *)
    (*     return (o @ o', mappings, counter+1) *)
    (*   ) *)
    (*   (o, mappings, 0) fspec.function_arguments *)
  in

  let@ (o, mappings) =
    ListM.fold_leftM (fun (o, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource (oroname, cond) ->
              let@ (o', mapping') = 
                apply_ownership_spec global
                  "end" mappings (loc, Some oroname, cond) 
              in
              let mappings = 
                mod_mapping "end" mappings 
                  (fun mapping -> mapping' @ mapping)
              in
              return (o @ o', mappings)
        | Ast.Constraint (oq, cond) ->
           let@ c = resolve_constraint loc global "end" mappings (oq, cond) in
           return (o @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = resolve_index_term loc global "end" mappings [] it in
           let mapping' = [{path = Ast.var name; it = sym_ (s, IT.bt it); o_sct}] in
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
        | `Define (s, it) -> LRT.Define ((s, it), info, lrt)
        | `Resource (s, re, oargs) -> LRT.Resource ((s, (re, oargs)), info, lrt)
        | `Constraint lc -> LRT.Constraint (lc, info, lrt)
      ) o LRT.I
  in
  let rt = RT.mComputational oA lrt in
  
  let lft =
    List.fold_right (fun (iarg, info) lft ->
        match iarg with
        | `Define (s, it) -> LAT.Define ((s, it), info, lft)
        | `Resource (s, re, oargs) -> LAT.Resource ((s, (re, oargs)), info, lft)
        | `Constraint lc -> LAT.Constraint (lc, info, lft)
      ) i (LAT.I rt)
  in
  let ft = AT.mComputationals iA (AT.L lft) in

  return (ft, fspec.trusted, StringMap.find "start" mappings)


  
let make_label_spec
      (fsym: Sym.t)
      (loc : Loc.t)
      (global : Global.t)
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
               ~path:item.path ~sct:garg.typ ~o_permission:None
           in
           let mappings = 
             mod_mapping lname mappings
               (fun mapping -> mapping' @ mapping)
           in
           return (i @ i', mappings)
      )
      (i, mappings) lspec.global_arguments
  in

  (* (\* fargs *\) *)
  (* let@ (i, mappings, _) =  *)
  (*   ListM.fold_leftM (fun (i, mappings, counter) aarg -> *)
  (*       let item = aarg_item loc aarg in *)
  (*       let (i', mapping') = make_owned_funarg loc counter item.it item.path aarg.typ in *)
  (*       let mappings =  *)
  (*         mod_mapping lname mappings *)
  (*           (fun mapping -> mapping' @ mapping) *)
  (*       in *)
  (*       return (i @ i', mappings, counter + 1) *)
  (*     ) *)
  (*     (i, mappings, 0) lspec.function_arguments *)
  (* in *)

  (* largs *)
  let@ (iA, i, mappings) = 
    (* In the label's argument list, the left-most arguments have the
       inner-most scope. In the mapping, we also want the arguments
       that are inner-most scoped-wise to be left-most. *)
    let@ (iA, i, mapping') = 
      ListM.fold_leftM (fun (iA, i, mapping) (aarg : aarg) ->
          let a = (aarg.asym, BT.Loc, (loc, None)) in
          let item = aarg_item loc aarg in
          let@ (i', mapping') = 
            make_owned ~loc ~oname:None ~pointer:item.it 
              ~path:item.path ~sct:aarg.typ ~o_permission:None
          in 
          let c = 
            (`Constraint (LC.t_ (good_ (pointer_ct aarg.typ, item.it))),
             (loc, None))
          in
          return (iA @ [a], i @ c :: i', (item :: mapping') @ mapping)
        )
        ([], i, []) lspec.label_arguments
    in
    let mappings =
      mod_mapping lname mappings
        (fun mapping -> List.rev mapping' @ mapping)
    in
    return (iA, i, mappings)
  in


  let@ (i, mappings) = 
    ListM.fold_leftM (fun (i, mappings) (loc, spec) ->
        match spec with
        | Ast.Resource (oroname, cond) ->
              let@ (i', mapping') = 
                apply_ownership_spec global
                  lname mappings (loc, Some oroname, cond) in
              let mappings = 
                mod_mapping lname mappings 
                  (fun mapping -> mapping' @ mapping)
              in
              return (i @ i', mappings)
        | Ast.Constraint (oq, cond) ->
           let@ c = resolve_constraint loc global lname mappings (oq, cond) in
           return (i @ [(`Constraint c, (loc, None))], mappings)
        | Ast.Define (name, it) -> 
           let s = Sym.fresh_named name in
           let@ (it, o_sct) = 
             resolve_index_term loc global lname mappings [] it
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


  let llt =
    List.fold_right (fun (iarg, info) lt ->
        match iarg with
        | `Define (s, it) -> LAT.Define ((s, it), info, lt)
        | `Resource (s, re, oargs) -> LAT.Resource ((s, (re, oargs)), info, lt)
        | `Constraint lc -> LAT.Constraint (lc, info, lt)
      ) i (LAT.I False.False)
  in
  let lt = AT.mComputationals iA (AT.L llt) in

  return (lt, StringMap.find lname mappings)





