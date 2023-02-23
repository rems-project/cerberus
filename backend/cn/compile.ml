module CF = Cerb_frontend
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module StringMap = Map.Make(String)
module LAT = LogicalArgumentTypes
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RET = ResourceTypes

open Pp

open CF.Cn
open Resultat
open TypeErrors

module SymMap = Map.Make(Sym)
module Y = Map.Make(String)



type function_sig = {
    args: (Sym.t * BaseTypes.t) list;
    return_bty: BaseTypes.t;
  }

type predicate_sig = {
  pred_iargs: (Sym.t * BaseTypes.t) list;
  pred_oargs: (Sym.t * BaseTypes.t) list;
}

type resource_def =
  | RPred_owned of Sctypes.t
  | RPred_block of Sctypes.t
  | RPred_named of Sym.t
  | RPred_I_owned of Sctypes.t
  | RPred_I_block of Sctypes.t
  | RPred_I_named of Sym.t

type resource_env = Resources.t list

(* the expression that encodes the current value of this c variable *)
type c_variable_env = IT.t SymMap.t

type env = {
  computationals: (BaseTypes.t (* * Sctypes.t option *)) SymMap.t;
  logicals: (BaseTypes.t (* * Sctypes.t option *)) SymMap.t;
  pred_names: Sym.t Y.t;
  predicates: predicate_sig SymMap.t;
  func_names: Sym.t Y.t;
  functions: function_sig SymMap.t;
  c_vars: c_variable_env;
  old_resources: (string * resource_env) list;
  datatypes : (BaseTypes.datatype_info * Sym.t Y.t) SymMap.t;
  datatype_constrs : BaseTypes.constr_info SymMap.t;
  tagDefs: Mucore.mu_tag_definitions;
}

let empty tagDefs =
  { computationals = SymMap.empty;
    logicals= SymMap.empty; 
    pred_names= Y.empty; 
    predicates= SymMap.empty;
    func_names = Y.empty; 
    functions = SymMap.empty; 
    c_vars= SymMap.empty;
    old_resources= [];
    datatypes = SymMap.empty; 
    datatype_constrs = SymMap.empty;
    tagDefs; 
  }

let name_to_sym loc nm m = match Y.find_opt nm m with
  | None ->
    let sym = Sym.fresh_named nm in
    return sym
  | Some _ ->
    let open TypeErrors in
    fail {loc; msg = Generic (Pp.string ("redefinition of name: " ^ nm))}

let add_computational sym bTy env =
  {env with computationals= SymMap.add sym bTy env.computationals }

let add_logical sym bTy env =
  {env with logicals= SymMap.add sym bTy env.logicals }

let add_function loc sym func_sig env =
  (* upstream of this an incorrect string->sym conversion was done *)
  let str = Tools.todo_string_of_sym sym in
  let@ _ = name_to_sym loc str env.func_names in
  return {env with functions= SymMap.add sym func_sig env.functions;
    func_names = Y.add str sym env.func_names }

let add_predicate sym pred_sig env =
  {env with predicates= SymMap.add sym pred_sig env.predicates }

let add_c_var_value c_sym x env =
  { env with c_vars= SymMap.add c_sym x env.c_vars }

let add_c_var_values xs env = List.fold_right (fun (sym, x) env ->
    add_c_var_value sym x env) xs env

let lookup_computational_or_logical sym env =
  match SymMap.find_opt sym env.logicals with
  | Some bt -> Some bt
  | None -> SymMap.find_opt sym env.computationals

let lookup_pred_name str env =
  Y.find_opt str env.pred_names

let lookup_predicate sym env =
  SymMap.find_opt sym env.predicates

let lookup_function sym env =
  SymMap.find_opt sym env.functions

let lookup_function_by_name nm env = match Y.find_opt nm env.func_names with
  | Some sym ->
    SymMap.find_opt sym env.functions |> Option.map (fun fs -> (sym, fs))
  | None -> None

(* let lookup_resource sym env = *)
(*   SymMap.find_opt sym env.resources *)

(* part of the Deref framework - rework or retire
let lookup_resource_for_pointer loc e env =
  let found = 
    List.find_opt (fun (ret, _) ->
        IT.equal (RET.pointer ret) e
      ) env.resources
  in
  match found with
  | Some resource -> return resource
  | None ->
     let msg = Generic (Pp.item "no resource found for pointer"
        (IT.pp e ^^^ !^ "amongst resources" ^^^ Pp.brackets (Pp.list (fun (ret, _) ->
            IT.pp (RET.pointer ret)) env.resources)))
     in
     fail {loc; msg}
*)

let lookup_struct sym env =
  match Pmap.lookup sym env.tagDefs with
    | Some (M_StructDef xs) ->
        Some xs
    | Some (M_UnionDef _)| None ->
        None

let lookup_datatype loc sym env = match SymMap.find_opt sym env.datatypes with
  | Some info -> return info
  | None -> fail (TypeErrors.{loc; msg = TypeErrors.Unknown_datatype sym})

let add_datatype sym info env =
  let datatypes = SymMap.add sym info env.datatypes in
  {env with datatypes}

let lookup_constr loc sym env = match SymMap.find_opt sym env.datatype_constrs with
  | Some info -> return info
  | None -> fail (TypeErrors.{loc; msg = TypeErrors.Unknown_datatype_constr sym})

let add_datatype_constr sym info env =
  let datatype_constrs = SymMap.add sym info env.datatype_constrs in
  {env with datatype_constrs}

let get_datatype_maps env =
  (SymMap.bindings (SymMap.map fst env.datatypes), 
   SymMap.bindings env.datatype_constrs)


let debug_known_preds env =
  Pp.debug 2 (lazy (Pp.item "known logical predicates"
      (Pp.list (fun (nm, _) -> Pp.string nm) (Y.bindings env.func_names))));
  Pp.debug 2 (lazy (Pp.item "known resource predicate names"
      (Pp.list (fun (nm, _) -> Pp.string nm) (Y.bindings env.pred_names))))









type cn_predicate =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_predicate

type cn_function =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_function

type cn_datatype =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_datatype



let rec translate_cn_base_type (bTy: CF.Symbol.sym cn_base_type) =
  let open BaseTypes in
  match bTy with
    | CN_unit ->
        Unit
    | CN_bool ->
        Bool
    | CN_integer ->
        Integer
    | CN_real ->
        Real
    | CN_loc ->
        Loc
    | CN_struct tag_sym ->
        Struct tag_sym
    | CN_datatype dt_sym ->
        Datatype dt_sym
    | CN_map (bTy1, bTy2) ->
        Map ( translate_cn_base_type bTy1
            , translate_cn_base_type bTy2 )
    | CN_list bTy' -> 
        List (translate_cn_base_type bTy')
    | CN_tuple bTys ->
        Tuple (List.map translate_cn_base_type bTys)
    | CN_set bTy' ->
        Set (translate_cn_base_type bTy')


open Resultat
open Effectful.Make(Resultat)

let mk_translate_binop loc bop (e1, e2) =
  let open IndexTerms in
  let@ mk = match bop, IT.bt e1 with
    | CN_add, _ ->
        return add_
    | CN_sub, _ ->
        return sub_
    | CN_mul, _ ->
        return mul_
    | CN_div, _ ->
        return div_
    | CN_equal, _ ->
        return eq_
    | CN_inequal, _ ->
        return ne_
    | CN_lt, (BT.Integer | BT.Real) ->
        return lt_
    | CN_lt, BT.Loc ->
        return ltPointer_
    | CN_le, (BT.Integer | BT.Real) ->
        return le_
    | CN_le, BT.Loc ->
        return lePointer_
    | CN_gt, (BT.Integer | BT.Real) ->
        return gt_
    | CN_gt, BT.Loc ->
        return gtPointer_
    | CN_ge, (BT.Integer | BT.Real) ->
        return ge_
    | CN_ge, BT.Loc ->
        return gePointer_
    | CN_or, BT.Bool ->
        return or2_
    | CN_and, BT.Bool ->
        return and2_
    | CN_map_get, _ ->
        return (fun (x, y) -> map_get_ x y)
    | CN_is_shape,_ ->
        (* should be handled separately *)
        assert false
    | _ ->
        let open Pp in
        fail {loc; msg = Generic (!^ "mk_translate_binop: types:" ^^^
                CF.Cn_ocaml.PpAil.pp_cn_binop bop ^^ colon ^^^
                Pp.list BT.pp [IT.bt e1; IT.bt e2] ^^ colon ^^^
                Pp.list IT.pp [e1; e2])}
  in
  return (mk (e1, e2))










(* just copy-pasting and adapting Kayvan's older version of this code *)
let translate_member_access loc env t member =
  match IT.bt t with
  | Record members ->
     let member' = Id.s member in
     let members' = List.map (fun (s, bt) -> (Tools.todo_string_of_sym s, (s, bt))) members in
     let@ (member, member_bt) = match List.assoc_opt String.equal member' members' with
       | Some (member, member_bt) -> return (member, member_bt)
       | None -> fail {loc; msg = Unknown_record_member (members, member)}
     in
     return (IT.recordMember_ ~member_bt (t, member))
  | Struct tag ->
     let@ members = match lookup_struct tag env with
       | None -> fail {loc; msg= Unknown_struct tag}
       | Some defs_ (* TODO flexible *) -> return (Memory.member_types defs_)
     in
     let@ ty = match List.assoc_opt Id.equal member members with
       | None -> fail {loc; msg = Unknown_member (tag, member)}
       | Some ty -> return ty
     in
     let member_bt = BaseTypes.of_sct ty in
     return ( IT.member_ ~member_bt (tag, t, member) )
  | Datatype tag ->
     let@ (dt_info, mem_syms) = lookup_datatype loc tag env in
     let@ sym = match StringMap.find_opt (Id.s member) mem_syms with
       | None -> fail {loc; msg= Generic (Pp.string ("Unknown member " ^ Id.s member ^
           " of datatype " ^ Sym.pp_string tag))}
       | Some sym -> return sym
     in
     let@ bt = match List.assoc_opt Sym.equal sym dt_info.dt_all_params with
       | None -> fail {loc; msg = Generic (Pp.string ("Unknown member " ^ Id.s member ^
           " of datatype " ^ Sym.pp_string tag ^ " at type lookup"))}
       | Some bt -> return bt
     in
     return (IT.IT (IT.Datatype_op (IT.DatatypeMember (t, sym)), bt))
  | has -> 
     fail {loc; msg = Illtyped_it' {it = t; has; expected = "struct"}}


let translate_is_shape env loc x shape_expr =
  let rec f x = function
    | CNExpr (loc2, CNExpr_cons (c_nm, exprs)) ->
        let@ cons_info = lookup_constr loc c_nm env in
        let@ (_, mem_syms) = lookup_datatype loc cons_info.c_datatype_tag env in
        let m1 = IT.datatype_is_cons_ c_nm x in
        let memb nm =
            let@ sym = match Y.find_opt (Id.s nm) mem_syms with
                | Some sym -> return sym
                | None -> fail {loc = loc2; msg = Generic
                    (Pp.string ("Unknown field of " ^ Sym.pp_string cons_info.c_datatype_tag
                        ^ ": " ^ Id.s nm))}
            in
            let bt = List.assoc Sym.equal sym cons_info.c_params in
            return (IT.datatype_member_ x sym bt)
        in
        let@ xs = ListM.mapM (fun (nm, shape) ->
            let@ x = memb nm in
            f x shape) exprs in
        return (m1 :: List.concat xs)
    | _ ->
    fail {loc; msg = Generic (Pp.string "rhs of ?? operation can only specify shape"
        (* FIXME: convert the dtree of the shape expr to something pp-able *))}
  in
  let@ xs = f x shape_expr in
  return (IT.and3_ xs)

let pp_cnexpr_kind expr_ =
  let open Pp in
  match expr_ with
  | CNExpr_const CNConst_NULL -> !^ "NULL"
  | CNExpr_const (CNConst_integer n) -> Pp.string (Z.to_string n)
  | CNExpr_const (CNConst_bool b) -> !^ (if b then "true" else "false")
  | CNExpr_var sym -> parens (typ (!^ "var") (Sym.pp sym))
  | CNExpr_deref e -> !^ "(deref ...)"
  | CNExpr_value_of_c_variable sym -> parens (typ (!^ "c:var") (Sym.pp sym))
  | CNExpr_list es_ -> !^ "[...]"
  | CNExpr_memberof (e, xs) -> !^ "_." ^^ Id.pp xs
  | CNExpr_binop (bop, x, y) -> !^ "(binop (_, _, _))"
  | CNExpr_sizeof ct -> !^ "(sizeof _)"
  | CNExpr_offsetof (tag, member) -> !^ "(offsetof (_, _))"
  | CNExpr_cast (bt, expr) -> !^ "(cast (_, _))"
  | CNExpr_call (nm, exprs) -> !^ "(" ^^ Id.pp nm ^^^ !^ "(...))"
  | CNExpr_cons (c_nm, exprs) -> !^ "(" ^^ Sym.pp c_nm ^^^ !^ "{...})"
  | CNExpr_each (sym, r, e) -> !^ "(each ...)"
  | CNExpr_ite (e1, e2, e3) -> !^ "(if ... then ...)"
  | CNExpr_good (ty, e) -> !^ "(good (_, _))"


let translate_cn_expr (env: env) expr =
  let open IndexTerms in
  let module BT = BaseTypes in
  let rec trans env (CNExpr (loc, expr_)) =
    let self = trans env in
    match expr_ with
      | CNExpr_const CNConst_NULL ->
          return null_
      | CNExpr_const (CNConst_integer n) ->
          return (z_ n)
      | CNExpr_const (CNConst_bool b) ->
          return (bool_ b)
      | CNExpr_var sym ->
          begin match lookup_computational_or_logical sym env with
            | None ->
                Pp.debug 2 (lazy (Pp.item ("failed lookup of CNExpr_var " ^ Sym.pp_string sym)
                  (Pp.list (fun (nm, _) -> Sym.pp nm) (SymMap.bindings env.computationals))));
                fail {loc; msg= Unknown_variable sym}
            | Some bTy -> return (IT (Lit (Sym sym), bTy))
          end
      | CNExpr_deref e ->
         Pp.debug 2 (lazy (Pp.string ("seeing CNExpr_deref")));
         assert false;
         (* to be fixed and/or retired
         let@ expr = self e in
         let@ (re, O oa) = lookup_resource_for_pointer loc expr env in
         begin match re with
         | P {name = Owned sct; _} -> 
            let pointee = 
              recordMember_ ~member_bt:(BT.of_sct sct) (oa, Resources.value_sym) in
            return pointee
         | _ -> 
            let msg = 
              !^"Can only dereference 'Owned' pointers." 
              ^^^ !^"The resource available for" ^^^ IT.pp expr ^^^ !^"is" 
              ^^^ RET.pp re
            in
            fail {loc; msg = Generic msg}
         end
         *)
      | CNExpr_value_of_c_variable sym ->
         begin match SymMap.find_opt sym env.c_vars with
         | None -> fail {loc; msg = Generic (!^ "no encoding for C variable (bug):" ^^^ Sym.pp sym)}
         | Some x -> return x
         end
      | CNExpr_list es_ ->
          let@ es = ListM.mapM self es_ in
          let item_bt = basetype (List.hd es) in
          return (list_ ~item_bt es)
      | CNExpr_memberof (e, xs) ->
         let@ e = self e in
         translate_member_access loc env e xs
      | CNExpr_binop (CN_sub, e1_, (CNExpr (_, CNExpr_cons _) as shape)) ->
          let@ e1 = self e1_ in
          translate_is_shape env loc e1 shape
      | CNExpr_binop (bop, e1_, e2_) ->
          let@ e1 = self e1_ in
          let@ e2 = self e2_ in
          mk_translate_binop loc bop (e1, e2)
      | CNExpr_sizeof ct ->
          let scty = Sctypes.of_ctype_unsafe loc ct in
          return (int_ (Memory.size_of_ctype scty))
      | CNExpr_offsetof (tag, member) ->
          let@ () = match lookup_struct tag env with
            | None -> fail {loc; msg= Unknown_struct tag}
            | Some _ -> return ()
          in
          return (memberOffset_ (tag, member))
      | CNExpr_cast (bt, expr) ->
          let@ expr = self expr in
          begin match bt with
          | CN_loc -> return (integerToPointerCast_ expr)
          | CN_integer -> return (pointerToIntegerCast_ expr)
          | _ -> fail {loc; msg = Generic (Pp.string "can only cast to pointer or integer")}
          end
      | CNExpr_call (nm, exprs) ->
          let@ args = ListM.mapM self exprs in
          let nm_s = Id.pp_string nm in
          let@ b = Builtins.apply_builtin_funs loc nm_s args in
          begin match b with
            | Some t -> return t
            | None ->
              let@ (sym, bt) = match lookup_function_by_name nm_s env with
                | Some (sym, fsig) -> return (sym, fsig.return_bty)
                | None ->
                    debug_known_preds env;
		    fail {loc; msg = Unknown_logical_predicate
                        {id = Sym.fresh_named nm_s; resource = false}}
              in
              return (pred_ sym args bt)
          end
      | CNExpr_cons (c_nm, exprs) ->
          let@ cons_info = lookup_constr loc c_nm env in
          let@ (_, mem_syms) = lookup_datatype loc cons_info.c_datatype_tag env in
          let@ exprs = ListM.mapM (fun (nm, expr) ->
              let@ expr = self expr in
              let@ sym = match Y.find_opt (Id.s nm) mem_syms with
                | Some sym -> return sym
                | None -> fail {loc; msg = Generic
                    (Pp.string ("Unknown field of " ^ Sym.pp_string cons_info.c_datatype_tag
                        ^ ": " ^ Id.s nm))}
              in
              return (sym, expr)) exprs
          in
          return (datatype_cons_ c_nm cons_info.c_datatype_tag exprs)
      | CNExpr_each (sym, r, e) ->
          let env' = add_logical sym BT.Integer env in
          let@ expr = trans env' e in
          return (eachI_ (Z.to_int (fst r), sym, Z.to_int (snd r)) expr)
      | CNExpr_ite (e1, e2, e3) ->
          let@ e1 = trans env e1 in
          let@ e2 = trans env e2 in
          let@ e3 = trans env e3 in
          return (ite_ (e1, e2, e3))
      | CNExpr_good (ty, e) ->
         let scty = Sctypes.of_ctype_unsafe loc ty in
         let@ e = trans env e in
         return (good_ (scty, e))
  in trans env expr


let translate_cn_res_info res_loc loc env res args =
  let@ args = ListM.mapM (translate_cn_expr env) args in
  let open Resources in
  let open RET in
  let@ (pname, oargs_ty, env_info) = match res with
    | CN_owned ty ->
      let scty = Sctypes.of_ctype_unsafe res_loc ty in
      return (Owned scty, owned_oargs scty, RPred_owned scty)
    | CN_block ty ->
      let scty = Sctypes.of_ctype_unsafe res_loc ty in
      return (Block scty, owned_oargs scty, RPred_block scty)
    | CN_named pred ->
      let@ pred_sig = match lookup_predicate pred env with
        | None -> fail {loc; msg = Unknown_resource_predicate {id = pred; logical = false}}
        | Some pred_sig -> return pred_sig
      in
      return (PName pred, BT.Record pred_sig.pred_oargs, RPred_named pred)
  in
  let@ (ptr_expr, iargs) = match args with
    | [] -> fail {loc; msg = First_iarg_missing {pname}}
    | (x :: xs) -> return (x, xs)
  in
  return (pname, ptr_expr, iargs, oargs_ty, env_info)

let split_pointer_linear_step loc q ptr_expr =
  let open IndexTerms in
  let open Pp in
  let qs = sym_ (q, BT.Integer) in
  let msg_s = "Iterated predicate pointer must be (ptr + (q_var * offs)):" in
  begin match term ptr_expr with
    | Pointer_op (IntegerToPointerCast (IT (Arith_op (Add (b, offs)), _))) ->
      begin match term b, term offs with
        | Pointer_op (PointerToIntegerCast p), Arith_op (Mul (x, y)) when IT.equal x qs ->
          return (p, y)
        | _ -> fail { loc; msg= Generic (!^msg_s ^^^ IT.pp ptr_expr)}
      end
    (* temporarily allow this more confusing but more concise syntax,
       until we have enriched Core's pointer base types *)
    | Arith_op (Add (p, IT (Arith_op (Mul (x, y)), _))) when IT.equal x qs ->
       return (p, y)       
    | _ ->
    fail { loc; msg= Generic (!^msg_s ^^^ IT.pp ptr_expr)}
  end

let mk_int_map bt = BT.Map (BT.Integer, bt)

let map_over_record loc ty =
  let lift (s, ty) = (s, mk_int_map ty) in
  match ty with
  | BT.Record xs ->
    return (BT.Record (List.map lift xs))
  | _ -> let open Pp in
    fail {loc; msg = Generic (!^ "map_over_record: not a record type:" ^^^ BT.pp ty)}

let get_single_member v =
  match IT.basetype v with
  | BT.Record [(sym, bt)] -> IT.recordMember_ ~member_bt:bt (v, sym)
  | ty -> assert false

let iterate_resource_env_info = function
  | RPred_owned ct -> RPred_I_owned ct
  | RPred_block ct -> RPred_I_block ct
  | RPred_named nm -> RPred_I_named nm
  | _ -> assert false

let owned_good loc sym res_t = match res_t with
  | (RET.P { name = Owned scty ; permission; _}, oargs_ty) ->
     let v = get_single_member (IT.sym_ (sym, oargs_ty)) in
     [(LC.T (IT.impl_ (permission, IT.good_ (scty, v))), 
       (loc, Some "default value constraint"))]
  | (RET.Q { name = Owned scty ; q; permission; _}, oargs_ty) ->
     let v = get_single_member (IT.sym_ (sym, oargs_ty)) in
     let v_el = IT.map_get_ v (IT.sym_ (q, BT.Integer)) in
     [(LC.forall_ (q, BT.Integer)
          (IT.impl_ (permission, IT.good_ (scty, v_el))),
        (loc, Some "default value constraint"))]
   | _ -> 
      []




let translate_cn_let_resource__pred env res_loc (pred_loc, res, args) =
  let@ (pname, ptr_expr, iargs, oargs_ty, env_info) =
         translate_cn_res_info res_loc pred_loc env res args in
  let pt = (RET.P { name = pname
            ; pointer= ptr_expr
            ; permission= IT.bool_ true
            ; iargs = iargs},
         oargs_ty)
  in
  return (env_info, pt)

let translate_cn_let_resource__each env res_loc (q, bt, guard, pred_loc, res, args) =
  let bt' = translate_cn_base_type bt in
  let@ () = 
    if BT.equal bt' BT.Integer then return ()
    else fail {loc = pred_loc; msg = let open Pp in
        Generic (!^ "quantified v must be integer:" ^^^ BT.pp bt')}
  in
  let env_with_q = add_logical q BT.Integer env in
  let@ guard_expr = translate_cn_expr env_with_q guard in
  let@ (pname, ptr_expr, iargs, oargs_ty, env_info) =
         translate_cn_res_info res_loc pred_loc env_with_q res args in
  let env_info = iterate_resource_env_info env_info in
  let@ (ptr_base, step) = split_pointer_linear_step pred_loc q ptr_expr in
  let@ m_oargs_ty = map_over_record pred_loc oargs_ty in
  let pt = (RET.Q { name = pname
            ; q
            ; pointer= ptr_base
            ; step
            ; permission= guard_expr
            ; iargs = iargs},
         m_oargs_ty)
  in
  return (env_info, pt)

let translate_cn_let_resource env (res_loc, sym, the_res) =
  let@ env_info, pt = match the_res with
    | CN_pred (pred_loc, res, args) ->
       translate_cn_let_resource__pred env res_loc 
         (pred_loc, res, args)
    | CN_each (q, bt, guard, pred_loc, res, args) ->
       translate_cn_let_resource__each env res_loc
         (q, bt, guard, pred_loc, res, args)  
  in
  return (env_info, pt, owned_good res_loc sym pt)


let translate_cn_assrt env (loc, assrt) =
  match assrt with
  | CN_assert_exp e_ ->
     let@ e = translate_cn_expr env e_ in
     return (LC.T e)
  | CN_assert_qexp (sym, bTy, e1_, e2_) ->
     let bt = translate_cn_base_type bTy in
     let env_with_q = add_logical sym bt env in
     let@ e1 = translate_cn_expr env_with_q e1_ in
     let@ e2 = translate_cn_expr env_with_q e2_ in
     return (LC.Forall ((sym, bt), IT.impl_ (e1, e2)))



let translate_cn_clause env clause =
  let open Resources in
  let rec translate_cn_clause_aux env acc clause =
    let module LAT = LogicalArgumentTypes in
    match clause with
      | CN_letResource (res_loc, sym, the_res, cl) ->
         let@ _, pt, lcs = 
           translate_cn_let_resource env (res_loc, sym, the_res) in
         let (pt_ret, oa_bt) = pt in
         let acc' z = 
           acc (LAT.mResource ((sym, pt), (res_loc, None)) 
               (LAT.mConstraints lcs z))
         in
         let env' = add_logical sym oa_bt env in
         translate_cn_clause_aux env' acc' cl
      | CN_letExpr (loc, sym, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              LAT.mDefine (sym, e, (loc, None)) z
            end in
          translate_cn_clause_aux (add_logical sym (IT.basetype e) env) acc' cl
      | CN_assert (loc, assrt, cl) ->
         let@ lc = translate_cn_assrt env (loc, assrt) in
         let acc' z = acc (LAT.mConstraint ( lc, (loc, None) ) z) in
         translate_cn_clause_aux env acc' cl
      | CN_return (loc, xs_) ->
          let@ xs =
            ListM.mapM (fun (sym, e_) ->
              let@ e = translate_cn_expr env e_ in
              return (OutputDef.{loc= loc; name= sym; value= e})
            ) xs_ in
          acc (LAT.I xs) 
  in
  translate_cn_clause_aux env (fun z -> return z) clause



let translate_cn_clauses env clauses =
  let rec self acc = function
    | CN_clause (loc, cl_) ->
        let@ cl = translate_cn_clause env cl_ in
        return (RP.{loc= loc; guard= IT.bool_ true; packing_ft= cl} :: acc)
    | CN_if (loc, e_, cl_, clauses') ->
      let@ e  = translate_cn_expr env e_ in
      let@ cl = translate_cn_clause env cl_ in
      self begin
        RP.{loc= loc; guard= e; packing_ft= cl} :: acc
      end clauses'
  in
  let@ xs = self [] clauses in
  return (List.rev xs)

let translate_option_cn_clauses env = function
  | Some clauses -> 
     let@ clauses = translate_cn_clauses env clauses in
     return (Some clauses)
  | None -> 
     return None


let translate_cn_func_body env body =
  let open LogicalPredicates in
  let rec aux env body =
    match body with
      | CN_fb_letExpr (loc, sym, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let env2 = add_logical sym (IT.basetype e) env in
          let@ b = aux env2 cl in
          return (Body.Let ((sym, e), b))
      | CN_fb_return (loc, x) ->
         let@ t = translate_cn_expr env x in
         return (Body.Term t)
      | CN_fb_cases (loc, x, cs) ->
         let@ x = translate_cn_expr env x in
         let@ cs = 
           ListM.mapM (fun (ctor, body) ->
               let@ body = aux env body in
               return (ctor, body)
             ) cs
         in
         return (Body.Case (x, cs))
  in
  aux env body



let register_cn_predicates env (defs: cn_predicate list) =
  let aux env def =
    let translate_args xs =
      List.map (fun (bTy, sym) ->
        (sym, translate_cn_base_type bTy)
      ) xs in
    let iargs = translate_args def.cn_pred_iargs in
    let oargs = translate_args def.cn_pred_oargs in
    add_predicate def.cn_pred_name { pred_iargs= iargs; pred_oargs= oargs } env in
  List.fold_left aux env defs

let register_cn_functions env (defs: cn_function list) =
  let aux env def =
    let args = List.map (fun (bTy, sym) -> (sym, translate_cn_base_type bTy)
      ) def.cn_func_args in
    let return_bt = translate_cn_base_type def.cn_func_return_bty in
    let fsig = {args; return_bty = return_bt} in
    add_function def.cn_func_loc def.cn_func_name fsig env
  in
  ListM.fold_leftM aux env defs

let known_attrs = ["rec"]

let translate_cn_function env (def: cn_function) =
  let open LogicalPredicates in
  Pp.debug 2 (lazy (Pp.item "translating function defn" (Sym.pp def.cn_func_name)));
  let args = 
    List.map (fun (bTy, sym) -> (sym, translate_cn_base_type bTy)
      ) def.cn_func_args in
  let env' =
    List.fold_left (fun acc (sym, bt) -> add_logical sym bt acc
      ) env args in
  let is_rec = List.exists (fun id -> String.equal (Id.s id) "rec") def.cn_func_attrs in
  let@ () = ListM.iterM (fun id -> if List.exists (String.equal (Id.s id)) known_attrs
    then return ()
    else fail {loc = def.cn_func_loc; msg = Generic (Pp.item "Unknown attribute" (Id.pp id))}
  ) def.cn_func_attrs in
  let@ definition = match def.cn_func_body with
    | Some body -> 
       let@ body = translate_cn_func_body env' body in
       return (if is_rec then Rec_Def body else Def body)
    | None -> return Uninterp in
  let return_bt = translate_cn_base_type def.cn_func_return_bty in
  let def2 = {loc = def.cn_func_loc; args; return_bt; definition} in
  return (def.cn_func_name, def2)



let translate_cn_predicate env (def: cn_predicate) =
  let open RP in
  Pp.debug 2 (lazy (Pp.item "translating predicate defn" (Sym.pp def.cn_pred_name)));
  let (iargs, oargs) =
    match lookup_predicate def.cn_pred_name env with
      | None ->
          assert false
      | Some pred_sig ->
          (pred_sig.pred_iargs, pred_sig.pred_oargs) in
  let env' =
    List.fold_left (fun acc (sym, bTy) ->
      add_logical sym bTy acc
    ) env iargs in
  let@ clauses = translate_option_cn_clauses env' def.cn_pred_clauses in
  match iargs with
    | (iarg0, BaseTypes.Loc) :: iargs' ->
        return 
          ( def.cn_pred_name
          , { loc= def.cn_pred_loc
            ; pointer= iarg0
            ; iargs= iargs'
            ; oargs= oargs
            ; clauses= clauses
            } )
    | (_, found_bty) :: _ ->
        fail { loc= def.cn_pred_loc; msg= First_iarg_not_pointer { pname= PName def.cn_pred_name; found_bty } }
    | [] ->
        fail { loc= def.cn_pred_loc; msg= First_iarg_missing { pname= PName def.cn_pred_name} }

let add_datatype_info env (dt : cn_datatype) =
  Pp.debug 2 (lazy (Pp.item "translating datatype declaration" (Sym.pp dt.cn_dt_name)));
  let add_param_sym m (ty, nm) =
    let bt = translate_cn_base_type ty in
    let nm_s = Id.s nm in
    match Y.find_opt nm_s m with
    | None ->
      let sym = Sym.fresh_named nm_s in
      return (Y.add nm_s (sym, bt) m)
    | Some (sym, bt2) -> if BT.equal bt bt2 then return m
      else fail {loc = Id.loc nm;
              msg = Generic (Pp.item "different type for datatype member" (Id.pp nm))}
  in
  let@ param_sym_tys = ListM.fold_leftM add_param_sym Y.empty
    (List.concat (List.map snd dt.cn_dt_cases)) in
  let param_syms = Y.map fst param_sym_tys in
  let add_constr env (cname, params) =
    let c_params = List.map (fun (_, nm) -> Y.find (Id.s nm) param_sym_tys) params in
    let info = BaseTypes.{c_params; c_datatype_tag = dt.cn_dt_name} in
    add_datatype_constr cname info env
  in
  let env = List.fold_left add_constr env dt.cn_dt_cases in
  let dt_all_params = Y.bindings param_sym_tys |> List.map snd in
  let dt_constrs = List.map fst dt.cn_dt_cases in
  return (add_datatype dt.cn_dt_name
    (BaseTypes.{dt_constrs; dt_all_params}, param_syms) env)

let add_datatype_infos env dts =
  ListM.fold_leftM add_datatype_info env dts
