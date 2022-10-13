module CF = Cerb_frontend

module BT = BaseTypes
module RP = ResourcePredicates

module IT = IndexTerms
module SymMap = Map.Make(Sym)
module StringMap = Map.Make(String)

module LAT = LogicalArgumentTypes

open CF.Cn
open TypeErrors



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
  let ptr_err = "pointer arithmetic not allowed in specifications: "^
                         "please instead use pointer/integer casts"
  in
  let@ mk = match bop, IT.bt e1 with
    | CN_add, (BT.Integer | BT.Real) ->
        return add_
    | CN_add, BT.Loc ->
        fail {loc; msg = Generic (Pp.string ptr_err)}
    | CN_sub, (BT.Integer | BT.Real) ->
        return sub_
    | CN_sub, BT.Loc ->
        fail {loc; msg = Generic (Pp.string ptr_err)}
    | CN_mul, (BT.Integer | BT.Real) ->
        return mul_
    | CN_div, (BT.Integer | BT.Real) ->
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
    | _ ->
        let open Pp in
        fail {loc; msg = Generic (!^ "mk_translate_binop: types:" ^^^
                CF.Cn_ocaml.PpAil.pp_cn_binop bop ^^ colon ^^^
                Pp.list BT.pp [IT.bt e1; IT.bt e2] ^^ colon ^^^
                Pp.list IT.pp [e1; e2])}
  in
  return (mk (e1, e2))

(* type message = *)
(*   | Invalid_oarg_owned of { invalid_ident: Id.t } *)
(*   | Invalid_oarg of { res_name: Sym.t; invalid_ident: Id.t } *)
(*   | Invalid_struct_member of { struct_name: Sym.t; invalid_ident: Id.t } *)
(*   | TypeMismatchBinary of { bTy1: BaseTypes.t; bTy2: BaseTypes.t } *)
(*   | TODO_error of string *)

(* type error = { *)
(*   loc: Locations.t; *)
(*   msg: message *)
(* } *)

(* let pp_message = let open Pp in function *)
(*   | Invalid_oarg_owned { invalid_ident } -> *)
(*       Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not an oarg of 'Owned()' (expecting '.value')" *)
(*   | Invalid_oarg { res_name; invalid_ident } -> *)
(*       Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not an oarg of" ^^^ *)
(*       Pp.squotes(Sym.pp res_name) *)
(*   | Invalid_struct_member { struct_name; invalid_ident } -> *)
(*       Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not a member of" ^^^ *)
(*       Pp.squotes(!^ "struct" ^^^ Sym.pp struct_name) *)
(*   | TypeMismatchBinary { bTy1; bTy2 } -> *)
(*       !^ "type mismatch in a binary operator" ^^^ Pp.parens ( *)
(*         Pp.squotes (BaseTypes.pp bTy1) ^^^ !^ " <-> " ^^^ Pp.squotes (BaseTypes.pp bTy2) *)
(*       ) *)
(*   | TODO_error str -> *)
(*       !^ ("TODO(msg): " ^ str) *)


(* let report_error {loc; msg} = *)
(*   let doc = pp_message msg in *)
(*   Pp.error loc doc [] *)

module Env = CompileEnv
open Env







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
       | Some (defs_, _) (* TODO flexible *) -> return defs_
     in
     let@ ty = match List.assoc_opt Id.equal member members with
       | None -> fail {loc; msg = Unknown_member (tag, member)}
       | Some (_, _, ty) -> return ty
     in
     let ty' = Sctypes.of_ctype_unsafe loc ty in
     let member_bt = BaseTypes.of_sct ty' in
     return ( IT.member_ ~member_bt (tag, t, member) )
  | Datatype tag ->
     let@ (dt_info, mem_syms) = Env.lookup_datatype loc tag env in
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




let translate_cn_expr (env: Env.t) expr =
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
          begin match Env.lookup_logical sym env with
            | None -> fail {loc; msg= Unknown_variable sym}
            | Some bTy -> return (IT (Lit (Sym sym), bTy))
          end
      | CNExpr_rvar sym ->
         let get_pred_sig s = 
           match Env.lookup_predicate s env with
           | None ->
              Env.debug_known_preds env;
	      fail {loc; msg = Unknown_resource_predicate {id = s; logical = false}}
           | Some pred_sig -> return pred_sig 
         in
         let@ bt =match Env.lookup_resource sym env with
           | None -> 
              fail {loc; msg= Unknown_variable sym}
           | Some RPred_owned sct ->
              return (Resources.owned_oargs sct)
           | Some RPred_block sct ->
              return (Resources.block_oargs)
           | Some RPred_named pnm ->
              let@ pred_sig = get_pred_sig pnm in
              return (BT.Record pred_sig.pred_oargs)
           | Some RPred_I_owned sct ->
              return (Resources.q_owned_oargs sct)
           | Some RPred_I_block sct ->
              return (Resources.q_block_oargs)
           | Some RPred_I_named pnm ->
              let@ pred_sig = get_pred_sig pnm in
              return (BT.Record (List.map_snd (BT.make_map_bt Integer) pred_sig.pred_oargs))
         in
         return (sym_ (sym, bt))
      | CNExpr_list es_ ->
          let@ es = ListM.mapM self es_ in
          let item_bt = basetype (List.hd es) in
          return (list_ ~item_bt es)
      | CNExpr_memberof (e, xs) ->
         let@ e = self e in
         translate_member_access loc env e xs
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
              let@ (sym, bt) = match Env.lookup_function_by_name nm_s env with
                | Some (sym, fsig) -> return (sym, fsig.return_bty)
                | None ->
                    Env.debug_known_preds env;
		    fail {loc; msg = Unknown_logical_predicate
                        {id = Sym.fresh_named nm_s; resource = false}}
              in
              return (pred_ sym args bt)
          end
      | CNExpr_cons (c_nm, exprs) ->
          let@ cons_info = Env.lookup_constr loc c_nm env in
          let@ (_, mem_syms) = Env.lookup_datatype loc cons_info.c_datatype_tag env in
          let@ exprs = ListM.mapM (fun (nm, expr) ->
              let@ expr = self expr in
              let@ sym = match Env.Y.find_opt (Id.s nm) mem_syms with
                | Some sym -> return sym
                | None -> fail {loc; msg = Generic
                    (Pp.string ("Unknown field of " ^ Sym.pp_string cons_info.c_datatype_tag
                        ^ ": " ^ Id.s nm))}
              in
              return (sym, expr)) exprs
          in
          return (datatype_cons_ c_nm cons_info.c_datatype_tag exprs)
      | CNExpr_each (sym, r, e) ->
          let env' = Env.add_logical sym BT.Integer env in
          let@ expr = trans env' e in
          return (eachI_ (Z.to_int (fst r), sym, Z.to_int (snd r)) expr)
  in trans env expr


let translate_cn_res_info res_loc loc env res args =
  let@ args = ListM.mapM (translate_cn_expr env) args in
  let open Resources in
  let open ResourceTypes in
  let@ (pname, oargs_ty, env_info) = match res with
    | CN_owned ty ->
      let scty = Sctypes.of_ctype_unsafe res_loc ty in
      return (Owned scty, owned_oargs scty, RPred_owned scty)
    | CN_block ty ->
      let scty = Sctypes.of_ctype_unsafe res_loc ty in
      return (Block scty, owned_oargs scty, RPred_block scty)
    | CN_named pred ->
      let@ pred_sig = match Env.lookup_predicate pred env with
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

let get_single_member loc v =
  match IT.basetype v with
  | BT.Record [(sym, bt)] -> IT.recordMember_ ~member_bt:bt (v, sym)
  | ty -> let open Pp in
    Pp.warn loc (!^ "get_single_member:" ^^^ typ (IT.pp v) (BT.pp ty));
    assert false

let iterate_resource_env_info = function
  | RPred_owned ct -> RPred_I_owned ct
  | RPred_block ct -> RPred_I_block ct
  | RPred_named nm -> RPred_I_named nm
  | _ -> assert false

let add_owned_good loc sym res_t lat = match res_t with
  | (ResourceTypes.P { name = Owned scty ; permission; _}, oargs_ty) ->
    let v = get_single_member loc (IT.sym_ (sym, oargs_ty)) in
    let good_lc = LogicalConstraints.T (IT.impl_ (permission, IT.good_ (scty, v))) in
    LAT.mConstraint (good_lc, (loc, None)) lat
  | (ResourceTypes.Q { name = Owned scty ; q; permission; _}, oargs_ty) ->
    let v = get_single_member loc (IT.sym_ (sym, oargs_ty)) in
    let v_el = IT.map_get_ v (IT.sym_ (q, BT.Integer)) in
    let good_lc = LogicalConstraints.Forall ((q, BT.Integer),
        (IT.impl_ (permission, IT.good_ (scty, v_el)))) in
    LAT.mConstraint (good_lc, (loc, None)) lat
   | _ -> lat

let translate_cn_clause env clause =
  let rec translate_cn_clause_aux env acc clause =
    let module LAT = LogicalArgumentTypes in
    match clause with
      | CN_letResource (res_loc, sym, res, cl) ->
          begin match res with
            | CN_pred (pred_loc, res, args) ->
               let@ (pname, ptr_expr, iargs, oargs_ty, env_info) =
                      translate_cn_res_info res_loc pred_loc env res args in
               let pt = (ResourceTypes.P { name = pname
                         ; pointer= ptr_expr
                         ; permission= IT.bool_ true
                         ; iargs = iargs},
                      oargs_ty)
               in
               let acc' = fun z -> acc (LAT.mResource ((sym, pt), (pred_loc, None))
                       (add_owned_good pred_loc sym pt z)) in
               let env' = Env.(add_resource sym env_info env) in
               translate_cn_clause_aux env' acc' cl
            | CN_each (q, bt, guard, pred_loc, res, args) ->
               let bt' = translate_cn_base_type bt in
               let@ () = if BT.equal bt' BT.Integer then return ()
                 else fail {loc = pred_loc; msg = let open Pp in
                     Generic (!^ "quantified v must be integer:" ^^^ BT.pp bt')}
               in
               let env' = Env.add_logical q BT.Integer env in
               let@ guard_expr = translate_cn_expr env' guard in
               let@ (pname, ptr_expr, iargs, oargs_ty, env_info) =
                      translate_cn_res_info res_loc pred_loc env' res args in
               let@ (ptr_base, step) = split_pointer_linear_step pred_loc q ptr_expr in
               let@ m_oargs_ty = map_over_record pred_loc oargs_ty in
               let qpt = (ResourceTypes.Q { name = pname
                         ; q
                         ; pointer= ptr_base
                         ; step
                         ; permission= guard_expr
                         ; iargs = iargs},
                      m_oargs_ty)
               in
               let acc' = fun z -> acc (LAT.mResource ((sym, qpt), (pred_loc, None))
                       (add_owned_good pred_loc sym qpt z)) in
               let env'' = Env.(add_resource sym (iterate_resource_env_info env_info)) env in
               translate_cn_clause_aux env'' acc' cl
          end
      | CN_letExpr (loc, sym, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              LAT.mDefine (sym, e, (loc, None)) z
            end in
          translate_cn_clause_aux (Env.add_logical sym (IT.basetype e) env) acc' cl
      | CN_assert (loc, CN_assert_exp e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              LAT.mConstraint ( LogicalConstraints.T e
                             , (loc, None) ) z
            end in
          translate_cn_clause_aux env acc' cl
      | CN_assert (loc, CN_assert_qexp (sym, bTy, e1_, e2_), cl) ->
          let bt = translate_cn_base_type bTy in
	  let env' = Env.add_logical sym bt env in
          let@ e1 = translate_cn_expr env' e1_ in
          let@ e2 = translate_cn_expr env' e2_ in
          let acc' =
            fun z -> acc begin
              LAT.mConstraint ( LogicalConstraints.Forall ((sym, bt), IT.impl_ (e1, e2))
                             , (loc, None) ) z
            end in
          translate_cn_clause_aux env acc' cl
      | CN_return (loc, xs_) ->
          let@ xs =
            ListM.mapM (fun (sym, e_) ->
              let@ e = translate_cn_expr env e_ in
              return (OutputDef.{loc= loc; name= sym; value= e})
            ) xs_ in
          acc (LAT.I xs) in
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
  let rec aux env body =
    match body with
      | CN_fb_letExpr (loc, sym, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let env2 = Env.add_logical sym (IT.basetype e) env in
          let@ b = aux env2 cl in
          return (IT.let_ sym e b)
      | CN_fb_return (loc, x) ->
         translate_cn_expr env x
      | CN_fb_cases (loc, x, cs) ->
         let@ x = translate_cn_expr env x in
         let@ dt_tag = match IT.basetype x with
           | BT.Datatype tag -> return tag
           | has -> fail {loc; msg = Illtyped_it' {it = x; has; expected = "datatype"}}
         in
         let@ (dt_info, _) = Env.lookup_datatype loc dt_tag env in
         let@ cs = ListM.mapM (fun (nm, case_body) ->
             let@ () = if List.exists (Sym.equal nm) dt_info.dt_constrs
                 then return ()
                 else fail {loc; msg = Unknown_datatype_constr nm}
             in
             let@ case_body = aux env case_body in
             return (nm, case_body)) cs in
         (* FIXME: add a default mechanism, and check that either the default is present
            or every case is present *)
         let@ (prev_cs, last) = match List.rev cs with
           | (x :: xs) -> return (List.rev xs, x)
           | [] -> fail {loc; msg = Generic (Pp.string "no cases")}
         in
         return (List.fold_right (fun (nm, y) z -> IT.ite_ (IT.datatype_is_cons_ nm x, y, z))
             prev_cs (snd last))
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
    Env.add_predicate def.cn_pred_name { pred_iargs= iargs; pred_oargs= oargs } env in
  List.fold_left aux env defs

let register_cn_functions env (defs: cn_function list) =
  let aux env def =
    let args = List.map (fun (bTy, sym) -> (sym, translate_cn_base_type bTy)
      ) def.cn_func_args in
    let return_bt = translate_cn_base_type def.cn_func_return_bty in
    let fsig = Env.{args; return_bty = return_bt} in
    Env.add_function def.cn_func_loc def.cn_func_name fsig env
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
    List.fold_left (fun acc (sym, bt) -> Env.add_logical sym bt acc
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
  return (env, (def.cn_func_name, def2))

let translate_and_register_cn_functions (env : Env.t) (to_translate: cn_function list) = 
  let@ env = register_cn_functions env to_translate in
  let@ (env, defs) = 
    ListM.fold_leftM (fun (env, defs) def ->
        let@ (env, def) = translate_cn_function env def in
        return (env, def :: defs)
      ) (env,[]) to_translate
  in
  return (env, List.rev defs)


let translate_cn_predicate env (def: cn_predicate) =
  let open RP in
  let (iargs, oargs) =
    match Env.lookup_predicate def.cn_pred_name env with
      | None ->
          assert false
      | Some pred_sig ->
          (pred_sig.pred_iargs, pred_sig.pred_oargs) in
  let env' =
    List.fold_left (fun acc (sym, bTy) ->
      Env.add_logical sym bTy acc
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
    match Env.Y.find_opt nm_s m with
    | None ->
      let sym = Sym.fresh_named nm_s in
      return (Env.Y.add nm_s (sym, bt) m)
    | Some (sym, bt2) -> if BT.equal bt bt2 then return m
      else fail {loc = Id.loc nm;
              msg = Generic (Pp.item "different type for datatype member" (Id.pp nm))}
  in
  let@ param_sym_tys = ListM.fold_leftM add_param_sym Env.Y.empty
    (List.concat (List.map snd dt.cn_dt_cases)) in
  let param_syms = Env.Y.map fst param_sym_tys in
  let add_constr env (cname, params) =
    let c_params = List.map (fun (_, nm) -> Env.Y.find (Id.s nm) param_sym_tys) params in
    let info = BaseTypes.{c_params; c_datatype_tag = dt.cn_dt_name} in
    Env.add_datatype_constr cname info env
  in
  let env = List.fold_left add_constr env dt.cn_dt_cases in
  let dt_all_params = Env.Y.bindings param_sym_tys |> List.map snd in
  let dt_constrs = List.map fst dt.cn_dt_cases in
  return (Env.add_datatype dt.cn_dt_name
    (BaseTypes.{dt_constrs; dt_all_params}, param_syms) env)

let translate tagDefs (f_defs: cn_function list) (pred_defs: cn_predicate list)
        (d_defs: cn_datatype list) =
  let env = Env.empty tagDefs in
  let@ env = ListM.fold_leftM add_datatype_info env d_defs in
  let@ (env, log_defs) = translate_and_register_cn_functions env f_defs in
  let env = register_cn_predicates env pred_defs in
  let@ pred_defs = ListM.mapM (translate_cn_predicate env) pred_defs in
  return ((log_defs, pred_defs), Env.get_datatype_maps env)

