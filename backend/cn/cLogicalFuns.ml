open Resultat
open Effectful.Make(Resultat)
open TypeErrors
module SymMap = Map.Make(Sym)
module SymSet = Set.Make(Sym)
module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)
module CF=Cerb_frontend

open Cerb_pp_prelude
open Mucore

module IT = IndexTerms

type 'a exec_result =
  | Call_Ret of IT.t
  | Compute of IT.t * 'a
  | If_Else of IT.t * 'a exec_result * 'a exec_result

let mu_val_to_it (M_V ((bt : BT.t), v)) =
  match v with
  | M_Vunit -> Some IT.unit_
  | M_Vtrue -> Some (IT.bool_ true)
  | M_Vfalse -> Some (IT.bool_ false)
  | M_Vobject (M_OV (_, M_OVinteger iv)) ->
    Some (IT.num_lit_ (Memory.z_of_ival iv) bt)
  | M_Vobject (M_OV (_, M_OVpointer ptr_val)) ->
    CF.Impl_mem.case_ptrval ptr_val
    ( fun _ -> Some IT.null_ )
    ( function
        | None -> None
        | Some sym -> Some (IT.sym_ (sym, BT.Loc)) )
    ( fun _prov p -> Some (IT.pointer_ p) )
  | M_Vctype ct -> Option.map (fun ct -> IT.const_ctype_ ct) (Sctypes.of_ctype ct)
  | M_Vfunction_addr sym -> Some (IT.sym_ (sym, BT.Loc))
  | _ -> None

let local_sym_ptr = Sym.fresh_named "local_ptr"

type state = {
  loc_map : (IT.t option) IntMap.t;
  next_loc : int;
}

type context = {
  label_defs : unit mu_label_defs;
  c_fun_pred_map : (Sym.t * LogicalFunctions.definition) SymMap.t;
  mu_call_funinfo : (symbol, Sctypes.c_concrete_sig) Pmap.map;
}

let init_state = { loc_map = IntMap.empty; next_loc = 1 }

let mk_local_ptr state =
  let loc_ix = state.next_loc in
  let ptr = IT.pred_ local_sym_ptr [IT.int_ loc_ix] BT.Loc in
  let loc_map = IntMap.add loc_ix None state.loc_map in
  let state = { loc_map; next_loc = loc_ix + 1 } in
  (ptr, state)

let is_local_ptr ptr = Option.bind (IT.is_pred_ ptr)
  (function
    | (name, [ix]) when Sym.equal name local_sym_ptr -> Option.map Z.to_int (IT.is_z ix)
    | _ -> None
  )

let get_local_ptr loc ptr = match is_local_ptr ptr with
  | None -> fail {loc; msg = Generic (Pp.item "use of non-local pointer" (IT.pp ptr))}
  | Some ix -> return ix

let upd_loc_state state ix v =
  let loc_map = IntMap.add ix (Some v) state.loc_map in
  { state with loc_map }

let triv_simp_ctxt = Simplify.default Global.empty

let simp_const loc lpp it =
  let it2 = Simplify.IndexTerms.simp triv_simp_ctxt it in
  match IT.is_z it2, IT.bt it2 with
  | Some z, _ -> return it2
  | _, BT.Integer -> fail {loc; msg = Generic (Pp.item
      "getting expr from C syntax: failed to simplify integer to numeral"
      (Pp.typ (Lazy.force lpp) (IT.pp it2)))}
  | _, _ -> return it2

let do_wrapI loc ct it =
  match Sctypes.is_integer_type ct with
  | Some ity ->
    return (IT.wrapI_ (ity, it))
  | None -> fail {loc; msg = Generic (Pp.item "expr from C syntax: coercion to non-int type"
      (Sctypes.pp ct))}

(* FIXME: this is yet another notion of whether a term is effectively a
   numeric constant and permitted for multiply/divide or not - similar to
   a simplifier-based notion in welltyped and a solver-based notion in check. *)
let rec is_const_num = function
  | IT.IT (IT.Const _, _) -> true
  | IT.IT (IT.Binop (binop, x, y), _) -> is_const_num x && is_const_num y &&
    begin match binop with
    | IT.Add
    | IT.Sub
    | IT.Mul
    | IT.Div
    | IT.Exp
    | IT.Rem
    | IT.Mod
    -> true
    | _ -> false
    end
  | _ -> false

let rec add_pattern p v var_map =
  let (M_Pattern (loc, _, _, pattern) : _ mu_pattern) = p in
  match pattern with
  | M_CaseBase (Some s, _) ->
    return (SymMap.add s v var_map)
  | M_CaseBase (None, _) ->
    return var_map
  | M_CaseCtor (M_Ctuple, ps) ->
    let@ vs = begin match v with
    | IT.IT (IT.Tuple vs, _) -> return vs
    | it ->
      fail {loc; msg = Generic (Pp.item "getting expr from C syntax: cannot tuple-split val"
        (Pp.typ (IT.pp it) (Pp_mucore.Basic.pp_pattern p)))}
    end in
    assert (List.length vs == List.length ps);
    ListM.fold_rightM (fun (p, v) var_map -> add_pattern p v var_map)
      (List.combine ps vs) var_map
  | _ ->
    fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported pattern"
        (Pp_mucore.Basic.pp_pattern p))}

let signed_int_ity = Sctypes.(IntegerTypes.Signed IntegerBaseTypes.Int_)
let signed_int_ty = Memory.bt_of_sct (Sctypes.Integer signed_int_ity)

let is_two_pow it = match IT.term it with
  | Terms.Binop (Terms.ExpNoSMT, x, y)
    when Option.equal Z.equal (IT.get_num_z x) (Some (Z.of_int 2)) ->
    Some y
  | Terms.Binop (Terms.Exp, x, y)
    when Option.equal Z.equal (IT.get_num_z x) (Some (Z.of_int 2)) ->
    Some y
  | _ -> None

let bool_ite_1_0 b = IT.ite_ (b, IT.int_lit_ 1 signed_int_ty, IT.int_lit_ 0 signed_int_ty)

let rec symb_exec_mu_pexpr ctxt var_map pexpr =
  let (M_Pexpr (loc, annots, _, pe)) = pexpr in
  let opt_bt = WellTyped.BaseTyping.integer_annot annots
    |> Option.map (fun ity -> Memory.bt_of_sct (Sctypes.Integer ity))
  in
  Pp.debug 22 (lazy (Pp.item "doing pure symb exec" (Pp.typ (Pp_mucore.pp_pexpr pexpr)
    (Pp.typ (!^ "typ info") (Pp.list BT.pp (Option.to_list opt_bt))))));
  let self = symb_exec_mu_pexpr ctxt in
  let simp_const_pe v = simp_const loc (lazy (Pp_mucore.pp_pexpr pexpr)) v in
  let unsupported msg doc = fail {loc;
    msg = Generic (Pp.item ("getting expr from C syntax: unsupported: " ^ msg)
        (Pp.typ doc (Pp_mucore_ast.pp_pexpr pexpr)))}
  in
  match pe with
  | M_PEsym sym -> begin match SymMap.find_opt sym var_map with
      | Some r -> return r
      | _ -> fail {loc; msg = Unknown_variable sym}
    end
  | M_PEval v ->
    begin match mu_val_to_it v with
      | Some r -> return r
      | _ -> unsupported "val" (Pp.typ (!^ "typ info") (Pp.list BT.pp (Option.to_list opt_bt)))
    end
  | M_PElet (p, e1, e2) ->
    let@ r_v = self var_map e1 in
    let@ var_map2 = add_pattern p r_v var_map in
    self var_map2 e2
  | M_PEif (cond_pe, x, y) ->
    if is_undef_pexpr x
    then self var_map y
    else if is_undef_pexpr y
    then self var_map x
    else
    let@ cond = self var_map cond_pe in
    let@ x_v = self var_map x in
    let@ y_v = self var_map y in
    return (IT.ite_ (cond, x_v, y_v))
  | M_PEop (op, x, y) ->
    let@ x_v = self var_map x in
    let@ y_v = self var_map y in
    let f x_v y_v = begin match op with
    | OpAdd -> IT.add_ (x_v, y_v)
    | OpSub -> IT.sub_ (x_v, y_v)
    | OpMul -> if is_const_num x_v || is_const_num y_v
        then IT.mul_ (x_v, y_v) else IT.mul_no_smt_ (x_v, y_v)
    | OpDiv -> if is_const_num y_v
        then IT.div_ (x_v, y_v) else IT.div_no_smt_ (x_v, y_v)
    | OpEq  -> IT.eq_ (x_v, y_v)
    | OpLt  -> IT.lt_ (x_v, y_v)
    | OpLe  -> IT.le_ (x_v, y_v)
    | OpGt  -> IT.gt_ (x_v, y_v)
    | OpGe  -> IT.ge_ (x_v, y_v)
    | OpAnd -> IT.and_ [x_v; y_v]
    | OpOr  -> IT.or_ [x_v; y_v]
    | OpExp -> if is_const_num x_v && is_const_num y_v
        then IT.exp_ (x_v, y_v) else IT.exp_no_smt_ (x_v, y_v)
    | OpRem_f -> if is_const_num y_v
        then IT.rem_ (x_v, y_v) else IT.rem_no_smt_ (x_v, y_v)
    | OpRem_t -> if is_const_num y_v
        then IT.mod_ (x_v, y_v) else IT.mod_no_smt_ (x_v, y_v)
    end in
    begin match op, x_v, is_two_pow y_v with
    | OpMul, _, Some exp ->
      return (IT.mul_ (x_v, IT.exp_ (IT.int_lit_ 2 (IT.bt x_v), exp)))
    | OpDiv, _, Some exp ->
      return (IT.div_ (x_v, IT.exp_ (IT.int_lit_ 2 (IT.bt x_v), exp)))
    | _, _, _ ->
      let@ res = simp_const_pe (f x_v y_v) in
      return res
    end
  | M_PEbitwise_unop (unop, pe1) ->
    let@ x = self var_map pe1 in
    let@ unop = match unop with
      | M_BW_CTZ -> return IT.BWCTZNoSMT
      | M_BW_FFS -> return IT.BWFFSNoSMT
      | _ -> unsupported "unary op" (!^ "")
    in
    simp_const_pe (IT.arith_unop unop x)
  | M_PEbitwise_binop (binop, pe1, pe2) ->
    let@ x = self var_map pe1 in
    let@ y = self var_map pe2 in
    let binop = match binop with
      | M_BW_AND -> IT.BWAndNoSMT
      | M_BW_OR -> IT.BWOrNoSMT
      | M_BW_XOR -> IT.XORNoSMT
    in
    simp_const_pe (IT.arith_binop binop (x, y))
  | M_PEbool_to_integer pe ->
    let@ x = self var_map pe in
    return (bool_ite_1_0 x)
  | M_PEnot pe ->
    let@ x = self var_map pe in
    return (IT.not_ x)
  | M_PEapply_fun (f, pes) ->
      let@ xs = ListM.mapM (self var_map) pes in
      begin match evaluate_fun f xs with
        | Some it -> return it
        | None -> unsupported "mucore apply_fun unspecified" (!^ "")
      end
  | M_PEctor (M_Ctuple, pes) ->
    let@ xs = ListM.mapM (self var_map) pes in
    return (IT.tuple_ xs)
  | M_PEconv_int (ct_expr, pe)
  | M_PEconv_loaded_int (ct_expr, pe) ->
    let@ x = self var_map pe in
    let@ ct_it = self var_map ct_expr in
    let@ ct = match IT.is_const ct_it with
    | Some (IT.CType_const ct, _) -> return ct
    | Some _ -> assert false (* shouldn't be possible given type *)
    | None -> fail {loc; msg = Generic (Pp.item "expr from C syntax: non-constant type"
        (IT.pp ct_it))}
    in
    begin match ct with
    | Sctypes.Integer Sctypes.IntegerTypes.Bool ->
      begin match IT.get_num_z x with
      | Some i -> return (IT.bool_ (not (Z.equal i Z.zero)))
      | _ -> return (bool_ite_1_0 (IT.eq_ (x, IT.int_lit_ 0 (IT.bt x))))
      end
    | _ -> do_wrapI loc ct x
    end
  | M_PEwrapI (act, pe) ->
    let@ x = self var_map pe in
    do_wrapI loc act.ct x
  | M_PEcatch_exceptional_condition (act, pe) ->
    let@ x = self var_map pe in
    do_wrapI loc act.ct x
  | M_PEbounded_binop (bk, op, pe_x, pe_y) ->
    let@ x = self var_map pe_x in
    let@ y = self var_map pe_y in
    let it = match op with
      | IOpAdd -> IT.add_ (x, y)
      | IOpSub -> IT.sub_ (x, y)
      | IOpMul -> IT.mul_ (x, y)
    in
    do_wrapI loc ((bound_kind_act bk).ct) it
  | M_PEcfunction pe ->
    let@ x = self var_map pe in
    let c_sig = Option.bind (IT.is_sym x)
      (fun (sym, _) -> Pmap.lookup sym ctxt.mu_call_funinfo) in
    let sig_it = Option.bind c_sig IT.const_of_c_sig in
    begin match sig_it with
      | Some it -> simp_const_pe it
      | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: c-function ptr"
        (Pp.typ (IT.pp x) (Pp_mucore_ast.pp_pexpr pexpr)))}
    end
  | _ -> unsupported "pure-expression type" (!^ "")


let rec symb_exec_mu_expr ctxt state_vars expr =
  let (state, var_map) = state_vars in
  let (M_Expr (loc, annots, _, e)) = expr in
  let opt_bt = WellTyped.BaseTyping.integer_annot annots
    |> Option.map (fun ity -> Memory.bt_of_sct (Sctypes.Integer ity))
  in
  Pp.debug 22 (lazy (Pp.item "doing symb exec" (Pp.typ (Pp_mucore.pp_expr expr)
    (Pp.typ (!^ "typ info") (Pp.list BT.pp (Option.to_list opt_bt))))));
  let rcval v st = return (Compute (v, st)) in
  match e with
  | M_Epure pe ->
    let@ r_v = symb_exec_mu_pexpr ctxt var_map pe in
    return (Compute (r_v, state))
  | M_Eif (g_e, e1, e2) ->
    if is_undef_expr e1
    then symb_exec_mu_expr ctxt (state, var_map) e2
    else if is_undef_expr e2
    then symb_exec_mu_expr ctxt (state, var_map) e1
    else
    let@ g_v = symb_exec_mu_pexpr ctxt var_map g_e in
    let@ r_e1 = symb_exec_mu_expr ctxt (state, var_map) e1 in
    let@ r_e2 = symb_exec_mu_expr ctxt (state, var_map) e2 in
    return (If_Else (g_v, r_e1, r_e2))
  | M_Elet (p, e1, e2) ->
    let@ r_v = symb_exec_mu_pexpr ctxt var_map e1 in
    let@ var_map2 = add_pattern p r_v var_map in
    symb_exec_mu_expr ctxt (state, var_map2) e2
  | M_Ewseq (p, e1, e2)
  | M_Esseq (p, e1, e2) ->
    let@ r1 = symb_exec_mu_expr ctxt (state, var_map) e1 in
    let rec cont = function
      | Call_Ret x -> (* early return *) return (Call_Ret x)
      | Compute (v, state) ->
        let@ var_map2 = add_pattern p v var_map in
        symb_exec_mu_expr ctxt (state, var_map2) e2
      | If_Else (t, x, y) ->
        let@ r_x = cont x in
        let@ r_y = cont y in
        return (If_Else (t, r_x, r_y))
    in
    cont r1
  | M_Eunseq exps ->
    let orig_expr = expr in
    let rec cont1 state exp_vals = function
      | [] -> rcval (IT.tuple_ (List.rev exp_vals)) state
      | (exp :: exps) ->
        let@ r = symb_exec_mu_expr ctxt (state, var_map) exp in
        cont2 exp_vals exps r
      and cont2 exp_vals exps = function
      | Call_Ret _ -> fail {loc; msg = Generic
          (Pp.item "unsequenced return" (Pp_mucore.pp_expr orig_expr))}
      | Compute (v, state) ->
        cont1 state (v :: exp_vals) exps
      | If_Else (t, x, y) ->
        let@ r_x = cont2 exp_vals exps x in
        let@ r_y = cont2 exp_vals exps y in
        return (If_Else (t, r_x, r_y))
    in
    cont1 state [] exps
  | M_Erun (sym, args) ->
    let@ arg_vs = ListM.mapM (symb_exec_mu_pexpr ctxt var_map) args in
    begin match Pmap.lookup sym ctxt.label_defs with
    | Some (M_Return _) ->
      assert (List.length args == 1);
      return (Call_Ret (List.hd arg_vs))
    | _ ->
       fail {loc; msg = Generic Pp.(!^"function has goto-labels in control-flow")}
    end
  | M_Ebound ex -> symb_exec_mu_expr ctxt (state, var_map) ex
  | M_Eaction (M_Paction (_, M_Action (_, action))) ->
    begin match action with
    | M_Create (pe, act, prefix) ->
      let (ptr, state) = mk_local_ptr state in
      rcval ptr state
    | M_Store (_, _, p_pe, v_pe, _) ->
      let@ p_v = symb_exec_mu_pexpr ctxt var_map p_pe in
      let@ v_v = symb_exec_mu_pexpr ctxt var_map v_pe in
      let@ ix = get_local_ptr loc p_v in
      rcval IT.unit_ (upd_loc_state state ix v_v)
    | M_Load (_, p_pe, _) ->
      let@ p_v = symb_exec_mu_pexpr ctxt var_map p_pe in
      let@ ix = get_local_ptr loc p_v in
      let@ v = match IntMap.find_opt ix state.loc_map with
        | None -> fail {loc; msg = Generic (Pp.item "unavailable memory address" (IT.pp p_v))}
        | Some None -> fail {loc; msg = Generic (Pp.item "uninitialised memory address" (IT.pp p_v))}
        | Some (Some ix) -> return ix
      in
      rcval v state
    | M_Kill (_, p_pe) ->
      let@ p_v = symb_exec_mu_pexpr ctxt var_map p_pe in
      let@ ix = get_local_ptr loc p_v in
      rcval IT.unit_ ({state with loc_map = IntMap.remove ix state.loc_map})
    | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported memory op"
        (Pp_mucore.pp_expr expr))}
    end
  | M_Eccall (act, fun_pe, args_pe) ->
    let@ fun_it = symb_exec_mu_pexpr ctxt var_map fun_pe in
    let@ args_its = ListM.mapM (symb_exec_mu_pexpr ctxt var_map) args_pe in
    let fail_fun_it msg = fail {loc;
        msg = Generic (Pp.item ("getting expr from C syntax: function val: " ^ msg)
            (Pp.typ (Pp_mucore.pp_pexpr fun_pe) (IT.pp fun_it)))} in
    let@ nm = match IT.is_sym fun_it with
    | None -> fail_fun_it "not a constant function address"
    | Some (nm, _) -> return nm
    in
    if SymMap.mem nm ctxt.c_fun_pred_map
    then begin
      let (pred, def) = SymMap.find nm ctxt.c_fun_pred_map in
      rcval (IT.pred_ pred args_its def.LogicalFunctions.return_bt) state
    end else if Sym.has_id_with Setup.unfold_stdlib_name nm
    then begin
      let s = Option.get (Sym.has_id nm) in
      let wrap_int x = IT.wrapI_ (signed_int_ity, x) in
      if String.equal s "ctz_proxy"
      then rcval (wrap_int (IT.arith_unop Terms.BWCTZNoSMT (List.hd args_its))) state
      else if List.exists (String.equal s) ["ffs_proxy"; "ffsl_proxy"; "ffsll_proxy"]
      then rcval (wrap_int (IT.arith_unop Terms.BWFFSNoSMT (List.hd args_its))) state
      else failwith ("unknown stdlib function: " ^ s)
    end else fail_fun_it "not a function with a pure/logical interpretation"
  | M_CN_progs _ ->
    rcval IT.unit_ state
  | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported"
        (Pp_mucore.pp_expr expr))}

let is_wild_pat = function
  | M_Pattern (_, _, _, M_CaseBase (None, _)) -> true
  | _ -> false

let rec filter_syms ss p =
  let (M_Pattern (a, b, c, pat)) = p in
  let mk pat = M_Pattern (a, b, c, pat) in
  match pat with
  | M_CaseBase (Some s, bt) ->
    if SymSet.mem s ss then p else mk (M_CaseBase (None, bt))
  | M_CaseBase (None, _) -> p
  | M_CaseCtor (M_Ctuple, ps) ->
    let ps = List.map (filter_syms ss) ps in
    if List.for_all is_wild_pat ps
    then mk (M_CaseBase (None, CF.Core.BTy_unit))
    else mk (M_CaseCtor (M_Ctuple, ps))
  | _ -> p

let rec get_ret_it bt = function
  | Call_Ret v -> Some v
  | Compute _ -> None
  | If_Else (t, x, y) ->
    Option.bind (get_ret_it bt x) (fun x_v ->
    Option.bind (get_ret_it bt y) (fun y_v ->
    Some (IT.ite_ (t, x_v, y_v))))

let embed_typing m = Typing.run Context.empty m

let c_fun_to_it id_loc glob_context (id : Sym.t) fsym def
        (fn : 'bty mu_fun_map_decl) =
  let def_args = def.LogicalFunctions.args
    |> List.map IndexTerms.sym_ in
  match fn with
  | M_Proc (loc, args_and_body, _trusted, _) ->
     let rec ignore_l = function
       | M_Define (_, _, l) -> ignore_l l
       | M_Resource (_, _, l) -> ignore_l l
       | M_Constraint (_, _, l) -> ignore_l l
       | M_I i -> i
     in
     let rec mk_var_map acc args_and_body def_args =
       (* TODO: fix: this is just ignoring the types *)
       match args_and_body, def_args with
       | M_Computational ((s, bt), _, args_and_body), 
         v :: def_args ->
          mk_var_map (SymMap.add s v acc) args_and_body def_args
       | M_L l, [] ->
          (acc, ignore_l l)
       | _ -> 
          assert false
     in
    let (arg_map, (body, labels, rt)) = mk_var_map SymMap.empty args_and_body def_args in
    let ctxt = {glob_context with label_defs = labels} in
    (* TODO: if labels are used, the WellTyped code will fail in an incomprehensible way,
        should probably give the user a better error first *)
    let@ body = embed_typing (WellTyped.BaseTyping.infer_expr SymMap.empty body) in
    let@ r = symb_exec_mu_expr ctxt (init_state, arg_map) body in
    begin match get_ret_it (def.LogicalFunctions.return_bt) r with
    | Some it -> return it
    | _ -> fail {loc;
        msg = Generic (Pp.item "c_fun_to_it: does not return" (Pp_mucore.pp_expr body))}
    end
  | _ ->
    fail {loc = id_loc;
        msg = Generic (Pp.string ("c_fun_to_it: not defined: " ^ Sym.pp_string fsym))}

let upd_def loc sym def_tm logical_predicates =
  let open LogicalFunctions in
  let@ (def, rem) = match List.partition (fun (sym2, _) -> Sym.equal sym sym2)
    logical_predicates
  with
  | ([], _) -> fail {loc;
        msg = Unknown_logical_function {id = sym; resource = false}}
  | ([(_, def)], rem) -> return (def, rem)
  | _ -> fail {loc;
        msg = Generic (Pp.typ (Pp.string "logical predicate multiply defined") (Sym.pp sym))}
  in
  match def.definition with
  | Uninterp -> return ((sym, { def with definition = Def def_tm }) :: rem)
  | _ -> fail {loc;
        msg = Generic (Pp.typ (Pp.string "logical predicate already defined") (Sym.pp sym))}

let add_c_fun_defs logical_predicates mu_call_funinfo log_c_defs =
  let pred_def_map = List.fold_left (fun m (sym, def) -> SymMap.add sym def m)
    SymMap.empty logical_predicates in
  let@ c_fun_pred_map = ListM.fold_leftM (fun m (fsym, _, loc, pred_sym) ->
        let@ def = match SymMap.find_opt pred_sym pred_def_map with
          | Some def -> return def
          | None -> fail {loc; msg = Unknown_logical_function
                {id = pred_sym; resource = false}}
        in
        return (SymMap.add fsym (pred_sym, def) m))
    SymMap.empty log_c_defs in
  let global_context = {label_defs = Pmap.empty Sym.compare; c_fun_pred_map; mu_call_funinfo} in
  let@ conv_defs = ListM.mapM (fun (fsym, fbody, loc, pred_sym) ->
        let (_, def) = SymMap.find fsym c_fun_pred_map in
        let@ it = c_fun_to_it loc global_context pred_sym fsym def fbody in
        Pp.debug 4 (lazy (Pp.item "converted c function body to logical fun"
            (Pp.typ (Sym.pp fsym) (IT.pp it))));
        return (loc, pred_sym, it)) log_c_defs in
  ListM.fold_leftM (fun lps (loc, id, it) -> upd_def loc id it lps) logical_predicates conv_defs

