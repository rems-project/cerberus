open TypeErrors
open Typing

open Effectful.Make (Typing)

module StringMap = Map.Make (String)
module IntMap = Map.Make (Int)
module CF = Cerb_frontend
module BT = BaseTypes
open Cerb_pp_prelude
module Mu = Mucore
module IT = IndexTerms

let fail_n m = fail (fun _ctxt -> m)

type 'a exec_result =
  | Call_Ret of IT.t
  | Compute of IT.t * 'a
  | If_Else of IT.t * 'a exec_result * 'a exec_result

let val_to_it loc (Mu.V ((bt : BT.t), v)) =
  match v with
  | Vunit -> Some (IT.unit_ loc)
  | Vtrue -> Some (IT.bool_ true loc)
  | Vfalse -> Some (IT.bool_ false loc)
  | Vobject (OV (_, OVinteger iv)) -> Some (IT.num_lit_ (Memory.z_of_ival iv) bt loc)
  | Vobject (OV (_, OVpointer ptr_val)) ->
    CF.Impl_mem.case_ptrval
      ptr_val
      (fun _ -> Some (IT.null_ loc))
      (function None -> None | Some sym -> Some (IT.sym_ (sym, BT.(Loc ()), loc)))
      (fun _prov _p -> (* how to correctly convert provenance? *) None)
  | Vctype ct -> Option.map (fun ct -> IT.const_ctype_ ct loc) (Sctypes.of_ctype ct)
  | Vfunction_addr sym -> Some (IT.sym_ (sym, BT.(Loc ()), loc))
  | _ -> None


let local_sym_ptr = Sym.fresh_named "local_ptr"

type state =
  { loc_map : IT.t option IntMap.t;
    next_loc : int
  }

type context =
  { label_defs : (Sym.t, unit Mu.label_def) Pmap.map;
    (* map from c functions to logical functions which we are building *)
    c_fun_pred_map : (Locations.t * Sym.t) Sym.Map.t;
    call_funinfo : (Sym.t, Sctypes.c_concrete_sig) Pmap.map
  }

let init_state = { loc_map = IntMap.empty; next_loc = 1 }

let mk_local_ptr state src_loc =
  let loc_ix = state.next_loc in
  let here = Locations.other __LOC__ in
  let ptr = IT.apply_ local_sym_ptr [ IT.int_ loc_ix here ] BT.(Loc ()) src_loc in
  let loc_map = IntMap.add loc_ix None state.loc_map in
  let state = { loc_map; next_loc = loc_ix + 1 } in
  (ptr, state)


let is_local_ptr ptr =
  Option.bind (IT.is_pred_ ptr) (function
    | name, [ ix ] when Sym.equal name local_sym_ptr -> Option.map Z.to_int (IT.is_z ix)
    | _ -> None)


let get_local_ptr loc ptr =
  match is_local_ptr ptr with
  | None -> fail_n { loc; msg = Generic (Pp.item "use of non-local pointer" (IT.pp ptr)) }
  | Some ix -> return ix


let upd_loc_state state ix v =
  let loc_map = IntMap.add ix (Some v) state.loc_map in
  { state with loc_map }


let triv_simp_ctxt = Simplify.default Global.empty

let simp_const loc lpp it =
  let it2 = Simplify.IndexTerms.simp triv_simp_ctxt it in
  match (IT.is_z it2, IT.get_bt it2) with
  | Some _z, _ -> return it2
  | _, BT.Integer ->
    fail_n
      { loc;
        msg =
          Generic
            (Pp.item
               "getting expr from C syntax: failed to simplify integer to numeral"
               (Pp.typ (Lazy.force lpp) (IT.pp it2)))
      }
  | _, _ -> return it2


let do_wrapI loc ct it =
  match Sctypes.is_integer_type ct with
  | Some ity ->
    let ity_bt = Memory.bt_of_sct ct in
    if BT.equal ity_bt (IT.get_bt it) then
      return it
    else
      return (IT.wrapI_ (ity, it) loc)
  | None ->
    fail_n
      { loc;
        msg =
          Generic (Pp.item "expr from C syntax: coercion to non-int type" (Sctypes.pp ct))
      }


(* FIXME: this is yet another notion of whether a term is effectively a numeric constant
   and permitted for multiply/divide or not - similar to a simplifier-based notion in
   welltyped and a solver-based notion in check. *)
let rec is_const_num = function
  | IT.IT (IT.Const _, _, _) -> true
  | IT.IT (IT.Binop (binop, x, y), _, _) ->
    is_const_num x
    && is_const_num y
    &&
      (match binop with
      | IT.Add | IT.Sub | IT.Mul | IT.Div | IT.Exp | IT.Rem | IT.Mod -> true
      | _ -> false)
  | _ -> false


let rec add_pattern p v var_map =
  let (Mu.Pattern (loc, _, _, pattern)) = p in
  match pattern with
  | CaseBase (Some s, _) -> return (Sym.Map.add s v var_map)
  | CaseBase (None, _) -> return var_map
  | CaseCtor (Ctuple, ps) ->
    let@ vs =
      match v with
      | IT.IT (IT.Tuple vs, _, _) -> return vs
      | it ->
        fail_n
          { loc;
            msg =
              Generic
                (Pp.item
                   "getting expr from C syntax: cannot tuple-split val"
                   (Pp.typ (IT.pp it) (Pp_mucore.Basic.pp_pattern p)))
          }
    in
    assert (List.length vs == List.length ps);
    ListM.fold_rightM
      (fun (p, v) var_map -> add_pattern p v var_map)
      (List.combine ps vs)
      var_map
  | _ ->
    fail_n
      { loc;
        msg =
          Generic
            (Pp.item
               "getting expr from C syntax: unsupported pattern"
               (Pp_mucore.Basic.pp_pattern p))
      }


let signed_int_ity = Sctypes.(IntegerTypes.Signed IntegerBaseTypes.Int_)

let signed_int_ty = Memory.bt_of_sct (Sctypes.Integer signed_int_ity)

let is_two_pow it =
  match IT.get_term it with
  | Terms.Binop (Terms.ExpNoSMT, x, y)
    when Option.equal Z.equal (IT.get_num_z x) (Some (Z.of_int 2)) ->
    Some (`Two_loc (IT.get_loc x), `Exp y)
  | Terms.Binop (Terms.Exp, x, y)
    when Option.equal Z.equal (IT.get_num_z x) (Some (Z.of_int 2)) ->
    Some (`Two_loc (IT.get_loc x), `Exp y)
  | _ -> None


let bool_rep_ty = Memory.bt_of_sct Sctypes.(Integer IntegerTypes.Bool)

let bool_ite_1_0 bt b loc = IT.ite_ (b, IT.int_lit_ 1 bt loc, IT.int_lit_ 0 bt loc) loc

(* FIXME: find a home for this, also needed in check, needs the Typing monad *)
let eval_fun f args orig_pexpr =
  let (Mu.Pexpr (loc, _, bt, _pe)) = orig_pexpr in
  match Mu.evaluate_fun f args with
  | Some (`Result_IT it) -> return it
  | Some (`Result_Integer z) ->
    let@ () = WellTyped.ensure_bits_type loc bt in
    let bits_info = Option.get (BT.is_bits_bt bt) in
    if BT.fits_range bits_info z then
      return (IT.num_lit_ z bt loc)
    else
      fail_n
        { loc;
          msg =
            Generic
              (Pp.item
                 "function application result out of range"
                 (Pp_mucore_ast.pp_pexpr orig_pexpr
                  ^^ Pp.hardline
                  ^^ Pp.typ (Pp.z z) (BT.pp bt)))
        }
  | None ->
    fail_n
      { loc;
        msg =
          Generic
            (Pp.item
               "cannot evaluate mucore function app"
               (Pp_mucore_ast.pp_pexpr orig_pexpr
                ^^ Pp.hardline
                ^^ !^"arg vals:"
                ^^^ Pp.brackets (Pp.list IT.pp args)))
      }


let rec symb_exec_pexpr ctxt var_map pexpr =
  let (Mu.Pexpr (loc, annots, _, pe)) = pexpr in
  let opt_bt =
    WellTyped.BaseTyping.integer_annot annots
    |> Option.map (fun ity -> Memory.bt_of_sct (Sctypes.Integer ity))
  in
  Pp.debug
    22
    (lazy
      (Pp.item
         "doing pure symb exec"
         (Pp.typ
            (Pp_mucore.pp_pexpr pexpr)
            (Pp.typ !^"typ info" (Pp.list BT.pp (Option.to_list opt_bt))))));
  let self = symb_exec_pexpr ctxt in
  let simp_const_pe v = simp_const loc (lazy (Pp_mucore.pp_pexpr pexpr)) v in
  let unsupported msg doc =
    fail_n
      { loc;
        msg =
          Generic
            (Pp.item
               ("getting expr from C syntax: unsupported: " ^ msg)
               (Pp.typ doc (Pp_mucore_ast.pp_pexpr pexpr)))
      }
  in
  match pe with
  | PEsym sym ->
    (match Sym.Map.find_opt sym var_map with
     | Some r -> return r
     | _ -> fail_n { loc; msg = Unknown_variable sym })
  | PEval v ->
    (match val_to_it loc v with
     | Some r -> return r
     | _ ->
       unsupported "val" (Pp.typ !^"typ info" (Pp.list BT.pp (Option.to_list opt_bt))))
  | PElet (p, e1, e2) ->
    let@ r_v = self var_map e1 in
    let@ var_map2 = add_pattern p r_v var_map in
    self var_map2 e2
  | PEif (cond_pe, x, y) ->
    if Mu.is_undef_or_error_pexpr x then
      self var_map y
    else if Mu.is_undef_or_error_pexpr y then
      self var_map x
    else
      let@ cond = self var_map cond_pe in
      let@ x_v = self var_map x in
      let@ y_v = self var_map y in
      return (IT.ite_ (cond, x_v, y_v) loc)
  | PEop (op, x, y) ->
    let@ x_v = self var_map x in
    let@ y_v = self var_map y in
    let f x_v y_v =
      match op with
      | OpAdd -> IT.add_ (x_v, y_v) loc
      | OpSub -> IT.sub_ (x_v, y_v) loc
      | OpMul ->
        if is_const_num x_v || is_const_num y_v then
          IT.mul_ (x_v, y_v) loc
        else
          IT.mul_no_smt_ (x_v, y_v) loc
      | OpDiv ->
        if is_const_num y_v then
          IT.div_ (x_v, y_v) loc
        else
          IT.div_no_smt_ (x_v, y_v) loc
      | OpEq -> IT.eq_ (x_v, y_v) loc
      | OpLt -> IT.lt_ (x_v, y_v) loc
      | OpLe -> IT.le_ (x_v, y_v) loc
      | OpGt -> IT.gt_ (x_v, y_v) loc
      | OpGe -> IT.ge_ (x_v, y_v) loc
      | OpAnd -> IT.and_ [ x_v; y_v ] loc
      | OpOr -> IT.or_ [ x_v; y_v ] loc
      | OpExp ->
        if is_const_num x_v && is_const_num y_v then
          IT.exp_ (x_v, y_v) loc
        else
          IT.exp_no_smt_ (x_v, y_v) loc
      | OpRem_f ->
        if is_const_num y_v then
          IT.rem_ (x_v, y_v) loc
        else
          IT.rem_no_smt_ (x_v, y_v) loc
      | OpRem_t ->
        if is_const_num y_v then
          IT.mod_ (x_v, y_v) loc
        else
          IT.mod_no_smt_ (x_v, y_v) loc
    in
    (match (op, x_v, is_two_pow y_v) with
     | OpMul, _, Some (`Two_loc two_loc, `Exp exp) ->
       let exp_loc = IT.get_loc y_v in
       return
         (IT.mul_ (x_v, IT.exp_ (IT.int_lit_ 2 (IT.get_bt x_v) two_loc, exp) exp_loc) loc)
     | OpDiv, _, Some (`Two_loc two_loc, `Exp exp) ->
       let exp_loc = IT.get_loc y_v in
       return
         (IT.div_ (x_v, IT.exp_ (IT.int_lit_ 2 (IT.get_bt x_v) two_loc, exp) exp_loc) loc)
     | _, _, _ ->
       let@ res = simp_const_pe (f x_v y_v) in
       return res)
  | PEbitwise_unop (unop, pe1) ->
    let@ x = self var_map pe1 in
    let@ unop =
      match unop with
      | BW_CTZ -> return IT.BW_CTZ_NoSMT
      | BW_FFS -> return IT.BW_FFS_NoSMT
      | _ -> unsupported "unary op" !^""
    in
    simp_const_pe (IT.arith_unop unop x loc)
  | PEbitwise_binop (binop, pe1, pe2) ->
    let@ x = self var_map pe1 in
    let@ y = self var_map pe2 in
    let binop =
      match binop with BW_AND -> IT.BW_And | BW_OR -> IT.BW_Or | BW_XOR -> IT.BW_Xor
    in
    simp_const_pe (IT.arith_binop binop (x, y) loc)
  | PEbool_to_integer pe ->
    let@ x = self var_map pe in
    return (bool_ite_1_0 signed_int_ty x loc)
  | PEnot pe ->
    let@ x = self var_map pe in
    return (IT.not_ x loc)
  | PEapply_fun (f, pes) ->
    let@ xs = ListM.mapM (self var_map) pes in
    eval_fun f xs pexpr
  | PEctor (Ctuple, pes) ->
    let@ xs = ListM.mapM (self var_map) pes in
    return (IT.tuple_ xs loc)
  | PEconv_int (ct_expr, pe) | PEconv_loaded_int (ct_expr, pe) ->
    let@ x = self var_map pe in
    let@ ct_it = self var_map ct_expr in
    let@ ct =
      match IT.is_const ct_it with
      | Some (IT.CType_const ct, _) -> return ct
      | Some _ -> assert false (* shouldn't be possible given type *)
      | None ->
        fail_n
          { loc;
            msg = Generic (Pp.item "expr from C syntax: non-constant type" (IT.pp ct_it))
          }
    in
    (match ct with
     | Sctypes.Integer Sctypes.IntegerTypes.Bool ->
       let here = Locations.other __LOC__ in
       simp_const_pe
         (bool_ite_1_0
            bool_rep_ty
            (IT.not_ (IT.eq_ (x, IT.int_lit_ 0 (IT.get_bt x) here) here) here)
            loc)
     | _ -> do_wrapI loc ct x)
  | PEwrapI (act, pe) ->
    let@ x = self var_map pe in
    do_wrapI loc act.ct x
  | PEcatch_exceptional_condition (act, pe) ->
    let@ x = self var_map pe in
    do_wrapI loc act.ct x
  | PEbounded_binop (bk, op, pe_x, pe_y) ->
    let@ x = self var_map pe_x in
    let@ y = self var_map pe_y in
    let here = Locations.other __LOC__ in
    let it =
      match op with
      | IOpAdd -> IT.add_ (x, y) loc
      | IOpSub -> IT.sub_ (x, y) loc
      | IOpMul -> IT.mul_ (x, y) loc
      | IOpShl -> IT.arith_binop Terms.ShiftLeft (x, IT.cast_ (IT.get_bt x) y here) loc
      | IOpShr -> IT.arith_binop Terms.ShiftRight (x, IT.cast_ (IT.get_bt x) y here) loc
    in
    do_wrapI loc (Mu.bound_kind_act bk).ct it
  | PEcfunction pe ->
    let@ x = self var_map pe in
    let sig_it =
      Option.(
        let@ sym, _ = IT.is_sym x in
        let@ c_sig = Pmap.lookup sym ctxt.call_funinfo in
        IT.const_of_c_sig c_sig loc)
    in
    (match sig_it with
     | Some it -> simp_const_pe it
     | _ ->
       fail_n
         { loc;
           msg =
             Generic
               (Pp.item
                  "getting expr from C syntax: c-function ptr"
                  (Pp.typ (IT.pp x) (Pp_mucore_ast.pp_pexpr pexpr)))
         })
  | _ -> unsupported "pure-expression type" !^""


let rec symb_exec_expr ctxt state_vars expr =
  let state, var_map = state_vars in
  let (Mu.Expr (loc, annots, _, e)) = expr in
  let opt_bt =
    WellTyped.BaseTyping.integer_annot annots
    |> Option.map (fun ity -> Memory.bt_of_sct (Sctypes.Integer ity))
  in
  Pp.debug
    22
    (lazy
      (Pp.item
         "doing symb exec"
         (Pp.typ
            (Pp_mucore.pp_expr expr)
            (Pp.typ !^"typ info" (Pp.list BT.pp (Option.to_list opt_bt))))));
  let rcval v st = return (Compute (v, st)) in
  match e with
  | Epure pe ->
    let@ r_v = symb_exec_pexpr ctxt var_map pe in
    return (Compute (r_v, state))
  | Eif (g_e, e1, e2) ->
    if Mu.is_undef_or_error_expr e1 then
      symb_exec_expr ctxt (state, var_map) e2
    else if Mu.is_undef_or_error_expr e2 then
      symb_exec_expr ctxt (state, var_map) e1
    else
      let@ g_v = symb_exec_pexpr ctxt var_map g_e in
      let@ r_e1 = symb_exec_expr ctxt (state, var_map) e1 in
      let@ r_e2 = symb_exec_expr ctxt (state, var_map) e2 in
      return (If_Else (g_v, r_e1, r_e2))
  | Elet (p, e1, e2) ->
    let@ r_v = symb_exec_pexpr ctxt var_map e1 in
    let@ var_map2 = add_pattern p r_v var_map in
    symb_exec_expr ctxt (state, var_map2) e2
  | Ewseq (p, e1, e2) | Esseq (p, e1, e2) ->
    let@ r1 = symb_exec_expr ctxt (state, var_map) e1 in
    let rec cont = function
      | Call_Ret x -> (* early return *) return (Call_Ret x)
      | Compute (v, state) ->
        let@ var_map2 = add_pattern p v var_map in
        symb_exec_expr ctxt (state, var_map2) e2
      | If_Else (t, x, y) ->
        let@ r_x = cont x in
        let@ r_y = cont y in
        return (If_Else (t, r_x, r_y))
    in
    cont r1
  | Eunseq exps ->
    let orig_expr = expr in
    let rec cont1 state exp_vals = function
      | [] -> rcval (IT.tuple_ (List.rev exp_vals) loc) state
      | exp :: exps ->
        let@ r = symb_exec_expr ctxt (state, var_map) exp in
        cont2 exp_vals exps r
    and cont2 exp_vals exps = function
      | Call_Ret _ ->
        fail_n
          { loc;
            msg = Generic (Pp.item "unsequenced return" (Pp_mucore.pp_expr orig_expr))
          }
      | Compute (v, state) -> cont1 state (v :: exp_vals) exps
      | If_Else (t, x, y) ->
        let@ r_x = cont2 exp_vals exps x in
        let@ r_y = cont2 exp_vals exps y in
        return (If_Else (t, r_x, r_y))
    in
    cont1 state [] exps
  | Erun (sym, args) ->
    let@ arg_vs = ListM.mapM (symb_exec_pexpr ctxt var_map) args in
    (match Pmap.lookup sym ctxt.label_defs with
     | Some (Return _) ->
       assert (List.length args == 1);
       return (Call_Ret (List.hd arg_vs))
     | _ ->
       fail_n { loc; msg = Generic Pp.(!^"function has goto-labels in control-flow") })
  | Ebound ex -> symb_exec_expr ctxt (state, var_map) ex
  | Eaction (Paction (_, Action (_, action))) ->
    (match action with
     | Create (_pe, _act, _prefix) ->
       let ptr, state = mk_local_ptr state loc in
       rcval ptr state
     | Store (_, _, p_pe, v_pe, _) ->
       let@ p_v = symb_exec_pexpr ctxt var_map p_pe in
       let@ v_v = symb_exec_pexpr ctxt var_map v_pe in
       let@ ix = get_local_ptr loc p_v in
       rcval (IT.unit_ loc) (upd_loc_state state ix v_v)
     | Load (_, p_pe, _) ->
       let@ p_v = symb_exec_pexpr ctxt var_map p_pe in
       let@ ix = get_local_ptr loc p_v in
       let@ v =
         match IntMap.find_opt ix state.loc_map with
         | None ->
           fail_n
             { loc; msg = Generic (Pp.item "unavailable memory address" (IT.pp p_v)) }
         | Some None ->
           fail_n
             { loc; msg = Generic (Pp.item "uninitialised memory address" (IT.pp p_v)) }
         | Some (Some ix) -> return ix
       in
       rcval v state
     | Kill (_, p_pe) ->
       let@ p_v = symb_exec_pexpr ctxt var_map p_pe in
       let@ ix = get_local_ptr loc p_v in
       rcval (IT.unit_ loc) { state with loc_map = IntMap.remove ix state.loc_map }
     | _ ->
       fail_n
         { loc;
           msg =
             Generic
               (Pp.item
                  "getting expr from C syntax: unsupported memory op"
                  (Pp_mucore.pp_expr expr))
         })
  | Eccall (_act, fun_pe, args_pe) ->
    let@ fun_it = symb_exec_pexpr ctxt var_map fun_pe in
    let@ args_its = ListM.mapM (symb_exec_pexpr ctxt var_map) args_pe in
    let fail_fun_it msg =
      fail_n
        { loc;
          msg =
            Generic
              (Pp.item
                 ("getting expr from C syntax: function val: " ^ msg)
                 (Pp.typ (Pp_mucore.pp_pexpr fun_pe) (IT.pp fun_it)))
        }
    in
    let@ nm =
      match IT.is_sym fun_it with
      | None -> fail_fun_it "not a constant function address"
      | Some (nm, _) -> return nm
    in
    if Sym.Map.mem nm ctxt.c_fun_pred_map then (
      let loc, l_sym = Sym.Map.find nm ctxt.c_fun_pred_map in
      let@ def = get_logical_function_def loc l_sym in
      rcval (IT.apply_ l_sym args_its def.Definition.Function.return_bt loc) state)
    else (
      let bail = fail_fun_it "not a function with a pure/logical interpretation" in
      match Sym.has_id nm with
      | None -> bail
      | Some s ->
        let wrap_int x = IT.wrapI_ (signed_int_ity, x) in
        if String.equal s "ctz_proxy" then
          rcval
            (wrap_int (IT.arith_unop Terms.BW_CTZ_NoSMT (List.hd args_its) loc) loc)
            state
        else if List.exists (String.equal s) [ "ffs_proxy"; "ffsl_proxy"; "ffsll_proxy" ]
        then
          rcval
            (wrap_int (IT.arith_unop Terms.BW_FFS_NoSMT (List.hd args_its) loc) loc)
            state
        else
          bail)
  | CN_progs _ -> rcval (IT.unit_ loc) state
  | _ ->
    fail_n
      { loc;
        msg =
          Generic
            (Pp.item "getting expr from C syntax: unsupported" (Pp_mucore.pp_expr expr))
      }


let is_wild_pat = function Mu.Pattern (_, _, _, CaseBase (None, _)) -> true | _ -> false

let rec filter_syms ss p =
  let (Mu.Pattern (a, b, c, pat)) = p in
  let mk pat = Mu.Pattern (a, b, c, pat) in
  match pat with
  | CaseBase (Some s, bt) -> if Sym.Set.mem s ss then p else mk (CaseBase (None, bt))
  | CaseBase (None, _) -> p
  | CaseCtor (Ctuple, ps) ->
    let ps = List.map (filter_syms ss) ps in
    if List.for_all is_wild_pat ps then
      mk (CaseBase (None, CF.Core.BTy_unit))
    else
      mk (CaseCtor (Ctuple, ps))
  | _ -> p


let rec get_ret_it loc body bt = function
  | Call_Ret v ->
    let@ () =
      if BT.equal (IT.get_bt v) bt then
        return ()
      else
        fail_n
          { loc;
            msg =
              Generic
                (Pp.item
                   "get_ret_it: basetype mismatch"
                   (Pp.infix_arrow (IT.pp_with_typ v) (BT.pp bt)))
          }
    in
    return v
  | Compute _ ->
    fail_n
      { loc;
        msg =
          Generic
            (Pp.item
               "cn_function c->logical conversion: does not return"
               (Pp_mucore.pp_expr body))
      }
  | If_Else (t, x, y) ->
    let@ x_v = get_ret_it loc body bt x in
    let@ y_v = get_ret_it loc body bt y in
    return (IT.ite_ (t, x_v, y_v) loc)


let c_fun_to_it id_loc glob_context (id : Sym.t) fsym def (fn : 'bty Mu.fun_map_decl) =
  let here = Locations.other __LOC__ in
  let def_args =
    def.Definition.Function.args
    (* TODO - add location information to binders *)
    |> List.map (fun (s, bt) -> IndexTerms.sym_ (s, bt, here))
  in
  Pp.debug
    3
    (lazy
      (Pp.item
         "cn_function converting C function to logical"
         (Pp.infix_arrow (Sym.pp fsym) (Sym.pp id))));
  match fn with
  | Proc { loc; args_and_body; _ } ->
    let rec ignore_l = function
      | Mu.Define (_, _, l) -> ignore_l l
      | Resource (_, _, l) -> ignore_l l
      | Constraint (_, _, l) -> ignore_l l
      | I i -> i
    in
    let rec mk_var_map acc args_and_body def_args =
      match (args_and_body, def_args) with
      | Mu.Computational ((s, bt), _, args_and_body), v :: def_args ->
        if BT.equal bt (IT.get_bt v) then
          mk_var_map (Sym.Map.add s v acc) args_and_body def_args
        else
          fail_n
            { loc;
              msg =
                Generic
                  Pp.(
                    !^"mismatched arguments:"
                    ^^^ parens (BT.pp (IT.get_bt v) ^^^ IT.pp v)
                    ^^^ !^"and"
                    ^^^ parens (BT.pp bt ^^^ Sym.pp s))
            }
      | L l, [] -> return (acc, ignore_l l)
      | _ ->
        fail_n
          { loc;
            msg =
              Generic
                Pp.(
                  !^"mismatched argument number for"
                  ^^^ Pp.infix_arrow (Sym.pp fsym) (Sym.pp id))
          }
    in
    let rec in_computational_ctxt args_and_body m =
      match args_and_body with
      | Mu.Computational ((s, bt), (loc, _info), args_and_body) ->
        Typing.bind
          (Typing.add_a s bt (loc, lazy (Pp.item "argument" (Sym.pp s))))
          (fun () -> in_computational_ctxt args_and_body m)
      | L _ -> m
    in
    let@ arg_map, (body, labels, rt) = mk_var_map Sym.Map.empty args_and_body def_args in
    let@ () =
      match rt with
      | ReturnTypes.Computational ((_, bt), _, _) ->
        let l_ret_bt = def.Definition.Function.return_bt in
        if BT.equal bt l_ret_bt then
          return ()
        else
          fail_n
            { loc = id_loc;
              msg =
                Generic
                  (Pp.item
                     "cn_function: return-type mismatch"
                     (Pp.infix_arrow
                        (Pp.typ (Sym.pp fsym) (BT.pp bt))
                        (Pp.typ (Sym.pp id) (BT.pp l_ret_bt))))
            }
    in
    let ctxt = { glob_context with label_defs = labels } in
    let label_context = WellTyped.WProc.label_context rt labels in
    let@ body =
      pure
        (in_computational_ctxt
           args_and_body
           (WellTyped.BaseTyping.infer_expr label_context body))
    in
    let@ r = symb_exec_expr ctxt (init_state, arg_map) body in
    let@ it = get_ret_it loc body def.Definition.Function.return_bt r in
    simp_const loc (lazy (Pp_mucore.pp_expr body)) it
  | _ ->
    fail_n
      { loc = id_loc;
        msg = Generic (Pp.string ("cn_function: not defined: " ^ Sym.pp_string fsym))
      }


let upd_def (loc, sym, def_tm) =
  let open Definition.Function in
  let@ def = get_logical_function_def loc sym in
  match def.body with
  | Uninterp -> add_logical_function sym { def with body = Def def_tm }
  | _ ->
    fail_n
      { loc;
        msg =
          Generic (Pp.typ (Pp.string "logical predicate already defined") (Sym.pp sym))
      }


let add_logical_funs_from_c call_funinfo funs_to_convert funs =
  let c_fun_pred_map =
    List.fold_left
      (fun m Mu.{ c_fun_sym; loc; l_fun_sym } -> Sym.Map.add c_fun_sym (loc, l_fun_sym) m)
      Sym.Map.empty
      funs_to_convert
  in
  let global_context =
    { label_defs = Pmap.empty Sym.compare; c_fun_pred_map; call_funinfo }
  in
  let@ conv_defs =
    ListM.mapM
      (fun Mu.{ c_fun_sym; loc; l_fun_sym } ->
        let@ def = get_logical_function_def loc l_fun_sym in
        let@ fbody =
          match Pmap.lookup c_fun_sym funs with
          | Some fbody -> return fbody
          | None -> fail_n { loc; msg = Unknown_function c_fun_sym }
        in
        let@ it = c_fun_to_it loc global_context l_fun_sym c_fun_sym def fbody in
        Pp.debug
          4
          (lazy
            (Pp.item
               "converted c function body to logical fun"
               (Pp.typ (Sym.pp c_fun_sym) (IT.pp it))));
        return (loc, l_fun_sym, it))
      funs_to_convert
  in
  ListM.iterM upd_def conv_defs
