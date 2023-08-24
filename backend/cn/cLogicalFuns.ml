open Resultat
open Effectful.Make(Resultat)
open TypeErrors
module SymMap = Map.Make(Sym)
module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)


open Mucore

module IT = IndexTerms

type 'a exec_result =
  | Call_Ret of IT.t
  | Compute of IT.t * 'a
  | If_Else of IT.t * 'a exec_result * 'a exec_result

let mu_val_to_it = function
  | M_Vunit -> Some IT.unit_
  | M_Vtrue -> Some (IT.bool_ true)
  | M_Vfalse -> Some (IT.bool_ false)
  | M_Vobject (M_OVinteger iv) -> Some (IT.z_ (Memory.z_of_ival iv))
  | _ -> None

let local_sym_ptr = Sym.fresh_named "local_ptr"

type state = {
  loc_map : (IT.t option) IntMap.t;
  next_loc : int;
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

let rec symb_exec_mu_pexpr var_map pexpr =
  let (M_Pexpr (loc, _, _, pe)) = pexpr in
  match pe with
  | M_PEsym sym -> begin match SymMap.find_opt sym var_map with
    | Some r -> return r
    | _ -> fail {loc; msg = Unknown_variable sym}
  end
  | M_PEval v -> begin match mu_val_to_it v with
    | Some r -> return r
    | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported val"
        (Pp_mucore.pp_pexpr pexpr))}
  end
  | M_PEop (op, x, y) ->
    let@ x_v = symb_exec_mu_pexpr var_map x in
    let@ y_v = symb_exec_mu_pexpr var_map y in
    begin match op with
    | OpAdd -> return (IT.add_ (x_v, y_v))
    | OpSub -> return (IT.sub_ (x_v, y_v))
    | OpEq  -> return (IT.eq_ (x_v, y_v))
    | OpLt  -> return (IT.lt_ (x_v, y_v))
    | OpLe  -> return (IT.le_ (x_v, y_v))
    | OpGt  -> return (IT.gt_ (x_v, y_v))
    | OpGe  -> return (IT.ge_ (x_v, y_v))
    | OpAnd -> return (IT.and_ [x_v; y_v])
    | OpOr  -> return (IT.or_ [x_v; y_v])
    | _ -> fail {loc; msg = Generic (Pp.item "expr from C syntax: unsupported op"
        (Pp_mucore.Basic.pp_binop op))}
    end
  | M_PEconv_int (ct_expr, pe)
  | M_PEconv_loaded_int (ct_expr, pe) ->
    (* FIXME revisit this, just ignoring wrapping here *)
    symb_exec_mu_pexpr var_map pe
  | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported pure expr"
        (Pp_mucore.pp_pexpr pexpr))}

let add_pattern p v expr var_map =
  let (M_Pattern (loc, _, pattern) : mu_pattern) = p in
  match pattern with
  | M_CaseBase (Some s, _) ->
    return (SymMap.add s v var_map)
  | M_CaseBase (None, _) ->
    return var_map
  | _ ->
    fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported pattern"
        (Pp_mucore.pp_expr expr))}

let rec mk_var_map nms vs = match nms, vs with
  | [], [] -> SymMap.empty
  | (nm :: nms, v :: vs) -> SymMap.add nm v (mk_var_map nms vs)
  | _ -> assert false

let rec symb_exec_mu_expr label_defs state_vars expr =
  let (state, var_map) = state_vars in
  let (M_Expr (loc, _, e)) = expr in
  match e with
  | M_Epure pe ->
    let@ r_v = symb_exec_mu_pexpr var_map pe in
    return (Compute (r_v, state))
  | M_Eif (g_e, e1, e2) ->
    let@ g_v = symb_exec_mu_pexpr var_map g_e in
    let@ r_e1 = symb_exec_mu_expr label_defs (state, var_map) e1 in
    let@ r_e2 = symb_exec_mu_expr label_defs (state, var_map) e2 in
    return (If_Else (g_v, r_e1, r_e2))
  | M_Elet (M_Pat p, e1, e2) ->
    let@ r_v = symb_exec_mu_pexpr var_map e1 in
    let@ var_map2 = add_pattern p r_v expr var_map in
    symb_exec_mu_expr label_defs (state, var_map2) e2
  | M_Ewseq (p, e1, e2)
  | M_Esseq (p, e1, e2) ->
    let@ r1 = symb_exec_mu_expr label_defs (state, var_map) e1 in
    let rec cont = function
      | Call_Ret x -> (* early return *) return (Call_Ret x)
      | Compute (v, state) ->
        let@ var_map2 = add_pattern p v expr var_map in
        symb_exec_mu_expr label_defs (state, var_map2) e2
      | If_Else (t, x, y) ->
        let@ r_x = cont x in
        let@ r_y = cont y in
        return (If_Else (t, r_x, r_y))
    in
    cont r1
  | M_Erun (sym, args) ->
    let@ arg_vs = ListM.mapM (symb_exec_mu_pexpr var_map) args in
    begin match Pmap.lookup sym label_defs with
    | Some (M_Return _) ->
      assert (List.length args == 1);
      return (Call_Ret (List.hd arg_vs))
    | _ ->
       fail {loc; msg = Generic Pp.(!^"function has goto-labels in control-flow")}
    end
  | M_Ebound ex -> symb_exec_mu_expr label_defs (state, var_map) ex
  | M_Eaction (M_Paction (_, M_Action (_, action))) ->
    begin match action with
    | M_Create (pe, act, prefix) ->
      let (ptr, state) = mk_local_ptr state in
      return (Compute (ptr, state))
    | M_Store (_, _, p_pe, v_pe, _) ->
      let@ p_v = symb_exec_mu_pexpr var_map p_pe in
      let@ v_v = symb_exec_mu_pexpr var_map v_pe in
      let@ ix = get_local_ptr loc p_v in
      return (Compute (IT.unit_, upd_loc_state state ix v_v))
    | M_Load (_, p_pe, _) ->
      let@ p_v = symb_exec_mu_pexpr var_map p_pe in
      let@ ix = get_local_ptr loc p_v in
      let@ v = match IntMap.find_opt ix state.loc_map with
        | None -> fail {loc; msg = Generic (Pp.item "unavailable memory address" (IT.pp p_v))}
        | Some None -> fail {loc; msg = Generic (Pp.item "uninitialised memory address" (IT.pp p_v))}
        | Some (Some ix) -> return ix
      in
      return (Compute (v, state))
    | M_Kill (_, p_pe) ->
      let@ p_v = symb_exec_mu_pexpr var_map p_pe in
      let@ ix = get_local_ptr loc p_v in
      return (Compute (IT.unit_, {state with loc_map = IntMap.remove ix state.loc_map}))
    | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported memory op"
        (Pp_mucore.pp_expr expr))}
    end
  | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported"
        (Pp_mucore.pp_expr expr))}

let c_function_to_it fsym rbt args body label_defs : (IT.t) m  =
  let (M_Pexpr (loc, _, _, pe_)) = body in
  match pe_ with
  | M_PEval _ -> fail {loc; msg = Generic (Pp.string "PEval")}
  | _ -> fail {loc; msg = Generic (Pp.string "not PEval")}

let c_function_to_it2 fsym rbt args body label_defs : (IT.t) m  =
  let (M_Expr (loc, _, e_)) = body in
  match e_ with
  | M_Epure pe -> c_function_to_it fsym rbt args pe label_defs
  | _ -> fail {loc; msg = Generic (Pp.item "c_function_to_it2" (Pp_mucore.pp_expr body))}

let rec get_ret_it = function
  | Call_Ret v -> Some v
  | Compute _ -> None
  | If_Else (t, x, y) ->
    Option.bind (get_ret_it x) (fun x_v ->
    Option.bind (get_ret_it y) (fun y_v ->
    Some (IT.ite_ (t, x_v, y_v))))

let c_fun_to_it id_loc (id : Sym.t) fsym def
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
    let@ r = symb_exec_mu_expr labels (init_state, arg_map) body in
    begin match get_ret_it r with
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

let add_c_fun_defs logical_predicates log_c_defs =
  let pred_def_map = List.fold_left (fun m (sym, def) -> SymMap.add sym def m)
    SymMap.empty logical_predicates in
  let@ conv_defs = ListM.mapM (fun (fsym, fbody, loc, pred_sym) ->
        let@ def = match SymMap.find_opt pred_sym pred_def_map with
          | Some def -> return def
          | None -> fail {loc; msg = Unknown_logical_function
                {id = pred_sym; resource = false}}
        in
        let@ it = c_fun_to_it loc pred_sym fsym def fbody in
        Pp.debug 4 (lazy (Pp.item "converted c function body to logical fun"
            (Pp.typ (Sym.pp fsym) (IT.pp it))));
        return (loc, pred_sym, it)) log_c_defs in
  ListM.fold_leftM (fun lps (loc, id, it) -> upd_def loc id it lps) logical_predicates conv_defs

