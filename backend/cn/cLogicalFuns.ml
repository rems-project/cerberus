open Resultat
open Effectful.Make(Resultat)
open TypeErrors
module SymMap = Map.Make(Sym)
module StringMap = Map.Make(String)


open Mucore

module IT = IndexTerms

type exec_result = CallRet of IT.t | Compute of IT.t

let mu_val_to_it = function
  | M_Vunit -> Some IT.unit_
  | M_Vtrue -> Some (IT.bool_ true)
  | M_Vfalse -> Some (IT.bool_ false)
  | M_Vobject (M_OVinteger iv) -> Some (IT.z_ (Memory.z_of_ival iv))
  | _ -> None

let symb_exec_mu_pexpr var_map pexpr =
  let (M_Pexpr (loc, _, _, pe)) = pexpr in
  match pe with
  | M_PEsym sym -> begin match SymMap.find_opt sym var_map with
    | Some r -> return r
    | _ -> fail {loc; msg = Unknown_variable sym}
  end
  | M_PEval v -> begin match mu_val_to_it v with
    | Some r -> return r
    | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported"
        (Pp_mucore.pp_pexpr pexpr))}
  end
  | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported"
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

let rec symb_exec_mu_expr label_defs var_map expr =
  let (M_Expr (loc, _, e)) = expr in
  match e with
  | M_Epure pe ->
    let@ r_v = symb_exec_mu_pexpr var_map pe in
    return (Compute r_v)
  | M_Elet (M_Pat p, e1, e2) ->
    let@ r_v = symb_exec_mu_pexpr var_map e1 in
    let@ var_map2 = add_pattern p r_v expr var_map in
    symb_exec_mu_expr label_defs var_map2 e2
  | M_Ewseq (p, e1, e2) ->
    let@ r1 = symb_exec_mu_expr label_defs var_map e1 in
    begin match r1 with
    | CallRet _ -> (* early return *) return r1
    | Compute v ->
      let@ var_map2 = add_pattern p v expr var_map in
      symb_exec_mu_expr label_defs var_map2 e2
    end
  | M_Esseq (p, e1, e2) ->
    let@ r1 = symb_exec_mu_expr label_defs var_map e1 in
    begin match r1 with
    | CallRet _ -> (* early return *) return r1
    | Compute v ->
      let@ var_map2 = add_pattern p v expr var_map in
      symb_exec_mu_expr label_defs var_map2 e2
    end
  | M_Erun (sym, args) ->
    let@ arg_vs = ListM.mapM (symb_exec_mu_pexpr var_map) args in
    begin match Pmap.lookup sym label_defs with
    | Some (M_Return _) ->
      assert (List.length args == 1);
      return (CallRet (List.hd arg_vs))
    | _ ->
       fail {loc; msg = Generic Pp.(!^"function has goto-labels in control-flow")}
    end
  | _ -> fail {loc; msg = Generic (Pp.item "getting expr from C syntax: unsupported"
        (Pp_mucore.pp_expr expr))}

let c_function_to_it fsym rbt args body label_defs : (IT.t, type_error) m  =
  let (M_Pexpr (loc, _, _, pe_)) = body in
  match pe_ with
  | M_PEval _ -> fail {loc; msg = Generic (Pp.string "PEval")}
  | _ -> fail {loc; msg = Generic (Pp.string "not PEval")}

let c_function_to_it2 fsym rbt args body label_defs : (IT.t, type_error) m  =
  let (M_Expr (loc, _, e_)) = body in
  match e_ with
  | M_Epure pe -> c_function_to_it fsym rbt args pe label_defs
  | _ -> fail {loc; msg = Generic (Pp.item "c_function_to_it2" (Pp_mucore.pp_expr body))}


let c_fun_to_it id fsym def
        (fn : 'bty mu_fun_map_decl) =
  let def_args = def.LogicalPredicates.args
    |> List.map IndexTerms.sym_ in
  match fn with
  | M_Fun (rbt, args, body) ->
    let arg_map = mk_var_map (List.map fst args) def_args in
    let@ r = symb_exec_mu_pexpr arg_map body in
    return r
  | M_Proc (loc, args_and_body, _ft, _trusted) ->
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
    let@ r = symb_exec_mu_expr labels arg_map body in
    begin match r with
    | CallRet it -> return it
    | _ -> fail {loc = Id.loc id;
        msg = Generic (Pp.item "c_fun_to_it: does not return" (Pp_mucore.pp_expr body))}
    end
  | _ ->
    fail {loc = Id.loc id;
        msg = Generic (Pp.string ("c_fun_to_it: not defined: " ^ Sym.pp_string fsym))}

let upd_def id def_tm logical_predicates =
  let open LogicalPredicates in
  let s = Id.s id in
  let@ (sym, def, rem) = match List.partition
    (fun (sym, _) -> String.equal s (Tools.todo_string_of_sym sym)) logical_predicates
  with
  | ([], _) -> fail {loc = Id.loc id;
        msg = Unknown_logical_predicate {id = Sym.fresh_named s; resource = false}}
  | ([(sym, def)], rem) -> return (sym, def, rem)
  | _ -> fail {loc = Id.loc id;
        msg = Generic (Pp.string ("logical predicate multiply defined: " ^ s))}
  in
  match def.definition with
  | Uninterp -> return ((sym, { def with definition = Def (Body.Term def_tm) }) :: rem)
  | _ -> fail {loc = Id.loc id;
        msg = Generic (Pp.string ("logical predicate already defined: " ^ s))}

let add_c_fun_defs logical_predicates log_c_defs =
  let pred_def_map = List.fold_left (fun m (sym, def) ->
    StringMap.add (Tools.todo_string_of_sym sym) def m) StringMap.empty
    logical_predicates in
  let@ conv_defs = ListM.mapM (fun (id, fsym, fn) ->
        let@ def = match StringMap.find_opt (Id.s id) pred_def_map with
          | Some def -> return def
          | None -> fail {loc = Id.loc id;
                msg = Unknown_logical_predicate {id = Sym.fresh_named (Id.s id); resource = false}}
        in
        let@ it = c_fun_to_it id fsym def fn in
        return (id, it)) log_c_defs in
  ListM.fold_leftM (fun lps (id, it) -> upd_def id it lps) logical_predicates conv_defs

