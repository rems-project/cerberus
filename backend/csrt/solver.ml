open Global
open Resultat
open List
open Pp
open TypeErrors
open LogicalConstraints
open Environment
module L = Local

(* copying bits and pieces from https://github.com/rems-project/asl-interpreter/blob/a896dd196996e2265eed35e8a1d71677314ee92c/libASL/tcheck.ml and https://github.com/Z3Prover/z3/blob/master/examples/ml/ml_example.ml *)



let logfile = "/tmp/z3.log"

let rem_t_warned = ref false
let rem_f_warned = ref false


let sym_to_symbol ctxt sym =
  let open Cerb_frontend.Symbol in
  let (Symbol (_digest, num, _mstring)) = sym in
  Z3.Symbol.mk_int ctxt num

let bt_name bt = 
  plain (BT.pp false bt)

let tuple_component_name bt i =
  bt_name bt ^ "__" ^ string_of_int i

let struct_member_name bt (BT.Member id) =
  bt_name bt ^ "__" ^ id

let member_sort ctxt = 
  Z3.Sort.mk_uninterpreted_s ctxt "member"

(* maybe fix Loc *)
let rec bt_to_sort loc {local;global} ctxt bt = 
  let open BaseTypes in
  let btname = bt_name bt in
  match bt with
  | Unit -> return (Z3.Sort.mk_uninterpreted_s ctxt btname)
  | Bool -> return (Z3.Boolean.mk_sort ctxt)
  | Integer -> return (Z3.Arithmetic.Integer.mk_sort ctxt)
  | Loc -> return (Z3.Sort.mk_uninterpreted_s ctxt btname)
  | Tuple bts ->
     let names = mapi (fun i _ -> Z3.Symbol.mk_string ctxt (tuple_component_name bt i)) bts in
     let* sorts = ListM.mapM (bt_to_sort loc {local;global} ctxt) bts in
     return (Z3.Tuple.mk_sort ctxt (Z3.Symbol.mk_string ctxt btname) names sorts)
  | Struct tag ->
     let* decl = Global.get_struct_decl loc global.struct_decls tag in
     let rec aux = function
       | (member,bt) :: members ->
          let* (names,sorts) = aux members in
          let* sort = bt_to_sort loc {local;global} ctxt bt in
          let names = Z3.Symbol.mk_string ctxt (struct_member_name bt member) :: names in
          let sorts = sort :: sorts in
          return (names,sorts)
       | [] -> return ([],[])
     in
     let* (names,sorts) = aux decl.raw in
     let name = Z3.Symbol.mk_string ctxt btname in
     let sort = Z3.Tuple.mk_sort ctxt name names sorts in
     return sort
  | Array ->
     return (Z3.Sort.mk_uninterpreted_s ctxt btname)
  | List _ ->
     return (Z3.Sort.mk_uninterpreted_s ctxt btname)
  | FunctionPointer _ -> 
     return (Z3.Sort.mk_uninterpreted_s ctxt btname)

let ls_to_sort loc {local;global} ctxt (LS.Base bt) =
  bt_to_sort loc {local;global} ctxt bt


let rec of_index_term loc {local;global} ctxt it = 
  let open Pp in
  let open IndexTerms in
  let nth_to_fundecl bt i = 
    let* sort = ls_to_sort loc {local;global} ctxt (Base bt) in
    let member_fun_decls = Z3.Tuple.get_field_decls sort in
    match List.nth_opt member_fun_decls i with
    | Some fundecl -> return fundecl
    | None -> fail loc (Internal !^"nth_to_fundecl")
  in
  let member_to_fundecl tag member = 
    let* decl = Global.get_struct_decl loc global.struct_decls tag in
    let* sort = ls_to_sort loc {local;global} ctxt (Base (Struct tag)) in
    let member_fun_decls = Z3.Tuple.get_field_decls sort in
    let member_names = map fst decl.raw in
    let member_funs = combine member_names member_fun_decls in
    Tools.assoc_err loc member member_funs (Internal !^"member_to_fundecl")
  in
  match it with
  | Num n -> 
     let nstr = Nat_big_num.to_string n in
     return (Z3.Arithmetic.Integer.mk_numeral_s ctxt nstr)
  | Bool true -> 
     return (Z3.Boolean.mk_true ctxt)
  | Bool false -> 
     return (Z3.Boolean.mk_false ctxt)
  | Add (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_add ctxt [a;a'])
  | Sub (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_sub ctxt [a;a'])
  | Mul (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_mul ctxt [a; a'])
  | Div (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_div ctxt a a')
  | Exp (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_power ctxt a a')
  | Rem_t (it,it') -> 
     if not !rem_t_warned then
       (rem_t_warned := true; Pp.warn !^"Rem_t constraint");
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.Integer.mk_rem ctxt a a')
  | Rem_f (it,it') -> 
     if not !rem_f_warned then
       (rem_f_warned := true; Pp.warn !^"Rem_f constraint");
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.Integer.mk_rem ctxt a a')
  | Min (it,it') -> 
     let it_elab = ITE (it %< it', it, it') in
     of_index_term loc {local;global} ctxt it_elab 
  | Max (it,it') -> 
     let it_elab = ITE (it %> it', it, it') in
     of_index_term loc {local;global} ctxt it_elab 
  | EQ (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Boolean.mk_eq ctxt a a')
  | NE (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Boolean.mk_distinct ctxt [a; a'])
  | LT (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_lt ctxt a a')
  | GT (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_gt ctxt a a') 
  | LE (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_le ctxt a a')
  | GE (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_ge ctxt a a')
  | Null t -> 
     let* locsort = ls_to_sort loc {local;global} ctxt (Base Loc) in
     let* boolsort = ls_to_sort loc {local;global} ctxt (Base Bool) in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt "null" [locsort] boolsort in
     let* a = of_index_term loc {local;global} ctxt t in
     return (Z3.Expr.mk_app ctxt fundecl [a])
  | And its -> 
     let* ts = ListM.mapM (of_index_term loc {local;global} ctxt) its in
     return (Z3.Boolean.mk_and ctxt ts)
  | Or its -> 
     let* ts = ListM.mapM (of_index_term loc {local;global} ctxt) its in
     return (Z3.Boolean.mk_or ctxt ts)
  | Impl (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Boolean.mk_implies ctxt a a')
  | Not it -> 
     let* a = of_index_term loc {local;global} ctxt it in
     return (Z3.Boolean.mk_not ctxt a)
  | ITE (it,it',it'') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     let* a'' = of_index_term loc {local;global} ctxt it'' in
     return (Z3.Boolean.mk_ite ctxt a a' a'')
  | S s -> 
     let* ls = Local.get_l loc s local in
     let sym = sym_to_symbol ctxt s in
     let* sort = ls_to_sort loc {local;global} ctxt ls in
     return (Z3.Expr.mk_const ctxt sym sort)
  | Member (tag, t, member) ->
     let* a = of_index_term loc {local;global} ctxt t in
     let* fundecl = member_to_fundecl tag member in
     return (Z3.Expr.mk_app ctxt fundecl [a])
  | MemberOffset (_tag, t, Member member) ->
     let* locsort = ls_to_sort loc {local;global} ctxt (Base Loc) in
     let membersort = member_sort ctxt in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt 
                     "memberOffset" [locsort;membersort] locsort in
     let* loc_const = of_index_term loc {local;global} ctxt t in
     let member_const = Z3.Expr.mk_const_s ctxt member membersort in
     return (Z3.Expr.mk_app ctxt fundecl [loc_const;member_const])
  | Struct (tag,members) ->
     let* sort = bt_to_sort loc {local;global} ctxt (Struct tag) in
     let constructor = Z3.Tuple.get_mk_decl sort in
     let* member_vals = 
       ListM.mapM (fun (_member,it) ->
           of_index_term loc {local;global} ctxt it
         ) members
     in
     return (Z3.Expr.mk_app ctxt constructor member_vals)
  | Nth (bt,i,t) ->
     let* a = of_index_term loc {local;global} ctxt t in
     let* fundecl = nth_to_fundecl bt i in
     return (Z3.Expr.mk_app ctxt fundecl [a])
  | Nil _ ->
     fail loc (Unsupported !^"Z3: Nil")
  | Cons _ ->
     fail loc (Unsupported !^"Z3: Cons")
  | Tuple ts ->
     fail loc (Unsupported !^"Z3: Tuple")
  | Head t ->
     fail loc (Unsupported !^"Z3: Head")
  | Tail t ->
     fail loc (Unsupported !^"Z3: Tail")
  | List (ts,bt) ->
     fail loc (Unsupported !^"Z3: List")



let negate (LogicalConstraints.LC c) = LogicalConstraints.LC (Not c)

let handle_z3_problems loc todo =
  if not (Z3.Log.open_ logfile) then 
    fail loc (Internal (!^("Z3 logfile: could not open " ^ logfile)))
  else 
    try let* result = todo () in Z3.Log.close (); return result with
    | Z3.Error (msg : string) -> 
       Z3.Log.close ();
       fail loc (Internal (!^"Z3 error:" ^^^ !^msg))


let debug_typecheck_lcs loc lcs {local;global} =
  if !Debug_ocaml.debug_level > 0 then return () else
    ListM.iterM (WellTyped.WLC.welltyped (loc: Loc.t) {local;global}) lcs

let constraint_holds loc {local;global} c = 
  let ctxt = Z3.mk_context [("model","true");("well_sorted_check","true")] in
  let solver = Z3.Solver.mk_simple_solver ctxt in
  let lcs = (negate c :: Local.all_constraints local) in
  let* () = debug_typecheck_lcs loc lcs {local;global} in
  let* checked = 
    handle_z3_problems loc 
      (fun () ->
        let* constrs = 
          ListM.mapM (fun (LC.LC it) -> 
              of_index_term loc {local;global} ctxt it
            ) lcs 
        in
        Z3.Solver.add solver constrs;
        return (Z3.Solver.check solver [])
      )
  in
  (* let () = Pp.p !^(Z3.Solver.to_string solver) in *)
  match checked with
  | UNSATISFIABLE -> return (true,ctxt,solver)
  | SATISFIABLE -> return (false,ctxt,solver)
  | UNKNOWN -> return (false,ctxt,solver)


let is_reachable loc {local;global} =
  let* (unreachable,_,_) = 
    constraint_holds loc {local;global} (LC (Bool false)) in
  return (not unreachable)


let rec matching_symbol syms num = 
  match syms with
  | sym :: syms when Sym.num sym = num -> Some sym
  | sym :: syms -> matching_symbol syms num
  | [] -> None




let equal loc {local;global} it1 it2 =
  let c = LC.LC (IndexTerms.EQ (it1, it2)) in
  let* (holds,_,_) = constraint_holds loc {local;global} c in
  return holds














let pp_model_v1 loc {local; global} consts = 

  let original_resources = map snd (L.all_resources local) in

  let lvars = 
    List.fold_left SymSet.union SymSet.empty 
      (List.map RE.vars_in original_resources)
  in
  (* try to find a known name to map the logical variables to: if the
     logical variable is named, then use that; otherwise, see if it is
     linked to a computational variable with a name *)
  let substs = 
    List.filter_map (fun l -> 
        if Sym.named l then None else 
          match L.cvar_for_lvar local l with
          | Some subst when Sym.named subst.after -> Some subst
          | _ -> None
      )
      (SymSet.elements lvars)
  in
  let tweaked_resources = List.map (RE.subst_vars substs) original_resources in

  let* lvar_info = 
    ListM.mapM (fun s ->
        let* ls = L.get_l loc s local in
        let ov = List.assoc_opt s consts in
        let name = Sym.substs substs s in
        return (name, ls, ov)
      ) (SymSet.elements lvars)
  in

  let pped_memory = 
    List.map (function 
        | RE.Uninit u -> 
           IT.pp ~quote:false u.RE.pointer ^^^ 
             !^"uninitialised" ^^^
               Pp.c_comment (!^"size" ^^^ Z.pp u.size)
             
        | RE.Points p -> 
           IT.pp ~quote:false p.RE.pointer ^^^ 
             equals ^^^ Sym.pp p.pointee ^^^
               Pp.c_comment (!^"size" ^^^ Z.pp p.size)
      ) 
      tweaked_resources  
  in

  let pped_lvars = 
    List.map (fun (name,ls,ov) ->
        match ov with
        | None -> typ (Sym.pp name) (LogicalSorts.pp false ls)
        | Some v ->
           typ (Sym.pp name) (LogicalSorts.pp false ls) ^^^
             !^":=" ^^^ !^v
      ) lvar_info
  in

  let pp = flow (comma ^^ break 1) (pped_lvars @ pped_memory) in

  return pp








  

let for_pointer (loc: Loc.t) {local;global} pointer_it
    : ((Sym.t * RE.t) option) m = 
  let* points = 
    Local.filterM (fun name vb ->
        match vb with 
        | VariableBinding.Resource re -> 
           let* holds = equal loc {local;global} pointer_it (RE.pointer re) in
           return (if holds then Some (name, re) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" points


let equal_lvars loc {local;global} lname =
  L.filterM (fun name b ->
      match b with
      | VariableBinding.Logical ls -> 
         let* equal = equal loc {local; global} (S lname) (S name) in
         return (if equal then Some (name, ls) else None)
      | _ -> 
         return None
    ) local




type lvar_equivalence_classes = (Sym.t * LS.t * SymSet.t) list

let lvar_equivalence_classes loc {local; global} lvars : lvar_equivalence_classes m = 
  ListM.fold_leftM (fun classes (l, ls) ->
      let rec aux = function
        | (representative, ls', clss) :: classes ->
           if LS.equal ls ls' then
             let* equal = equal loc {local; global} (S l) (S representative) in
             if equal then
               let clss' = SymSet.add l clss in
               let representative' = 
                 if Sym.named representative 
                 then representative else l
               in
               return ((representative', ls', clss') :: classes)
             else 
               let* classes' = aux classes in
               return ((representative, ls', clss) :: classes')
           else
             let* classes' = aux classes in
             return ((representative, ls', clss) :: classes')
        | [] -> 
           return [(l, ls, SymSet.singleton l)]
      in
      aux classes
    ) [] lvars


let find_good_name_subst loc lvar_eq_classes l =
  let rec aux = function
    | (representative, _ls, clss) :: _ when SymSet.mem l clss ->
       return representative
    | _ :: rest -> aux rest
    | [] -> fail loc (Internal (!^"error finding equivalence class for" ^^^ Sym.pp l))
  in
  let* representative = aux lvar_eq_classes in
  return (Subst.{before = l; after = representative})


let dedup symlist = SymSet.elements (SymSet.of_list symlist)


let bigunion = List.fold_left SymSet.union SymSet.empty

let all_it_names_good it = 
  SymSet.for_all (fun s -> Sym.named s) (IT.vars_in it)

let pp_model loc {local; global} consts = 
  let cvars = L.all_computational local in
  let lvars = L.all_logical local in
  let resources = L.all_resources local in
  let* substs = 
    let* lvar_classes = lvar_equivalence_classes loc {local; global} lvars in
    let relevant_lvars = 
      let lvarses1 = List.map (fun (_,r) -> (RE.vars_in r)) resources in
      let lvarses2 = List.map (fun (_,(l,_)) -> SymSet.singleton l) cvars in
      bigunion (lvarses1 @ lvarses2)
    in
    ListM.mapM (find_good_name_subst loc lvar_classes)
      (SymSet.elements relevant_lvars) 
  in
  let resources = 
    List.map (fun (rname,r) -> (rname, RE.subst_vars substs r)) resources
  in
  let cvars = 
    List.map (fun (c,(l,bt)) -> (c, (Sym.substs substs l, bt))) cvars
  in
  let* cvars = 
    ListM.fold_rightM (fun (c,(l,bt)) vars ->
        if Sym.named c && bt = BT.Loc then
          let* o_re = for_pointer loc {local; global} (S l) in
          return ((c, (l, bt), o_re) :: vars)
        else return vars
      ) cvars []
  in
  let mentioned_resources = 
    List.fold_left (fun acc (c, _, o_r) ->
        match o_r with
        | None -> acc
        | Some (rname, _) ->
           let already_mentioned = Option.value [] (SymMap.find_opt rname acc) in
           SymMap.add rname (c :: already_mentioned) acc
      ) SymMap.empty cvars
  in

  let (pped_cvars, mentioned_lvars) = 
    List.fold_right (fun (s, (lname, bt), o_re) (acc_pp, acc_mentioned) ->
        begin match o_re with
        | Some (_, RE.Uninit u) -> 
           let pp = 
             Sym.pp s ^^^
               !^"at location" ^^^ IT.pp ~quote:false u.RE.pointer ^^^
                 !^"uninitialised" ^^^ Pp.c_comment (!^"of size" ^^^ Z.pp u.size)
           in
           let mentioned = 
             SymSet.union (IT.vars_in u.RE.pointer) 
               acc_mentioned 
           in
           (pp :: acc_pp, mentioned)
        | Some (_, RE.Points p) -> 
           let pp = 
             Sym.pp s ^^^
               !^"at location" ^^^ IT.pp ~quote:false p.RE.pointer ^^^
                 equals ^^^ Sym.pp p.pointee ^^^
                   Pp.c_comment (!^"size" ^^^ Z.pp p.size)
           in
           let mentioned = 
             SymSet.add p.pointee
               (SymSet.union (IT.vars_in p.RE.pointer) acc_mentioned)
           in
           (pp :: acc_pp, mentioned)
        | None ->
           let pp = 
             Sym.pp s ^^^
               !^"at location" ^^^ Sym.pp lname ^^^
                 parens (!^"no ownership of memory")
           in
           (pp :: acc_pp, acc_mentioned)
        end
      ) cvars ([], SymSet.empty)
  in

  let unmentioned_resources = 
    List.filter (fun (name,re) ->
        Option.is_none (SymMap.find_opt name mentioned_resources)
      ) 
      resources
  in

  let (pped_extra_memory, mentioned_lvars) = 
    List.fold_right (fun re (acc_pp, acc_mentioned) ->
        match re with
        | RE.Uninit u -> 
           let pp = 
             IT.pp ~quote:false u.RE.pointer ^^^ 
               !^"uninitialised" ^^^
                 Pp.c_comment (!^"size" ^^^ Z.pp u.size)
           in
           let mentioned = 
             SymSet.union (IT.vars_in u.RE.pointer) acc_mentioned 
           in
           (pp :: acc_pp, mentioned)
        | RE.Points p -> 
           let pp = 
             IT.pp ~quote:false p.RE.pointer ^^^ 
               equals ^^^ Sym.pp p.pointee ^^^
                 Pp.c_comment (!^"size" ^^^ Z.pp p.size)
           in
           let mentioned = 
             SymSet.add p.pointee
               (SymSet.union (IT.vars_in p.RE.pointer) acc_mentioned)
           in
           (pp :: acc_pp, mentioned)
      ) 
      (map snd unmentioned_resources) ([], mentioned_lvars)
  in



  let aliases = 
    List.filter_map (fun (_,vars) -> 
        if List.length vars > 1 then Some vars else None
      ) (SymMap.bindings mentioned_resources)
  in

  let* lvar_info = 
    ListM.mapM (fun s ->
        let* ls = L.get_l loc s local in
        let ov = List.assoc_opt s consts in
        return (s, ls, ov)
      ) (SymSet.elements mentioned_lvars)
  in

  let pped_lvars = 
    List.map (fun (name,ls,ov) ->
        match ov with
        | None -> typ (Sym.pp name) (LogicalSorts.pp false ls)
        | Some v ->
           typ (Sym.pp name) (LogicalSorts.pp false ls) ^^^
             !^":=" ^^^ !^v
      ) lvar_info
  in

  let pped_aliases = match aliases with
    | []-> Pp.empty
    | _ ->
       flow_map (comma ^^ break 1) (fun l ->
             pp_list Sym.pp l ^^^ !^"alias"
         ) aliases
  in
  let pp = 
    flow (comma ^^ hardline) 
      (pped_cvars @ pped_extra_memory @ pped_lvars) ^^^
      pped_aliases
  in

  return pp




(* maybe should fail if symbol mapping is missing? *)
let model loc {local;global} solver =
  (* let unsat_core = 
   *   String.concat ", "
   *     (map Z3.Expr.to_string (Z3.Solver.get_unsat_core solver))
   * in *)
  match Z3.Solver.get_model solver with
  | None -> return None
  | Some model ->
     let syms = Local.all_names local in
     let z3_model = Z3.Model.get_const_decls model in
     let* consts =
       ListM.filter_mapM (fun decl -> 
           (* this ignores constants that can't be mapped back to
              symbols *)
           let name = Z3.FuncDecl.get_name decl in
           if not (Z3.Symbol.is_int_symbol name) then return None else 
             let osym = matching_symbol syms (Z3.Symbol.get_int name) in
             match osym with
             | None -> return None
             | Some sym -> 
                let ov = Z3.Model.get_const_interp model decl in
                match ov with
                | Some v -> return (Some (sym, Z3.Expr.to_string v))
                | None ->
                   let err = 
                     "reconstructing counter model: " ^
                       "missing value for " ^ Sym.pp_string sym
                   in
                   fail loc (Internal !^err)
         ) z3_model
     in
     let* pped = pp_model loc {local; global} consts in
     return (Some pped)

let is_reachable_and_model loc {local;global} =
  let* (unreachable,_, solver) = 
    constraint_holds loc {local;global} (LC (Bool false)) in
  let* model = 
    handle_z3_problems loc
      (fun () -> model loc {local;global} solver) 
  in
  return (not unreachable, model)
