open Environment
open List
open Pp
open TypeErrors
open Except


(* copying bits and pieces from https://github.com/rems-project/asl-interpreter/blob/a896dd196996e2265eed35e8a1d71677314ee92c/libASL/tcheck.ml and https://github.com/Z3Prover/z3/blob/master/examples/ml/ml_example.ml *)

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
let rec bt_to_sort loc env ctxt bt = 
  let open BaseTypes in
  let btname = bt_name bt in
  match bt with
  | Unit -> return (Z3.Sort.mk_uninterpreted_s ctxt btname)
  | Bool -> return (Z3.Boolean.mk_sort ctxt)
  | Int -> return (Z3.Arithmetic.Integer.mk_sort ctxt)
  | Loc -> return (Z3.Sort.mk_uninterpreted_s ctxt btname)
  | Tuple bts ->
     let names = mapi (fun i _ -> Z3.Symbol.mk_string ctxt (tuple_component_name bt i)) bts in
     let* sorts = mapM (bt_to_sort loc env ctxt) bts in
     return (Z3.Tuple.mk_sort ctxt (Z3.Symbol.mk_string ctxt btname) names sorts)
  | Struct tag ->
     let* decl = Environment.Global.get_struct_decl loc env.Env.global tag in
     let rec aux = function
       | (member,bt) :: members ->
          let* (names,sorts) = aux members in
          let* sort = bt_to_sort loc env ctxt bt in
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

let ls_to_sort loc env ctxt ls = 
  match ls with
  | LogicalSorts.Base bt -> bt_to_sort loc env ctxt bt


let rec of_index_term loc env ctxt it = 
  let open Pp in
  let open IndexTerms in

  let member_to_fundecl tag member = 
    let* decl = Environment.Global.get_struct_decl loc env.Env.global tag in
    let* sort = ls_to_sort loc env ctxt (Base (Struct tag)) in
    let member_fun_decls = Z3.Tuple.get_field_decls sort in
    let member_names = map fst decl.raw in
    let member_funs = combine member_names member_fun_decls in
    Tools.assoc_err loc member member_funs "member_to_fundecl"
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
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_add ctxt [a;a'])
  | Sub (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_sub ctxt [a;a'])
  | Mul (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_mul ctxt [a; a'])
  | Div (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_div ctxt a a')
  | Exp (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_power ctxt a a')
  | Rem_t (it,it') -> 
     let* () = warn !^"Rem_t constraint" in
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.Integer.mk_rem ctxt a a')
  | Rem_f (it,it') -> 
     let* () = warn !^"Rem_f constraint" in
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.Integer.mk_rem ctxt a a')
  | EQ (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Boolean.mk_eq ctxt a a')
  | NE (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Boolean.mk_distinct ctxt [a; a'])
  | LT (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_lt ctxt a a')
  | GT (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_gt ctxt a a') 
  | LE (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_le ctxt a a')
  | GE (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Arithmetic.mk_ge ctxt a a')
  | Null t -> 
     let* locsort = ls_to_sort loc env ctxt (Base Loc) in
     let* boolsort = ls_to_sort loc env ctxt (Base Bool) in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt "null" [locsort] boolsort in
     let* a = of_index_term loc env ctxt t in
     return (Z3.Expr.mk_app ctxt fundecl [a])
  | And (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Boolean.mk_and ctxt [a; a'])
  | Or (it,it') -> 
     let* a = of_index_term loc env ctxt it in
     let* a' = of_index_term loc env ctxt it' in
     return (Z3.Boolean.mk_or ctxt [a; a'])
  | Not it -> 
     let* a = of_index_term loc env ctxt it in
     return (Z3.Boolean.mk_not ctxt a)
  | S s -> 
     let* bt = Env.get_ALvar loc env s in
     let s = sym_to_symbol ctxt s in
     let* bt = ls_to_sort loc env ctxt (Base bt) in
     return (Z3.Expr.mk_const ctxt s bt)
  | Member (tag, t, member) ->
     let* a = of_index_term loc env ctxt t in
     let* fundecl = member_to_fundecl tag member in
     return (Z3.Expr.mk_app ctxt fundecl [a])
  | MemberOffset (_tag, t, Member member) ->
     let* locsort = ls_to_sort loc env ctxt (Base Loc) in
     let membersort = member_sort ctxt in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt 
                     "memberOffset" [locsort;membersort] locsort in
     let* loc_const = of_index_term loc env ctxt t in
     let member_const = Z3.Expr.mk_const_s ctxt member membersort in
     return (Z3.Expr.mk_app ctxt fundecl [loc_const;member_const])
  | Nil _ ->
     fail loc (Z3_IT_not_implemented_yet it)
  | Cons _ ->
     fail loc (Z3_IT_not_implemented_yet it)
  | Tuple ts ->
     fail loc (Z3_IT_not_implemented_yet it)
  | Head t ->
     fail loc (Z3_IT_not_implemented_yet it)
  | Tail t ->
     fail loc (Z3_IT_not_implemented_yet it)
  | Nth (i,t) ->
     fail loc (Z3_IT_not_implemented_yet it)
  | List (ts,bt) ->
     fail loc (Z3_IT_not_implemented_yet it)



let z3_check loc ctxt solver constrs : Z3.Solver.status m = 
  begin 
    let logfile = "/tmp/z3.log" in
    if not (Z3.Log.open_ logfile) 
    then fail loc (TypeErrors.Z3_fail "could not open /tmp/z3.log")
    else 
      try 
        Z3.Solver.add solver constrs;
        let result = Z3.Solver.check solver [] in
        Z3.Log.close ();
        return result
      with Z3.Error (msg : string) -> 
        Z3.Log.close ();
        fail loc (TypeErrors.Z3_fail msg)
  end


let negate (LogicalConstraints.LC c) = 
  (LogicalConstraints.LC (Not c))

let constraint_holds_given_constraints loc env constraints c = 
  let open PPrint in
  let ctxt = Z3.mk_context [("model","true");("well_sorted_check","true")] in
  let solver = Z3.Solver.mk_simple_solver ctxt in
  let lcs = (negate c :: constraints) in
  let* constrs = 
    mapM (fun (LogicalConstraints.LC it) -> 
        match of_index_term loc env ctxt it with
        (* | Exception (_, Z3_LS_not_implemented_yet _)
         * | Exception (_, Z3_IT_not_implemented_yet _) ->
         *    of_index_term loc env ctxt (Bool true) *)
        | Exception (loc,e) ->
           fail loc e
        | r ->r
      ) lcs 
  in
  let* () = debug_print 4 (action "checking satisfiability of constraints") in
  let* () = debug_print 4 (blank 3 ^^ item "constraints" (flow_map (break 1) (LogicalConstraints.pp true) lcs)) in
  let* checked = z3_check loc ctxt solver constrs in
  match checked with
  | UNSATISFIABLE -> 
     let* () = debug_print 2 (blank 3 ^^ !^"unsatisfiable") in
     return (true,ctxt,solver)
  | SATISFIABLE -> 
     let* () = debug_print 2 (blank 3 ^^ !^"satisfiable") in
     return (false,ctxt,solver)
  | UNKNOWN ->
     let* () = warn !^"constraint solver returned unknown" in
     return (false,ctxt,solver)


let constraint_holds loc env c = 
  constraint_holds_given_constraints loc env (Env.get_all_constraints env) c 




let is_unreachable loc env =
  constraint_holds loc env (LC (Bool false))


(* let rec check_constraints_hold loc env constr = 
 *   let open PPrint in
 *   let open Env in
 *   match constr with
 *   | [] -> return ()
 *   | c :: constrs ->
 *      let* () = debug_print 2 (action "checking constraint") in
 *      let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) in
 *      let* () = debug_print 2 (blank 3 ^^ item "constraint" (LogicalConstraints.pp false c)) in
 *      let* (holds,ctxt,solver) = constraint_holds loc env c in
 *      if holds then
 *        let* () = debug_print 2 (blank 3 ^^ !^(greenb "constraint holds")) in
 *        check_constraints_hold loc env constrs
 *      else
 *        let* () = debug_print 2 (blank 3 ^^ !^(redb "constraint does not hold")) in
 *        let* () = match Z3.Solver.get_model solver with
 *          | Some model -> 
 *             debug_print 2 (blank 3 ^^ item "model" (!^(Z3.Model.to_string model)))
 *          | None -> return ()
 *        in
 *        fail loc (Call_error (Unsat_constraint c)) *)
