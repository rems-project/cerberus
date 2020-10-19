open Global
open Resultat
open List
open Pp
open TypeErrors
open Environment
module IT=IndexTerms
module LC=LogicalConstraints
module TE=TypeErrors

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
    | None -> fail loc (unreachable !^"nth_to_fundecl")
  in
  let member_to_fundecl tag member = 
    let* decl = Global.get_struct_decl loc global.struct_decls tag in
    let* sort = ls_to_sort loc {local;global} ctxt (Base (Struct tag)) in
    let member_fun_decls = Z3.Tuple.get_field_decls sort in
    let member_names = map fst decl.raw in
    let member_funs = combine member_names member_fun_decls in
    Tools.assoc_err loc member member_funs (unreachable !^"member_to_fundecl")
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
    fail loc (TypeErrors.z3_fail (!^("could not open " ^ logfile)))
  else 
    try let* result = todo () in Z3.Log.close (); return result with
    | Z3.Error (msg : string) -> 
       Z3.Log.close ();
       fail loc (TypeErrors.z3_fail !^msg)


let debug_typecheck_lcs loc lcs {local;global} =
  if !Debug_ocaml.debug_level < 1 then return () else
    ListM.iterM (fun (LC.LC lc) -> 
        let* _ = IndexTermTyping.check_index_term (loc: Loc.t) {local;global} 
                   (LS.Base BT.Bool) lc in
        return ()
      ) lcs

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
  | sym :: syms when Sym.symbol_num sym = num -> Some sym
  | sym :: syms -> matching_symbol syms num
  | [] -> None



(* maybe should fail if symbol mapping is missing? *)
let model loc {local;global} solver : (TE.model option) m = 
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
           let n = Z3.Symbol.get_int (Z3.FuncDecl.get_name decl) in
           let ov = Z3.Model.get_const_interp model decl in
           match matching_symbol syms n, ov with
           | Some sym, Some v -> 
              return (Some (sym, Z3.Expr.to_string v))
           | None, _ -> 
              let err = 
                "reconstructing counter model: " ^
                  "missing symbol for " ^ string_of_int n
              in
              fail loc (Unreachable !^err)
           | Some s, None ->
              let err = 
                "reconstructing counter model: " ^
                  "missing value for " ^ Sym.pp_string s
              in
              fail loc (Unreachable !^err)

         ) z3_model
     in
     return (Some consts)

let is_reachable_and_model loc {local;global} =
  let* (unreachable,_, solver) = 
    constraint_holds loc {local;global} (LC (Bool false)) in
  let* model = model loc {local;global} solver in
  return (not unreachable, model)


let equal loc {local;global} it1 it2 =
  let c = LC.LC (IT.EQ (it1, it2)) in
  let* (holds,_,_) = constraint_holds loc {local;global} c in
  return holds
