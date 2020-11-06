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



(*** mapping to Z3 ************************************************************)

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
  | Loc -> return (Z3.Arithmetic.Integer.mk_sort ctxt)
  (* | Loc -> return (Z3.Sort.mk_uninterpreted_s ctxt btname) *)
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
  | MemberOffset (tag, t, member) ->
     let* a = of_index_term loc {local;global} ctxt t in
     let* offset = Memory_aux.offset loc {local; global} tag member in
     let offset_s = Nat_big_num.to_string offset in
     let offset_n = Z3.Arithmetic.Integer.mk_numeral_s ctxt offset_s in
     return (Z3.Arithmetic.mk_add ctxt [a;offset_n])
  | Offset (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_add ctxt [a;a'])
  | Aligned (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     let t = 
       Z3.Boolean.mk_eq ctxt
         (Z3.Arithmetic.Integer.mk_mod ctxt a a')
         (Z3.Arithmetic.Integer.mk_numeral_s ctxt "0")
     in
     return t
  | LocLT (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_lt ctxt a a')
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
     fail loc (Unsupported !^"todo: Z3: Nil")
  | Cons _ ->
     fail loc (Unsupported !^"todo: Z3: Cons")
  | Tuple ts ->
     fail loc (Unsupported !^"todo: Z3: Tuple")
  | Head t ->
     fail loc (Unsupported !^"todo: Z3: Head")
  | Tail t ->
     fail loc (Unsupported !^"todo: Z3: Tail")
  | List (ts,bt) ->
     fail loc (Unsupported !^"todo: Z3: List")







(*** counter models ***********************************************************)


let rec matching_symbol syms num = 
  match syms with
  | sym :: syms when Sym.num sym = num -> Some sym
  | sym :: syms -> matching_symbol syms num
  | [] -> None


type constant_mapping = (Sym.t * string) list


(* maybe should fail if symbol mapping is missing? *)
let model loc {local;global} solver : (constant_mapping option) m =
  (* let unsat_core = 
   *   String.concat ", "
   *     (map Z3.Expr.to_string (Z3.Solver.get_unsat_core solver))
   * in *)
  match Z3.Solver.get_model solver with
  | None -> 
     return None
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
     return (Some consts)





(*** running Z3 **************************************************************)


let handle_z3_problems loc todo =
  if not (Z3.Log.open_ logfile) then 
    fail loc (Internal (!^("Z3 logfile: could not open " ^ logfile)))
  else 
    try let* result = todo () in Z3.Log.close (); return result with
    | Z3.Error (msg : string) -> 
       Z3.Log.close ();
       fail loc (Internal (!^"Z3 error:" ^/^ !^msg))


let debug_typecheck_lcs loc lcs {local;global} =
  if !Debug_ocaml.debug_level > 0 then return () else
    ListM.iterM (WellTyped.WLC.welltyped (loc: Loc.t) {local;global}) lcs



let footprints_disjoint (location1, size1) (location2, size2) = 
  let fp1_before_fp2 = IT.LocLT (Offset (location1, Num size1), location2) in
  let fp2_before_fp1 = IT.LocLT (Offset (location2, Num size2), location1) in
  IT.Or [fp1_before_fp2; fp2_before_fp1]

let rec disjoint_footprints = function
  | [] -> []
  | fp :: after -> 
     map (footprints_disjoint fp) after @ 
       disjoint_footprints after

  


let constraint_holds loc {local;global} do_model c = 
  let ctxt = 
    Z3.mk_context [
        ("model", if do_model then "true" else "false");
        ("well_sorted_check","true")
      ] 
  in
  let solver = Z3.Solver.mk_simple_solver ctxt in
  let disjointness_lc = 
    let footprints = 
      map (fun (_, r) -> (RE.pointer r, RE.size r)) (L.all_resources local) in
    map (fun lc -> LC.LC lc) (disjoint_footprints footprints)
  in
  let lcs = 
    negate c :: (disjointness_lc @ Local.all_constraints local)
  in
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
    constraint_holds loc {local;global} false (LC (Bool false)) in
  return (not unreachable)



let equal loc {local;global} it1 it2 =
  let c = LC.LC (IndexTerms.EQ (it1, it2)) in
  let* (holds,_,_) = constraint_holds loc {local;global} false c in
  return holds



let is_reachable_and_model loc {local;global} =
  let* (unreachable,_, solver) = 
    constraint_holds loc {local;global} true (LC (Bool false)) in
  let* model = 
    handle_z3_problems loc
      (fun () -> model loc {local;global} solver) 
  in
  return (not unreachable, model)
