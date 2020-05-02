open BaseTypes
open Cerb_frontend
open IndexTerms
open LogicalConstraints
open Environment
open Env
open PPrint
open Pp_tools
open TypeErrors
open Except

(* copying bits and pieces from https://github.com/rems-project/asl-interpreter/blob/a896dd196996e2265eed35e8a1d71677314ee92c/libASL/tcheck.ml and https://github.com/Z3Prover/z3/blob/master/examples/ml/ml_example.ml *)





let sym_to_symbol ctxt (Symbol.Symbol (_digest, num, _mstring)) =
  Z3.Symbol.mk_int ctxt num

let bt_to_sort loc ctxt bt = 
  match bt with
  | Unit -> return (Z3.Sort.mk_uninterpreted_s ctxt "unit")
  | Bool -> return (Z3.Boolean.mk_sort ctxt)
  | Int -> return (Z3.Arithmetic.Integer.mk_sort ctxt)
  | Loc -> 
     warn !^"Loc base type" >>= fun () ->
     return (Z3.Arithmetic.Integer.mk_sort ctxt)
  | Array
  | List _
  | Tuple _
  | Struct _
  | StructField _ -> 
     fail loc (Z3_BT_not_implemented_yet bt)


let rec of_index_term loc ctxt it = 
  match it with
  | Num n -> 
     let nstr = Nat_big_num.to_string n in
     return (Z3.Arithmetic.Integer.mk_numeral_s ctxt nstr)
  | Bool true -> 
     return (Z3.Boolean.mk_true ctxt)
  | Bool false -> 
     return (Z3.Boolean.mk_false ctxt)
  | Add (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_add ctxt [a;a'])
  | Sub (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_sub ctxt [a;a'])
  | Mul (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_mul ctxt [a; a'])
  | Div (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_div ctxt a a')
  | Exp (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_power ctxt a a')
  | Rem_t (it,it') -> 
     warn !^"Rem_t constraint" >>= fun () -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.Integer.mk_rem ctxt a a')
  | Rem_f (it,it') -> 
     warn !^"Rem_f constraint" >>= fun () ->
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.Integer.mk_rem ctxt a a')
  | EQ (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Boolean.mk_eq ctxt a a')
  | NE (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Boolean.mk_distinct ctxt [a; a'])
  | LT (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_lt ctxt a a')
  | GT (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_gt ctxt a a') 
  | LE (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_le ctxt a a')
  | GE (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Arithmetic.mk_ge ctxt a a')
  (* | Null t ->  *)
  | And (it,it') -> 
     of_index_term loc ctxt it >>= fun a ->
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Boolean.mk_and ctxt [a; a'])
  | Or (it,it') -> 
     of_index_term loc ctxt it >>= fun a -> 
     of_index_term loc ctxt it' >>= fun a' ->
     return (Z3.Boolean.mk_or ctxt [a; a'])
  | Not it -> 
     of_index_term loc ctxt it >>= fun a ->
     return (Z3.Boolean.mk_not ctxt a)
  (* | Tuple of t * t list
   * | Nth of num * t (\* of tuple *\)
   * 
   * | List of t * t list
   * | Head of t
   * | Tail of t *)
  | S (s,bt) -> 
     let s = sym_to_symbol ctxt s in
     bt_to_sort loc ctxt bt >>= fun bt ->
     return (Z3.Expr.mk_const ctxt s bt)
  | _ -> 
     fail loc (Z3_IT_not_implemented_yet it)


let z3_check loc ctxt solver constrs : (Z3.Solver.status, (Loc.t * TypeErrors.t)) m = 
  begin 
    try return (Z3.Solver.check solver constrs) 
    with Z3.Error (msg : string) -> fail loc (TypeErrors.Z3_fail msg)
  end


let negate (LC c) = (LC (Not c))

let constraint_holds loc env c = 
  debug_print 1 (action "checking constraint") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp_filtered (false,false,false,true) env.local)) >>= fun () ->
  debug_print 1 (blank 3 ^^ item "constraint" (LogicalConstraints.pp c)) >>= fun () ->
  let ctxt = Z3.mk_context [] in
  let solver = Z3.Solver.mk_simple_solver ctxt in
  let lcs = (negate c :: (Env.get_all_constraints env)) in
  mapM (fun (LC it) -> of_index_term loc ctxt it) lcs >>= fun constrs ->
  debug_print 21 (action "checking satisfiability of constraints") >>= fun () ->
  debug_print 2 (blank 3 ^^ item "constraints" (flow_map (break 1) LogicalConstraints.pp lcs)) >>= fun () ->
  z3_check loc ctxt solver [] >>= function
  (* the conjunction of existing constraints and 'not c' is unsatisfiable *)
  | UNSATISFIABLE -> 
     debug_print 1 (blank 3 ^^ !^(greenb "(satisfied)")) >>= fun () ->
     debug_print 1 PPrint.empty >>= fun () ->
     return true
  (* the conjunction of existing constraints and 'not c' is satisfiable *)
  | SATISFIABLE ->
     debug_print 1 (blank 3 ^^ !^(redb "(unsatisfied)")) >>= fun () ->
     debug_print 1 PPrint.empty >>= fun () ->
     return false
  | UNKNOWN ->
     debug_print 1 (blank 3 ^^ !^(redb "(unknown)")) >>= fun () ->
     debug_print 1 PPrint.empty >>= fun () ->
     return false
