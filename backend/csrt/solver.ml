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

let struct_member_name bt member =
  bt_name bt ^ "__" ^ Pp.plain (Id.pp member)

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
    assoc_err loc Id.equal member member_funs (Internal !^"member_to_fundecl")
  in
  match it with
  | Num n -> 
     let nstr = Nat_big_num.to_string n in
     return (Z3.Arithmetic.Integer.mk_numeral_s ctxt nstr)
  | Pointer n -> 
     let nstr = Nat_big_num.to_string n in
     return (Z3.Arithmetic.Integer.mk_numeral_s ctxt nstr)
  | Bool true -> 
     return (Z3.Boolean.mk_true ctxt)
  | Bool false -> 
     return (Z3.Boolean.mk_false ctxt)
  | Unit ->
     let* unitsort = ls_to_sort loc {local;global} ctxt (Base Unit) in
     return (Z3.Expr.mk_const_s ctxt "unit" unitsort)
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
     let* offset = Memory.member_offset loc tag member in
     let offset_s = Nat_big_num.to_string offset in
     let offset_n = Z3.Arithmetic.Integer.mk_numeral_s ctxt offset_s in
     return (Z3.Arithmetic.mk_add ctxt [a;offset_n])
  | AllocationSize t ->
     let* locsort = ls_to_sort loc {local;global} ctxt (Base Loc) in
     let* intsort = ls_to_sort loc {local;global} ctxt (Base Integer) in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt "allocationSize" [locsort] intsort in
     let* a = of_index_term loc {local;global} ctxt t in
     return (Z3.Expr.mk_app ctxt fundecl [a])
  | Offset (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_add ctxt [a;a'])
  | LocLT (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_lt ctxt a a')
  | LocLE (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     return (Z3.Arithmetic.mk_le ctxt a a')
  | Disjoint ((it,s),(it',s')) ->
     let fp1_before_fp2 = IT.LocLT (Offset (Offset (it, Num s), IT.int (-1)), it') in
     let fp2_before_fp1 = IT.LocLT (Offset (Offset (it', Num s'), IT.int (-1)), it) in
     let t = Or [fp1_before_fp2; fp2_before_fp1] in
     of_index_term loc {local; global} ctxt t
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
  | Aligned (st,it') -> 
     let* align = Memory.align_of_stored_type loc st in
     let* a = of_index_term loc {local;global} ctxt (Num align) in
     let* a' = of_index_term loc {local;global} ctxt it' in
     let t = 
       Z3.Boolean.mk_eq ctxt
         (Z3.Arithmetic.Integer.mk_mod ctxt a' a)
         (Z3.Arithmetic.Integer.mk_numeral_s ctxt "0")
     in
     return t
  | AlignedI (it,it') -> 
     let* a = of_index_term loc {local;global} ctxt it in
     let* a' = of_index_term loc {local;global} ctxt it' in
     let t = 
       Z3.Boolean.mk_eq ctxt
         (Z3.Arithmetic.Integer.mk_mod ctxt a' a)
         (Z3.Arithmetic.Integer.mk_numeral_s ctxt "0")
     in
     return t
  | Representable (st, t) ->
     let* rangef = Memory.representable_stored_type loc st in
     let (LC it) = rangef t in
     of_index_term loc {local; global} ctxt it
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





  


let constraint_holds loc {local;global} do_model c = 
  let ctxt = 
    Z3.mk_context [
        ("model", if do_model then "true" else "false");
        ("well_sorted_check","true")
      ] 
  in
  let solver = Z3.Solver.mk_simple_solver ctxt in
  let lcs = negate c :: Local.all_constraints local in
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








let resource_for_pointer_strictly_within (loc: Loc.t) {local;global} pointer_it
     : ((Sym.t * RE.t) option) m = 
   let* points = 
     Local.filterM (fun name vb ->
         match vb with 
         | VariableBinding.Resource re -> 
            let lc = 
              IT.And [IndexTerms.LocLT (RE.pointer re, pointer_it);
                      IndexTerms.LocLT (pointer_it, Offset (RE.pointer re, Num (RE.size re)))]
            in
            let* (holds,_,_) = constraint_holds loc {local;global} false (LC.LC lc) in
            return (if holds then Some (name, re) else None)
         | _ -> 
            return None
       ) local
   in
   at_most_one loc !^"multiple points-to for same pointer" points


let resource_for_pointer (loc: Loc.t) {local;global} pointer_it
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
   at_most_one loc !^"multiple points-to for same pointer" points



module StringMap = Map.Make(String)

let evaluate loc model expr = 
  match Z3.Model.evaluate model expr true with
  | None -> fail loc (Internal !^"failure constructing counter model")
  | Some evaluated_expr -> return evaluated_expr


let all_it_names_good it = 
  SymSet.for_all (fun s -> Sym.named s) (IT.vars_in it)




let model loc {local;global} context solver : TypeErrors.model option m =
  match Z3.Solver.get_model solver with
  | None -> 
     return None
  | Some model ->
     let* all_locations = 
       let from_context = 
         filter_map (fun (s, ls) -> 
             if LS.equal ls (LS.Base Loc) then Some (IT.S s) else None
           ) (L.all_logical local)
       in
       let from_resources = 
         map (fun (_, r) -> RE.pointer r) (L.all_resources local)
       in
       ListM.fold_rightM (fun location_it acc ->
           let* expr = of_index_term loc {local; global} context location_it in
           let* expr_val = evaluate loc model expr in
           let expr_val = Z3.Expr.to_string expr_val in
           return (StringMap.add expr_val location_it acc)
         ) (from_context @ from_resources) StringMap.empty
     in
     let* memory_state = 
       ListM.mapM (fun (location_s, location_it) ->
           let* o_resource = resource_for_pointer loc {local; global} location_it in
           let open TypeErrors in
           let* state = match o_resource with
             | None -> 
                let* o_resource2 = 
                  resource_for_pointer_strictly_within loc {local; global} location_it in
                begin match o_resource2 with
                | None -> return Unowned
                | Some (rname,r) -> 
                   let* within_expr = of_index_term loc {local; global} context (RE.pointer r) in
                   let* within_expr_val = evaluate loc model within_expr in
                   let within_expr_val = Z3.Expr.to_string within_expr_val in
                   return (Within {base_location = within_expr_val; resource = rname} )
                end
             | Some (_, RE.Uninit u) -> 
                return (Uninit u.size)
             | Some (_, RE.Points p) -> 
                let* (Base ls) = L.get_l loc p.pointee local in
                let* expr = of_index_term loc {local; global} context (S p.pointee) in
                let* expr_val = evaluate loc model expr in
                begin match ls with
                | Integer -> 
                   let expr_val = Z3.Expr.to_string expr_val in
                   return (Integer (expr_val, p.size))
                | Loc -> 
                   let expr_val = Z3.Expr.to_string expr_val in
                   return (Location (expr_val, p.size))
                | Struct _ ->
                   fail loc (Internal !^"todo: value of struct in counter model")
                | Array ->
                   fail loc (Internal !^"todo: value of array in counter model")
                | _ -> 
                   fail loc (Internal !^"non-object stored in memory")
                end
           in
           return { location = location_s; state }
         ) (StringMap.bindings all_locations)
     in
     let* variable_locations =
       ListM.filter_mapM (fun (c, (l, bt)) ->
           let* expr = of_index_term loc {local; global} context (S l) in
           let* expr_val = evaluate loc model expr in
           let expr_val = Z3.Expr.to_string expr_val in
           let entry = match Sym.name c, bt with
             | Some name, BT.Loc -> Some { name; location = expr_val }
             | _, _ -> None
           in
           return entry
         ) (L.all_computational local)
     in
     return (Some { memory_state; variable_locations })




let is_reachable_and_model loc {local;global} =
  let* (unreachable, context, solver) = 
    constraint_holds loc {local;global} true (LC (Bool false)) 
  in
  let* model = 
    handle_z3_problems loc (fun () -> model loc {local;global} context solver) 
  in
  return (not unreachable, model)
