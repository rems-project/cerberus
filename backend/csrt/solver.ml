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
     let* offset = Memory.offset loc {local; global} tag member in
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
  | InRange (ct, _bt, t) ->
     let* rangef = Conversions.in_range_of_ctype loc global.struct_decls ct in
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







(*** counter models ***********************************************************)



module VarEquivalenceClass = struct

  let counter = ref 0

  type t = 
    { representative : Sym.t;
      sort: LS.t;
      lelements : SymSet.t;
      celements : SymSet.t;
    }


  let ls_prefix (LS.Base bt) = 
    match bt with
    | Unit -> "u"
    | Bool -> "b"
    | Integer -> "i"
    | Loc -> "l"
    | Array -> "a"
    | List _ -> "l"
    | Tuple _ -> "p"
    | Struct _ -> "s"
    | FunctionPointer _ -> "f"

  let name veclass = 
    match SymSet.find_first_opt Sym.named veclass.celements with
    | Some s -> s
    | None -> 
       match SymSet.find_first_opt Sym.named veclass.lelements with
       | Some s -> s
       | None -> veclass.representative

  let print_name veclass = 
    match SymSet.find_first_opt Sym.named veclass.celements with
    | Some s -> s
    | None -> 
       match SymSet.find_first_opt Sym.named veclass.lelements with
       | Some s -> s
       | None -> veclass.representative

  let new_class l ls = 
    counter := !counter + 1;
    { representative = l;
      sort = ls;
      lelements = SymSet.singleton l;
      celements = SymSet.empty;
    }

  let insert_l l veclass = 
    { veclass with lelements = SymSet.add l veclass.lelements }

  let insert_c c veclass = 
    { veclass with celements = SymSet.add c veclass.celements }

  let o_insert_c o_c veclass = 
    match o_c with
    | None -> veclass
    | Some c -> insert_c c veclass

  let classify loc {local; global} classes l ls o_c : t list m =
    let rec aux = function
      | veclass :: veclasses ->
         let* found_class = 
           if not (LS.equal veclass.sort ls) then return false else
             equal loc {local; global} 
               (S veclass.representative) (S l)
         in
         if found_class then 
           return (o_insert_c o_c (insert_l l veclass) :: veclasses) 
         else 
           let* veclasses' = aux veclasses in
           return (veclass :: veclasses')
      | [] -> 
         return [o_insert_c o_c (new_class l ls)]
    in
    aux classes

  

end
  





let rec matching_symbol syms num = 
  match syms with
  | sym :: syms when Sym.num sym = num -> Some sym
  | sym :: syms -> matching_symbol syms num
  | [] -> None


type constant_mapping = (Sym.t * Z3.Expr.expr) list


(* Maybe should fail if symbol mapping is missing? The code below
   ignores constants that can't be mapped back to symbols. Also look
   at unsat_core? *)

let const_mapping_of_model all_syms (model : Z3.Model.model) : constant_mapping = 
  let open Option in
  let z3_model = Z3.Model.get_const_decls model in
  List.filter_map (fun decl -> 
      let name = Z3.FuncDecl.get_name decl in
      if not (Z3.Symbol.is_int_symbol name) then fail else 
        let* sym = matching_symbol all_syms (Z3.Symbol.get_int name) in
        let* expr = Z3.Model.get_const_interp model decl in
        return (sym, expr)
    ) z3_model


open VarEquivalenceClass



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
   Tools.at_most_one loc !^"multiple points-to for same pointer" points


module StringMap = Map.Make(String)

let evaluate loc model expr = 
  match Z3.Model.evaluate model expr true with
  | None -> fail loc (Internal !^"failure constructing counter model")
  | Some evaluated_expr -> return evaluated_expr


let all_it_names_good it = 
  SymSet.for_all (fun s -> Sym.named s) (IT.vars_in it)


let model loc {local;global} context solver : Pp.document option m =
  match Z3.Solver.get_model solver with
  | None -> 
     return None
  | Some model ->
     let c = L.all_computational local in
     let l = L.all_logical local in
     let r = L.all_resources local in
     let* veclasses = 
       let* with_l = 
         ListM.fold_leftM (fun classes (l, ls) ->
             classify loc {local; global} classes l ls None
           ) [] l
       in
       let* with_c = 
         ListM.fold_leftM (fun classes (c, (l, bt)) ->
             classify loc {local; global} classes l (LS.Base bt) (Some c)
           ) with_l c
       in
       return with_c
     in
     let print_substs =
       List.fold_right (fun veclass substs ->
         let name = print_name veclass in
         let to_substitute = SymSet.union veclass.celements veclass.lelements in
         SymSet.fold (fun sym substs ->
             Subst.{ before = sym; after = name } :: substs
           ) to_substitute substs 
         ) veclasses []
     in
     let* all_locations = 
       let from_context = 
         filter_map (fun (s, ls) -> 
             if LS.equal ls (LS.Base Loc) then Some (IT.S s) else None
           ) l
       in
       let from_resources = 
         map (fun (_, r) -> RE.pointer r) r in
       ListM.fold_rightM (fun location_it acc ->
           let* expr = of_index_term loc {local; global} context location_it in
           let* evaluated_expr = evaluate loc model expr in
           return (StringMap.add (Z3.Expr.to_string evaluated_expr) location_it acc)
         ) (from_context @ from_resources) StringMap.empty
     in
     let* pped_state = 
       ListM.fold_rightM (fun (location_string, location_it) acc_pp ->
           let* o_resource = resource_for_pointer loc {local; global} location_it in
           let* pp = match o_resource with
             | None -> 
                return (!^"location" ^^^ !^location_string ^^^ !^"unowned")
             | Some (_, RE.Uninit u) -> 
                return (!^"location" ^^^ !^location_string ^^^ parens (Z.pp u.size ^^^ !^"bytes size") ^^^ 
                          !^"uninitialised")
             | Some (_, RE.Points p) -> 
                let* (Base ls) = L.get_l loc p.pointee local in
                let* expr = of_index_term loc {local; global} context (S p.pointee) in
                let* evaluated_expr = evaluate loc model expr in
                let loc_pp = !^location_string ^^^ parens (Z.pp p.size ^^^ !^"bytes size") in
                let val_pp = !^(Z3.Expr.to_string evaluated_expr) in
                let location_it_pp = 
                  let it = IT.subst_vars print_substs location_it in
                  if all_it_names_good it then IT.pp it ^^^ !^"at" ^^ space else Pp.empty 
                in
                match ls with
                | Integer -> 
                   return (location_it_pp ^^ !^"location" ^^^ loc_pp ^^^ !^"stores integer" ^^^ val_pp)
                | Loc -> 
                   return (location_it_pp ^^ !^"location" ^^^ loc_pp ^^^ !^"stores pointer to location" ^^^ val_pp)
                | Array ->
                   fail loc (Internal !^"todo: array print reporting")
                | Struct _ ->
                   fail loc (Internal !^"todo: struct print reporting")
                | Unit 
                | Bool
                | List _
                | Tuple _
                | FunctionPointer _ -> fail loc (Internal !^"non-object stored in memory")
           in
           return (pp :: acc_pp)
         ) (StringMap.bindings all_locations) []
     in


  return (Some (flow hardline pped_state))




let is_reachable_and_model loc {local;global} =
  let* (unreachable, context, solver) = 
    constraint_holds loc {local;global} true (LC (Bool false)) in
  let* model = 
    handle_z3_problems loc (fun () -> model loc {local;global} context solver) in

  return (not unreachable, model)
