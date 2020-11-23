open Global
open List
open Pp
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
let rec bt_to_sort {local;global} ctxt bt = 
  let open BaseTypes in
  let btname = bt_name bt in
  match bt with
  | Unit -> Z3.Sort.mk_uninterpreted_s ctxt btname
  | Bool -> Z3.Boolean.mk_sort ctxt
  | Integer -> Z3.Arithmetic.Integer.mk_sort ctxt
  | Loc -> Z3.Arithmetic.Integer.mk_sort ctxt
  (* | Loc -> return (Z3.Sort.mk_uninterpreted_s ctxt btname) *)
  | Tuple bts ->
     let names = mapi (fun i _ -> Z3.Symbol.mk_string ctxt (tuple_component_name bt i)) bts in
     let sorts = List.map (bt_to_sort {local;global} ctxt) bts in
     Z3.Tuple.mk_sort ctxt (Z3.Symbol.mk_string ctxt btname) names sorts
  | Struct tag ->
     let decl = SymMap.find tag global.struct_decls in
     let rec aux = function
       | (member, ( _, bt)) :: members ->
          let (names,sorts) = aux members in
          let sort = bt_to_sort {local;global} ctxt bt in
          let names = Z3.Symbol.mk_string ctxt (struct_member_name bt member) :: names in
          let sorts = sort :: sorts in
          (names,sorts)
       | [] -> ([],[])
     in
     let (names,sorts) = aux decl.members in
     let name = Z3.Symbol.mk_string ctxt btname in
     let sort = Z3.Tuple.mk_sort ctxt name names sorts in
     sort
  | Array ->
     Z3.Sort.mk_uninterpreted_s ctxt btname
  | List _ ->
     Z3.Sort.mk_uninterpreted_s ctxt btname
  | FunctionPointer _ -> 
     Z3.Sort.mk_uninterpreted_s ctxt btname

let ls_to_sort {local;global} ctxt (LS.Base bt) =
  bt_to_sort {local;global} ctxt bt


let rec of_index_term {local;global} ctxt it = 
  let open Pp in
  let open IndexTerms in
  let nth_to_fundecl bt i = 
    let sort = ls_to_sort {local;global} ctxt (Base bt) in
    let member_fun_decls = Z3.Tuple.get_field_decls sort in
    List.nth member_fun_decls i
  in
  let member_to_fundecl tag member = 
    let decl = SymMap.find tag global.struct_decls in
    let sort = ls_to_sort {local;global} ctxt (Base (Struct tag)) in
    let member_fun_decls = Z3.Tuple.get_field_decls sort in
    let member_names = map fst decl.members in
    let member_funs = combine member_names member_fun_decls in
    assoc Id.equal member member_funs
  in
  match it with
  | Num n -> 
     let nstr = Nat_big_num.to_string n in
     Z3.Arithmetic.Integer.mk_numeral_s ctxt nstr
  | Pointer n -> 
     let nstr = Nat_big_num.to_string n in
     Z3.Arithmetic.Integer.mk_numeral_s ctxt nstr
  | Bool true -> 
     Z3.Boolean.mk_true ctxt
  | Bool false -> 
     Z3.Boolean.mk_false ctxt
  | Unit ->
     let unitsort = ls_to_sort {local;global} ctxt (Base Unit) in
     Z3.Expr.mk_const_s ctxt "unit" unitsort
  | Add (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_add ctxt [a;a']
  | Sub (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_sub ctxt [a;a']
  | Mul (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_mul ctxt [a; a']
  | Div (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_div ctxt a a'
  | Exp (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_power ctxt a a'
  | Rem_t (it,it') -> 
     if not !rem_t_warned then
       (rem_t_warned := true; Pp.warn !^"Rem_t constraint");
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.Integer.mk_rem ctxt a a'
  | Rem_f (it,it') -> 
     if not !rem_f_warned then
       (rem_f_warned := true; Pp.warn !^"Rem_f constraint");
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.Integer.mk_rem ctxt a a'
  | Min (it,it') -> 
     let it_elab = ITE (it %< it', it, it') in
     of_index_term {local;global} ctxt it_elab 
  | Max (it,it') -> 
     let it_elab = ITE (it %> it', it, it') in
     of_index_term {local;global} ctxt it_elab 
  | EQ (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Boolean.mk_eq ctxt a a'
  | NE (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Boolean.mk_distinct ctxt [a; a']
  | LT (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_lt ctxt a a'
  | GT (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_gt ctxt a a'
  | LE (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_le ctxt a a'
  | GE (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_ge ctxt a a'
  | Null t -> 
     let locsort = ls_to_sort {local;global} ctxt (Base Loc) in
     let boolsort = ls_to_sort {local;global} ctxt (Base Bool) in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt "null" [locsort] boolsort in
     let a = of_index_term {local;global} ctxt t in
     let is_null = Z3.Expr.mk_app ctxt fundecl [a] in
     let zero_str = Nat_big_num.to_string Z.zero in
     let zero_expr = Z3.Arithmetic.Integer.mk_numeral_s ctxt zero_str in
     let is_zero = Z3.Boolean.mk_eq ctxt a zero_expr in
     Z3.Boolean.mk_and ctxt [is_null; is_zero]
  | And its -> 
     let ts = List.map (of_index_term {local;global} ctxt) its in
     Z3.Boolean.mk_and ctxt ts
  | Or its -> 
     let ts = List.map (of_index_term {local;global} ctxt) its in
     Z3.Boolean.mk_or ctxt ts
  | Impl (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Boolean.mk_implies ctxt a a'
  | Not it -> 
     let a = of_index_term {local;global} ctxt it in
     Z3.Boolean.mk_not ctxt a
  | ITE (it,it',it'') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     let a'' = of_index_term {local;global} ctxt it'' in
     Z3.Boolean.mk_ite ctxt a a' a''
  | S s -> 
     let ls = Local.get_l s local in
     let sym = sym_to_symbol ctxt s in
     let sort = ls_to_sort {local;global} ctxt ls in
     Z3.Expr.mk_const ctxt sym sort
  | Member (tag, t, member) ->
     let a = of_index_term {local;global} ctxt t in
     let fundecl = member_to_fundecl tag member in
     Z3.Expr.mk_app ctxt fundecl [a]
  | MemberOffset (tag, t, member) ->
     let a = of_index_term {local;global} ctxt t in
     let offset = Memory.member_offset tag member in
     let offset_s = Nat_big_num.to_string offset in
     let offset_n = Z3.Arithmetic.Integer.mk_numeral_s ctxt offset_s in
     Z3.Arithmetic.mk_add ctxt [a;offset_n]
  | AllocationSize t ->
     let locsort = ls_to_sort {local;global} ctxt (Base Loc) in
     let intsort = ls_to_sort {local;global} ctxt (Base Integer) in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt "allocationSize" [locsort] intsort in
     let a = of_index_term {local;global} ctxt t in
     Z3.Expr.mk_app ctxt fundecl [a]
  | Offset (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_add ctxt [a;a']
  | LocLT (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_lt ctxt a a'
  | LocLE (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Arithmetic.mk_le ctxt a a'
  | Disjoint ((it,s),(it',s')) ->
     let fp1_before_fp2 = IT.LocLT (Offset (Offset (it, Num s), IT.int (-1)), it') in
     let fp2_before_fp1 = IT.LocLT (Offset (Offset (it', Num s'), IT.int (-1)), it) in
     let t = Or [fp1_before_fp2; fp2_before_fp1] in
     of_index_term {local; global} ctxt t
  | Struct (tag,members) ->
     let sort = bt_to_sort {local;global} ctxt (Struct tag) in
     let constructor = Z3.Tuple.get_mk_decl sort in
     let member_vals = 
       List.map (fun (_member,it) ->
           of_index_term {local;global} ctxt it
         ) members
     in
     Z3.Expr.mk_app ctxt constructor member_vals
  | Nth (bt,i,t) ->
     let a = of_index_term {local;global} ctxt t in
     let fundecl = nth_to_fundecl bt i in
     Z3.Expr.mk_app ctxt fundecl [a]
  | Aligned (st,it') -> 
     let align = Memory.align_of_stored_type st in
     let a = of_index_term {local;global} ctxt (Num align) in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Boolean.mk_eq ctxt
       (Z3.Arithmetic.Integer.mk_mod ctxt a' a)
       (Z3.Arithmetic.Integer.mk_numeral_s ctxt "0")
  | AlignedI (it,it') -> 
     let a = of_index_term {local;global} ctxt it in
     let a' = of_index_term {local;global} ctxt it' in
     Z3.Boolean.mk_eq ctxt
       (Z3.Arithmetic.Integer.mk_mod ctxt a' a)
       (Z3.Arithmetic.Integer.mk_numeral_s ctxt "0")
  | Representable (st, t) ->
     let rangef = Memory.representable_stored_type global.struct_decls st in
     of_index_term {local; global} ctxt (LC.unpack (rangef t))
  | Nil _ ->
     Debug_ocaml.error "todo: Z3: Nil"
  | Cons _ ->
     Debug_ocaml.error "todo: Z3: Cons"
  | Tuple ts ->
     Debug_ocaml.error "todo: Z3: Tuple"
  | Head t ->
     Debug_ocaml.error "todo: Z3: Head"
  | Tail t ->
     Debug_ocaml.error "todo: Z3: Tail"
  | List (ts,bt) ->
     Debug_ocaml.error "todo: Z3: List"








(*** running Z3 **************************************************************)


let handle_z3_problems todo =
  if not (Z3.Log.open_ logfile) then 
    Debug_ocaml.error ("Z3 logfile: could not open " ^ logfile)
  else 
    try let result = todo () in Z3.Log.close (); result with
    | Z3.Error (msg : string) -> 
       Z3.Log.close ();
       Debug_ocaml.error ("Z3 error:" ^ msg)


(* let debug_typecheck_lcs lcs {local;global} =
 *   if !Debug_ocaml.debug_level > 0 then () else
 *     List.iter (fun lc -> 
 *         match WellTyped.WLC.welltyped (loc: Loc.t) {local;global} lc with
 *         | Ok () -> ()
 *         | Error _ -> Debug_ocaml.error "illtyped logical constraint"
 *       ) lcs *)





  


let constraint_holds {local;global} do_model c = 
  let ctxt = 
    Z3.mk_context [
        ("model", if do_model then "true" else "false");
        ("well_sorted_check","true")
      ] 
  in
  let solver = Z3.Solver.mk_simple_solver ctxt in
  let lcs = negate c :: Local.all_constraints local in
  (* let () = debug_typecheck_lcs lcs {local;global} in *)
  let checked = 
    handle_z3_problems
      (fun () ->
        let constrs = 
          List.map (fun lc -> 
              of_index_term {local;global} ctxt (unpack lc)
            ) lcs 
        in
        Z3.Solver.add solver constrs;
        Z3.Solver.check solver []
      )
  in
  match checked with
  | UNSATISFIABLE -> (true,ctxt,solver)
  | SATISFIABLE -> (false,ctxt,solver)
  | UNKNOWN -> (false,ctxt,solver)


let is_consistent {local;global} =
  let (unreachable,_,_) = 
    constraint_holds {local;global} false (LC (Bool false)) in
  (not unreachable)



let equal {local;global} it1 it2 =
  let c = LC.LC (IndexTerms.EQ (it1, it2)) in
  let (holds,_,_) = constraint_holds {local;global} false c in
  holds








let resource_for_pointer {local;global} pointer_it
     : (Sym.t * RE.t) option = 
  let points = 
    List.filter_map (fun (name, re) ->
        let holds = equal {local;global} pointer_it (RE.pointer re) in
        (if holds then Some (name, re) else None)
      ) (Local.all_resources local)
  in
  Tools.at_most_one "multiple points-to for same pointer" points


let used_resource_for_pointer {local;global} pointer_it
    : (Loc.t list) option = 
  let points = 
    List.filter_map (fun (name, re, where) ->
        let holds = equal {local; global} pointer_it (RE.pointer re) in
        (if holds then Some (where) else None)
      ) (Local.all_used_resources local)
  in
  Tools.at_most_one "multiple points-to for same pointer" points


module StringMap = Map.Make(String)

let evaluate model expr = 
  match Z3.Model.evaluate model expr true with
  | None -> Debug_ocaml.error "failure constructing counter model"
  | Some evaluated_expr -> evaluated_expr


let all_it_names_good it = 
  SymSet.for_all (fun s -> Sym.named s) (IT.vars_in it)





(* more to be added *)
type memory_state = 
  | Nothing
  | Uninit of RE.size
  | Integer of string * RE.size
  | Location of string * RE.size
  | Within of {base_location : string; resource : Sym.t}
  | Padding of RE.size
  | Predicate of {name : RE.predicate_name; args : string list}

type location_state = { location : string; state : memory_state; }
type variable_location = { name : string; location : string}

type model = 
  { memory_state : location_state list;
    variable_locations : variable_location list;
  }


let model {local;global} context solver : model option =
  match Z3.Solver.get_model solver with
  | None -> None
  | Some model ->
     let all_locations = 
       let from_context = 
         filter_map (fun (s, ls) -> 
             if LS.equal ls (LS.Base Loc) then Some (IT.S s) else None
           ) (L.all_logical local)
       in
       let from_resources = 
         map (fun (_, r) -> RE.pointer r) (L.all_resources local)
       in
       List.fold_right (fun location_it acc ->
           let expr = of_index_term {local; global} context location_it in
           let expr_val = evaluate model expr in
           let expr_val = Z3.Expr.to_string expr_val in
           (StringMap.add expr_val location_it acc)
         ) (from_context @ from_resources) StringMap.empty
     in
     let memory_state = 
       List.map (fun (location_s, location_it) ->
           let o_resource = resource_for_pointer {local; global} location_it in
           let state = match o_resource with
             | None -> Nothing
             | Some (_, RE.Uninit u) -> (Uninit u.size)
             | Some (_, RE.Points p) -> 
                let (Base ls) = L.get_l p.pointee local in
                let expr = of_index_term {local; global} context (S p.pointee) in
                let expr_val = evaluate model expr in
                begin match ls with
                | Integer -> 
                   Integer (Z3.Expr.to_string expr_val, p.size)
                | Loc -> 
                   Location (Z3.Expr.to_string expr_val, p.size)
                | Struct _ ->
                   Debug_ocaml.error "todo: value of struct in counter model"
                | Array ->
                   Debug_ocaml.error "todo: value of array in counter model"
                | _ -> 
                   Debug_ocaml.error "non-object stored in memory"
                end
             | Some (_, RE.Predicate p) -> 
                let args = 
                  List.map (fun arg ->
                      let expr = of_index_term {local; global} context (S arg) in
                      let expr_val = evaluate model expr in
                      Z3.Expr.to_string expr_val
                    ) p.args
                in
                Predicate {name = p.name; args}
             | Some (_, RE.Padding p) -> 
                Padding p.size
           in
           { location = location_s; state }
         ) (StringMap.bindings all_locations)
     in
     let variable_locations =
       List.filter_map (fun (c, (l, bt)) ->
           let expr = of_index_term {local; global} context (S l) in
           let expr_val = evaluate model expr in
           let expr_val = Z3.Expr.to_string expr_val in
           let entry = match Sym.name c, bt with
             | Some name, BT.Loc -> Some { name; location = expr_val }
             | _, _ -> None
           in
           entry
         ) (L.all_computational local)
     in
     Some { memory_state; variable_locations }




let is_reachable_and_model {local;global} =
  let (unreachable, context, solver) = 
    constraint_holds {local;global} true (LC (Bool false)) 
  in
  let model = 
    handle_z3_problems (fun () -> model {local;global} context solver) 
  in
  (not unreachable, model)







let pp_variable_and_location_state ( ovar, { location; state } ) =
  let var = match ovar with
    | None -> Pp.empty
    | Some v -> !^v
  in
  let value, size = match state with
    | Nothing -> Pp.empty, Pp.empty
    | Uninit size -> !^"uninitialised", Z.pp size
    | Integer (value, size) -> typ !^value !^"integer", Z.pp size
    | Location (value, size) -> typ !^value !^"pointer", Z.pp size
    | Within {base_location; _} -> 
       parens (!^"within owned region at" ^^^ !^base_location), Pp.empty
    | Predicate {name; args} ->
       begin match name with
       | Id id ->
          Id.pp id ^^ parens (separate_map (space ^^ comma) string args), Pp.empty
       | Tag tag ->
          Sym.pp tag ^^ parens (separate_map (space ^^ comma) string args), Pp.empty
       end
    | Padding size ->
       !^"padding", Z.pp size
  in
  ( (R, var), (R, !^location), (R, size), (L, value) )


let pp_model model = 
  let variable_and_location_state : (string option * location_state) list = 
    List.concat_map (fun (ls : location_state) ->
        let vars = 
          List.filter (fun vl -> String.equal ls.location vl.location
            ) model.variable_locations
        in
        match vars with
        | [] -> [(None, ls)]
        | _ -> List.map (fun v -> (Some v.name, ls)) vars
      ) model.memory_state
  in
  Pp.table4 
    (("var"), ("location"), ("size") , ("value"))
    (List.map pp_variable_and_location_state variable_and_location_state)
