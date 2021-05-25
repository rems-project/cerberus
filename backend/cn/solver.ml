open IndexTerms
open BaseTypes
module SymMap=Map.Make(Sym)
module IT = IndexTerms


let context = 
  Z3.mk_context [
      ("model", "true");
      ("well_sorted_check","true");
      (* ("auto_config", "false"); *)
      (* ("trace", "true");
       * ("trace_file_name", "trace.smt") *)
    ] 



(* let tactic = Z3.Tactic.mk_tactic context "default" *)
let params = Z3.Params.mk_params context 
let () = Z3.Params.add_int params (Z3.Symbol.mk_string context "smt.random_seed") 98234
let () = Z3.set_global_param "solver.smtlib2_log" "z3.smt2"

module BTtbl = Hashtbl.Make(BaseTypes)
module ITtbl = Hashtbl.Make(IndexTerms)


module Make (G : sig val global : Global.t end) = struct

  let bt_name bt = Pp.plain (BT.pp bt)
  let bt_symbol bt = Z3.Symbol.mk_string context (bt_name bt)
  let tuple_field_name i = "comp" ^ string_of_int i
  let tuple_field_symbol i = Z3.Symbol.mk_string context (tuple_field_name i)
  let member_name id = Id.s id
  let member_symbol id = Z3.Symbol.mk_string context (member_name id)


  let sort_of_bt =
    let tbl = BTtbl.create 10 in
    let rec aux bt =
      match bt with
      | Unit ->
         Z3.Sort.mk_uninterpreted_s context "unit"
      | Bool ->
         Z3.Boolean.mk_sort context
      | Integer ->
         Z3.Arithmetic.Integer.mk_sort context
      | Real -> 
         Z3.Arithmetic.Real.mk_sort context
      | Loc ->
         Z3.Arithmetic.Integer.mk_sort context
      | List bt ->
         Z3.Z3List.mk_sort context (bt_symbol bt) (aux bt) 
      | Tuple bts ->
         let field_symbols = List.mapi (fun i _ -> tuple_field_symbol i) bts in
         let sorts = List.map aux bts in
         Z3.Tuple.mk_sort context (bt_symbol (Tuple bts)) field_symbols sorts
      | Struct tag ->
         let layout = SymMap.find tag G.global.struct_decls in
         let members = Memory.member_types layout in
         let member_symbols = List.map (fun (id,_) -> member_symbol id) members in
         let member_sorts = 
           List.map (fun (_, sct) -> 
               aux (BT.of_sct sct)
             ) members 
         in
         Z3.Tuple.mk_sort context (bt_symbol (Struct tag)) 
           member_symbols member_sorts
      | Set bt ->
         Z3.Set.mk_sort context (aux bt)
      | Option bt ->
         let a_sort = aux bt in
         let some_c = 
           let recognizer = Z3.Symbol.mk_string context ("some_" ^ bt_name bt ^ "_recognizer") in
           let value_field = Z3.Symbol.mk_string context ("some_" ^ bt_name bt ^ "_value") in
           Z3.Datatype.mk_constructor_s context ("some_" ^ bt_name bt) 
             recognizer [value_field] [Some a_sort] [1 (*?*)]
         in
         let none_c = 
           let recognizer = Z3.Symbol.mk_string context ("none_" ^ bt_name bt ^ "_recognizer") in
           Z3.Datatype.mk_constructor_s context ("none_" ^ bt_name bt) 
             recognizer [] [] []
         in
         Z3.Datatype.mk_sort_s context (bt_name (BT.Option bt)) [some_c; none_c]
      | Param (abt, rbt) ->
         Z3.Z3Array.mk_sort context (aux abt) (aux rbt)
    in    

    fun bt ->
    match BTtbl.find_opt tbl bt with
    | Some sort -> sort
    | None ->
       let sort = aux bt in
       let () = BTtbl.add tbl bt sort in
       sort



  let of_index_term_aux =

    let rec term =
      let tbl = ITtbl.create 5000 in
      fun it ->
      Pp.debug 10 (lazy (Pp.item "translating term" (IT.pp it)));
      match ITtbl.find_opt tbl it with
      | Some sc -> sc
      | None ->
         let (IT (it_, bt)) = it in
         (* Pp.debug 10 (lazy (Pp.item "still translating term" (IT.pp it))); *)
         let sc = match it_ with
           | Lit t -> lit t bt
           | Arith_op t -> arith_op t bt
           | Bool_op t -> bool_op t bt
           | Cmp_op t -> cmp_op t bt
           | Tuple_op t -> tuple_op t bt
           | Struct_op t -> struct_op t bt
           | Pointer_op t -> pointer_op t bt
           | List_op t -> list_op t bt
           | Set_op t -> set_op t bt
           | CT_pred t -> ct_pred t bt
           | Option_op t -> option_op t bt
           | Param_op t -> param_op t bt
         in
         let () = ITtbl.add tbl it sc in
         sc

    and lit it bt =
      match it with
      | Sym s -> 
         let sym = Z3.Symbol.mk_string context (Sym.pp_string s) in
         Z3.Expr.mk_const context sym (sort_of_bt bt)
      | Z z ->
         Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
      | Q (i,i') ->
         Z3.Arithmetic.Real.mk_numeral_nd context i i'
      | Pointer z ->
         Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
      | Bool true ->
         Z3.Boolean.mk_true context
      | Bool false ->
         Z3.Boolean.mk_false context
      | Unit ->
         Z3.Expr.mk_fresh_const context "unit" (sort_of_bt Unit)
      | Default bt -> 
         let sym = Z3.Symbol.mk_string context ("default" ^ (bt_name bt)) in
         Z3.Expr.mk_const context sym (sort_of_bt bt)
         


    (* fix rem_t vs rem_f *)
    and arith_op it bt = 
      match it with
      | Add (t1, t2) ->
         Z3.Arithmetic.mk_add context [term t1; term t2]
      | Sub (t1, t2) ->
         Z3.Arithmetic.mk_sub context [term t1; term t2]
      | Mul (t1, t2) ->
         Z3.Arithmetic.mk_mul context [term t1; term t2]
      | Div (t1, t2) ->
         Z3.Arithmetic.mk_div context (term t1) (term t2)
      | Exp (t1, t2) ->
         Z3.Arithmetic.mk_power context (term t1) (term t2)
      | Rem_t (t1, t2) ->
         Z3.Arithmetic.Integer.mk_rem context (term t1) (term t2)
      | Rem_f (t1, t2) ->
         Z3.Arithmetic.Integer.mk_rem context (term t1) (term t2)

    and cmp_op it bt =
      match it with
      | LT (t1, t2) ->
         Z3.Arithmetic.mk_lt context (term t1) (term t2)
      | LE (t1, t2) ->
         Z3.Arithmetic.mk_le context (term t1) (term t2)

    and bool_op it bt =
      match it with
      | And ts -> 
         Z3.Boolean.mk_and context (List.map term ts)
      | Or ts -> 
         Z3.Boolean.mk_or context (List.map term ts)
      | Impl (t1, t2) -> 
         Z3.Boolean.mk_implies context (term t1) (term t2)
      | Not t ->
         Z3.Boolean.mk_not context (term t)
      | ITE (t1, t2, t3) ->
         Z3.Boolean.mk_ite context (term t1) (term t2) (term t3)
      | EQ (t1, t2) ->
         Z3.Boolean.mk_eq context (term t1) (term t2)
      | Forall ((s, bt), it) ->
         let q = term (sym_ (s, bt)) in
         let body = (term it) in
         let q = 
           Z3.Quantifier.mk_forall_const context [q] 
             body None [] [] None None 
         in
         Z3.Quantifier.expr_of_quantifier q


    and tuple_op it bt =
      match it with
      | Tuple ts ->
         let constructor = Z3.Tuple.get_mk_decl (sort_of_bt bt) in
         Z3.Expr.mk_app context constructor (List.map term ts)
      | NthTuple (n, t) ->
         let destructors = Z3.Tuple.get_field_decls (sort_of_bt (IT.bt t)) in
         Z3.Expr.mk_app context (List.nth destructors n) [term t]

    and struct_op it bt =
      match it with
      | Struct (tag, mts) ->
         let constructor = Z3.Tuple.get_mk_decl (sort_of_bt bt) in
         Z3.Expr.mk_app context constructor (List.map (fun (_, t) -> term t) mts)
      | StructMember (tag, t, member) ->
         let layout = SymMap.find tag G.global.struct_decls in
         let members = List.map fst (Memory.member_types layout) in
         let destructors = Z3.Tuple.get_field_decls (sort_of_bt (Struct tag)) in
         let member_destructors = List.combine members destructors in
         let destructor = List.assoc Id.equal member member_destructors in
         Z3.Expr.mk_app context destructor [term t]       

    and pointer_op it bt =
      match it with
      | Null ->
         term (int_ 0)
      | AddPointer (t1, t2) ->
         Z3.Arithmetic.mk_add context [term t1; term t2]
      | SubPointer (t1, t2) ->
         Z3.Arithmetic.mk_sub context [term t1; term t2]
      | MulPointer (t1, t2) ->
         Z3.Arithmetic.mk_mul context [term t1; term t2]
      | LTPointer (t1, t2) ->
         Z3.Arithmetic.mk_lt context (term t1) (term t2)
      | LEPointer (t1, t2) ->
         Z3.Arithmetic.mk_le context (term t1) (term t2)
      | IntegerToPointerCast t ->
         term t
      | PointerToIntegerCast t ->
         term t

    and list_op _ _ =
      Debug_ocaml.error "todo: SMT mapping for list operations"

    and set_op it bt =
      match it with
      | SetMember (t1, t2) ->
          Z3.Set.mk_membership context (term t1) (term t2)
      | SetUnion ts ->
          Z3.Set.mk_union context (List.map term (List1.to_list ts))
      | SetIntersection ts ->
          Z3.Set.mk_intersection context (List.map term (List1.to_list ts))
      | SetDifference (t1, t2) ->
         Z3.Set.mk_difference context (term t1) (term t2)
      | Subset (t1, t2) ->
         Z3.Set.mk_subset context (term t1) (term t2)

    and ct_pred it bt =
      match it with
      | Representable (ct, t) ->
         term (representable_ctype 
                 (fun tag -> (SymMap.find tag G.global.struct_decls))
                 ct t)
      | AlignedI (t1, t2) ->
         term (eq_ (rem_t_ (t2, t1), int_ 0))
      | Aligned (ct, t) ->
         let alignment = match ct with
           | Sctype (_, Function _) -> int_ 1
           | _ -> z_ (Memory.align_of_ctype ct)
         in
         term (eq_ (rem_t_ (t, alignment), int_ 0))

    and option_op it bt = 
      match it with
      | Something it ->
         let option_sort = sort_of_bt bt in
         let constructors = Z3.Datatype.get_constructors option_sort in
         Z3.Expr.mk_app context (List.hd constructors) [term it]
      | Nothing _ ->
         let option_sort = sort_of_bt bt in
         let constructors = Z3.Datatype.get_constructors option_sort in
         Z3.Expr.mk_app context (List.hd (List.tl constructors)) []
      | Is_some it -> 
         let option_sort = sort_of_bt (IT.bt it) in
         let recognisers = Z3.Datatype.get_recognizers option_sort in
         Z3.Expr.mk_app context (List.hd recognisers) [term it]
      | Value_of_some it -> 
         let option_sort = sort_of_bt (IT.bt it) in
         let accessors = Z3.Datatype.get_accessors option_sort in
         Z3.Expr.mk_app context (List.hd (List.hd accessors)) [term it]

    and param_op it bt = 
      match it with
      | Const t ->
         Z3.Z3Array.mk_const_array context (sort_of_bt Integer) (term t)
      | Mod (t1, t2, t3) ->
         Z3.Z3Array.mk_store context (term t1) (term t2) (term t3)  
      | App (f, arg) ->
         begin match f with
         | IT (Param_op (Param (t_arg, body)),_) ->
            let subst = Subst.{before = (fst t_arg); after = arg} in
            term (IT.subst_it subst body)
         | _ ->
            Z3.Z3Array.mk_select context (term f) (term arg)
         end
      | Param ((sym, abt), body) ->
         let err = 
           "SMT solver applied to parameterised expression (of_index_term): " ^
             Pp.plain (IT.pp (IT (Param_op it, bt)))
         in
         Debug_ocaml.error err
    in

    fun it ->
    term it



  let of_index_term it = 
    try of_index_term_aux it with
    | Z3.Error err -> 
       Debug_ocaml.error ("Z3 error: " ^ err)


  let check ?(ignore_unknown=false) local (expr : Z3.Expr.expr) = 
    let solver = Z3.Solver.mk_simple_solver context in
    let neg_expr = Z3.Boolean.mk_not context expr in
    let assumptions = List.map of_index_term (Local.all_constraints local) in
    let constraints = neg_expr :: assumptions in
    Z3.Solver.add solver constraints;
    let result = Z3.Solver.check solver [] in
    (* let () =
     *   if !Pp.print_level >= 3 then
     *     let oc = open_out "smt.smt" in
     *     (\* output_string oc (Z3.SMT.benchmark_to_smtstring context 
     *      *                     "experiment" "" "unknown" "" assumptions neg_expr); *\)
     *     output_string oc (Z3.Solver.to_string solver);
     *     close_out oc
     * in *)
    match result with
    | Z3.Solver.UNSATISFIABLE -> (true, solver)
    | Z3.Solver.SATISFIABLE -> (false, solver)
    | Z3.Solver.UNKNOWN -> 
       if ignore_unknown then 
         (false, solver) 
       else
         let reason = Z3.Solver.get_reason_unknown solver in
         Debug_ocaml.error ("SMT solver returned 'unknown'. Reason: " ^ reason)
  
  let holds ?(ignore_unknown=false) local it = 
    try fst (check ~ignore_unknown local (of_index_term it)) with
    | Z3.Error err -> 
       Debug_ocaml.error ("Z3 error: " ^ err)

  let holds_and_solver ?(ignore_unknown=false) local it = 
    try check ~ignore_unknown local (of_index_term it) with
    | Z3.Error err -> 
       Debug_ocaml.error ("Z3 error: " ^ err)


  let is_inconsistent local = holds local (bool_ false)

  let get_model solver = Z3.Solver.get_model solver


end



