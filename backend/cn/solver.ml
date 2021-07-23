open IndexTerms
open BaseTypes
module SymMap=Map.Make(Sym)
module IT = IndexTerms
module LC = LogicalConstraints
open LogicalConstraints


let context = 
  Z3.mk_context [
      ("model", "true");
      ("well_sorted_check","false");
      (* ("trace", "true");
       * ("trace_file_name", "trace.smt") *)
    ] 


let params = Z3.Params.mk_params context 
let () = Z3.set_global_param "smt.auto-config" "false"
let () = Z3.set_global_param "smt.mbqi" "false"
let () = Z3.set_global_param "smt.pull-nested-quantifiers" "true"
let () = Z3.set_global_param "smt.macro_finder" "true"




let unit_sort = Z3.Sort.mk_uninterpreted_s context "unit"
let bool_sort = Z3.Boolean.mk_sort context
let integer_sort = Z3.Arithmetic.Integer.mk_sort context
let real_sort = Z3.Arithmetic.Real.mk_sort context



module BTtbl = Hashtbl.Make(BaseTypes)
module ITtbl = Hashtbl.Make(IndexTerms)


module type S = sig

  val provable : Z3.Expr.expr list -> LC.t -> bool
  val provable_and_solver : Z3.Expr.expr list -> LC.t -> bool * Z3.Solver.solver
  val provably_inconsistent : Z3.Expr.expr list -> bool
  val get_model : Z3.Solver.solver -> Z3.Model.model
  val symbol_expression : Sym.t -> BT.t -> Z3.Expr.expr
  val expr : IT.t -> Z3.Expr.expr * Z3.Expr.expr list
  val constr : LC.t -> Z3.Expr.expr list

end




module Make (SD : sig val struct_decls : Memory.struct_decls end) : S = struct

  let bt_name bt = Pp.plain (BT.pp bt)
  let bt_symbol bt = Z3.Symbol.mk_string context (bt_name bt)
  let tuple_field_name i = "comp" ^ string_of_int i
  let tuple_field_symbol i = Z3.Symbol.mk_string context (tuple_field_name i)
  let member_name id = Id.s id
  let member_symbol bt id = Z3.Symbol.mk_string context (bt_name bt ^ "_" ^ member_name id)
  let sym_to_sym s = 
    let (digest,id, oname) = Sym.dest s in
    let str = match oname with
      | None -> string_of_int id ^"." ^ digest
      | Some s -> string_of_int id ^"." ^ digest
    in
    Z3.Symbol.mk_string context str

  let sort_of_bt =
    let tbl = BTtbl.create 10 in
    let rec aux bt =
      match bt with
      | Unit -> unit_sort
      | Bool -> bool_sort
      | Integer -> integer_sort
      | Real -> real_sort
      | Loc -> integer_sort
      | List bt ->
         Z3.Z3List.mk_sort context (bt_symbol bt) (aux bt) 
      | Tuple bts ->
         let field_symbols = List.mapi (fun i _ -> tuple_field_symbol i) bts in
         let sorts = List.map aux bts in
         Z3.Tuple.mk_sort context (bt_symbol (Tuple bts)) field_symbols sorts
      | Struct tag ->
         let layout = SymMap.find tag SD.struct_decls in
         let members = Memory.member_types layout in
         let member_symbols = List.map (fun (id,_) -> member_symbol (BT.Struct tag) id) members in
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


  let symbol_expression s bt =
    Z3.Expr.mk_const context 
      (sym_to_sym s) (sort_of_bt bt)



  let of_index_term =

    let rec term =
      let tbl = ITtbl.create 5000 in
      fun it ->
      Pp.debug 10 (lazy (Pp.item "translating term" (IT.pp it)));
      match ITtbl.find_opt tbl it with
      | Some (sc, scs) -> (sc, scs)
      | None ->
         let (IT (it_, bt)) = it in
         Pp.debug 10 (lazy (Pp.item "still translating term" (IT.pp it)));
         Pp.debug 10 (lazy (Pp.item "of type" (BT.pp (IT.bt it))));
         let sc, scs = match it_ with
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
         let () = ITtbl.add tbl it (sc, scs) in
         (sc, scs)

    and lit it bt =
      let e = match it with
        | Sym s ->    
           Z3.Expr.mk_const context (sym_to_sym s) (sort_of_bt bt)
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
      in
      (e, [])
         


    (* fix rem_t vs rem_f *)
    and arith_op it bt = 
      match it with
      | Add (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Arithmetic.mk_add context [t1; t2], e1 @ e2)
      | Sub (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Arithmetic.mk_sub context [t1; t2], e1 @ e2)
      | Mul (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Arithmetic.mk_mul context [t1; t2], e1 @ e2)
      | Div (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Arithmetic.mk_div context t1 t2, e1 @ e2)
      | Exp (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Arithmetic.mk_power context t1 t2, e1 @ e2)
      | Rem (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Arithmetic.Integer.mk_rem context t1 t2, e1 @ e2)

    and cmp_op it bt =
      match it with
      | LT (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Arithmetic.mk_lt context t1 t2, e1 @ e2)
      | LE (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Arithmetic.mk_le context t1 t2, e1 @ e2)

    and bool_op it bt =
      match it with
      | And ts -> 
         let ts, es = List.split (List.map term ts) in
         (Z3.Boolean.mk_and context ts, List.concat es)
      | Or ts -> 
         let ts, es = List.split (List.map term ts) in
         (Z3.Boolean.mk_or context ts, List.concat es)
      | Impl (t1, t2) -> 
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Boolean.mk_implies context t1 t2, e1 @ e2)
      | Not t ->
         let (t, e) = term t in
         (Z3.Boolean.mk_not context t, e)
      | ITE (t1, t2, t3) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         let (t3, e3) = term t3 in
         (Z3.Boolean.mk_ite context t1 t2 t3, e1 @ e2 @ e3)
      | EQ (t1, t2) ->
         let (t1, e1) = term t1 in
         let (t2, e2) = term t2 in
         (Z3.Boolean.mk_eq context t1 t2, e1 @ e2)


    and tuple_op it bt =
      match it with
      | Tuple ts ->
         let ts, es = List.split (List.map term ts) in
         let constructor = Z3.Tuple.get_mk_decl (sort_of_bt bt) in
         (Z3.Expr.mk_app context constructor ts, List.concat es)
      | NthTuple (n, t) ->
         let destructors = Z3.Tuple.get_field_decls (sort_of_bt (IT.bt t)) in
         let t, e = term t in
         (Z3.Expr.mk_app context (List.nth destructors n) [t], e)

    and struct_op it bt =
      match it with
      | Struct (tag, mts) ->
         let constructor = Z3.Tuple.get_mk_decl (sort_of_bt bt) in
         let mts = (List.map (fun (_, t) -> term t) mts) in
         let ts, es = List.split mts in
         (Z3.Expr.mk_app context constructor ts, List.concat es)
      | StructMember (t, member) ->
         let tag = match IT.bt t with
           | Struct tag -> tag
           | _ -> Debug_ocaml.error "illtyped index term: not a struct"
         in
         let layout = SymMap.find tag SD.struct_decls in
         let members = List.map fst (Memory.member_types layout) in
         let destructors = Z3.Tuple.get_field_decls (sort_of_bt (Struct tag)) in
         let member_destructors = List.combine members destructors in
         let destructor = List.assoc Id.equal member member_destructors in
         let t, e = term t in
         (Z3.Expr.mk_app context destructor [t], e)

    and pointer_op it bt =
      match it with
      | Null ->
         term (int_ 0)
      | AddPointer (t1, t2) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         (Z3.Arithmetic.mk_add context [t1; t2], e1 @ e2)
      | SubPointer (t1, t2) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         (Z3.Arithmetic.mk_sub context [t1; t2], e1 @ e2)
      | MulPointer (t1, t2) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         (Z3.Arithmetic.mk_mul context [t1; t2], e1 @ e2)
      | LTPointer (t1, t2) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         (Z3.Arithmetic.mk_lt context t1 t2, e1 @ e2)
      | LEPointer (t1, t2) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         (Z3.Arithmetic.mk_le context t1 t2, e1 @ e2)
      | IntegerToPointerCast t ->
         term t
      | PointerToIntegerCast t ->
         term t
      | MemberOffset (tag, member) ->
         let o_offset = 
           Memory.member_offset
             (SymMap.find tag SD.struct_decls) member
         in
         let offset = match o_offset with
           | Some offset -> offset 
           | None -> Debug_ocaml.error "illtyped index term: member offset does not apply"
         in
         term (z_ offset)
      | ArrayOffset (ct, t) ->
         term (mul_ (z_ (Memory.size_of_ctype ct), t))
  

    and list_op _ _ =
      Debug_ocaml.error "todo: SMT mapping for list operations"

    and set_op it bt =
      match it with
      | SetMember (t1, t2) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         (Z3.Set.mk_membership context t1 t2, e1 @ e2)
      | SetUnion ts ->
         let ts, es = List.split (List.map term (List1.to_list ts)) in
         (Z3.Set.mk_union context ts, List.concat es)
      | SetIntersection ts ->
         let ts, es = List.split (List.map term (List1.to_list ts)) in
         (Z3.Set.mk_intersection context ts, List.concat es)
      | SetDifference (t1, t2) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         (Z3.Set.mk_difference context t1 t2, e1 @ e2)
      | Subset (t1, t2) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         (Z3.Set.mk_subset context t1 t2, e1 @ e2)

    and ct_pred it bt =
      match it with
      | Representable (ct, t) ->
         term (representable_ctype 
                 (fun tag -> (SymMap.find tag SD.struct_decls))
                 ct t)
      | AlignedI t ->
         term (eq_ (rem_ (t.t, t.align), int_ 0))
      | Aligned (t, ct) ->
         let alignment = match ct with
           | Sctype (_, Function _) -> int_ 1
           | _ -> z_ (Memory.align_of_ctype ct)
         in
         term (eq_ (rem_ (t, alignment), int_ 0))

    and option_op it bt = 
      match it with
      | Something it ->
         let option_sort = sort_of_bt bt in
         let constructors = Z3.Datatype.get_constructors option_sort in
         let t, e = term it in
         (Z3.Expr.mk_app context (List.hd constructors) [t], e)
      | Nothing _ ->
         let option_sort = sort_of_bt bt in
         let constructors = Z3.Datatype.get_constructors option_sort in
         (Z3.Expr.mk_app context (List.hd (List.tl constructors)) [], [])
      | Is_some it -> 
         let option_sort = sort_of_bt (IT.bt it) in
         let recognisers = Z3.Datatype.get_recognizers option_sort in
         let t, e = term it in
         (Z3.Expr.mk_app context (List.hd recognisers) [t], e)
      | Value_of_some it -> 
         let option_sort = sort_of_bt (IT.bt it) in
         let accessors = Z3.Datatype.get_accessors option_sort in
         let t, e = term it in
         (Z3.Expr.mk_app context (List.hd (List.hd accessors)) [t], e)

    and param_op it bt = 
      match it with
      | Const t ->
         let t, e = term t in
         (Z3.Z3Array.mk_const_array context (sort_of_bt Integer) t, e)
      | Mod (t1, t2, t3) ->
         let t1, e1 = term t1 in
         let t2, e2 = term t2 in
         let t3, e3 = term t3 in
         (Z3.Z3Array.mk_store context t1 t2 t3, e1 @ e2 @ e3)
      | App (f, arg) ->
         begin match f with
         | IT (Param_op (Param (t_arg, body)),_) ->
            let subst = Subst.{before = (fst t_arg); after = arg} in
            term (IT.subst_it subst body)
         | _ ->
            let f, e1 = term f in
            let a, e2 = term arg in
            (Z3.Z3Array.mk_select context f a, e1 @ e2)
         end
      | Param ((i, abt), body) ->
         let array_s = Sym.fresh () in
         let array_t = Z3.Expr.mk_const context (sym_to_sym array_s) (sort_of_bt bt) in
         let body_t, body_e = term body in
         let select_t, select_e = term (app_ (sym_ (array_s, bt)) (sym_ (i, abt))) in
         let constr = 
           Z3.Quantifier.expr_of_quantifier (
           Z3.Quantifier.mk_forall_const context 
             [Z3.Expr.mk_const context (sym_to_sym i) (sort_of_bt abt)]
             (Z3.Boolean.mk_eq context select_t body_t)
             None 
             [Z3.Quantifier.mk_pattern context [select_t]]
             [] None None
           )
         in
         (array_t, constr :: select_e @ body_e)


    in
      

    fun it ->
      let () = Debug_ocaml.begin_csv_timing "of_index_term" in
      let expr = term it in
      let () = Debug_ocaml.end_csv_timing "of_index_term" in
      expr


  let expr = of_index_term



  let rec make_trigger = function
    | T_Term (IT (Lit (Sym s), bt)) -> 
       let t = Z3.Expr.mk_const context (sym_to_sym s) (sort_of_bt bt) in
       (bt, t, [])
    | T_Term it -> 
       let _, t1 = IT.fresh (IT.bt it) in
       let t1, e1 = of_index_term t1 in
       let t2, e2 = of_index_term it in
       (IT.bt it, t1, Z3.Boolean.mk_eq context t1 t2 :: e1 @ e2)
    | T_App (t, t') ->
       let (bt, t, cs) = make_trigger t in
       let (_, t', cs') = make_trigger t' in
       let (_, rbt) = param_bt bt in
       (rbt, Z3.Z3Array.mk_select context t t', cs @ cs')
    | T_Member (t, member) ->
       let (sbt, t, cs) = make_trigger t in
       let tag = match sbt with
         | Struct tag -> tag
         | _ -> Debug_ocaml.error "illtyped index term: not a struct"
       in
       let layout = SymMap.find tag SD.struct_decls in
       let members = List.map fst (Memory.member_types layout) in
       let bt = BT.of_sct (List.assoc Id.equal member (Memory.member_types layout)) in
       let destructors = Z3.Tuple.get_field_decls (sort_of_bt (Struct tag)) in
       let member_destructors = List.combine members destructors in
       let destructor = List.assoc Id.equal member member_destructors in
       (bt, Z3.Expr.mk_app context destructor [t], cs)


  let of_logical_constraint c = 
    match c with
    | T it -> 
       let t, e = of_index_term it in
       t :: e
    | Forall ((s, bt), trigger, body) ->
       let (triggers, cs) = match trigger with
         | Some trigger -> 
            let (_, t, cs) = make_trigger trigger in
            ([Z3.Quantifier.mk_pattern context [t]], cs)
         | None ->
            ([], [])
       in
       let body, cs' = of_index_term body in
       let q = 
         Z3.Quantifier.mk_forall_const context 
           [Z3.Expr.mk_const context (sym_to_sym s) (sort_of_bt bt)] 
           body 
           None triggers [] None None 
       in
       cs @ cs' @ [Z3.Quantifier.expr_of_quantifier q]


  let check (assumptions: Z3.Expr.expr list) (lc : LC.t) =  
    (* as similarly suggested by Robbert *)
    match lc with
    | T (IT (Bool_op (EQ (it, it')), _)) when IT.equal it it' ->
       let solver = Z3.Solver.mk_simple_solver context in
       (`YES, solver)
    | _ ->
       let solver = Z3.Solver.mk_simple_solver context in
       Z3.Solver.add solver [Z3.Boolean.mk_and context assumptions];
       begin
         match lc with
         | T t ->
            let t, e = of_index_term t in
            Z3.Solver.add solver (Z3.Boolean.mk_not context t :: e)
         | Forall ((s, bt), _trigger, t) -> 
            let s' = Sym.fresh () in
            let t = IndexTerms.subst_var Subst.{before=s; after=s'} t in
            let t, e = of_index_term t in
               Z3.Solver.add solver (Z3.Boolean.mk_not context t :: e)
       end;
       let result = 
         try Z3.Solver.check solver [] with
         | Z3.Error err -> 
            Debug_ocaml.error ("Z3 error: " ^ err)
       in
       match result with
       | Z3.Solver.UNSATISFIABLE -> (`YES, solver)
       | Z3.Solver.SATISFIABLE -> (`NO, solver)
       | Z3.Solver.UNKNOWN -> (`MAYBE, solver)

  let constr = of_logical_constraint


  let provable assumptions lc = 
    let (result, _solver) = check assumptions lc in
    match result with
    | `YES -> true
    | `NO -> false
    | `MAYBE -> false


  let provable_and_solver assumptions lc = 
    let (result, solver) = check assumptions lc in
    match result with
    | `YES -> (true, solver)
    | `NO -> (false, solver)
    | `MAYBE -> (false, solver)


  let provably_inconsistent assumptions = provable assumptions (t_ (bool_ false))

  let get_model solver = 
    Option.value_err "Z3 did not produce a counter model"
      (Z3.Solver.get_model solver)


end



