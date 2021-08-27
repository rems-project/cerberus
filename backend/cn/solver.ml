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



module BTtbl = Hashtbl.Make(BaseTypes)
module ITtbl = Hashtbl.Make(IndexTerms)


module type S = sig

  val provable : Z3.Solver.solver -> LC.t -> bool
  val provably_inconsistent : Z3.Solver.solver -> bool
  val get_model : Z3.Solver.solver -> Z3.Model.model
  val term : IT.t -> Z3.Expr.expr
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
    let (digest, id, _) = Sym.dest s in
    let str = string_of_int id ^"." ^ digest in
    Z3.Symbol.mk_string context str




  let sort =

    let unit_sort = Z3.Sort.mk_uninterpreted_s context "unit" in
    let bool_sort = Z3.Boolean.mk_sort context in
    let integer_sort = Z3.Arithmetic.Integer.mk_sort context in
    let real_sort = Z3.Arithmetic.Real.mk_sort context in

    let rec translate = function
      | Unit -> 
         unit_sort
      | Bool -> 
         bool_sort
      | Integer -> 
         integer_sort
      | Real -> 
         real_sort
      | Loc -> 
         integer_sort
      | List bt ->
         Z3.Z3List.mk_sort context (bt_symbol bt) (translate bt) 
      | Tuple bts ->
         let field_symbols = List.mapi (fun i _ -> tuple_field_symbol i) bts in
         let sorts = List.map translate bts in
         Z3.Tuple.mk_sort context (bt_symbol (Tuple bts)) field_symbols sorts
      | Struct tag ->
         let layout = SymMap.find tag SD.struct_decls in
         let members = Memory.member_types layout in
         let member_symbols = List.map (fun (id,_) -> member_symbol (BT.Struct tag) id) members in
         let member_sorts = 
           List.map (fun (_, sct) -> 
               translate (BT.of_sct sct)
             ) members 
         in
         Z3.Tuple.mk_sort context (bt_symbol (Struct tag)) 
           member_symbols member_sorts
      | Set bt ->
         Z3.Set.mk_sort context (translate bt)
      | Option bt ->
         let a_sort = translate bt in
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
      | Array (abt, rbt) ->
         Z3.Z3Array.mk_sort context (translate abt) (translate rbt)
    in    

    let sort = 
      let tbl = BTtbl.create 10 in
      fun bt ->
      match BTtbl.find_opt tbl bt with
      | Some sort -> sort
      | None ->
         let sort = translate bt in
         let () = BTtbl.add tbl bt sort in
         sort
    in

    sort



  let term : IT.t -> Z3.Expr.expr =

    let unit_term = Z3.Expr.mk_fresh_const context "unit" (sort Unit) in
    let true_term = Z3.Boolean.mk_true context in
    let false_term = Z3.Boolean.mk_false context in

    let rec translate (IT (it_, bt)) =
      begin match it_ with
      | Lit lit -> 
         begin match lit with
         | Sym s ->    
            Z3.Expr.mk_const context (sym_to_sym s) (sort bt)
         | Z z ->
            Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
         | Q (i,i') ->
            Z3.Arithmetic.Real.mk_numeral_nd context i i'
         | Pointer z ->
            Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
         | Bool true ->
            true_term
         | Bool false ->
            false_term
         | Unit ->
            unit_term
         | Default bt -> 
            let sym = Z3.Symbol.mk_string context ("default" ^ (bt_name bt)) in
            Z3.Expr.mk_const context sym (sort bt)
         end
      | Arith_op arith_op -> 
         begin match arith_op with
         | Add (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_add context [t1; t2]
         | Sub (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_sub context [t1; t2]
         | Mul (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_mul context [t1; t2]
         | Div (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_div context t1 t2
         | Exp (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_power context t1 t2
         | Rem (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.Integer.mk_rem context t1 t2
         end
      | Bool_op bool_op -> 
         begin match bool_op with
         | And ts -> 
            let ts = List.map term ts in
            Z3.Boolean.mk_and context ts
         | Or ts -> 
            let ts = List.map term ts in
            Z3.Boolean.mk_or context ts
         | Impl (t1, t2) -> 
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Boolean.mk_implies context t1 t2
         | Not t ->
            let t = term t in
            Z3.Boolean.mk_not context t
         | ITE (t1, t2, t3) ->
            let t1 = term t1 in
            let t2 = term t2 in
            let t3 = term t3 in
            Z3.Boolean.mk_ite context t1 t2 t3
         | EQ (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Boolean.mk_eq context t1 t2
         end
      | Cmp_op cmp_op -> 
         begin match cmp_op with
         | LT (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_lt context t1 t2
         | LE (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_le context t1 t2
         end
      | Tuple_op tuple_op -> 
         begin match tuple_op with
         | Tuple ts ->
            let ts = List.map term ts in
            let constructor = Z3.Tuple.get_mk_decl (sort bt) in
            Z3.Expr.mk_app context constructor ts
         | NthTuple (n, t) ->
            let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
            let t = term t in
            Z3.Expr.mk_app context (List.nth destructors n) [t]
         end
      | Struct_op struct_op -> 
         begin match struct_op with
         | Struct (tag, mts) ->
            let constructor = Z3.Tuple.get_mk_decl (sort bt) in
            let mts = (List.map (fun (_, t) -> term t) mts) in
            Z3.Expr.mk_app context constructor mts
         | StructMember (t, member) ->
            let tag = BT.struct_bt (IT.bt t) in
            let layout = SymMap.find tag SD.struct_decls in
            let members = List.map fst (Memory.member_types layout) in
            let destructors = Z3.Tuple.get_field_decls (sort (Struct tag)) in
            let member_destructors = List.combine members destructors in
            let destructor = List.assoc Id.equal member member_destructors in
            let t = term t in
            Z3.Expr.mk_app context destructor [t]
         end
      | Pointer_op pointer_op -> 
         begin match pointer_op with
         | Null ->
            term (int_ 0)
         | AddPointer (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_add context [t1; t2]
         | SubPointer (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_sub context [t1; t2]
         | MulPointer (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_mul context [t1; t2]
         | LTPointer (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_lt context t1 t2
         | LEPointer (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Arithmetic.mk_le context t1 t2
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
            term (int_ offset)
         | ArrayOffset (ct, t) ->
            term (mul_ (int_ (Memory.size_of_ctype ct), t))
         end
      | List_op t -> 
         Debug_ocaml.error "todo: SMT mapping for list operations"
      | Set_op set_op -> 
         begin match set_op with
         | SetMember (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Set.mk_membership context t1 t2
         | SetUnion ts ->
            let ts = List.map term (List1.to_list ts) in
            Z3.Set.mk_union context ts
         | SetIntersection ts ->
            let ts = List.map term (List1.to_list ts) in
            Z3.Set.mk_intersection context ts
         | SetDifference (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Set.mk_difference context t1 t2
         | Subset (t1, t2) ->
            let t1 = term t1 in
            let t2 = term t2 in
            Z3.Set.mk_subset context t1 t2
         end
      | CT_pred ct_pred -> 
         begin match ct_pred with
         | Representable (ct, t) ->
            let sdecl_lookup tag = SymMap.find tag SD.struct_decls in
            term (representable_ctype sdecl_lookup ct t)
         | AlignedI t ->
            term (eq_ (rem_ (t.t, t.align), int_ 0))
         | Aligned (t, ct) ->
            let alignment = match ct with
              | Sctype (_, Function _) -> int_ 1
              | _ -> int_ (Memory.align_of_ctype ct)
            in
            term (eq_ (rem_ (t, alignment), int_ 0))
         end
      | Option_op option_op -> 
         begin match option_op with
         | Something t ->
            let option_sort = sort bt in
            let constructors = Z3.Datatype.get_constructors option_sort in
            Z3.Expr.mk_app context (List.hd constructors) [term t]
         | Nothing _ ->
            let option_sort = sort bt in
            let constructors = Z3.Datatype.get_constructors option_sort in
            Z3.Expr.mk_app context (List.hd (List.tl constructors)) []
         | Is_some t -> 
            let option_sort = sort (IT.bt t) in
            let recognisers = Z3.Datatype.get_recognizers option_sort in
            Z3.Expr.mk_app context (List.hd recognisers) [term t]
         | Value_of_some t -> 
            let option_sort = sort (IT.bt t) in
            let accessors = Z3.Datatype.get_accessors option_sort in
            Z3.Expr.mk_app context (List.hd (List.hd accessors)) [term t]
         end
      | Array_op array_op -> 
         begin match array_op with
         | Const t ->
            let t = term t in
            Z3.Z3Array.mk_const_array context (sort Integer) t
         | Mod (t1, t2, t3) ->
            let t1 = term t1 in
            let t2 = term t2 in
            let t3 = term t3 in
            Z3.Z3Array.mk_store context t1 t2 t3
         | App (f, arg) ->
            let f = term f in
            let a = term arg in
            Z3.Z3Array.mk_select context f a
         end
      end
  
    and term : IT.t -> Z3.Expr.expr =
      let tbl = ITtbl.create 5000 in
      fun it ->
      match ITtbl.find_opt tbl it with
      | Some sc -> sc
      | None ->
         let t = translate it in
         let () = ITtbl.add tbl it t in
         t
    in
      
    term



  let rec make_trigger = function
    | T_Term (IT (Lit (Sym s), bt)) -> 
       let t = Z3.Expr.mk_const context (sym_to_sym s) (sort bt) in
       (bt, t, [])
    | T_Term it -> 
       let _, t1 = IT.fresh (IT.bt it) in
       let t1 = term t1 in
       let t2 = term it in
       (IT.bt it, t1, [Z3.Boolean.mk_eq context t1 t2])
    | T_App (t, t') ->
       let (bt, t, cs) = make_trigger t in
       let (_, t', cs') = make_trigger t' in
       let (_, rbt) = BT.array_bt bt in
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
       let destructors = Z3.Tuple.get_field_decls (sort (Struct tag)) in
       let member_destructors = List.combine members destructors in
       let destructor = List.assoc Id.equal member member_destructors in
       (bt, Z3.Expr.mk_app context destructor [t], cs)


  let of_logical_constraint c = 
    match c with
    | T it -> 
       [term it]
    | Forall ((s, bt), trigger, body) ->
       let (triggers, cs) = match trigger with
         | Some trigger -> 
            let (_, t, cs) = make_trigger trigger in
            ([Z3.Quantifier.mk_pattern context [t]], cs)
         | None ->
            ([], [])
       in
       let q = 
         Z3.Quantifier.mk_forall_const context 
           [Z3.Expr.mk_const context (sym_to_sym s) (sort bt)] 
           (term body) 
           None triggers [] None None 
       in
       Z3.Quantifier.expr_of_quantifier q :: cs


  let check solver (lc : LC.t) =  
    let () = Debug_ocaml.begin_csv_timing "solver" in
    let result = match lc with
      (* as similarly suggested by Robbert *)
      | T (IT (Bool_op (EQ (it, it')), _)) when IT.equal it it' ->
         let solver = Z3.Solver.mk_simple_solver context in
         (`YES, solver)
      | _ ->
         let result = match lc with
           | T t ->
              let t = term t in
              Z3.Solver.check solver [Z3.Boolean.mk_not context t]
           | Forall ((s, bt), _trigger, t) -> 
              let s' = Sym.fresh () in
              let t = IT.subst [(s, sym_ (s', bt))] t in
              Z3.Solver.check solver [Z3.Boolean.mk_not context (term t)]
         in
         match result with
         | Z3.Solver.UNSATISFIABLE -> (`YES, solver)
         | Z3.Solver.SATISFIABLE -> (`NO, solver)
         | Z3.Solver.UNKNOWN -> (`MAYBE, solver)
    in
    let () = Debug_ocaml.end_csv_timing "solver" in
    result

  
  let constr = of_logical_constraint


  let provable assumptions lc = 
    let (result, _solver) = check assumptions lc in
    match result with
    | `YES -> true
    | `NO -> false
    | `MAYBE -> false


  let provably_inconsistent assumptions = provable assumptions (t_ (bool_ false))

  let get_model solver = 
    Option.value_err "Z3 did not produce a counter model"
      (Z3.Solver.get_model solver)


end



