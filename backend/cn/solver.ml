open IndexTerms
open BaseTypes
module SymMap=Map.Make(Sym)
module IT = IndexTerms
module LC = LogicalConstraints
open LogicalConstraints


let context_params = [
    ("model", "true");
    ("well_sorted_check","true");
    (* ("trace", "true");
     * ("trace_file_name", "trace.smt") *)
  ]

let global_params = [
    ("smt.auto-config", "false");
    ("smt.mbqi", "true");
    (* ("smt.ematching", "true");
     * ("smt.pull-nested-quantifiers", "true");
     * ("smt.macro_finder", "true"); *)
    ("smt.arith.solver", "2");
    (* ("model.compact", "true"); *)
    ("model.completion", "true");
    (* ("model.inline_def", "true"); *)
    ("model_evaluator.completion", "true");
    (* ("model_evaluator.array_as_stores", "true"); *)
    (* ("model_evaluator.array_equalities", "false"); *)
  ]



let context = Z3.mk_context context_params 

let () = List.iter (fun (c,v) -> Z3.set_global_param c v) global_params



module Sort_HashedType = struct
  type t = Z3.Sort.sort
  let equal = Z3.Sort.equal
  let hash s = Z3.Sort.get_id s
end



module BT_Sort_Table = TwoMap.Make(BT)(Sort_HashedType)
module ITtbl = Hashtbl.Make(IndexTerms)





module type S = sig

  val sort : BT.t -> Z3.Sort.sort
  val provable : Z3.Solver.solver -> LC.t -> bool
  val model : Z3.Solver.solver -> Z3.Model.model
  val term : IT.t -> Z3.Expr.expr
  val lambda : (Sym.t * BT.t) -> IT.t -> Z3.Expr.expr
  val constr : LC.t -> Z3.Expr.expr list

end




module Make (SD : sig val struct_decls : Memory.struct_decls end) : S = struct

  let bt_sort_table = BT_Sort_Table.create 1000

  let bt_name bt = 
    Pp.plain (BT.pp bt)
  let bt_symbol bt = 
    Z3.Symbol.mk_string context (bt_name bt)

  let tuple_field_name i = 
    "comp" ^ string_of_int i
  let tuple_field_symbol i = 
    Z3.Symbol.mk_string context (tuple_field_name i)

  let member_name tag id = 
    bt_name (BT.Struct tag) ^ "_" ^ Id.s id
  let member_symbol tag id = 
    Z3.Symbol.mk_string context (member_name tag id)

  let sym_to_sym s = Z3.Symbol.mk_string context (CF.Pp_symbol.to_string_pretty s)


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
         let member_symbols, member_sorts = 
           List.map_split (fun (id,sct) -> 
               (member_symbol tag id, translate (BT.of_sct sct))
             ) (Memory.member_types layout)
         in
         Z3.Tuple.mk_sort context (bt_symbol (Struct tag)) 
           member_symbols member_sorts
      | Set bt ->
         Z3.Set.mk_sort context (translate bt)
      | Array (abt, rbt) ->
         Z3.Z3Array.mk_sort context (translate abt) (translate rbt)
    in

    let sort bt = 
      match BT_Sort_Table.left_to_right bt_sort_table bt with
      | Some sort -> sort
      | None ->
         let sort = translate bt in
         let () = BT_Sort_Table.add bt_sort_table (bt, sort) in
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
            let constructor = Z3.Tuple.get_mk_decl (sort bt) in
            let ts = List.map term ts in
            Z3.Expr.mk_app context constructor ts
         | NthTuple (n, t) ->
            let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
            Z3.Expr.mk_app context (List.nth destructors n) [term t]
         end
      | Struct_op struct_op -> 
         begin match struct_op with
         | Struct (tag, mts) ->
            let constructor = Z3.Tuple.get_mk_decl (sort bt) in
            let mts = (List.map (fun (_, t) -> term t) mts) in
            Z3.Expr.mk_app context constructor mts
         | StructMember (t, member) ->
            let layout = SymMap.find (struct_bt (IT.bt t)) SD.struct_decls in
            let n = Option.get (Memory.member_number layout member) in
            let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
            Z3.Expr.mk_app context (List.nth destructors n) [term t]
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
      | Array_op array_op -> 
         begin match array_op with
         | Const (index_bt, t) ->
            let t = term t in
            Z3.Z3Array.mk_const_array context (sort index_bt) t
         | Set (t1, t2, t3) ->
            let t1 = term t1 in
            let t2 = term t2 in
            let t3 = term t3 in
            Z3.Z3Array.mk_store context t1 t2 t3
         | Get (IT (Array_op (Def ((s, bt), body)), _), arg) ->
            term (IT.subst [(s, arg)] body)
         | Get (f, arg) ->
            let f = term f in
            let a = term arg in
            Z3.Z3Array.mk_select context f a
         | Def _ ->
            let it_pp = Pp.plain (IT.pp (IT (it_, bt))) in
            Debug_ocaml.error ("uninstantiated array definition: " ^ it_pp)
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


  let lambda (q_s, q_bt) body = 
    let q = term (sym_ (q_s, q_bt)) in
    Z3.Quantifier.expr_of_quantifier
      (Z3.Quantifier.mk_lambda_const context
         [q] (term body))
      



  (* let rec make_trigger = function
   *   | T_Term (IT (Lit (Sym s), bt)) -> 
   *      let t = Z3.Expr.mk_const context (sym_to_sym s) (sort bt) in
   *      (bt, t, [])
   *   | T_Term it -> 
   *      let _, t1 = IT.fresh (IT.bt it) in
   *      let t1 = term t1 in
   *      let t2 = term it in
   *      (IT.bt it, t1, [Z3.Boolean.mk_eq context t1 t2])
   *   | T_Get (t, t') ->
   *      let (bt, t, cs) = make_trigger t in
   *      let (_, t', cs') = make_trigger t' in
   *      let (_, rbt) = BT.array_bt bt in
   *      (rbt, Z3.Z3Array.mk_select context t t', cs @ cs')
   *   | T_Member (t, member) ->
   *      let (sbt, t, cs) = make_trigger t in
   *      let tag = match sbt with
   *        | Struct tag -> tag
   *        | _ -> Debug_ocaml.error "illtyped index term: not a struct"
   *      in
   *      let layout = SymMap.find tag SD.struct_decls in
   *      let members = List.map fst (Memory.member_types layout) in
   *      let bt = BT.of_sct (List.assoc Id.equal member (Memory.member_types layout)) in
   *      let destructors = Z3.Tuple.get_field_decls (sort (Struct tag)) in
   *      let member_destructors = List.combine members destructors in
   *      let destructor = List.assoc Id.equal member member_destructors in
   *      (bt, Z3.Expr.mk_app context destructor [t], cs) *)


  let constr c = 
    match c with
    | T it -> 
       [term it]
    | Forall ((s, bt), body) ->
       let (triggers, cs) = 
         (* match trigger with
          * | Some trigger -> 
          *    let (_, t, cs) = make_trigger trigger in
          *    ([Z3.Quantifier.mk_pattern context [t]], cs)
          * | None -> *)
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
      (* problematic for getting a model out *)
      (* (\* as similarly suggested by Robbert *\)
       * | T (IT (Bool_op (EQ (it, it')), _)) when IT.equal it it' ->
       *    (`YES, solver) *)
      | _ ->
         let result = match lc with
           | T t ->
              let t = term t in
              Z3.Solver.check solver [Z3.Boolean.mk_not context t]
           | Forall ((s, bt), t) -> 
              let s' = Sym.fresh () in
              let t = IT.subst [(s, sym_ (s', bt))] t in
              Z3.Solver.check solver [Z3.Boolean.mk_not context (term t)]
         in
         match result with
         | Z3.Solver.UNSATISFIABLE -> `YES
         | Z3.Solver.SATISFIABLE -> `NO
         | Z3.Solver.UNKNOWN -> `MAYBE
    in
    let () = Debug_ocaml.end_csv_timing "solver" in
    result

  

  let provable solver lc = 
    let result = check solver lc in
    match result with
    | `YES -> true
    | `NO -> false
    | `MAYBE -> 
       let open Pp in
       print stdout (item "MAYBE" !^(Z3.Solver.get_reason_unknown solver) ^^ comma ^^^ item "LC" (LC.pp lc));
       (* print stdout (item "ASSUMPTIONS:" (list (fun e -> string (Z3.Expr.to_string e)) (Z3.Solver.get_assertions solver))); *)
       false


  let model solver = 
    Option.value_err "Z3 did not produce a counter model"
      (Z3.Solver.get_model solver)










  


end



