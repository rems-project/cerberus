open IndexTerms
open BaseTypes
module SymMap=Map.Make(Sym)
module IT = IndexTerms
module LC = LogicalConstraints
open LogicalConstraints
open List1
open List
open Pp



let context_params = [
    ("model", "true");
    ("well_sorted_check","true");
    (* ("trace", "true");
     * ("trace_file_name", "trace.smt") *)
  ]

let global_params = [
    ("smt.auto-config", "false");
    ("smt.mbqi", "true");
    ("smt.arith.solver", "2");
    ("model.completion", "true");
    ("model_evaluator.completion", "true");
    (* ("model.compact", "true"); *)
    ("model.inline_def", "true");
    ("model_evaluator.array_as_stores", "true");
    (* ("model_evaluator.array_equalities", "false"); *)
    (* ("smt.ematching", "true"); *)
    (* ("smt.pull-nested-quantifiers", "true"); *)
    (* ("smt.macro_finder", "true"); *)
  ]



let context = Z3.mk_context context_params 

let () = List.iter (fun (c,v) -> Z3.set_global_param c v) global_params



module Sort_HashedType = struct
  type t = Z3.Sort.sort
  let equal = Z3.Sort.equal
  let hash s = Z3.Sort.get_id s
end

(* all our symbols are created with strings *)
let z3_symbol_equal s s' = 
  String.equal (Z3.Symbol.get_string s) (Z3.Symbol.get_string s')

module Z3Symbol_HashedType = struct
  type t = Z3.Symbol.symbol
  let equal = z3_symbol_equal
  let hash s = 
    (* rubbish hash function *)
    String.length (Z3.Symbol.get_string s)
end

module BT_Sort_Table = TwoMap.Make(BT)(Sort_HashedType)
module IT_Table = Hashtbl.Make(IndexTerms)
module Z3Symbol_Table = Hashtbl.Make(Z3Symbol_HashedType)



module type S = sig

  val sort : BT.t -> Z3.Sort.sort
  val provable : Z3.Solver.solver -> LC.t -> bool
  val model : Z3.Solver.solver -> Z3.Model.model
  val term : IT.t -> Z3.Expr.expr
  val lambda : (Sym.t * BT.t) -> IT.t -> Z3.Expr.expr
  val constr : LC.t -> Z3.Expr.expr list

  val z3_sort : Z3.Sort.sort -> BT.t
  val z3_expr : Z3.Expr.expr -> IT.t option

end




module Make (SD : sig val struct_decls : Memory.struct_decls end) : S = struct

  let bt_sort_table = BT_Sort_Table.create 1000
  let member_funcdecl_table = Z3Symbol_Table.create 100
  let struct_funcdecl_table = Z3Symbol_Table.create 100


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



  let unit_sort = Z3.Sort.mk_uninterpreted_s context "unit"
  let bool_sort = Z3.Boolean.mk_sort context
  let integer_sort = Z3.Arithmetic.Integer.mk_sort context
  let real_sort = Z3.Arithmetic.Real.mk_sort context

  let loc_to_integer_symbol = Z3.Symbol.mk_string context "loc_to_integer"
  let loc_sort_symbol = bt_symbol Loc
  let loc_sort = Z3.Tuple.mk_sort context loc_sort_symbol [loc_to_integer_symbol] [integer_sort]

  let loc_to_integer_fundecl = nth (Z3.Tuple.get_field_decls loc_sort) 0
  let integer_to_loc_fundecl = Z3.Tuple.get_mk_decl loc_sort
  let integer_to_loc_symbol = Z3.FuncDecl.get_name integer_to_loc_fundecl

  let loc_to_integer l = Z3.Expr.mk_app context loc_to_integer_fundecl [l]
  let integer_to_loc i = Z3.Expr.mk_app context integer_to_loc_fundecl [i]


  let sort =


    let rec translate = function
      | Unit -> unit_sort
      | Bool -> bool_sort
      | Integer -> integer_sort
      | Real -> real_sort
      | Loc -> loc_sort
      | List bt -> Z3.Z3List.mk_sort context (bt_symbol bt) (translate bt) 
      | Set bt -> Z3.Set.mk_sort context (translate bt)
      | Array (abt, rbt) -> Z3.Z3Array.mk_sort context (translate abt) (translate rbt)
      | Tuple bts ->
         let field_symbols = mapi (fun i _ -> tuple_field_symbol i) bts in
         let sorts = map translate bts in
         Z3.Tuple.mk_sort context (bt_symbol (Tuple bts)) field_symbols sorts
      | Struct tag ->
         let struct_symbol = bt_symbol (Struct tag) in
         Z3Symbol_Table.add struct_funcdecl_table struct_symbol tag;
         let layout = SymMap.find tag SD.struct_decls in
         let member_symbols, member_sorts = 
           map_split (fun (id,sct) -> 
               let s = member_symbol tag id in
               Z3Symbol_Table.add member_funcdecl_table s (tag, id);
               (s, translate (BT.of_sct sct))
             ) (Memory.member_types layout)
         in
         Z3.Tuple.mk_sort context struct_symbol
           member_symbols member_sorts
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



  let sym_to_sym s = 
    Z3.Symbol.mk_string context (CF.Pp_symbol.to_string_pretty_cn s)


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
         | Q q -> 
            Z3.Arithmetic.Real.mk_numeral_s context (Q.to_string q)
         | Pointer z -> 
            integer_to_loc
              (Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z))
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
         let open Z3.Arithmetic in
         begin match arith_op with
         | Add (t1, t2) -> mk_add context [term t1; term t2]
         | Sub (t1, t2) -> mk_sub context [term t1; term t2]
         | Mul (t1, t2) -> mk_mul context [term t1; term t2]
         | Div (t1, t2) -> mk_div context (term t1) (term t2)
         | Exp (t1, t2) -> mk_power context (term t1) (term t2)
         | Rem (t1, t2) -> Integer.mk_rem context (term t1) (term t2)
         | Mod (t1, t2) -> Integer.mk_mod context (term t1) (term t2)
         | LT (t1, t2) -> mk_lt context (term t1) (term t2)
         | LE (t1, t2) -> mk_le context (term t1) (term t2)
         end
      | Bool_op bool_op -> 
         let open Z3.Boolean in
         begin match bool_op with
         | And ts -> mk_and context (map term ts)
         | Or ts -> mk_or context (map term ts)
         | Impl (t1, t2) -> mk_implies context (term t1) (term t2)
         | Not t -> mk_not context (term t)
         | ITE (t1, t2, t3) -> mk_ite context (term t1) (term t2) (term t3)
         | EQ (t1, t2) -> mk_eq context (term t1) (term t2)
         | EachI ((i1, s, i2), t) -> 
             let rec aux i = 
               if i <= i2 
               then IT.subst [(s, int_ i)] t :: aux (i + 1)
               else []
             in
             term (and_ (aux i1))
         end
      | Tuple_op tuple_op -> 
         begin match tuple_op with
         | Tuple ts ->
            let constructor = Z3.Tuple.get_mk_decl (sort bt) in
            Z3.Expr.mk_app context constructor (map term ts)
         | NthTuple (n, t) ->
            let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
            Z3.Expr.mk_app context (nth destructors n) [term t]
         end
      | Struct_op struct_op -> 
         begin match struct_op with
         | Struct (tag, mts) ->
            let constructor = Z3.Tuple.get_mk_decl (sort bt) in
            Z3.Expr.mk_app context constructor (map (fun (_, t) -> term t) mts)
         | StructMember (t, member) ->
            let layout = SymMap.find (struct_bt (IT.bt t)) SD.struct_decls in
            let n = Option.get (Memory.member_number layout member) in
            let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
            Z3.Expr.mk_app context (nth destructors n) [term t]
         end
      | Pointer_op pointer_op -> 
         let open Z3.Arithmetic in
         begin match pointer_op with
         | Null -> 
            integer_to_loc
              (term (int_ 0))
         | AddPointer (t1, t2) -> 
            integer_to_loc
              (mk_add context [loc_to_integer (term t1); term t2])
         | SubPointer (t1, t2) -> 
            integer_to_loc
              (mk_sub context [loc_to_integer (term t1); term t2])
         | MulPointer (t1, t2) -> 
            integer_to_loc
              (mk_mul context [loc_to_integer (term t1); term t2])
         | LTPointer (t1, t2) -> 
            mk_lt context (loc_to_integer (term t1)) 
              (loc_to_integer (term t2))
         | LEPointer (t1, t2) -> 
            mk_le context (loc_to_integer (term t1))
              (loc_to_integer (term t2))
         | IntegerToPointerCast t -> 
            integer_to_loc (term t)
         | PointerToIntegerCast t -> 
            loc_to_integer (term t)
         | MemberOffset (tag, member) ->
            let decl = SymMap.find tag SD.struct_decls in
            term (int_ (Option.get (Memory.member_offset decl member)))
         | ArrayOffset (ct, t) -> 
            term (mul_ (int_ (Memory.size_of_ctype ct), t))
         end
      | List_op t -> 
         Debug_ocaml.error "todo: SMT mapping for list operations"
      | Set_op set_op -> 
         let open Z3.Set in
         begin match set_op with
         | SetMember (t1, t2) -> mk_membership context (term t1) (term t2)
         | SetUnion ts -> mk_union context (map term (to_list ts))
         | SetIntersection ts -> mk_intersection context (map term (to_list ts))
         | SetDifference (t1, t2) -> mk_difference context (term t1) (term t2)
         | Subset (t1, t2) -> mk_subset context (term t1) (term t2)
         end
      | CT_pred ct_pred -> 
         begin match ct_pred with
         | AlignedI t ->
            term (eq_ (rem_ (pointerToIntegerCast_ t.t, t.align), int_ 0))
         | Aligned (t, ct) ->
            term (alignedI_ ~t ~align:(int_ (Memory.align_of_ctype ct)))
         | Representable (ct, t) ->
            let sdecl_lookup tag = SymMap.find tag SD.struct_decls in
            term (representable sdecl_lookup ct t)
         | Good (ct, t) ->
            let sdecl_lookup tag = SymMap.find tag SD.struct_decls in
            term (good_value sdecl_lookup ct t)
         end
      | Array_op array_op -> 
         let open Z3.Z3Array in
         begin match array_op with
         | Const (abt, t) -> 
            mk_const_array context (sort abt) (term t)
         | Set (t1, t2, t3) -> 
            mk_store context (term t1) (term t2) (term t3)
         | Get (IT (Array_op (Def ((s, bt), body)), _), arg) -> 
            term (IT.subst [(s, arg)] body)
         | Get (f, arg) -> 
            mk_select context (term f) (term arg)
         | Def ((q_s, q_bt), body) ->
            (* warn (!^"generating lambda" ^^ colon ^^^ IT.pp (IT (it_, bt))); *)
            warn (!^"generating lambda");
            Z3.Quantifier.expr_of_quantifier
              (Z3.Quantifier.mk_lambda_const context
                 [term (sym_ (q_s, q_bt))] (term body))
         end
      end
  
    and term : IT.t -> Z3.Expr.expr =
      let tbl = IT_Table.create 5000 in
      fun it ->
      match IT_Table.find_opt tbl it with
      | Some sc -> sc
      | None ->
         let t = translate it in
         let () = IT_Table.add tbl it t in
         t
    in
      
    term


  let lambda (q_s, q_bt) body = 
    Z3.Quantifier.expr_of_quantifier
      (Z3.Quantifier.mk_lambda_const context
         [term (sym_ (q_s, q_bt))] (term body))
      



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
         | Z3.Solver.UNKNOWN -> 
            warn !^"solver returned unknown";
            `MAYBE
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




  let z3_sort (sort : Z3.Sort.sort) = 
    Option.get (BT_Sort_Table.right_to_left bt_sort_table sort)

  exception Unsupported of string


  let z3_expr = 
    let counter = ref 0 in
    let new_q () = 
      let c = !counter in 
      let () = counter := c+1 in
      Sym.fresh_pretty ("p" ^ string_of_int c)
    in
    let rec aux (binders : (Sym.t * BT.t) list) (expr : Z3.Expr.expr) : IT.t = 
      let unsupported what = 
        let err = 
          Printf.sprintf "unsupported %s. expr: %s"
            what (Z3.Expr.to_string expr)
        in
        raise (Unsupported err)
      in
      let args = try Z3.Expr.get_args expr with | _ -> [] in
      let args = List.map (aux binders) args in
      match () with

      | () when Z3.AST.is_quantifier (Z3.Expr.ast_of_expr expr) ->
         let qexpr = Z3.Quantifier.quantifier_of_expr expr in
         let body = Z3.Quantifier.get_body qexpr in
         let quantifier_sorts = Z3.Quantifier.get_bound_variable_sorts qexpr in
         let q_bt = match quantifier_sorts with
           | [q_sort] -> z3_sort q_sort
           | _ -> unsupported "z3 quantifier list"
         in
         let q_s = new_q () in
         array_def_ (q_s, q_bt) (aux ((q_s, q_bt) :: binders) body)

      | () when Z3.Arithmetic.is_add expr ->
         List.fold_left (Tools.curry add_) (hd args) (tl args)

      | () when Z3.Boolean.is_and expr ->
         and_ args

      | () when Z3.Z3Array.is_as_array expr ->
         unsupported "z3 as-array"         

      | () when Z3.Z3Array.is_constant_array expr ->
         let abt = z3_sort (Z3.Z3Array.get_range (Z3.Expr.get_sort expr)) in
         const_ abt (hd args)

      | () when Z3.Z3Array.is_default_array expr ->
         unsupported "z3 array default"

      | () when Z3.Set.is_difference expr ->
         setDifference_ (nth args 0, nth args 1)

      | () when Z3.Boolean.is_distinct expr ->
         unsupported "z3 is_distinct"

      | () when Z3.Arithmetic.is_idiv expr ->
         div_ (nth args 0, nth args 1)

      | () when Z3.Boolean.is_eq expr ->
         eq_ (nth args 0, nth args 1)

      | () when Z3.Boolean.is_false expr ->
         bool_ false

      | () when Z3.Arithmetic.is_ge expr ->
         ge_ (nth args 0, nth args 1)

      | () when Z3.Arithmetic.is_gt expr ->
         gt_ (nth args 0, nth args 1)

      | () when Z3.Boolean.is_implies expr ->
         impl_ (nth args 0, nth args 1)

      | () when Z3.Arithmetic.is_int_numeral expr ->
         z_ (Z3.Arithmetic.Integer.get_big_int expr)

      | () when  Z3.Set.is_intersect expr ->
         setIntersection_ (List1.make (hd args, tl args))

      | () when Z3.Boolean.is_ite expr ->
         ite_ (nth args 0, nth args 1, nth args 2)

      | () when Z3.Arithmetic.is_le expr ->
         le_ (nth args 0, nth args 1)

      | () when Z3.Arithmetic.is_lt expr ->
         lt_ (nth args 0, nth args 1)

      | () when Z3.Arithmetic.is_modulus expr ->
         mod_ (nth args 0, nth args 1)

      | () when Z3.Arithmetic.is_mul expr ->
         mul_ (nth args 0, nth args 1)

      | () when Z3.Boolean.is_not expr ->
         not_ (nth args 0)

      | () when Z3.Boolean.is_or expr ->
         or_ args

      | () when Z3.Arithmetic.is_rat_numeral expr ->
         q1_ (Z3.Arithmetic.Real.get_ratio expr)

      | () when Z3.Arithmetic.is_remainder expr ->
         rem_ (nth args 0, nth args 1)

      | () when Z3.Z3Array.is_select expr ->
         get_ (nth args 0) (nth args 1)

      | () when Z3.Z3Array.is_store expr ->
         set_ (nth args 0) (nth args 1, nth args 2)

      | () when Z3.Arithmetic.is_sub expr ->
         sub_ (nth args 0, nth args 1)

      | () when Z3.Set.is_subset expr ->
         subset_ (nth args 0, nth args 1)

      | () when Z3.Boolean.is_true expr ->
         bool_ true

      | () when Z3.Arithmetic.is_uminus expr ->
         let arg = nth args 0 in
         begin match IT.bt arg with
         | Integer -> sub_ (int_ 0, arg)
         | Real -> sub_ (q_ (0, 1), arg)
         | _ -> Debug_ocaml.error "illtyped index term"
         end

      | () when Z3.Set.is_union expr ->
         setUnion_ (List1.make (hd args, tl args))

      | () when Z3.AST.is_var (Z3.Expr.ast_of_expr expr) ->
         sym_ (nth binders (Z3.Quantifier.get_index expr))

      | () ->
        let func_decl = Z3.Expr.get_func_decl expr in
        let func_name = Z3.FuncDecl.get_name func_decl in
        match () with

        | () when z3_symbol_equal func_name loc_to_integer_symbol ->
           let p = nth args 0 in
           begin match IT.is_pointer p with
           | Some z -> z_ z
           | _ -> pointerToIntegerCast_ (nth args 0)
           end

        | () when z3_symbol_equal func_name integer_to_loc_symbol ->
           let i = nth args 0 in
           begin match IT.is_z i with
           | Some z -> pointer_ z
           | _ -> integerToPointerCast_ i
           end

        | () when Z3Symbol_Table.mem member_funcdecl_table func_name ->
           let (tag, member) = Z3Symbol_Table.find member_funcdecl_table func_name in
           let sd = Memory.member_types (SymMap.find tag SD.struct_decls) in
           let member_bt = BT.of_sct (List.assoc Id.equal member sd) in
           member_ ~member_bt (tag, nth args 0, member)

        | () when Z3Symbol_Table.mem struct_funcdecl_table func_name ->
           let tag = Z3Symbol_Table.find struct_funcdecl_table func_name in
           let sd = Memory.members (SymMap.find tag SD.struct_decls) in
           struct_ (tag, List.combine sd args)

        | () ->
           unsupported "z3 expression"

    in

    fun expr -> 
    try Some (aux [] expr) with
    | Unsupported err -> None

      

end

