module CF = Cerb_frontend
open IndexTerms
open BaseTypes
module SymMap=Map.Make(Sym)
module IT = IndexTerms
module LC = LogicalConstraints
open LogicalConstraints
open List
open Pp
open Global
open LogicalPredicates


type solver = { fancy: Z3.Solver.solver }
type expr = Z3.Expr.expr
type sort = Z3.Sort.sort
type model = Z3.Model.model
type model_with_q = model * (Sym.t * BT.t) option




let logging_params = [
    (* ("trace", "true");
     * ("trace_file_name", Filename.get_temp_dir_name () ^ "/z3.log");
     * ("solver.smtlib2_log", Filename.get_temp_dir_name () ^ "/z3_smtlib2.log"); *)
  ]

let no_automation_params = [
    ("auto_config", "false");
    ("smt.auto_config", "false");
  ]

let no_randomness_params = [
    ("sat.random_seed", "1");
    ("nlsat.randomize", "false");
    ("fp.spacer.random_seed", "1");
    ("smt.arith.random_initial_value", "false");
    ("smt.random_seed", "1");
    ("sls.random_offset", "false");
    ("sls.random_seed", "1");
  ]

let solver_params = [
    ("smt.logic", "ALL");
    ("smt.arith.solver", "2");
    ("smt.macro_finder", "true");
    ("smt.pull-nested-quantifiers", "true");
    (* ("smt.mbqi", "false"); *)
  ]

let rewriter_params = [
    ("rewriter.expand_nested_stores", "true");
    ("rewriter.elim_rem", "true");
  ]

let model_params = [
    ("model", "true");
    ("model.completion", "true");
    ("model_evaluator.completion", "true");
  ]

let params =
  logging_params
  @ no_automation_params
  @ no_randomness_params
  @ solver_params
  @ rewriter_params
  @ model_params



let tactics = [
    "propagate-values";
    "propagate-ineqs";
    "purify-arith";
    "elim-term-ite";
    "add-bounds";
    "simplify";
    "solve-eqs";
    "aufnira";
    (* "qe2"; *)
    "smt";
  ]


let context = 
  List.iter (fun (c,v) -> Z3.set_global_param c v) params;
  Z3.mk_context []



module Translate = struct

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

  (* for caching the translation *)
  module BT_Table = Hashtbl.Make(BT)
  module IT_Table = Hashtbl.Make(IndexTerms)

  (* for translating back *)
  module Sort_Table = Hashtbl.Make(Sort_HashedType)
  module Z3Symbol_Table = Hashtbl.Make(Z3Symbol_HashedType)


  type z3sym_table_entry = 
    | MemberFunc of { tag : Sym.t; member : Id.t }
    | StructFunc of { tag : Sym.t }
    | CompFunc of { bts : BT.t list; i : int }
    | TupleFunc of  { bts : BT.t list }
    | DefaultFunc of { bt : BT.t }



  let bt_table = BT_Table.create 1000
  let sort_table = Sort_Table.create 1000

  let it_table = IT_Table.create 500000


  let z3sym_table : z3sym_table_entry Z3Symbol_Table.t = 
    Z3Symbol_Table.create 10000








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


  let sort : Memory.struct_decls -> BT.t -> sort =

    fun struct_decls ->

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
         let bt_symbol = bt_symbol (Tuple bts) in
         Z3Symbol_Table.add z3sym_table bt_symbol (TupleFunc {bts});
         let field_symbols = 
           mapi (fun i _ -> 
               let sym = tuple_field_symbol i in
               Z3Symbol_Table.add z3sym_table sym (CompFunc {bts; i});
               sym
             ) bts 
         in
         let sorts = map translate bts in
         Z3.Tuple.mk_sort context bt_symbol field_symbols sorts
      | Struct tag ->
         let struct_symbol = bt_symbol (Struct tag) in
         Z3Symbol_Table.add z3sym_table struct_symbol (StructFunc {tag});
         let layout = SymMap.find tag struct_decls in
         let member_symbols, member_sorts = 
           map_split (fun (id,sct) -> 
               let s = member_symbol tag id in
               Z3Symbol_Table.add z3sym_table s (MemberFunc {tag; member=id});
               (s, translate (BT.of_sct sct))
             ) (Memory.member_types layout)
         in
         Z3.Tuple.mk_sort context struct_symbol
           member_symbols member_sorts
    in

    let sort bt = 
      match BT_Table.find_opt bt_table bt with
      | Some sort -> sort
      | None ->
         let sort = translate bt in
         let () = BT_Table.add bt_table bt sort in
         let () = Sort_Table.add sort_table sort bt in
         sort
    in

    sort



  let sym_to_sym s = 
    Z3.Symbol.mk_string context (CF.Pp_symbol.to_string_pretty_cn s)


  let term ?(warn_lambda=true) struct_decls : IT.t -> expr =

    let sort = sort struct_decls in

    let unit_symbol = Z3.Symbol.mk_string context "unit" in
    let unit_term = Z3.Expr.mk_const context unit_symbol unit_sort in
    let true_term = Z3.Boolean.mk_true context in
    let false_term = Z3.Boolean.mk_false context in

    let rec translate (IT (it_, bt)) =
      begin match it_ with
      | Lit lit -> 
         begin match lit with
         | Sym s -> 
            let z3_sym = sym_to_sym s in
            Z3.Expr.mk_const context z3_sym (sort bt)
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
            let () = Z3Symbol_Table.add z3sym_table sym (DefaultFunc {bt}) in
            Z3.Expr.mk_const context sym (sort bt)
         | Null -> 
            integer_to_loc (term (int_ 0))
         end
      | Arith_op arith_op -> 
         let open Z3.Arithmetic in
         begin match arith_op with
         | Add (t1, t2) -> mk_add context [term t1; term t2]
         | Sub (t1, t2) -> mk_sub context [term t1; term t2]
         | Mul (t1, t2) -> mk_mul context [term t1; term t2]
         | Div (t1, t2) -> mk_div context (term t1) (term t2)
         | Exp (t1, t2) -> Real.mk_real2int context (mk_power context (term t1) (term t2))
         | Rem (t1, t2) -> Integer.mk_rem context (term t1) (term t2)
         | Mod (t1, t2) -> Integer.mk_mod context (term t1) (term t2)
         | LT (t1, t2) -> mk_lt context (term t1) (term t2)
         | LE (t1, t2) -> mk_le context (term t1) (term t2)
         | Min (t1, t2) -> term (ite_ (le_ (t1, t2), t1, t2))
         | Max (t1, t2) -> term (ite_ (ge_ (t1, t2), t1, t2))
         | IntToReal t -> Integer.mk_int2real context (term t)
         | RealToInt t -> Real.mk_real2int context (term t)
         | FlipBit fb ->
            (* looking at https://en.wikipedia.org/wiki/Bitwise_operation#XOR *)
            let bit = mod_ (div_ (fb.t, exp_ (int_ 2, fb.bit)), int_ 2) in
            let to_add_or_sub = exp_ (int_ 2, fb.bit) in
            let result = 
              ite_ (eq_ (bit, int_ 1),
                    sub_ (fb.t, to_add_or_sub),
                    add_ (fb.t, to_add_or_sub))
            in
            term result
         (* | XOR (ity, t1, t2) ->
          *    let bit_width = Memory.bits_per_byte * Memory.size_of_integer_type ity in
          *    let bt1 = Z3.Arithmetic.Integer.mk_int2bv context bit_width (term t1) in
          *    let bt2 = Z3.Arithmetic.Integer.mk_int2bv context bit_width (term t2) in
          *    let btv = Z3.BitVector.mk_xor context bt1 bt2 in
          *    Z3.BitVector.mk_bv2int context btv (CF.AilTypesAux.is_signed_ity ity) *)
         | XOR (ity, t1, t2) ->
            (* looking at https://en.wikipedia.org/wiki/Bitwise_operation#XOR *)
            assert (CF.AilTypesAux.is_unsigned_ity ity);
            let bit_width = Memory.bits_per_byte * Memory.size_of_integer_type ity in
            let shift_to_pos n pos = div_ (n, exp_ (int_ 2, int_ pos)) in
            (* let zero_one_pos n pos = mod_ (shift_to_pos n pos, int_ 2) in *)
            let zero_one_pos n pos = shift_to_pos n pos in
            let xor_pos n1 n2 pos = 
              mod_ (add_ (zero_one_pos n1 pos,
                          zero_one_pos n2 pos),
                    int_ 2)
            in
            let rec sum pos = 
              if pos < 0 then int_ 0 
              else add_ (sum (pos - 1), mul_ (xor_pos t1 t2 pos, exp_ (int_ 2, int_ pos)))
            in
            term (sum (bit_width - 1))
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
         | NE (t1, t2) -> mk_distinct context [term t1; term t2]
         | EachI ((i1, s, i2), t) -> 
             let rec aux i = 
               if i <= i2 
               then IT.subst (make_subst [(s, int_ i)]) t :: aux (i + 1)
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
            let layout = SymMap.find (struct_bt (IT.bt t)) struct_decls in
            let n = Option.get (Memory.member_number layout member) in
            let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
            Z3.Expr.mk_app context (nth destructors n) [term t]
         end
      | Pointer_op pointer_op -> 
         let open Z3.Arithmetic in
         begin match pointer_op with
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
            let decl = SymMap.find tag struct_decls in
            term (int_ (Option.get (Memory.member_offset decl member)))
         | ArrayOffset (ct, t) -> 
            term (mul_ (int_ (Memory.size_of_ctype ct), t))
         | CellPointer {base;step;starti;endi;p} ->
            term 
              (Resources.RE.subarray_condition ~base ~item_size:step 
                 ~from_index:starti ~to_index:endi ~qpointer:p)
         end
      | List_op t -> 
         Debug_ocaml.error "todo: SMT mapping for list operations"
      | Set_op set_op -> 
         let open Z3.Set in
         begin match set_op with
         | SetMember (t1, t2) -> mk_membership context (term t1) (term t2)
         | SetUnion ts -> mk_union context (map term (List1.to_list ts))
         | SetIntersection ts -> mk_intersection context (map term (List1.to_list ts))
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
            term (representable struct_decls ct t)
         | Good (ct, t) ->
            term (good_value struct_decls ct t)
         end
      | Array_op array_op -> 
         let open Z3.Z3Array in
         begin match array_op with
         | Const (abt, t) -> 
            mk_const_array context (sort abt) (term t)
         | Set (t1, t2, t3) -> 
            mk_store context (term t1) (term t2) (term t3)
         | Get (IT (Array_op (Def ((s, bt), body)), _), arg) -> 
            term (IT.subst (make_subst [(s, arg)]) body)
         | Get (f, arg) -> 
            mk_select context (term f) (term arg)
         | Def ((q_s, q_bt), body) ->
            if warn_lambda then
              warn (!^"generating lambda");
              (* warn (!^"generating lambda" ^^ colon ^^^ IT.pp (IT (it_, bt))); *)
            Z3.Quantifier.expr_of_quantifier
              (Z3.Quantifier.mk_lambda_const context
                 [term (sym_ (q_s, q_bt))] (term body))
         end
      | Let ((s, bound), body) ->
         term 
           (Simplify.simp struct_decls [] 
              (IT.subst (IT.make_subst [(s, bound)]) body))

         (* let body = IT.subst (IT.make_subst [(s, bound)]) body in
          * term body *)
         (* reading
            https://stackoverflow.com/questions/24188626/performance-issues-about-z3-for-java
            and
            https://stackoverflow.com/questions/14392957/encoding-let-expressions-in-z3
            and
            https://gitter.im/chc-comp/Lobby?at=5b1ae86e106f3c24bde6fea4
            *)
         (* let sym_s, sym = IT.fresh (IT.bt bound) in
          * let body = IT.subst (IT.make_subst [(s, sym)]) body in
          * Z3.Expr.substitute_one (term body) (term sym) (term bound) *)
      end

    and term : IT.t -> Z3.Expr.expr =
      fun it ->
      match IT_Table.find_opt it_table it with
      | Some sc -> sc
      | None ->
         let t = translate it in
         let () = IT_Table.add it_table it t in
         t
    in

    fun it -> 
    term it





end



let constr global c = 
  let open Translate in
  let term it = term global.struct_decls it in
  let sort bt = sort global.struct_decls bt in
  match c with
  | T it -> 
     Some (term it)
  | Forall ((s, bt), body) ->
     let q = 
       Z3.Quantifier.mk_forall_const context 
         [Z3.Expr.mk_const context (sym_to_sym s) (sort bt)] 
         (term body) 
         None [] [] None None 
     in
     Some (Z3.Quantifier.expr_of_quantifier q)
  | Pred pred ->
     let def = Option.get (get_logical_predicate_def global pred.name) in
     Some (term (LogicalPredicates.open_pred global def pred.args))
  | QPred _ ->
     (* QPreds are not automatically expanded: to avoid
        all-quantifiers *)
     None
     


module ReduceQuery = struct

  let forall (s, bt) t =
    let s' = Sym.fresh () in
    (IT.subst (make_subst [(s, sym_ (s', bt))]) t, Some (s', bt))

  let pred global (pred : LC.Pred.t) = 
    let def = Option.get (get_logical_predicate_def global pred.name) in
    (open_pred global def pred.args, None)

  let qpred global assumptions qpred = 
    (* fresh name to instantiate quantifiers with *)
    let s_inst = Sym.fresh () in
    let instantiate {q = (s, bt); condition; pred} = 
      let def = Option.get (get_logical_predicate_def global pred.name) in
      let subst = make_subst [(s, sym_ (s_inst, bt))] in
      (IT.subst subst condition, IT.subst subst (open_pred global def pred.args))
    in
    (* Want to prove "body[s_inst/s]" assuming 'condition[s_inst/s]',
       using the qpred assumptions from the context for the same
       predicate, also instantiated with s_inst *)
    let (condition, body) = instantiate qpred in
    let assumptions =
      condition ::
      List.filter_map (function
        | QPred qpred' when String.equal qpred.pred.name qpred'.pred.name ->
           let (condition', body') = instantiate qpred' in
           Some (impl_ (condition', body'))
        | _ -> 
           None
        ) assumptions
    in
    (impl_ (and_ assumptions, body), Some (s_inst, snd qpred.q))

  let plain it = 
    match it with
    | IT (Bool_op (EachI ((i1, i_s, i2), body)), _) ->
       let i = sym_ (i_s, Integer) in
       let condition = and_ [IT.le_ (int_ i1, i); IT.le_ (i, int_ i2)] in
       forall (i_s, Integer) (impl_ (condition, body))
    | _ -> 
       (it, None)



  let constr global assumptions (lc : LC.t) =
    match lc with
    | T t -> plain t
    | Forall ((s, bt), t) -> forall (s, bt) t
    | Pred predicate -> pred global predicate
    | QPred qpredicate -> qpred global assumptions qpredicate
       


end


let solver : solver = 
  (* https://stackoverflow.com/a/14305028 describes an example where
     tactics are useful *)
  (* http://www.cs.tau.ac.il/~msagiv/courses/asv/z3py/strategies-examples.htm *)
  (* also see: https://z3prover.github.io/api/html/group__capi.html
     regarding "and-then" *)
  let fancy = 
    let mk_tactic = Z3.Tactic.mk_tactic context in
    let mk_then = function
      | t1 :: t2 :: ts -> Z3.Tactic.and_then context t1 t2 ts 
      | _ -> assert false;
    in
    let tactic = mk_then (List.map mk_tactic tactics) in
    Z3.Solver.mk_solver_t context tactic
  in
  { fancy }



let init () = Z3.Solver.reset solver.fancy


let push () = 
  Z3.Solver.push solver.fancy


let pop () =
  Translate.IT_Table.clear Translate.it_table;
  Z3.Solver.pop solver.fancy 1


let add global lc = 
  match constr global lc with
  | None -> ()
  | Some sc -> Z3.Solver.add solver.fancy [sc]


(* as similarly suggested by Robbert *)
let shortcut it = 
  let it = Simplify.simp [] [] it in
  match it with
  | IT (Lit (Bool true), _) -> `True
  | IT (Lit (Bool false), _) -> `False it
  | _ -> `No_shortcut it





type model_state =
  | Model_fancy_solver of (Sym.t * LogicalSorts.t) option
  | No_model

let model_state = 
  ref No_model



let model () = 
  match !model_state with
  | Model_fancy_solver oq ->
     let omodel = Z3.Solver.get_model solver.fancy in
     let model = Option.value_err "Z3 did not produce a counter model" omodel in
     (model, oq)
  | No_model ->
     assert false


let provable ~shortcut_false global assumptions lc = 
  let it, oq = ReduceQuery.constr global assumptions lc in
  match shortcut it with
  | `True -> 
     model_state := No_model; 
     `True
  | `False _ when shortcut_false ->
     model_state := No_model; 
     `False
  | (`False it | `No_shortcut it) ->
     let t = Translate.term global.struct_decls (not_ it) in
     match Z3.Solver.check solver.fancy [t] with
     | Z3.Solver.UNSATISFIABLE -> 
        model_state := No_model; 
        `True
     | Z3.Solver.SATISFIABLE -> 
        model_state := Model_fancy_solver oq; 
        `False
     | Z3.Solver.UNKNOWN -> 
        model_state := No_model; 
        warn !^"solver returned unknown"; 
        `False



exception Unsupported of string

let eval struct_decls model to_be_evaluated = 

  let open Translate in

  let z3_sort (sort : Z3.Sort.sort) = 
    Sort_Table.find sort_table sort in

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
         (* informed by this:
            https://stackoverflow.com/questions/22885457/read-func-interp-of-a-z3-array-from-the-z3-model/22918197 *)
         let abt = z3_sort (Z3.Z3Array.get_range (Z3.Expr.get_sort expr)) in
         let as_array_func_decl = Z3.Expr.get_func_decl expr in
         let as_array_parameters = Z3.FuncDecl.get_parameters as_array_func_decl in
         let as_array_func_parameter = List.nth as_array_parameters 0 in
         let array_func_decl = Z3.FuncDecl.Parameter.get_func_decl as_array_func_parameter in
         let array_func_interp = match Z3.Model.get_func_interp model array_func_decl with
           | None -> Debug_ocaml.error "as-array: func_decl without interpretation"
           | Some interp -> interp
         in
         let base_value = aux binders (Z3.Model.FuncInterp.get_else array_func_interp) in
         let entries = Z3.Model.FuncInterp.get_entries array_func_interp in
         List.fold_right (fun entry array_value ->
             match Z3.Model.FuncInterp.FuncEntry.get_args entry with
             | [index] ->
                let index = aux binders index in
                let value = aux binders (Z3.Model.FuncInterp.FuncEntry.get_value entry) in
                set_ array_value (index, value)
             | [] ->
                Debug_ocaml.error "unexpected zero-dimenstional array"
             | _ ->
                raise (Unsupported "multi-dimensional arrays (from as-value)")
           ) entries (const_ abt base_value)

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

        | () when Z3Symbol_Table.mem z3sym_table func_name ->
           begin match Z3Symbol_Table.find z3sym_table func_name with
           | DefaultFunc {bt} ->
              default_ bt
           | MemberFunc {tag; member} ->
              let sd = Memory.member_types (SymMap.find tag struct_decls) in
              let member_bt = BT.of_sct (List.assoc Id.equal member sd) in
              member_ ~member_bt (tag, nth args 0, member)
           | StructFunc {tag} ->
              let sd = Memory.members (SymMap.find tag struct_decls) in
              struct_ (tag, List.combine sd args)
           | CompFunc {bts; i} ->
              let comp_bt = List.nth bts i in
              nthTuple_ ~item_bt:comp_bt (i, nth args 0)
           | TupleFunc {bts} ->
              tuple_ args
           end

        | () when String.equal (Z3.Symbol.to_string func_name) "^" ->
           exp_ (nth args 0, nth args 1)

        | () when Z3.Arithmetic.is_real2int expr ->
           realToInt_ (nth args 0)

        | () when Z3.Arithmetic.is_int2real expr ->
           intToReal_ (nth args 0)

        | () when String.equal (Z3.Symbol.get_string func_name) "unit" ->
           unit_
        | () ->
           unsupported ("z3 expression. func_name " ^ Z3.Symbol.to_string func_name)

    in

    fun expr -> 
    aux [] expr
  in

  let expr = Translate.term ~warn_lambda:false struct_decls to_be_evaluated in
  match Z3.Model.eval model expr true with
  | None -> None
  | Some v -> Some (z3_expr v)
