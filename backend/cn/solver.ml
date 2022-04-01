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
module LCSet = Set.Make(LC)


let save_slow_problems = 
  ref (if !Debug_ocaml.debug_level > 0
       then (5.0, (Some "slow_smt.txt" : string option))
       else (99999999999.0, None))

type solver = { 
    context : Z3.context;
    incremental : Z3.Solver.solver;
    fancy : Z3.Solver.solver;
  }
type expr = Z3.Expr.expr
type sort = Z3.Sort.sort
type model = Z3.context * Z3.Model.model
type model_with_q = model * (Sym.t * BT.t) option


type handle_blast = 
  | BlastFlatAdd
  | BlastITE

let handle_blast = BlastITE


let logging_params = 
  (* if !Debug_ocaml.debug_level > 0 then  *)
    [
      ("solver.smtlib2_log", Filename.get_temp_dir_name () ^ "/z3_log.smt");
    ]
  (* else *)
  (*   [] *)

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
    ("smt.logic", "AUFLIRA");
    ("smt.arith.solver", "2");
    ("smt.macro_finder", "true");
    ("smt.pull-nested-quantifiers", "true");
    ("smt.mbqi", "true");
    ("smt.ematching", "true");
  ]

let rewriter_params = [
    ("rewriter.expand_nested_stores", "true");
  ]

let model_params = [
    ("model", "true");
    ("model.compact", "true");
    ("model.completion", "true");
    ("model.inline_def", "true");
    ("model_evaluator.completion", "true");
    ("model_evaluator.array_as_stores", "false");
  ]

let params =
  logging_params
  @ no_automation_params
  @ no_randomness_params
  @ solver_params
  @ rewriter_params
  @ model_params












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

  (* for translating back *)
  module Sort_Table = Hashtbl.Make(Sort_HashedType)
  module Z3Symbol_Table = Hashtbl.Make(Z3Symbol_HashedType)


  type z3sym_table_entry = 
    | MemberFunc of { tag : Sym.t; member : Id.t }
    | StructFunc of { tag : Sym.t }
    | CompFunc of { bts : BT.t list; i : int }
    | TupleFunc of  { bts : BT.t list }
    | DefaultFunc of { bt : BT.t }
    (* | SomethingFunc of { bt : BT.t } *)
    (* | NothingFunc of { bt : BT.t } *)
    (* | IsSomethingFunc of { bt : BT.t } *)
    (* | ValueOfSomethingFunc of { bt : BT.t } *)





  let bt_table = BT_Table.create 1000
  let sort_table = Sort_Table.create 1000



  let z3sym_table : z3sym_table_entry Z3Symbol_Table.t = 
    Z3Symbol_Table.create 10000





  let symbol context str = 
    Z3.Symbol.mk_string context str
  

  let bt_name bt = 
    Pp.plain (BT.pp bt)
  (* let bt_symbol bt = 
   *   Z3.Symbol.mk_string context (bt_name bt) *)

  let tuple_field_name bts i = 
    bt_name (Tuple bts) ^ string_of_int i
  (* let tuple_field_symbol i = 
   *   Z3.Symbol.mk_string context (tuple_field_name i) *)

  let member_name tag id = 
    bt_name (BT.Struct tag) ^ "_" ^ Id.s id
  (* let member_symbol tag id = 
   *   Z3.Symbol.mk_string context (member_name tag id) *)




  let sort : Z3.context -> Memory.struct_decls -> BT.t -> sort =

    fun context struct_decls ->

    let symbol str = symbol context str in

    let rec translate = function
      | Unit -> Z3.Sort.mk_uninterpreted_s context "unit"
      | Bool -> Z3.Boolean.mk_sort context
      | Integer -> Z3.Arithmetic.Integer.mk_sort context
      | Real -> Z3.Arithmetic.Real.mk_sort context
      | Loc -> 
         Z3.Tuple.mk_sort context 
           (symbol (bt_name Loc))
           [symbol "loc_to_integer"] 
           [sort BT.Integer]
      | List bt -> Z3.Z3List.mk_sort context (symbol (bt_name bt)) (sort bt) 
      | Set bt -> Z3.Set.mk_sort context (sort bt)
      | Map (abt, rbt) -> Z3.Z3Array.mk_sort context (sort abt) (sort rbt)
      | Tuple bts ->
         let bt_symbol = symbol (bt_name (Tuple bts)) in
         Z3Symbol_Table.add z3sym_table bt_symbol (TupleFunc {bts});
         let field_symbols = 
           mapi (fun i _ -> 
               let sym = symbol (tuple_field_name bts i) in
               Z3Symbol_Table.add z3sym_table sym (CompFunc {bts; i});
               sym
             ) bts 
         in
         let sorts = map sort bts in
         Z3.Tuple.mk_sort context bt_symbol field_symbols sorts
      | Struct tag ->
         let struct_symbol = symbol (bt_name (Struct tag)) in
         Z3Symbol_Table.add z3sym_table struct_symbol (StructFunc {tag});
         let layout = SymMap.find tag struct_decls in
         let member_symbols, member_sorts = 
           map_split (fun (id,sct) -> 
               let s = symbol (member_name tag id) in
               Z3Symbol_Table.add z3sym_table s (MemberFunc {tag; member=id});
               (s, sort (BT.of_sct sct))
             ) (Memory.member_types layout)
         in
         Z3.Tuple.mk_sort context struct_symbol
           member_symbols member_sorts

    and sort bt = 
      match BT_Table.find_opt bt_table bt with
      | Some sort -> sort
      | None ->
         let sort = translate bt in
         let () = BT_Table.add bt_table bt sort in
         let () = Sort_Table.add sort_table sort bt in
         sort
    in

    sort



  let init structs context = 
    BT_Table.clear bt_table;
    Sort_Table.clear sort_table;
    let _ = sort context structs BT.Integer in
    let _ = sort context structs BT.Bool in
    ()


  let loc_to_integer_fundecl context struct_decls = 
    nth (Z3.Tuple.get_field_decls (sort context struct_decls Loc)) 0

  let integer_to_loc_fundecl context struct_decls = 
    Z3.Tuple.get_mk_decl (sort context struct_decls Loc)


  let term ?(warn_lambda=true) context struct_decls : IT.t -> expr =

    let sort bt = sort context struct_decls bt in
    let symbol str = symbol context str in

    (* let integer_to_loc_symbol = Z3.FuncDecl.get_name integer_to_loc_fundecl in *)
  
    let loc_to_integer l = 
      Z3.Expr.mk_app context 
        (loc_to_integer_fundecl context struct_decls) [l] 
    in
    let integer_to_loc i = 
      Z3.Expr.mk_app context 
        (integer_to_loc_fundecl context struct_decls) [i] 
    in



    let rec term (IT (it_, bt)) =
      begin match it_ with
      | Lit lit -> 
         begin match lit with
         | Sym s -> 
            let str = CF.Pp_symbol.to_string_pretty_cn s in
            Z3.Expr.mk_const context (symbol str) (sort bt)
         | Z z -> 
            Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
         | Q q -> 
            Z3.Arithmetic.Real.mk_numeral_s context (Q.to_string q)
         | Pointer z -> 
            integer_to_loc
              (Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z))
         | Bool true -> 
            Z3.Boolean.mk_true context
         | Bool false -> 
            Z3.Boolean.mk_false context
         | Unit -> 
            Z3.Expr.mk_const context (symbol "unit") (sort Unit)
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
         | Exp (t1, t2) -> 
            begin match is_z t1, is_z t2 with
            | Some z1, Some z2 when Z.fits_int z2 ->
               term (z_ (Z.pow z1 (Z.to_int z2)))
            | _, _ ->
               warn (!^"generating power");
               Real.mk_real2int context (mk_power context (term t1) (term t2))
            end
         | Rem (t1, t2) -> Integer.mk_rem context (term t1) (term t2)
         | Mod (t1, t2) -> Integer.mk_mod context (term t1) (term t2)
         | LT (t1, t2) -> mk_lt context (term t1) (term t2)
         | LE (t1, t2) -> mk_le context (term t1) (term t2)
         | Min (t1, t2) -> term (ite_ (le_ (t1, t2), t1, t2))
         | Max (t1, t2) -> term (ite_ (ge_ (t1, t2), t1, t2))
         | IntToReal t -> Integer.mk_int2real context (term t)
         | RealToInt t -> Real.mk_real2int context (term t)
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
         | Blast ((i1, s, v, i2), body) ->
            begin match handle_blast with
            | BlastFlatAdd ->
               let inst_body i = IT.subst (IT.make_subst [(s, int_ i)]) body in
               let v_blasted_values = 
                 ite_ (or_ [v %< int_ i1; v %> int_ i2], default_ Integer, int_ 0) ::
                   if i1 > i2 then [] else
                     List.init (i2 - i1 + 1) (fun i ->
                         let i = i + i1 in
                         ite_ (eq_ (v, int_ i), inst_body i, int_ 0)
                       )
               in
               term (List.fold_right (fun i j -> add_ (i, j)) v_blasted_values (int_ 0))
            | BlastITE ->
               let inst_body i = IT.subst (IT.make_subst [(s, int_ i)]) body in
               let v_blasted_values = 
                 if i1 > i2 then [] else
                   List.init (i2 - i1 + 1) (fun i ->
                       let i = i + i1 in
                       (eq_ (v, int_ i), inst_body i)
                     )
               in
               let value = 
                 List.fold_right (fun (g,v) acc -> 
                     ite_ (g, v, acc)
                   ) v_blasted_values (default_ Integer)
               in
               term value
            end
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
         end
      | List_op t -> 
         Debug_ocaml.error "todo: SMT mapping for list operations"
      | Set_op set_op -> 
         let open Z3.Set in
         begin match set_op with
         | SetMember (t1, t2) -> mk_membership context (term t1) (term t2)
         | SetUnion ts -> mk_union context (map term ts)
         | SetIntersection ts -> mk_intersection context (map term ts)
         | SetDifference (t1, t2) -> mk_difference context (term t1) (term t2)
         | Subset (t1, t2) -> mk_subset context (term t1) (term t2)
         end
      | CT_pred ct_pred -> 
         begin match ct_pred with
         | AlignedI t ->
            term (eq_ (mod_ (pointerToIntegerCast_ t.t, t.align), int_ 0))
         | Aligned (t, ct) ->
            term (alignedI_ ~t ~align:(int_ (Memory.align_of_ctype ct)))
         | Representable (ct, t) ->
            term (representable struct_decls ct t)
         | Good (ct, t) ->
            term (good_value struct_decls ct t)
         end
      | Map_op map_op -> 
         let open Z3.Z3Array in
         begin match map_op with
         | Const (abt, t) -> 
            mk_const_array context (sort abt) (term t)
         | Set (t1, t2, t3) -> 
            mk_store context (term t1) (term t2) (term t3)
         | Get (IT (Map_op (Def ((s, bt), body)), _), arg) -> 
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
      (* | Option_op option_op -> *)
      (*    begin match option_op with *)
      (*    | Nothing vbt -> *)
      (*       let nothing_constructor = List.nth (Z3.Datatype.get_constructors (sort bt)) 0 in *)
      (*       Z3.Expr.mk_app context nothing_constructor [] *)
      (*    | Something t -> *)
      (*       let something_constructor = List.nth (Z3.Datatype.get_constructors (sort bt)) 1 in *)
      (*       Z3.Expr.mk_app context something_constructor [term t] *)
      (*    | Is_nothing t -> *)
      (*       let nothing_recogniser = List.nth (Z3.Datatype.get_recognizers (sort (IT.bt t))) 0 in *)
      (*       Z3.Expr.mk_app context nothing_recogniser [term t] *)
      (*    | Is_something t -> *)
      (*       let something_recogniser = List.nth (Z3.Datatype.get_recognizers (sort (IT.bt t))) 1 in *)
      (*       Z3.Expr.mk_app context something_recogniser [term t] *)
      (*    | Get_some_value t -> *)
      (*       let something_value_accessor = hd (List.nth (Z3.Datatype.get_accessors (sort (IT.bt t))) 1) in *)
      (*       Z3.Expr.mk_app context something_value_accessor [term t] *)
      (*    end *)
      (* | Let ((s, bound), body) -> *)
         (* let bound = term bound in *)
         (* term (IT.subst (IT.make_subst [(s, bound)]) body)) *)

         (* let body = IT.subst (IT.make_subst [(s, bound)]) body in
          * term body *)
         (* reading
            https://stackoverflow.com/questions/24188626/performance-issues-about-z3-for-java
            and
            https://stackoverflow.com/questions/14392957/encoding-let-expressions-in-z3
            and
            https://gitter.im/chc-comp/Lobby?at=5b1ae86e106f3c24bde6fea4
            *)
         (* let sym_s, sym = IT.fresh (IT.bt bound) in *)
         (* let body = IT.subst (IT.make_subst [(s, sym)]) body in *)
         (* Z3.Expr.substitute_one (term body) (term sym) (term bound) *)
      end

    in

    fun it -> 
    term it





end



let constr context global c = 
  let open Translate in
  let term it = term context global.struct_decls it in
  match c with
  | T it -> 
     Some (term it)
  | Forall ((s, bt), body) ->
     let q = 
       Z3.Quantifier.mk_forall_const context 
         [term (sym_ (s, bt))] (term body) 
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

  open Pred
  open QPred

  type reduction = {
      lc : IT.t;
      oq : (Sym.t * BT.t) option; (* for UI only *)
    }

  let forall (s, bt) t =
    let s' = Sym.fresh () in
    { lc = IT.subst (make_subst [(s, sym_ (s', bt))]) t; 
      oq = Some (s', bt) }

  let pred global (pred : LC.Pred.t) = 
    let def = Option.get (get_logical_predicate_def global pred.name) in
    { lc = open_pred global def pred.args; 
      oq = None }

  let qpred global assumptions qpred =
    let def = Option.get (get_logical_predicate_def global qpred.pred.name) in
    (* fresh name to instantiate quantifiers with *)
    let s_inst = Sym.fresh () in
    let instantiate {q = (s, bt); condition; pred} = 
      let subst = make_subst [(s, sym_ (s_inst, bt))] in
      IT.subst subst (impl_ (condition, open_pred global def pred.args))
    in
    (* Want to prove "body[s_inst/s]" assuming 'condition[s_inst/s]',
       using the qpred assumptions from the context for the same
       predicate, also instantiated with s_inst *)
    let extra_assumptions =
      Context.LCSet.fold (fun lc acc ->
          match lc with
          | QPred qpred' when String.equal qpred.pred.name qpred'.pred.name ->
             instantiate qpred' :: acc
          | _ -> 
             acc
        ) assumptions []
    in
    { lc = impl_ (and_ extra_assumptions, instantiate qpred);
      oq = Some (s_inst, snd qpred.q); }


  let plain it = 
    match it with
    (* | IT (Bool_op (EachI ((i1, i_s, i2), body)), _) -> *)
    (*    let i = sym_ (i_s, Integer) in *)
    (*    let condition = and_ [IT.le_ (int_ i1, i); IT.le_ (i, int_ i2)] in *)
    (*    forall (i_s, Integer) (impl_ (condition, body)) *)
    | _ -> 
       { lc = it;
         oq = None }



  let constr global assumptions (lc : LC.t) =
    match lc with
    | T t -> plain t
    | Forall ((s, bt), t) -> forall (s, bt) t
    | Pred predicate -> pred global predicate
    | QPred qpredicate -> qpred global assumptions qpredicate
       


end









let tactics context ts = 
  match List.map (Z3.Tactic.mk_tactic context) ts with
  | [] -> Z3.Tactic.skip context
  | [t] -> t
  | t1::t2::ts -> Z3.Tactic.and_then context t1 t2 ts

let tactic context = 
  tactics context [
      (* "blast-term-ite"; *)
      (* "cofactor-term-ite"; *)
      "solve-eqs";
      "simplify";
      (* "elim-term-ite"; *)
      "aufnira";
    ]

let make struct_decls : solver = 
  Z3.Memory.reset ();

  List.iter (fun (c,v) -> Z3.set_global_param c v) params;

  let context = Z3.mk_context [] in

  Translate.init struct_decls context;

  let params = Z3.Params.mk_params context in
  Z3.Params.add_int params (Z3.Symbol.mk_string context "timeout") 500;

  let incremental = Z3.Solver.mk_simple_solver context in
  Z3.Solver.set_parameters incremental params;

  let fancy = Z3.Solver.mk_solver_t context (tactic context) in
  (* let fancy = Z3.Solver.mk_solver_s context "AUFLIA" in *)

  { context; incremental; fancy }






let push solver = 
  (* do nothing to fancy solver, because that is reset for every query *)
  Z3.Solver.push solver.incremental

let pop solver =
  (* do nothing to fancy solver, because that is reset for every query *)
  Z3.Solver.pop solver.incremental 1


let add solver global lc = 
  (* do nothing to fancy solver, because that is reset for every query *)
  match constr solver.context global lc with
  | None -> ()
  | Some sc -> Z3.Solver.add solver.incremental [sc]


(* as similarly suggested by Robbert *)
let shortcut struct_decls it = 
  let it = Simplify.simp struct_decls SymMap.empty LCSet.empty it in
  match it with
  | IT (Lit (Bool true), _) -> `True
  | IT (Lit (Bool false), _) -> `False it
  | _ -> `No_shortcut it





type model_state =
  | Model of Z3.context * Z3.Solver.solver * (Sym.t * LogicalSorts.t) option
  | No_model

let model_state = 
  ref No_model



let model () = 
  match !model_state with
  | No_model ->
     assert false
  | Model (context, z3_solver, oq) ->
     let omodel = Z3.Solver.get_model z3_solver in
     let model = Option.value_err "SMT solver did not produce a counter model" omodel in
     ((context, model), oq)

let maybe_save_slow_problem solv_inst lc lc_t time solver = match ! save_slow_problems with
  | (_, None) -> ()
  | (cutoff, _) when (Stdlib.Float.compare time cutoff) = -1 -> ()
  | (_, Some fname) ->
    let channel = open_out_gen [Open_append; Open_creat] 0o666 fname in
    output_string channel "\n\n";
    Colour.without_colour (fun () -> print channel (item "Slow problem"
      (Pp.list (fun pp -> pp) [
          item "time taken" (format [] (Float.to_string time));
          item "constraint" (LC.pp lc);
          item "reduced constraint" (IT.pp lc_t);
          if !Pp.print_level >= 10 then item "solver statistics" !^(Z3.Statistics.to_string (Z3.Solver.get_statistics solver)) else Pp.empty;
          if !Pp.print_level >= 11 then item "SMT assertions" (Pp.list (fun e -> format [] (Z3.Expr.to_string e)) (Z3.Solver.get_assertions solv_inst)) else Pp.empty;
      ]))) ();
    output_string channel "\n";
    close_out channel

let provable ~loc ~shortcut_false ~solver ~global ~trace_length ~assumptions ~pointer_facts lc = 
  let context = solver.context in
  let structs = global.struct_decls in
  (* debug 5 (lazy (item "provable check" (LC.pp lc))); *)
  let ReduceQuery.{lc = it; oq} = ReduceQuery.constr global assumptions lc in
  (* debug 6 (lazy (item "reduced" (IT.pp it))); *)
  let rtrue () = model_state := No_model; `True in
  let rfalse = function
    | Some solver -> model_state := Model (context, solver, oq); `False
    | None -> model_state := No_model; `False
  in
  match shortcut structs it with
  | `True -> rtrue ()
  | `False _ when shortcut_false -> rfalse None
  | (`False it | `No_shortcut it) ->
     let translate it = Translate.term context structs it in
     let t = translate (not_ it) in
     let assumptions = List.map translate pointer_facts in
     let res = time_f_logs loc 5 "Z3(inc)" trace_length
                 (Z3.Solver.check solver.incremental) 
                 (t :: assumptions) 
     in
     match res with
     | Z3.Solver.UNSATISFIABLE -> rtrue ()
     | Z3.Solver.SATISFIABLE -> rfalse (Some solver.incremental)
     | Z3.Solver.UNKNOWN ->
        (* print stdout (item "checking" !^(Z3.Expr.to_string t)); *)
        let add sc = Z3.Solver.add solver.fancy [sc] in
        Z3.Solver.reset solver.fancy;
        debug 5 (lazy (format [] "Z3(inc) unknown/timeout, running full solver"));
        add t;
        List.iter add assumptions;
        List.iter add (Z3.Solver.get_assertions solver.incremental);
        let (elapsed, res) = time_f_elapsed (time_f_logs loc 5 "Z3" trace_length
                (Z3.Solver.check solver.fancy)) [] in
        maybe_save_slow_problem solver.fancy lc it elapsed solver.fancy;
        match res with
        | Z3.Solver.UNSATISFIABLE -> rtrue ()
        | Z3.Solver.SATISFIABLE -> rfalse (Some solver.fancy)
        | Z3.Solver.UNKNOWN -> 
           let reason = Z3.Solver.get_reason_unknown solver.fancy in
           failwith ("SMT solver returned 'unknown'; reason: " ^ reason)



exception Unsupported of string

let eval struct_decls (context, model) to_be_evaluated = 

  let open Translate in

  let z3_sort (sort : Z3.Sort.sort) = 
    try Sort_Table.find sort_table sort with
    | Not_found -> 
       failwith ("could not find sort '"^Z3.Sort.to_string sort^"' in Sort_Table")
  in

  let z3_expr = 
    let counter = ref 0 in
    let new_q () = 
      let c = !counter in 
      let () = counter := c+1 in
      Sym.fresh_pretty ("p" ^ string_of_int c)
    in
    (* TODO: check about binders, shouldn't those be empty here? *)
    let rec func_interp binders func_decl = 
      let domain = match Z3.FuncDecl.get_domain func_decl with
        | [domain] -> domain
        | [] -> Debug_ocaml.error "unexpected constant function"
        | _ -> raise (Unsupported "multi-argument functions")
      in      
      let func_interp = match Z3.Model.get_func_interp model func_decl with
        | None -> Debug_ocaml.error "func_decl without interpretation"
        | Some interp -> interp
      in
      let base_value = aux binders (Z3.Model.FuncInterp.get_else func_interp) in
      let entries = Z3.Model.FuncInterp.get_entries func_interp in
      List.fold_right (fun entry map_value ->
          match Z3.Model.FuncInterp.FuncEntry.get_args entry with
          | [index] ->
             let index = aux binders index in
             let value = aux binders (Z3.Model.FuncInterp.FuncEntry.get_value entry) in
             map_set_ map_value (index, value)
          | [] ->
             Debug_ocaml.error "unexpected constant function"
          | _ ->
             raise (Unsupported "multi-argument functions")
        ) entries (const_map_ (z3_sort domain) base_value)


    and aux (binders : (Sym.t * BT.t) list) (expr : Z3.Expr.expr) : IT.t = 
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
         map_def_ (q_s, q_bt) (aux ((q_s, q_bt) :: binders) body)

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
         List.fold_right (fun entry map_value ->
             match Z3.Model.FuncInterp.FuncEntry.get_args entry with
             | [index] ->
                let index = aux binders index in
                let value = aux binders (Z3.Model.FuncInterp.FuncEntry.get_value entry) in
                map_set_ map_value (index, value)
             | [] ->
                Debug_ocaml.error "unexpected zero-dimenstional map/array"
             | _ ->
                raise (Unsupported "multi-dimensional maps/arrays (from as-value)")
           ) entries (const_map_ abt base_value)

      | () when Z3.Z3Array.is_constant_array expr ->
         let abt = z3_sort (Z3.Z3Array.get_range (Z3.Expr.get_sort expr)) in
         const_map_ abt (hd args)

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

      (* | () when  Z3.Set.is_intersect expr ->
       *    setIntersection_ args *)

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
         map_get_ (nth args 0) (nth args 1)

      | () when Z3.Z3Array.is_store expr ->
         map_set_ (nth args 0) (nth args 1, nth args 2)

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

      (* | () when Z3.Set.is_union expr ->
       *    setUnion_ args *)

      | () when Z3.AST.is_var (Z3.Expr.ast_of_expr expr) ->
         sym_ (nth binders (Z3.Quantifier.get_index expr))

      | () ->
        let func_decl = Z3.Expr.get_func_decl expr in
        let func_name = Z3.FuncDecl.get_name func_decl in
        match () with

        | () when 
               Z3.FuncDecl.equal func_decl
                 (loc_to_integer_fundecl context struct_decls) ->
           let p = nth args 0 in
           begin match IT.is_pointer p with
           | Some z -> z_ z
           | _ -> pointerToIntegerCast_ p
           end

        | () when 
               Z3.FuncDecl.equal func_decl 
                 (integer_to_loc_fundecl context struct_decls) ->
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
           (* | SomethingFunc { bt } -> *)
           (*    something_ (List.hd args) *)
           (* | NothingFunc { bt }-> *)
           (*    nothing_ bt *)
           (* | IsSomethingFunc { bt } -> *)
           (*    is_something_ (List.hd args) *)
           (* | ValueOfSomethingFunc { bt } -> *)
           (*    get_some_value_ (List.hd args) *)
           end

        | () when String.equal (Z3.Symbol.to_string func_name) "^" ->
           exp_ (nth args 0, nth args 1)

        | () when Z3.Arithmetic.is_real2int expr ->
           realToInt_ (nth args 0)

        | () when Z3.Arithmetic.is_int2real expr ->
           intToReal_ (nth args 0)

        | () when String.equal (Z3.Symbol.get_string func_name) "unit" ->
           unit_
        | () when BT.equal Unit (z3_sort (Z3.Expr.get_sort expr)) ->
           unit_
        | () -> 
           let func_decl = 
             try Z3.Expr.get_func_decl expr with
             | _ ->
                print_endline (Z3.Model.to_string model);
                unsupported ("z3 expression. func_name " ^ Z3.Symbol.to_string func_name)
           in
           let arg = match args with
             | [arg] -> arg
             | [] -> Debug_ocaml.error ("unexpected constant function: "  
                                        ^ Z3.Symbol.to_string func_name)
             | _ -> raise (Unsupported "multi-argument functions")
           in      
           map_get_ (func_interp binders func_decl) arg

    in

    fun expr -> 
    aux [] expr
  in

  let expr = 
    Translate.term ~warn_lambda:false context 
      struct_decls to_be_evaluated 
  in
  match Z3.Model.eval model expr true with
  | None -> None
  | Some v -> Some (z3_expr v)
