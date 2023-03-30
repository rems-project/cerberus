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
open LogicalFunctions
module LCSet = Set.Make(LC)
module BT = BaseTypes


let random_seed = ref 1

let slow_smt_file =
  let open Filename in
  get_temp_dir_name () ^ dir_sep ^ "slow_smt.txt"


let save_slow_problems, saved_slow_problem = 
  (* not yet written this run, > 3.0s counts as slow, append to this fname *)
  let slow_problem_ref = ref (false, 3.0, Some slow_smt_file) in
  let save_slow_problems () =
    if !Debug_ocaml.debug_level > 0
    then ! slow_problem_ref
    else (false, 0.0, None)
  in
  let saved_slow_problem () = match ! slow_problem_ref with
    | (false, t, fn) -> slow_problem_ref := (true, t, fn)
    | _ -> ()
  in
  save_slow_problems, saved_slow_problem


type solver = { 
    context : Z3.context;
    incremental : Z3.Solver.solver;
    fancy : Z3.Solver.solver;
  }
type expr = Z3.Expr.expr
type sort = Z3.Sort.sort
type model = Z3.context * Z3.Model.model
type model_with_q = model * (Sym.t * BT.t) list



let mul_no_smt_solver_sym = Sym.fresh_named "mul_uf"
let div_no_smt_solver_sym = Sym.fresh_named "div_uf"
let exp_no_smt_solver_sym = Sym.fresh_named "power_uf"
let mod_no_smt_solver_sym = Sym.fresh_named "mod_uf"
let rem_no_smt_solver_sym = Sym.fresh_named "rem_uf"
let xor_no_smt_solver_sym = Sym.fresh_named "xor_uf"






let logging_params = 
    [
      (* ("solver.smtlib2_log", Filename.get_temp_dir_name () ^ "/z3_log.smt"); *)
    ]

let no_automation_params = [
    ("auto_config", "false");
    ("smt.auto_config", "false");
  ]

let no_randomness_params () =
  let seed_str = Int.to_string (! random_seed) in
  [
    ("sat.random_seed", seed_str);
    ("nlsat.randomize", "false");
    ("fp.spacer.random_seed", seed_str);
    ("smt.arith.random_initial_value", "false");
    ("smt.random_seed", seed_str);
    ("sls.random_offset", "false");
    ("sls.random_seed", seed_str);
  ]

let solver_params = [
    ("smt.logic", "QF_AUFLIA");
    ("smt.arith.solver", "2");
    ("smt.macro_finder", "true");
    ("smt.pull-nested-quantifiers", "true");
    ("smt.mbqi", "true");
    ("smt.ematching", "false");
    ("smt.arith.nl", "false");
    ("smt.arith.nl.branching", "false");
    ("smt.arith.nl.rounds", "0");
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

let params () =
  logging_params
  @ no_automation_params
  @ no_randomness_params ()
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
    (* rubbish hash function *)
    let hash s = String.length (Z3.Symbol.get_string s)
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
    | RecordFunc of { mbts : BT.member_types }
    | RecordMemberFunc of { mbts : BT.member_types; member : Sym.t }
    | DefaultFunc of { bt : BT.t }
    | DatatypeConsFunc of { nm: Sym.t }
    | DatatypeConsRecogFunc of { nm: Sym.t }
    | DatatypeAccFunc of { nm: Sym.t; dt: Sym.t; bt: BT.t }
    | UninterpretedVal of { nm : Sym.t }
  [@@deriving eq]






  let bt_table = BT_Table.create 1000
  let sort_table = Sort_Table.create 1000

  let bt_id_table = BT_Table.create 1000

  let z3sym_table : z3sym_table_entry Z3Symbol_Table.t = 
    Z3Symbol_Table.create 10000





  let string context str =
    Z3.Symbol.mk_string context str
  let symbol_string pfx sym = pfx ^ Sym.pp_string sym ^ "_a" ^ string_of_int (Sym.num sym)
  let prefix_symbol context pfx sym =
    Z3.Symbol.mk_string context (symbol_string pfx sym)
  let symbol context sym = prefix_symbol context "" sym

  let bt_id bt = match BT_Table.find_opt bt_id_table bt with
    | Some id -> id
    | None ->
      let id = BT_Table.length bt_id_table + 1 in
      let () = BT_Table.add bt_id_table bt id in
      id

  let bt_pp_name bt =
    let open Pp in
    match bt with
      | BT.Struct nm -> !^ "struct_" ^^ Sym.pp nm
      | BT.Datatype nm -> !^ "datatype_" ^^ Sym.pp nm
      | BT.Tuple _ -> !^ "tuple_" ^^ Pp.int (bt_id bt)
      | BT.List _ -> !^ "list_" ^^ Pp.int (bt_id bt)
      | BT.Record mems -> !^ "rec_" ^^
          Pp.flow_map (!^ "_") (fun (nm, _) -> Sym.pp nm) mems ^^ !^ "_" ^^ Pp.int (bt_id bt)
      | _ -> BT.pp bt

  let bt_name bt = Pp.plain (bt_pp_name bt)

  let bt_suffix_name nm bt = Pp.plain (!^ nm ^^ !^ "_" ^^ bt_pp_name bt)

  let tuple_field_name bts i = 
    bt_name (Tuple bts) ^ string_of_int i

  let record_member_name bts member = 
    Sym.pp_string member ^ "_of_" ^ bt_name (Record bts)

  let member_name tag id = 
    bt_name (BT.Struct tag) ^ "_" ^ Id.s id

  let dt_recog_name context nm = prefix_symbol context "is_" nm


  let translate_datatypes other_sort context global =
    let to_translate = global.datatypes |> SymMap.bindings
      |> List.filter (fun (nm, _) -> not (BT_Table.mem bt_table (BT.Datatype nm)))
      |> List.mapi (fun i (nm, _) -> (nm, i))
    in
    let arg_sort bt = match bt with
      | BT.Datatype nm -> begin match BT_Table.find_opt bt_table bt with
          | Some sort -> (Some sort, 0)
          | None -> (None, List.assoc Sym.equal nm to_translate)
        end
      | _ -> (Some (other_sort bt), 0)
    in
    let conv_cons dt_nm nm =
      let info = SymMap.find nm global.datatype_constrs in
      let r = List.map (fun (_, bt) -> arg_sort bt) info.c_params in
      let sym = symbol context nm in
      let is_sym = dt_recog_name context nm in
      Z3Symbol_Table.add z3sym_table sym (DatatypeConsFunc {nm});
      (* Z3Symbol_Table.add z3sym_table is_sym (DatatypeConsRecogFunc {nm}); *)
      List.iter (fun (nm, bt) -> Z3Symbol_Table.add z3sym_table
          (symbol context nm) (DatatypeAccFunc {nm; dt = dt_nm; bt})) info.c_params;
      Z3.Datatype.mk_constructor context sym is_sym
          (List.map (fun (nm, _) -> symbol context nm) info.c_params)
          (List.map fst r) (List.map snd r)
    in
    let conv_dt nm =
      let info = SymMap.find nm global.datatypes in
      List.map (conv_cons nm) info.dt_constrs
    in
    let sorts = Z3.Datatype.mk_sorts context
        (List.map (fun (nm, _) -> symbol context nm) to_translate)
        (List.map (fun (nm, _) -> conv_dt nm) to_translate)
    in
    List.iter2 (fun (nm, _) sort -> begin
            BT_Table.add bt_table (BT.Datatype nm) sort;
            Sort_Table.add sort_table sort (BT.Datatype nm);
        end) to_translate sorts

  let sort : Z3.context -> Global.t -> BT.t -> sort =

    fun context global ->

    let string str = string context str in

    let rec translate = function
      | Unit -> Z3.Sort.mk_uninterpreted_s context "unit"
      | Bool -> Z3.Boolean.mk_sort context
      | Integer -> Z3.Arithmetic.Integer.mk_sort context
      | Real -> Z3.Arithmetic.Real.mk_sort context
      | Loc -> 
         Z3.Tuple.mk_sort context 
           (string (bt_name Loc))
           [string "loc_to_integer"] 
           [sort BT.Integer]
      | List bt -> (* lists are represented as uninterpreted sorts *)
        Z3.Sort.mk_uninterpreted_s context (bt_name (List bt))
      | Set bt -> Z3.Set.mk_sort context (sort bt)
      | Map (abt, rbt) -> Z3.Z3Array.mk_sort context (sort abt) (sort rbt)
      | Tuple bts ->
         let bt_symbol = string (bt_name (Tuple bts)) in
         Z3Symbol_Table.add z3sym_table bt_symbol (TupleFunc {bts});
         let field_symbols = 
           mapi (fun i _ -> 
               let sym = string (tuple_field_name bts i) in
               Z3Symbol_Table.add z3sym_table sym (CompFunc {bts; i});
               sym
             ) bts 
         in
         let sorts = map sort bts in
         Z3.Tuple.mk_sort context bt_symbol field_symbols sorts
      | Struct tag ->
         let struct_symbol = string (bt_name (Struct tag)) in
         Z3Symbol_Table.add z3sym_table struct_symbol (StructFunc {tag});
         let layout = SymMap.find tag global.struct_decls in
         let member_symbols, member_sorts = 
           map_split (fun (id,sct) -> 
               let s = string (member_name tag id) in
               Z3Symbol_Table.add z3sym_table s (MemberFunc {tag; member=id});
               (s, sort (BT.of_sct sct))
             ) (Memory.member_types layout)
         in
         Z3.Tuple.mk_sort context struct_symbol
           member_symbols member_sorts
      | Datatype tag ->
         translate_datatypes sort context global;
         BT_Table.find bt_table (Datatype tag)
      | Record members ->
         let bt_symbol = string (bt_name (Record members)) in
         Z3Symbol_Table.add z3sym_table bt_symbol (RecordFunc {mbts=members});
         let member_symbols = 
           map (fun (member, bt) -> 
               let sym = string (record_member_name members member) in
               Z3Symbol_Table.add z3sym_table sym (RecordMemberFunc {mbts=members; member});
               sym
             ) members
         in
         let member_sorts = map (fun (_, bt) -> sort bt) members in
         Z3.Tuple.mk_sort context bt_symbol
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



  let init global context = 
    BT_Table.clear bt_table;
    Sort_Table.clear sort_table;
    let _ = sort context global BT.Integer in
    let _ = sort context global BT.Bool in
    ()


  let loc_to_integer_fundecl context global = 
    nth (Z3.Tuple.get_field_decls (sort context global Loc)) 0

  let integer_to_loc_fundecl context global = 
    Z3.Tuple.get_mk_decl (sort context global Loc)
  

  let term ?(warn_lambda=true) context global : IT.t -> expr =

    let struct_decls = global.struct_decls in
    let sort bt = sort context global bt in
    let symbol sym = symbol context sym in
    let string str = string context str in

    (* let integer_to_loc_symbol = Z3.FuncDecl.get_name integer_to_loc_fundecl in *)
  
    let loc_to_integer l = 
      Z3.Expr.mk_app context 
        (loc_to_integer_fundecl context global) [l] 
    in
    let integer_to_loc i = 
      Z3.Expr.mk_app context 
        (integer_to_loc_fundecl context global) [i] 
    in


    let apply_matching_func sym_role fds args =
      let matching fd = equal_z3sym_table_entry sym_role
          (Z3Symbol_Table.find z3sym_table (Z3.FuncDecl.get_name fd))
      in
      let fd = List.find matching fds in
      Z3.FuncDecl.apply fd args
    in


    let rec term (IT (it_, bt)) =
      begin match it_ with
      | Sym s -> 
         Z3.Expr.mk_const context (symbol s) (sort bt)
      | Const (Z z) -> 
         Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
      | Const (Q q) -> 
         Z3.Arithmetic.Real.mk_numeral_s context (Q.to_string q)
      | Const (Pointer z) -> 
         integer_to_loc
           (Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z))
      | Const (Bool true) -> 
         Z3.Boolean.mk_true context
      | Const (Bool false) -> 
         Z3.Boolean.mk_false context
      | Const Unit -> 
         Z3.Expr.mk_const context (string "unit") (sort Unit)
      | Const (Default bt) -> 
         let sym = Z3.Symbol.mk_string context ("default" ^ (bt_name bt)) in
         let () = Z3Symbol_Table.add z3sym_table sym (DefaultFunc {bt}) in
         Z3.Expr.mk_const context sym (sort bt)
      | Const Null -> 
         integer_to_loc (term (int_ 0))
      | Binop (bop, t1, t2) -> 
         let open Z3.Arithmetic in
         let make_uf sym ret_sort args =
           let decl = Z3.FuncDecl.mk_func_decl context (symbol sym)
                        (List.map (fun it -> sort (IT.bt it)) args) (sort ret_sort)
           in
           Z3.Expr.mk_app context decl (List.map term args)
         in
         begin match bop with
         | Add -> mk_add context [term t1; term t2]
         | Sub -> mk_sub context [term t1; term t2]
         | Mul -> mk_mul context [term t1; term t2]
         | MulNoSMT -> 
            make_uf mul_no_smt_solver_sym (IT.bt t1) [t1; t2]
         | Div -> mk_div context (term t1) (term t2)
         | DivNoSMT ->
            make_uf div_no_smt_solver_sym (IT.bt t1) [t1; t2]
         | Exp -> 
            begin match is_z t1, is_z t2 with
            | Some z1, Some z2 when Z.fits_int z2 ->
               term (z_ (Z.pow z1 (Z.to_int z2)))
            | _, _ ->
               assert false
            end
         | ExpNoSMT ->
            make_uf exp_no_smt_solver_sym (Integer) [t1; t2]
         | Rem -> Integer.mk_rem context (term t1) (term t2)
         | RemNoSMT ->
            make_uf rem_no_smt_solver_sym (Integer) [t1; t2]
         | Mod -> Integer.mk_mod context (term t1) (term t2)
         | ModNoSMT ->
            make_uf mod_no_smt_solver_sym (Integer) [t1; t2]
         | LT -> mk_lt context (term t1) (term t2)
         | LE -> mk_le context (term t1) (term t2)
         | Min -> term (ite_ (le_ (t1, t2), t1, t2))
         | Max -> term (ite_ (ge_ (t1, t2), t1, t2))
         | XORNoSMT ->
            make_uf xor_no_smt_solver_sym (Integer) [t1; t2]
         | EQ -> Z3.Boolean.mk_eq context (term t1) (term t2)
         | SetMember -> Z3.Set.mk_membership context (term t1) (term t2)
         | SetUnion -> Z3.Set.mk_union context (map term [t1;t2])
         | SetIntersection -> Z3.Set.mk_intersection context (map term [t1;t2])
         | SetDifference -> Z3.Set.mk_difference context (term t1) (term t2)
         | Subset -> Z3.Set.mk_subset context (term t1) (term t2)
         | LTPointer -> 
            Z3.Arithmetic.mk_lt context (loc_to_integer (term t1)) 
              (loc_to_integer (term t2))
         | LEPointer -> 
            Z3.Arithmetic.mk_le context (loc_to_integer (term t1))
              (loc_to_integer (term t2))
         | And -> Z3.Boolean.mk_and context (map term [t1;t2])
         | Or -> Z3.Boolean.mk_or context (map term [t1;t2])
         | Impl -> Z3.Boolean.mk_implies context (term t1) (term t2)
         end
      | Not t -> Z3.Boolean.mk_not context (term t)
      | ITE (t1, t2, t3) -> Z3.Boolean.mk_ite context (term t1) (term t2) (term t3)
      | EachI ((i1, s, i2), t) -> 
         let rec aux i = 
           if i <= i2 
           then IT.subst (make_subst [(s, int_ i)]) t :: aux (i + 1)
           else []
         in
         term (and_ (aux i1))
      | Tuple ts ->
         let constructor = Z3.Tuple.get_mk_decl (sort bt) in
         Z3.Expr.mk_app context constructor (map term ts)
      | NthTuple (n, t) ->
         let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
         Z3.Expr.mk_app context (nth destructors n) [term t]
      | Struct (tag, mts) ->
         let constructor = Z3.Tuple.get_mk_decl (sort bt) in
         Z3.Expr.mk_app context constructor (map (fun (_, t) -> term t) mts)
      | StructMember (t, member) ->
         let layout = SymMap.find (struct_bt (IT.bt t)) struct_decls in
         let n = Option.get (Memory.member_number layout member) in
         let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
         Z3.Expr.mk_app context (nth destructors n) [term t]
      | StructUpdate ((t, member), v) ->
         let tag = BT.struct_bt (IT.bt t) in
         let layout = SymMap.find (struct_bt (IT.bt t)) struct_decls in
         let members = Memory.member_types layout in
         let str =
           List.map (fun (member', sct) ->
               let value = 
                 if Id.equal member member' then v 
                 else member_ ~member_bt:(BT.of_sct sct) (tag, t, member')
               in
               (member', value)
             ) members
         in
         term (struct_ (tag, str))
      | Record mts ->
         let constructor = Z3.Tuple.get_mk_decl (sort bt) in
         Z3.Expr.mk_app context constructor (map (fun (_, t) -> term t) mts)
      | RecordMember (t, member) ->
         let members = BT.record_bt (IT.bt t) in
         let members_i = List.mapi (fun i (m, _) -> (m, i)) members in
         let n = List.assoc Sym.equal member members_i in
         let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
         Z3.Expr.mk_app context (nth destructors n) [term t]
      | RecordUpdate ((t, member), v) ->
         let members = BT.record_bt (IT.bt t) in
         let str =
           List.map (fun (member', bt) ->
               let value = 
                 if Sym.equal member member' then v 
                 else IT ((RecordMember (t, member')), bt)
               in
               (member', value)
             ) members
         in
         term (IT ((Record str), IT.bt t))
      | DatatypeCons (c_nm, elts_rec) ->
         (* ensure datatype added first *)
         let dt_sort = sort bt in
         let info = SymMap.find c_nm global.datatype_constrs in
         let args = List.map (fun (nm, _) -> term (Simplify.IndexTerms.record_member_reduce elts_rec nm))
                      info.c_params in
         apply_matching_func (DatatypeConsFunc {nm = c_nm})
           (Z3.Datatype.get_constructors dt_sort) args
      | DatatypeMember (it, member) ->
         (* ensure datatype added first *)
         let dt_sort = sort (IT.bt it) in
         let dt_nm = match IT.bt it with
           | BT.Datatype nm -> nm
           | _ -> assert false
         in
         apply_matching_func (DatatypeAccFunc {nm = member; dt = dt_nm; bt})
           (List.concat (Z3.Datatype.get_accessors dt_sort)) [term it]
      | DatatypeIsCons (c_nm, t) ->
         (* ensure datatype added *)
         let dt_sort = sort (IT.bt t) in
         let recogs = Z3.Datatype.get_recognizers dt_sort in
         (* something's funny with these recognizers. assume in same order as constructors *)
         let dt_nm = Option.get (BT.is_datatype_bt (IT.bt t)) in
         let info = SymMap.find dt_nm global.datatypes in
         let assocs = List.map2 (fun c_nm fd -> (c_nm, fd)) info.dt_constrs recogs in
         let fd = List.assoc Sym.equal c_nm assocs in
         Z3.FuncDecl.apply fd [term t]
      | Cast (cbt, t) ->
         begin match IT.bt t, cbt with
         | Integer, Loc ->
            integer_to_loc (term t)
         | Loc, Integer ->
            loc_to_integer (term t)
         | Real, Integer ->
            Z3.Arithmetic.Real.mk_real2int context (term t)
         | Integer, Real ->
            Z3.Arithmetic.Integer.mk_int2real context (term t)
         | _ -> 
            assert false
         end
      | MemberOffset (tag, member) ->
         let decl = SymMap.find tag struct_decls in
         term (int_ (Option.get (Memory.member_offset decl member)))
      | ArrayOffset (ct, t) -> 
         term (mul_ (int_ (Memory.size_of_ctype ct), t))
      | NthList (i, xs, d) ->
         let args = List.map term [i; xs; d] in
         let nm = bt_suffix_name "nth_list" bt in
         let fdec = Z3.FuncDecl.mk_func_decl_s context nm
                      (List.map sort (List.map IT.bt [i; xs; d])) (sort bt) in
         Z3.FuncDecl.apply fdec args
      | ArrayToList (arr, i, len) ->
         let args = List.map term [arr; i; len] in
         let list_bt = Option.get (BT.is_list_bt bt) in
         let nm = bt_suffix_name "array_to_list" list_bt in
         let fdec = Z3.FuncDecl.mk_func_decl_s context nm
                      (List.map sort (List.map IT.bt [arr; i; len])) (sort bt) in
         Z3.FuncDecl.apply fdec args
      | Aligned t ->
         term (divisible_ (pointerToIntegerCast_ t.t, t.align))
      | Representable (ct, t) ->
         term (representable struct_decls ct t)
      | Good (ct, t) ->
         term (good_value struct_decls ct t)
      | MapConst (abt, t) -> 
         Z3.Z3Array.mk_const_array context (sort abt) (term t)
      | MapSet (t1, t2, t3) -> 
         Z3.Z3Array.mk_store context (term t1) (term t2) (term t3)
      (* | MapGet (IT (Map_op (Def ((s, bt), body)), _), arg) ->  *)
      (*    term (IT.subst (make_subst [(s, arg)]) body) *)
      | MapGet (f, arg) -> 
         Z3.Z3Array.mk_select context (term f) (term arg)
      | MapDef ((q_s, q_bt), body) ->
         if warn_lambda then
           warn_noloc (!^"generating lambda");
         (* warn (!^"generating lambda" ^^ colon ^^^ IT.pp (IT (it_, bt))); *)
         Z3.Quantifier.expr_of_quantifier
           (Z3.Quantifier.mk_lambda_const context
              [term (sym_ (q_s, q_bt))] (term body))
      | Apply (name, args) ->
         let def = Option.get (get_logical_function_def global name) in
         begin match def.definition with
         | Def body ->
            term (LogicalFunctions.Body.to_term def.return_bt
                    (LogicalFunctions.open_fun def.args body args))
         | _ ->
            let decl = 
              Z3.FuncDecl.mk_func_decl context (symbol name)
                (List.map (fun it -> sort (IT.bt it)) args)
                (sort def.return_bt)
            in
            Z3.Expr.mk_app context decl (List.map term args)
       end
      | _ ->
         Debug_ocaml.error "todo: SMT mapping"
      end

    in

    fun it -> 
    term it


    


  let assumption context global c = 
    let term it = term context global it in
    match c with
    | T it -> 
       Some (term it)
    | Forall ((s, bt), body) ->
       None
       (* let q =  *)
       (*   Z3.Quantifier.mk_forall_const context  *)
       (*     [term (sym_ (s, bt))] (term body)  *)
       (*     None [] [] None None  *)
       (* in *)
       (* Some (Z3.Quantifier.expr_of_quantifier q) *)


  type reduction = {
      expr : Z3.Expr.expr;
      it : IT.t;
      qs : (Sym.t * BT.t) list;
    }

  let goal context global lc =
    let term it = term context global it in
    match lc with
    | T it -> 
       { expr = term it; it; qs = [] }
    | Forall ((s, bt), it) -> 
       let v_s, v = IT.fresh_same bt s in
       let it = IT.subst (make_subst [(s, v)]) it in
       { expr = term it; it; qs = [(v_s, bt)] }


  let extra_assumptions assumptions qs = 
    List.concat_map (fun (s, bt) ->
        let v = sym_ (s, bt) in
        LCSet.fold (fun lc acc ->
            match lc with
            | Forall ((s', bt'), it') when BT.equal bt bt' ->
               IT.subst (make_subst [(s', v)]) it' :: acc
            | _ -> acc
          ) assumptions []
      ) qs


  let extra_logical_facts global terms constraints =
    let ts = List.filter_map (function | LC.T t -> Some t | _ -> None) constraints in
    let all_ts = LogicalFunctions.add_unfolds_to_terms
        global.logical_functions (ts @ terms) in
    IT.nth_array_to_list_facts all_ts


end









let tactics context ts = 
  match List.map (Z3.Tactic.mk_tactic context) ts with
  | [] -> Z3.Tactic.skip context
  | [t] -> t
  | t1::t2::ts -> Z3.Tactic.and_then context t1 t2 ts

let tactic context = 
  tactics context [
      "propagate-values";
      "solve-eqs";
      "smt";
    ]

let make global : solver = 
  Z3.Memory.reset ();

  List.iter (fun (c,v) -> Z3.set_global_param c v) (params ());

  let context = Z3.mk_context [] in

  Translate.init global context;

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


let add_assumption solver global lc = 
  (* do nothing to fancy solver, because that is reset for every query *)
  match Translate.assumption solver.context global lc with
  | None -> ()
  | Some sc -> Z3.Solver.add solver.incremental [sc]


(* as similarly suggested by Robbert *)
let shortcut simp_ctxt lc = 
  let lc = Simplify.LogicalConstraints.simp simp_ctxt lc in
  match lc with
  | LC.T (IT (Const (Bool true), _)) -> `True
  | _ -> `No_shortcut lc





type model_state =
  | Model of Z3.context * Z3.Solver.solver * (Sym.t * LogicalSorts.t) list
  | No_model

let model_state = 
  ref No_model



let model () = 
  match !model_state with
  | No_model ->
     assert false
  | Model (context, z3_solver, qs) ->
     let omodel = Z3.Solver.get_model z3_solver in
     let model = Option.value_err "SMT solver did not produce a counter model" omodel in
     ((context, model), qs)

let maybe_save_slow_problem solv_inst lc lc_t time solver = match save_slow_problems () with
  | (_, _, None) -> ()
  | (_, cutoff, _) when (Stdlib.Float.compare time cutoff) = -1 -> ()
  | (prev_msg, _, Some fname) ->
    let channel = open_out_gen [Open_append; Open_creat] 0o666 fname in
    output_string channel "\n\n";
    if prev_msg then output_string channel "## New CN run ##\n\n" else ();
    Colour.without_colour (fun () -> print channel (item "Slow problem"
      (Pp.list (fun pp -> pp) [
          item "time taken" (format [] (Float.to_string time));
          item "constraint" (LC.pp lc);
          item "SMT constraint" !^(Z3.Expr.to_string lc_t);
          if !Pp.print_level >= 10 then item "solver statistics" !^(Z3.Statistics.to_string (Z3.Solver.get_statistics solver)) else Pp.empty;
          if !Pp.print_level >= 11 then item "SMT assertions" (Pp.list (fun e -> format [] (Z3.Expr.to_string e)) (Z3.Solver.get_assertions solv_inst)) else Pp.empty;
      ]))) ();
    output_string channel "\n";
    saved_slow_problem ();
    close_out channel

let provable ~loc ~solver ~global ~assumptions ~simp_ctxt ~pointer_facts lc = 
  debug 12 (lazy (item "provable: checking constraint" (LC.pp lc)));
  let context = solver.context in
  debug 13 (lazy (item "context" (Context.pp_constraints assumptions)));
  let rtrue () = model_state := No_model; `True in
  let rfalse qs solver = model_state := Model (context, solver, qs); `False in
  match shortcut simp_ctxt lc with
  | `True -> rtrue ()
  | `No_shortcut lc ->
     let Translate.{expr; it; qs} = Translate.goal context global lc in
     let nlc = Z3.Boolean.mk_not context expr in
     let extra1 = pointer_facts @ Translate.extra_assumptions assumptions qs in
     let extra2 = Translate.extra_logical_facts global
         (it :: extra1) (LCSet.elements assumptions) in
     let assumptions = List.map (Translate.term context global) (extra1 @ extra2) in
     let res = 
       time_f_logs loc 5 "Z3(inc)"
         (Z3.Solver.check solver.incremental) 
         (nlc :: assumptions) 
     in
     match res with
     | Z3.Solver.UNSATISFIABLE -> rtrue ()
     | Z3.Solver.SATISFIABLE -> rfalse qs solver.incremental
     | Z3.Solver.UNKNOWN ->
        debug 5 (lazy (format [] "Z3(inc) unknown/timeout, running full solver"));
        let (elapsed, res) = 
          time_f_elapsed 
            (time_f_logs loc 5 "Z3"
               (Z3.Solver.check solver.fancy))
            (nlc :: assumptions @ Z3.Solver.get_assertions solver.incremental)
        in
        maybe_save_slow_problem solver.fancy lc expr elapsed solver.fancy;
        match res with
        | Z3.Solver.UNSATISFIABLE -> rtrue ()
        | Z3.Solver.SATISFIABLE -> rfalse qs solver.fancy
        | Z3.Solver.UNKNOWN -> 
           let reason = Z3.Solver.get_reason_unknown solver.fancy in
           failwith ("SMT solver returned 'unknown'; reason: " ^ reason)


module Eval = struct

  open Translate

  let trace_z3_evals = ref false

  let trace_z3_eval expr evaluated =
    if ! trace_z3_evals then
      Pp.debug 8 (lazy (Pp.item "Z3 evaluation" (Pp.list
        (fun expr -> Pp.string (Z3.Expr.to_string expr)) [expr; evaluated])))
    else ()


  let is_array_sort sort = 
    try 
      Some (Z3.Z3Array.get_domain sort, 
            Z3.Z3Array.get_range sort) 
    with 
    | _ -> None

  let find_already_translated_sort sort = 
    try Sort_Table.find sort_table sort with
    | Not_found -> failwith (Z3.Sort.to_string sort^"' not in Sort_Table")

  let rec z3_sort (sort : Z3.Sort.sort) = 
    match is_array_sort sort with
    | Some (domain, range) -> Map (z3_sort domain, z3_sort range)
    | None -> find_already_translated_sort sort


  let eval global (context, model) to_be_evaluated = 

    let unsupported expr what = 
      let err = 
        Printf.sprintf "unsupported %s. expr: %s"
          what (Z3.Expr.to_string expr)
      in
      failwith err
    in

    (* informed by this: https://stackoverflow.com/questions/22885457/read-func-interp-of-a-z3-array-from-the-z3-model/22918197 *)
    let rec func_interp func_decl = 
      let domain = Z3.FuncDecl.get_domain func_decl in
      assert (List.length domain = 1);
      let argument_sort = List.hd domain in
      let func_interp = Option.get (Z3.Model.get_func_interp model func_decl) in
      let base_value = z3_expr (Z3.Model.FuncInterp.get_else func_interp) in
      let entries = Z3.Model.FuncInterp.get_entries func_interp in
      List.fold_right (fun entry map_value ->
          let entry_args = Z3.Model.FuncInterp.FuncEntry.get_args entry in
          assert (List.length entry_args = 1);
          let index = List.hd entry_args in
          let value = z3_expr (Z3.Model.FuncInterp.FuncEntry.get_value entry) in
          map_set_ map_value (z3_expr index, value)
        ) entries (const_map_ (z3_sort argument_sort) base_value)


    and z3_expr (expr : Z3.Expr.expr) : IT.t = 
      let args = try Z3.Expr.get_args expr with | _ -> [] in
      let args = List.map z3_expr args in
      match () with

      | () when Z3.AST.is_quantifier (Z3.Expr.ast_of_expr expr) ->
         unsupported expr "quantifiers/lambdas"

      | () when Z3.Arithmetic.is_add expr ->
         List.fold_left (Tools.curry add_) (hd args) (tl args)

      | () when Z3.Boolean.is_and expr ->
         and_ args

      | () when Z3.Z3Array.is_as_array expr ->
         (* informed by this:
            https://stackoverflow.com/questions/22885457/read-func-interp-of-a-z3-array-from-the-z3-model/22918197 *)
         let as_array_func_parameter = List.hd (Z3.FuncDecl.get_parameters (Z3.Expr.get_func_decl expr)) in
         let func_decl = Z3.FuncDecl.Parameter.get_func_decl as_array_func_parameter in
         func_interp func_decl

      | () when Z3.Z3Array.is_constant_array expr ->
         let abt = z3_sort (Z3.Z3Array.get_range (Z3.Expr.get_sort expr)) in
         const_map_ abt (hd args)

      | () when Z3.Z3Array.is_default_array expr ->
         unsupported expr "z3 array default"

      | () when Z3.Set.is_difference expr ->
         setDifference_ (nth args 0, nth args 1)

      | () when Z3.Boolean.is_distinct expr ->
         unsupported expr "z3 is_distinct"

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

      | () when Z3.AST.is_var (Z3.Expr.ast_of_expr expr) ->
         unsupported expr "variables from quantifiers/lambdas"

      | () ->
        let func_decl = Z3.Expr.get_func_decl expr in
        let func_name = Z3.FuncDecl.get_name func_decl in
        let expr_bt = z3_sort (Z3.Expr.get_sort expr) in
        match () with

        | () when 
               Z3.FuncDecl.equal func_decl
                 (loc_to_integer_fundecl context global) ->
           let p = nth args 0 in
           begin match IT.is_pointer p with
           | Some z -> z_ z
           | _ -> pointerToIntegerCast_ p
           end

        | () when 
               Z3.FuncDecl.equal func_decl 
                 (integer_to_loc_fundecl context global) ->
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
              let sd = Memory.member_types (SymMap.find tag global.struct_decls) in
              let member_bt = BT.of_sct (List.assoc Id.equal member sd) in
              member_ ~member_bt (tag, nth args 0, member)
           | StructFunc {tag} ->
              let sd = Memory.members (SymMap.find tag global.struct_decls) in
              struct_ (tag, List.combine sd args)
           | CompFunc {bts; i} ->
              let comp_bt = List.nth bts i in
              nthTuple_ ~item_bt:comp_bt (i, nth args 0)
           | TupleFunc {bts} ->
              tuple_ args
           | RecordFunc {mbts} ->
              IT ((Record (List.combine (List.map fst mbts) args)), 
                  Record mbts)
           | RecordMemberFunc {mbts; member} ->
              let member_bt = List.assoc Sym.equal member mbts in
              IT ((RecordMember (nth args 0, member)), member_bt)
           | DatatypeConsFunc {nm} ->
              let info = SymMap.find nm global.datatype_constrs in
              datatype_cons_ nm info.c_datatype_tag
                  (List.combine (List.map fst info.c_params) args)
           | DatatypeConsRecogFunc {nm} ->
              (* not supported inside CN, hopefully we shouldn't need it *)
              unsupported expr ("Reconstructing Z3 term with datatype recogniser")
           | DatatypeAccFunc xs ->
              Simplify.IndexTerms.datatype_member_reduce (nth args 0) xs.nm xs.bt
           | UninterpretedVal {nm} -> sym_ (nm, expr_bt)
           end

        | () when String.equal (Z3.Symbol.to_string func_name) "^" ->
           exp_ (nth args 0, nth args 1)

        | () when Z3.Arithmetic.is_real2int expr ->
           realToInt_ (nth args 0)

        | () when Z3.Arithmetic.is_int2real expr ->
           intToReal_ (nth args 0)

        | () when BT.equal Unit expr_bt ->
           unit_

        | () when Option.is_some (BT.is_list_bt expr_bt) && List.length args == 0 ->
           (* Z3 creates unspecified consts within uninterpreted types - map to vars *)
           let nm = Sym.fresh_named (Z3.Symbol.to_string func_name) in
           Z3Symbol_Table.add z3sym_table func_name (UninterpretedVal {nm});
           sym_ (nm, expr_bt)

        | () when Option.is_some (Z3.Model.get_func_interp model func_decl) ->
           assert (List.length args = 1);
           map_get_ (func_interp func_decl) (List.hd args)

        | () ->
           unsupported expr ("Reconstructing unknown Z3 term")

    in

    let expr = Translate.term ~warn_lambda:false context global to_be_evaluated in
    match Z3.Model.eval model expr true with
    | None -> None
    | Some v ->
      trace_z3_eval expr v;
      Some (z3_expr v)

end

let eval = Eval.eval
