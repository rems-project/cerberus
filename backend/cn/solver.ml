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
module StringSet = Set.Make(String)


let random_seed = ref 1
let log_to_temp = ref false

let slow_smt_file () =
  let open Filename in
  get_temp_dir_name () ^ dir_sep ^ "slow_smt.txt"


let save_slow_problems, saved_slow_problem, set_slow_threshold =
  (* not yet written this run, > 3.0s counts as slow, append to this fname *)
  let slow_problem_ref = ref (true, 3.0, None) in
  let save_slow_problems () = (! slow_problem_ref) in
  let saved_slow_problem () = match ! slow_problem_ref with
    | (true, t, fn) -> slow_problem_ref := (false, t, fn)
    | _ -> ()
  in
  let set_slow_threshold t =
    (slow_problem_ref := (true, t, Some (slow_smt_file ())))
  in
  save_slow_problems, saved_slow_problem, set_slow_threshold


type solver = {
    context : Z3.context;
    incremental : Z3.Solver.solver;
    focus_terms : ((IT.t_bindings * IT.t) list) ref;
  }
type expr = Z3.Expr.expr
type sort = Z3.Sort.sort
type model = Z3.context * Z3.Model.model
type model_with_q = model * (Sym.t * BT.t) list




let log_file () = match ! log_to_temp with
  | false -> None
  | true -> Some (Filename.get_temp_dir_name () ^ "/z3_log.smt")

let logging_params () = match log_file () with
  | None -> []
  | Some fname -> [ ("solver.smtlib2_log", fname ) ]

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
    ("smt.macro_finder", "false");
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
  logging_params ()
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
    | RecordMemberFunc of { mbts : BT.member_types; member : Id.t }
    | DefaultFunc of { bt : BT.t }
    | DatatypeConsFunc of { nm: Sym.t }
    | DatatypeConsRecogFunc of { nm: Sym.t }
    | DatatypeAccFunc of { member: Id.t; dt: Sym.t; bt: BT.t }
    | UninterpretedVal of { nm : Sym.t }
    | Term of { it : IT.t }
    | UnsignedToSigned of int
    | SignedToUnsigned of int
  [@@deriving eq]


  module Z3ExprMap = Map.Make(struct type t = Z3.Expr.expr let compare = Z3.Expr.compare end)



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
      | BT.Tuple [BT.Alloc_id; BT.Integer] -> !^ "pointer"
      | BT.Tuple _ -> !^ "tuple_" ^^ Pp.int (bt_id bt)
      | BT.List _ -> !^ "list_" ^^ Pp.int (bt_id bt)
      | BT.Set _ -> !^ "set_" ^^ Pp.int (bt_id bt)
      | BT.Map _ -> !^ "map_" ^^ Pp.int (bt_id bt)
      | BT.Record mems -> !^ "rec_" ^^ Pp.int (bt_id bt) ^^
          Pp.flow_map (!^ "_") (fun (nm, _) -> Id.pp nm) mems ^^ !^ "_" ^^ Pp.int (bt_id bt)
      | _ -> BT.pp bt

  let bt_name bt = Pp.plain (bt_pp_name bt)

  let bt_suffix_name nm bt = Pp.plain (!^ nm ^^ !^ "_" ^^ bt_pp_name bt)

  module ITMap = Map.Make(IT)

  let uninterp_tab = ref (ITMap.empty, 0)

  let uninterp_term context sort (it : IT.t) =
    let (m, n) = ! uninterp_tab in
    match ITMap.find_opt it m with
    | Some z3_exp -> z3_exp
    | None -> begin
      let nm = "uninterp_" ^ Int.to_string n ^ "_" ^ bt_name (IT.bt it) in
      let sym = string context nm in
      let z3_exp = Z3.Expr.mk_const context sym sort in
      uninterp_tab := (ITMap.add it z3_exp m, n + 1);
      Z3Symbol_Table.add z3sym_table sym (Term {it});
      z3_exp
    end

  let is_uninterp_bt (bt : BT.t) = match bt with
    | Unit -> true
    | CType -> true
    | List bt -> true
    | _ -> false

  let tuple_field_name bts i =
    bt_name (Tuple bts) ^ string_of_int i

  let record_member_name bts member =
    Id.pp_string member ^ "_of_" ^ bt_name (Record bts)

  let accessor_name dt_name member =
    symbol_string "" dt_name ^ "_" ^ Id.s member

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
      List.iter (fun (member, bt) -> Z3Symbol_Table.add z3sym_table
          (string context (accessor_name dt_nm member)) (DatatypeAccFunc {member; dt = dt_nm; bt})) info.c_params;
      Z3.Datatype.mk_constructor context sym is_sym
          (List.map (fun (member, _) -> string context (accessor_name dt_nm member)) info.c_params)
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
      | Bits (Unsigned, n) -> 
         Z3.BitVector.mk_sort context n
      | Bits (Signed, n) -> 
         (*copying/adjusting Dhruv's code for Alloc_id*)
         let bt_symbol = string (bt_name (Bits (Signed, n))) in
         let field_symbol = string ("unsigned_" ^ string_of_int n) in
         Z3Symbol_Table.add z3sym_table bt_symbol (UnsignedToSigned n);
         Z3Symbol_Table.add z3sym_table field_symbol (SignedToUnsigned n);
         Z3.Tuple.mk_sort context
            bt_symbol
            [field_symbol]
            [sort (Bits (Unsigned, n))]
      | Real -> Z3.Arithmetic.Real.mk_sort context
      | Loc -> translate BT.(Tuple [Alloc_id; Memory.intptr_bt])
      | Alloc_id ->
         Z3.Tuple.mk_sort context
           (string (bt_name Alloc_id))
           [string "alloc_id_to_integer"]
           [sort BT.Integer]
      | CType -> (* the ctype type is represented as an uninterpreted sort *)
        Z3.Sort.mk_uninterpreted_s context (bt_name CType)
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
               (s, sort (Memory.bt_of_sct sct))
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


  let loc_to_alloc_id_fundecl context global =
    nth (Z3.Tuple.get_field_decls (sort context global Loc)) 0

  let loc_to_addr_fundecl context global =
    nth (Z3.Tuple.get_field_decls (sort context global Loc)) 1

  let alloc_id_addr_to_loc_fundecl context global =
    Z3.Tuple.get_mk_decl (sort context global Loc)

  let integer_to_alloc_id_fundecl context global =
    Z3.Tuple.get_mk_decl (sort context global Alloc_id)

  (*copying/adjusting Dhruv's code from above*)
  let signed_to_unsigned_fundecl context global n =
   nth (Z3.Tuple.get_field_decls (sort context global (Bits (Signed, n)))) 0

 let unsigned_to_signed_fundecl context global n =
   Z3.Tuple.get_mk_decl (sort context global (Bits (Signed, n)))


  let adjust_term global : IT.t -> IT.t option =

    let struct_decls = global.struct_decls in

    let intptr_cast = cast_ Memory.intptr_bt in

    fun it ->
      begin match IT.term it with
      | Const Null -> Some (pointer_ Z.zero)
      | Binop (op, t1, t2) -> begin match op with
         | Exp -> begin match is_z t1, is_z t2 with
            | Some z1, Some z2 when Z.fits_int z2 ->
              Some (z_ (Z.pow z1 (Z.to_int z2)))
            | _, _ ->
              assert false
            end
         | Min -> Some (ite_ (le_ (t1, t2), t1, t2))
         | Max -> Some (ite_ (ge_ (t1, t2), t1, t2))
         | LTPointer -> Some (lt_ (intptr_cast t1, intptr_cast t2))
         | LEPointer -> Some (le_ (intptr_cast t1, intptr_cast t2))
         | _ -> None
         end
      | EachI ((i1, (s, _), i2), t) ->
         let rec aux i =
           if i <= i2
           then IT.subst (make_subst [(s, int_ i)]) t :: aux (i + 1)
           else []
         in
         Some (and_ (aux i1))
      | StructUpdate ((t, member), v) ->
         let tag = BT.struct_bt (IT.bt t) in
         let layout = SymMap.find (struct_bt (IT.bt t)) struct_decls in
         let members = Memory.member_types layout in
         let str =
           List.map (fun (member', sct) ->
               let value =
                 if Id.equal member member' then v
                 else member_ ~member_bt:(Memory.bt_of_sct sct) (tag, t, member')
               in
               (member', value)
             ) members
         in
         Some (struct_ (tag, str))
      | RecordUpdate ((t, member), v) ->
         let members = BT.record_bt (IT.bt t) in
         let str =
           List.map (fun (member', bt) ->
               let value =
                 if Id.equal member member' then v
                 else IT ((RecordMember (t, member')), bt)
               in
               (member', value)
             ) members
         in
         Some (IT ((Record str), IT.bt t))
      | MemberOffset (tag, member) ->
         let decl = SymMap.find tag struct_decls in
         Some (int_lit_ (Option.get (Memory.member_offset decl member)) Memory.intptr_bt)
      | ArrayOffset (ct, t) ->
         Some (mul_ (int_lit_ (Memory.size_of_ctype ct) Memory.intptr_bt, cast_ Memory.intptr_bt t))
      | SizeOf ct ->
         Some (int_lit_ (Memory.size_of_ctype ct) (IT.bt it))
      | Aligned t ->
         let addr = pointerToIntegerCast_ t.t in
         assert (BT.equal (IT.bt addr) (IT.bt t.align));
         Some (divisible_ (addr, t.align))
      | Representable (CT.Pointer _ as ct, t) ->
         Some (representable struct_decls ct t)
      | Representable (ct, t) ->
         Some (representable struct_decls ct t)
      | Good (ct, t) ->
         Some (good_value struct_decls ct t)
      | WrapI (ity, arg) ->
         (* unlike previously (and std.core), implemented natively using bitvector ops *)
         None
      | Apply (name, args) ->
         let def = Option.get (get_logical_function_def global name) in
         begin match def.definition with
         | Def body ->
            Some (LogicalFunctions.open_fun def.args body args)
         | _ -> None
         end
      | Let ((nm, t1), t2) ->
         Some (IT.substitute_lets it)
      | _ ->
         None
      end


  let term ?(warn_lambda=true) context global : IT.t -> expr =

    let struct_decls = global.struct_decls in
    let sort bt = sort context global bt in
    let symbol sym = symbol context sym in
    let string str = string context str in

    (* let integer_to_loc_symbol = Z3.FuncDecl.get_name integer_to_loc_fundecl in *)

    let loc_to_addr l =
      Z3.Expr.mk_app context
        (loc_to_addr_fundecl context global) [l]
    in

    let loc_to_alloc_id l =
      Z3.Expr.mk_app context
        (loc_to_alloc_id_fundecl context global) [l]
    in

    let integer_to_alloc_id i =
      Z3.Expr.mk_app context
        (integer_to_alloc_id_fundecl context global) [i]
    in

    let alloc_id_addr_to_loc id i =
      Z3.Expr.mk_app context
        (alloc_id_addr_to_loc_fundecl context global) [id; i]
    in

    let apply_matching_func sym_role fds args =
      let matching fd = equal_z3sym_table_entry sym_role
          (Z3Symbol_Table.find z3sym_table (Z3.FuncDecl.get_name fd))
      in
      let fd = List.find matching fds in
      Z3.FuncDecl.apply fd args
    in


    let mk_bv_cast context (to_bt, from_bt, x) =
      let bits_info bt = match BT.is_bits_bt bt with
        | Some (sign, sz) -> (BT.equal_sign sign BT.Signed, sz)
        | None -> failwith ("mk_bv_cast: non-bv type: " ^ Pp.plain (BT.pp bt))
      in
      let (to_signed, to_sz) = bits_info to_bt in
      let (from_signed, from_sz) = bits_info from_bt in
      let step1 = if from_signed
        then Z3.Expr.mk_app context (signed_to_unsigned_fundecl context global from_sz) [x]
        else x
      in
      let step2 = if to_sz == from_sz
        then step1
        else if to_sz < from_sz
        then Z3.BitVector.mk_extract context (to_sz - 1) 0 step1
        else if from_signed
        then Z3.BitVector.mk_sign_ext context (to_sz - from_sz) step1
        else Z3.BitVector.mk_zero_ext context (to_sz - from_sz) step1
      in
      if to_signed
        then Z3.Expr.mk_app context (unsigned_to_signed_fundecl context global to_sz) [step2]
        else step2
    in

    let unsigned_of bt = match bt with
      | BT.Bits (BT.Signed, n) -> BT.Bits (BT.Unsigned, n)
      | _ -> failwith ("unsigned_of: not signed")
    in
    let via_unsigned context bt op t1 t2 =
      let to_u t = mk_bv_cast context (unsigned_of bt, bt, t) in
      mk_bv_cast context (bt, unsigned_of bt, op (to_u t1) (to_u t2))
    in
    let cmp_in_unsigned context bt op t1 t2 =
      let to_u t = mk_bv_cast context (unsigned_of bt, bt, t) in
      op (to_u t1) (to_u t2)
    in

    let rec term it =
      let bt = IT.bt it in
      let adj () = match adjust_term global it with
      | None ->
        Pp.debug 1 (lazy (Pp.item "Translate.term: failed to adjust_term" (IT.pp it)));
        assert false
      | Some it2 ->
        term it2
      in
      begin match IT.term it with
      | Sym s ->
         Z3.Expr.mk_const context (symbol s) (sort bt)
      | Const (Z z) ->
         Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
      | Const (Bits ((Unsigned,n),v)) ->
         Z3.BitVector.mk_numeral context (Z.to_string v) n
      | Const (Bits ((Signed,n),v)) ->
         Z3.Expr.mk_app context
           (unsigned_to_signed_fundecl context global n)
           [Z3.BitVector.mk_numeral context (Z.to_string v) n]
      | Const (Q q) ->
         Z3.Arithmetic.Real.mk_numeral_s context (Q.to_string q)
      | Const (Pointer z) ->
         alloc_id_addr_to_loc
           (term (alloc_id_ Z.zero))
           (term (intptr_const_ z))
      | Const (Alloc_id z) ->
         integer_to_alloc_id
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
      | Const Null -> adj ()
      | Const (CType_const ct) -> uninterp_term context (sort bt) it
      | Unop (uop, t) ->
         begin match uop with
           | Not -> Z3.Boolean.mk_not context (term t)
         (* | BWCLZNoSMT -> make_uf "bw_clz_uf" (Integer) [t] *)
         (* | BWCTZNoSMT -> make_uf "bw_ctz_uf" (Integer) [t] *)
         (* | BWFFSNoSMT -> make_uf "bw_ffs_uf" (Integer) [t] *)
           | _ ->
           Pp.debug 1 (lazy (Pp.item "not yet restored" (IT.pp_with_typ it)));
           failwith "todo"
         end
      | Binop (bop, t1, t2) ->
         if BT.equal (IT.bt t1) (IT.bt t2)
           then ()
           else begin
             Pp.debug 1 (lazy (Pp.item "mismatching binop" (IT.pp it)));
             assert false
           end;
         let open Z3.Arithmetic in
         let module BV = Z3.BitVector in
         let bv_arith_case t sgn_v u_v arith_v = match IT.bt t with
           | BT.Bits (BT.Signed, _) -> sgn_v
           | BT.Bits (BT.Unsigned, _) -> u_v
           | BT.Integer -> arith_v
           | BT.Real -> arith_v
           | _ -> failwith "bv_arith_case"
         in
         let l_bop f ctxt x y = f ctxt [x; y] in
         let via_u t op ctxt = via_unsigned ctxt (IT.bt t) (op ctxt) in
         let cmp_u t op ctxt = cmp_in_unsigned ctxt (IT.bt t) (op ctxt) in
         begin match bop with
         | Add -> (bv_arith_case t1 (via_u t1 BV.mk_add) BV.mk_add (l_bop mk_add))
                 context (term t1) (term t2)
         | Sub -> (bv_arith_case t1 (via_u t1 BV.mk_sub) BV.mk_sub (l_bop mk_sub))
                 context (term t1) (term t2)
         | Mul -> (bv_arith_case t1 (via_u t1 BV.mk_mul) BV.mk_mul (l_bop mk_mul))
                 context (term t1) (term t2)
         | MulNoSMT -> make_uf "mul_uf" (IT.bt t1) [t1; t2]
         | Div -> (bv_arith_case t1 BV.mk_sdiv BV.mk_udiv mk_div) context (term t1) (term t2)
         | DivNoSMT -> make_uf "div_uf" (IT.bt t1) [t1; t2]
         | Exp -> adj ()
         | ExpNoSMT -> make_uf "exp_uf" (Integer) [t1; t2]
         | Rem -> (bv_arith_case t1 (via_u t1 BV.mk_srem) BV.mk_urem Integer.mk_rem)
                     context (term t1) (term t2)
         | RemNoSMT -> make_uf "rem_uf" (Integer) [t1; t2]
         | Mod -> (bv_arith_case t1 (via_u t1 BV.mk_smod) BV.mk_urem Integer.mk_mod)
                     context (term t1) (term t2)
         | ModNoSMT -> make_uf "mod_uf" (Integer) [t1; t2]
         | LT -> (bv_arith_case t1 (cmp_u t1 BV.mk_slt) BV.mk_ult mk_lt) context (term t1) (term t2)
         | LE -> (bv_arith_case t1 (cmp_u t1 BV.mk_sle) BV.mk_ule mk_le) context (term t1) (term t2)
         | Min -> adj ()
         | Max -> adj ()
         | XORNoSMT -> BV.mk_xor context (term t1) (term t2)
         | BWAndNoSMT -> BV.mk_and context (term t1) (term t2)
         | BWOrNoSMT -> BV.mk_or context (term t1) (term t2)
         | ShiftLeft -> (bv_arith_case t1 (via_u t1 BV.mk_shl) BV.mk_shl
                 (fun _ -> failwith "int ShiftLeft")) context (term t1) (term t2)
         | ShiftRight -> (bv_arith_case t1 (via_u t1 BV.mk_ashr) BV.mk_shl
                 (fun _ -> failwith "int ShiftRight")) context (term t1) (term t2)
         | EQ -> Z3.Boolean.mk_eq context (term t1) (term t2)
         | SetMember -> Z3.Set.mk_membership context (term t1) (term t2)
         | SetUnion -> Z3.Set.mk_union context (map term [t1;t2])
         | SetIntersection -> Z3.Set.mk_intersection context (map term [t1;t2])
         | SetDifference -> Z3.Set.mk_difference context (term t1) (term t2)
         | Subset -> Z3.Set.mk_subset context (term t1) (term t2)
         | LTPointer -> adj ()
         | LEPointer -> adj ()
         | And -> Z3.Boolean.mk_and context (map term [t1;t2])
         | Or -> Z3.Boolean.mk_or context (map term [t1;t2])
         | Impl -> Z3.Boolean.mk_implies context (term t1) (term t2)
         end
      | ITE (t1, t2, t3) -> Z3.Boolean.mk_ite context (term t1) (term t2) (term t3)
      | EachI _ -> adj ()
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
      | StructUpdate _ -> adj ()
      | Record mts ->
         let constructor = Z3.Tuple.get_mk_decl (sort bt) in
         Z3.Expr.mk_app context constructor (map (fun (_, t) -> term t) mts)
      | RecordMember (t, member) ->
         let members = BT.record_bt (IT.bt t) in
         let members_i = List.mapi (fun i (m, _) -> (m, i)) members in
         let n = List.assoc Id.equal member members_i in
         let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
         Z3.Expr.mk_app context (nth destructors n) [term t]
      | RecordUpdate _ -> adj ()
      | Cast (cbt, t) ->
         begin match IT.bt t, cbt with
         | Integer, Loc ->
            alloc_id_addr_to_loc (term (alloc_id_ Z.zero)) (term t)
         | Bits _, Loc ->
            alloc_id_addr_to_loc (term (alloc_id_ Z.zero)) (term t)
         | Loc, Integer ->
            loc_to_addr (term t)
         | Loc, Bits _ ->
            loc_to_addr (term t)
         | Loc, Alloc_id ->
            loc_to_alloc_id (term t)
         | Real, Integer ->
            Z3.Arithmetic.Real.mk_real2int context (term t)
         | Integer, Real ->
            Z3.Arithmetic.Integer.mk_int2real context (term t)
         | Bits _, Bits _ -> mk_bv_cast context (cbt, IT.bt t, term t)
         | _ ->
            assert false
         end
      | MemberOffset _ -> adj ()
      | ArrayOffset _ -> adj ()
      | SizeOf _ -> adj ()
      | Nil ibt ->
         make_uf (plain (!^"nil_uf"^^angles(BT.pp ibt))) (List ibt) []
      | Cons (t1, t2) ->
         let ibt = IT.bt t1 in
         make_uf (plain (!^"cons_uf"^^angles(BT.pp ibt))) (List ibt) [t1; t2]
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
      | Aligned _ -> adj ()
      | Representable _ -> adj ()
      | Good _ -> adj ()
      | WrapI (ity, arg) ->
         mk_bv_cast context (Memory.bt_of_sct (Sctypes.Integer ity), IT.bt arg, term arg)
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
         | Def body -> adj ()
         | _ ->
            let decl =
              Z3.FuncDecl.mk_func_decl context (symbol name)
                (List.map (fun it -> sort (IT.bt it)) args)
                (sort def.return_bt)
            in
            Z3.Expr.mk_app context decl (List.map term args)
       end
      | Let _ -> adj ()
      | Constructor (constr, args) ->
         datatypeCons (constr, args)
      (* copying and adjusting Thomas's code from compile.ml *)
      | Match (matched, cases) ->
         (* let _sort = sort (IT.bt matched) in *)
         let matched = term matched in
         let cases = 
           List.map (fun (pat, body) ->
               (* print stdout (item "pat" (pp_pattern pat)); *)
               (* print stdout (item "body" (IT.pp body)); *)
               let (cond, substs) = translate_case matched pat in
               let froms, tos = List.split substs in
               let body = Z3.Expr.substitute (term body) froms tos in
               (cond, body)
             ) cases 
         in
         let rec aux = function
           | [] -> term (default_ bt)
           | (cond, body) :: cases -> Z3.Boolean.mk_ite context cond body (aux cases)
         in
         let result = aux cases in
         (* print stdout (item "matched" !^(Z3.Expr.to_string matched)); *)
         (* print stdout (item "result" !^(Z3.Expr.to_string result)); *)
         result
      | _ ->
         Pp.print stdout (Pp.item "smt mapping issue" (IT.pp it));
         Cerb_debug.error "todo: SMT mapping"
      end

(* for extreme printf-debugging
      and term it =
        Pp.debug 22 (lazy (Pp.item "Translate.term" (IT.pp it)));
        let z3_term = term1 it in
        Pp.debug 22 (lazy (Pp.item "Translate.term: done with"
            (Pp.typ (IT.pp it) (Pp.string (Z3.Expr.to_string z3_term)))));
        z3_term
*)

      and translate_case (matched : Z3.Expr.expr) pat = 
        match pat with
        | Pat (PConstructor (c_nm, args), pbt) ->
           let m1 = datatypeIsCons (c_nm, matched) in
           let constr_info = SymMap.find c_nm global.datatype_constrs in
           let dt_tag = constr_info.c_datatype_tag in
           assert (List.for_all2 (fun (id,_) (id',_) -> Id.equal id id') constr_info.c_params args);
           let args_conds_substs = 
             List.map (fun (id, (Pat (_, abt) as apat)) ->
                 let member = datatypeMember ((matched, Datatype dt_tag), (id,abt)) in
                 translate_case member apat
               ) args 
           in
           let args_conds, args_substs = List.split args_conds_substs in
           (Z3.Boolean.mk_and context (m1 :: args_conds), List.concat args_substs)
       | Pat (PSym s, pbt) ->
          let subst = (term (IT.sym_ (s, pbt)), matched) in
          (Z3.Boolean.mk_true context, [subst])
       | Pat (PWild, _pbt) ->
          (Z3.Boolean.mk_true context, [])



      and make_uf name ret_bt args =
        let decl =
          Z3.FuncDecl.mk_func_decl context (string name)
            (List.map (fun it -> sort (IT.bt it)) args) (sort ret_bt)
        in
        Z3.Expr.mk_app context decl (List.map term args)

      and datatypeCons (c_nm, args) =
        (* ensure datatype added first *)
        let constr_info = SymMap.find c_nm global.datatype_constrs in
        let dt_sort = sort (Datatype constr_info.c_datatype_tag) in
        assert (List.for_all2 (fun (id,_) (id',_) -> Id.equal id id') constr_info.c_params args);
        let args = List.map (fun (_id, t) -> term t) args in
        apply_matching_func (DatatypeConsFunc {nm = c_nm})
          (Z3.Datatype.get_constructors dt_sort) args

      and datatypeMember ((dt_it, dt_bt), (member,bt)) =
        (* ensure datatype added first *)
        let dt_sort = sort dt_bt in
        let dt_nm = datatype_bt dt_bt in
        apply_matching_func (DatatypeAccFunc {member = member; dt = dt_nm; bt})
          (List.concat (Z3.Datatype.get_accessors dt_sort)) [dt_it]

      and datatypeIsCons (c_nm, t) =
        let dt_tag = (SymMap.find c_nm global.datatype_constrs).c_datatype_tag in
        (* ensure datatype added *)
        let dt_sort = sort (Datatype dt_tag) in
        let recogs = Z3.Datatype.get_recognizers dt_sort in
        (* something's funny with these recognizers. assume in same order as constructors *)
        let info = SymMap.find dt_tag global.datatypes in
        let assocs = List.map2 (fun c_nm fd -> (c_nm, fd)) info.dt_constrs recogs in
        let fd = List.assoc Sym.equal c_nm assocs in
        Z3.FuncDecl.apply fd [t]

    in

    fun it ->
    term it



  let fold_with_adj : 'a. Global.t -> ('bt IT.bindings -> 'a -> 'bt term -> 'a) ->
        'a -> 'bt term -> 'a =
    fun global f ->
    let f2 bs (acc, adj_ts) t =
      let acc = f bs acc t in
      match adjust_term global t with
      | Some t2 ->
        let t2 = IT.substitute_lets t2 in
        (acc, (bs, t2) :: adj_ts)
      | None -> (acc, adj_ts)
    in
    let rec fold_list acc = function
      | [] -> acc
      | ((bs, t) :: adj_ts) ->
        let (acc, adj_ts) = IT.fold f2 bs (acc, adj_ts) t in
        fold_list acc adj_ts
    in
    fun acc t ->
    fold_list acc [([], t)]

  let focus_terms global it = fold_with_adj global
    (fun bs its it ->
    let interesting = match IT.term it with
      | IT.NthList _ -> true
      | IT.ArrayToList _ -> true
      | IT.Binop (IT.EQ, x, y) -> Option.is_some (IT.is_sym x) || Option.is_some (IT.is_sym y)
      | _ -> false
    in
    if not interesting then its
    else (bs, it) :: its)
    [] it

  let assumption context global c =
    let term it = term context global it in
    match c with
    | T it ->
       Some (it, term it, focus_terms global it)
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
      extra : IT.t list;
      focused : (IT.t_bindings * IT.t) list;
    }
[@@warning "-unused-field"]

  let goal1 context global lc =
    let term it = term context global it in
    match lc with
    | T it ->
       { expr = term it; it; qs = []; extra = []; focused = [] }
    | Forall ((s, bt), it) ->
       let v_s, v = IT.fresh_same bt s in
       let it = IT.subst (make_subst [(s, v)]) it in
       { expr = term it; it; qs = [(v_s, bt)]; extra = []; focused = [] }

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

  let goal solver global assumptions pointer_facts lc =
    let g1 = goal1 solver.context global lc in
    let extra1 = extra_assumptions assumptions g1.qs in
    let focused = List.concat_map (focus_terms global) extra1 @ (! (solver.focus_terms)) in
    let extra2 = IT.nth_array_to_list_facts focused in
    { g1 with extra = extra2 @ extra1; focused = focused }

end




let make global : solver =
  Z3.Memory.reset ();
  List.iter (fun (c,v) -> Z3.set_global_param c v) (params ());
  let context = Z3.mk_context [] in
  Translate.init global context;
  let incremental = Z3.Solver.mk_solver_t context (Z3.Tactic.mk_tactic context "default") in
  { context; incremental; focus_terms = ref [] }






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
  | Some (it, sc, focus) ->
    Z3.Solver.add solver.incremental [sc];
    solver.focus_terms := (focus @ (! (solver.focus_terms)))


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

let paren_sexp nm doc = Pp.parens (!^ nm ^^^ doc)

let scan_z3_log_file_decls fname =
  let f = open_in fname in
  (* String.fold_left arrives in 4.13 which we're not all on yet *)
  let paren_count l = Seq.fold_left (fun i c -> if c == '('
    then i + 1 else if c == ')' then i - 1
    else i) 0 (String.to_seq l) in
  let rec read_loop parens ls groups = try
    let l = input_line f in
    let parens = parens + paren_count l in
    if parens == 0 then read_loop 0 [] (rev (l :: ls) :: groups)
      else read_loop parens (l :: ls) groups
    with End_of_file -> List.rev groups
  in
  let groups = read_loop 0 [] []
    |> List.filter (function | [] -> false | (s :: _) -> Tools.starts_with "(declar" s)
  in
  let rec remdups ss gps = function
    | [] -> List.rev gps
    | (gp :: gps2) ->
      let s = String.concat "\n" gp in
      if StringSet.mem s ss then remdups ss gps gps2
      else remdups (StringSet.add s ss) (gp :: gps) gps2
  in
  remdups StringSet.empty [] groups
  |> List.map (fun ss -> Pp.flow_map (Pp.break 1) Pp.string ss)

let maybe_save_slow_problem kind context extra_assertions lc lc_t time solver =
  match save_slow_problems () with
  | (_, _, None) -> ()
  | (_, cutoff, _) when (Stdlib.Float.compare time cutoff) = -1 -> ()
  | (first_msg, _, Some fname) ->
    let channel = open_out_gen [Open_append; Open_creat] 0o666 fname in
    output_string channel "\n\n";
    if first_msg then output_string channel "## New CN run ##\n\n" else ();
    let lc_doc = Pp.string (Z3.Expr.to_string lc_t) in
    let check_doc = paren_sexp "check-sat" lc_doc in
    let ass_docs = extra_assertions @ Z3.Solver.get_assertions solver
        |> List.map (fun e -> paren_sexp "assert" (Pp.string (Z3.Expr.to_string e))) in
    let smt_item = match log_file () with
      | None -> ("SMT assertions (set z3 logging for complete problem)",
          ass_docs @ [check_doc])
      | Some fname ->
      let decls = scan_z3_log_file_decls fname in
      ("SMT problem", (decls @ ass_docs @ [check_doc]))
    in
    Cerb_colour.without_colour (fun () -> print channel (item "Slow problem"
      (Pp.flow Pp.hardline [
          item "time taken" (format [] (Float.to_string time));
          item "constraint" (LC.pp lc);
          item "SMT constraint" lc_doc;
          item "solver statistics" !^(Z3.Statistics.to_string (Z3.Solver.get_statistics solver));
          item (fst smt_item) (Pp.flow (Pp.break 1) (snd smt_item));
      ]))) ();
    output_string channel "\n";
    saved_slow_problem ();
    close_out channel

let provable ~loc ~solver ~global ~assumptions ~simp_ctxt ~pointer_facts lc =
  Cerb_debug.begin_csv_timing ();
  debug 12 (lazy (item "provable: checking constraint" (LC.pp lc)));
  let context = solver.context in
  debug 13 (lazy (item "context" (Context.pp_constraints assumptions)));
  let rtrue () = model_state := No_model; `True in
  let rfalse qs solver = model_state := Model (context, solver, qs); `False in
  match shortcut simp_ctxt lc with
  | `True ->
     Cerb_debug.end_csv_timing "Solver.provable shortcut";
     rtrue ()
  | `No_shortcut lc ->
     (*print stdout (item "lc" (LC.pp lc ^^ hardline));*)
     let Translate.{expr; qs; extra; _} = Translate.goal solver
         global assumptions pointer_facts lc in
     let nlc = Z3.Boolean.mk_not context expr in
     let extra = List.map (Translate.term context global) extra in
     let (elapsed, res) =
       time_f_elapsed (time_f_logs loc 5 "Z3(inc)"
           (Z3.Solver.check solver.incremental))
         (nlc :: extra)
     in
     begin match lc with
     | LC.T (IT (Const (Bool false), _)) ->
      Cerb_debug.end_csv_timing "Solver.provable false"
     | _ ->
     Cerb_debug.end_csv_timing "Solver.provable noshortcut"
     end;
     match res with
     | Z3.Solver.UNSATISFIABLE ->
        maybe_save_slow_problem "unsat" solver.context extra
            lc expr elapsed solver.incremental;
        rtrue ()
     | Z3.Solver.SATISFIABLE -> rfalse qs solver.incremental
     | Z3.Solver.UNKNOWN ->
        maybe_save_slow_problem "unknown" solver.context extra
            lc expr elapsed solver.incremental;
        let reason = Z3.Solver.get_reason_unknown solver.incremental in
        failwith ("SMT solver returned 'unknown'; reason: " ^ reason)

let get_solver_focused_terms solver ~assumptions ~pointer_facts global =
  let tr = Translate.goal solver global assumptions pointer_facts (LC.T (IT.bool_ true)) in
  tr.Translate.focused

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
         let abt = z3_sort (Z3.Z3Array.get_domain (Z3.Expr.get_sort expr)) in
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

      | () when Z3.BitVector.is_bv_numeral expr ->
         let s = Z3.BitVector.numeral_to_string expr in
         let z = Z.of_string s in
         num_lit_ z (BT.Bits (BT.Unsigned, Z3.BitVector.get_size (Z3.Expr.get_sort expr)))

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
         | _ -> Cerb_debug.error "illtyped index term"
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
                 (loc_to_addr_fundecl context global) ->
           let p = nth args 0 in
           (* fiddly in the pointer-is-bitvector case
           begin match IT.is_pointer p with
           | Some z -> z_ z
           | _ -> pointerToIntegerCast_ p
           end *) pointerToIntegerCast_ p

        | () when
               Z3.FuncDecl.equal func_decl
                 (alloc_id_addr_to_loc_fundecl context global) ->
           let _id = nth args 0 in
           let i = nth args 1 in
           (* begin match IT.is_z i with
           | Some z -> pointer_ z
           | _ -> integerToPointerCast_ i
           end *) integerToPointerCast_ i

        | () when
               Z3.FuncDecl.equal func_decl
                 (integer_to_alloc_id_fundecl context global) ->
           let i = nth args 0 in
           begin match IT.is_z i with
           | Some z -> alloc_id_ z
           | _ -> assert false
           end

        | () when Z3Symbol_Table.mem z3sym_table func_name ->
           begin match Z3Symbol_Table.find z3sym_table func_name with
           | DefaultFunc {bt} ->
              default_ bt
           | MemberFunc {tag; member} ->
              let sd = Memory.member_types (SymMap.find tag global.struct_decls) in
              let member_bt = Memory.bt_of_sct (List.assoc Id.equal member sd) in
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
              let member_bt = List.assoc Id.equal member mbts in
              IT ((RecordMember (nth args 0, member)), member_bt)
           | DatatypeConsFunc {nm} ->
              let info = SymMap.find nm global.datatype_constrs in
               IT (Constructor (nm, (List.combine (List.map fst info.c_params) args)),
                   Datatype info.c_datatype_tag)
           | DatatypeConsRecogFunc {nm} ->
              (* not supported inside CN, hopefully we shouldn't need it *)
              unsupported expr ("Reconstructing Z3 term with datatype recogniser")
           | DatatypeAccFunc xs ->
              unsupported expr ("Reconstructing Z3 term with datatype accessor")
              (* Simplify.IndexTerms.datatype_member_reduce (nth args 0) xs.member xs.bt *)
           | UninterpretedVal {nm} -> sym_ (nm, expr_bt)
           | Term {it} -> it
           | UnsignedToSigned n ->
              cast_ (Bits (Signed, n)) (nth args 0)
           | SignedToUnsigned n ->
              cast_ (Bits (Unsigned, n)) (nth args 0)
           end

        | () when String.equal (Z3.Symbol.to_string func_name) "^" ->
           exp_ (nth args 0, nth args 1)

        | () when Z3.Arithmetic.is_real2int expr ->
           realToInt_ (nth args 0)

        | () when Z3.Arithmetic.is_int2real expr ->
           intToReal_ (nth args 0)

        | () when BT.equal Unit expr_bt ->
           unit_

        | () when is_uninterp_bt expr_bt && List.length args == 0 ->
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
