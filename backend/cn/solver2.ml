module CF = Cerb_frontend
open IndexTerms
open BaseTypes
module SymMap = Map.Make (Sym)
module IT = IndexTerms
module LC = LogicalConstraints
open LogicalConstraints
open List
open Pp
open Global
open LogicalFunctions
module LCSet = Set.Make (LC)
module BT = BaseTypes
module StringSet = Set.Make (String)

let random_seed = ref 1

let log_to_temp = ref false

let log_dir = ref (None : string option)

let trace_all_queries = ref false

let solver_path = ref (None : string option)

let solver_type = ref (None : Simple_smt.solver_extensions option)

let solver_flags = ref (None : string list option)

module Slow_SMT_Tracing = struct
  let settings = ref (None : (string * float) option)

  let num_traced = ref 0

  let run_name () =
    let open Unix in
    let tm = Unix.localtime (Unix.time ()) in
    let tm_str = Printf.sprintf "%d_%02d_%02d" tm.tm_hour tm.tm_min tm.tm_sec in
    "cn_run_" ^ tm_str


  let dir_exists dirname = Sys.file_exists dirname && Sys.is_directory dirname

  let get_tracing_dir dirname =
    if not (dir_exists dirname) then
      failwith ("directory does not exist: " ^ dirname)
    else
      ();
    let dirname2 = dirname ^ Filename.dir_sep ^ run_name () in
    if not (dir_exists dirname2) then Sys.mkdir dirname2 0o755 else ();
    dirname2


  let get_tracing_tmp_dir () =
    let open Filename in
    let dirname = get_temp_dir_name () ^ dir_sep ^ "slow_smt" in
    if not (dir_exists dirname) then Sys.mkdir dirname 0o755 else ();
    get_tracing_dir dirname


  let set_settings threshold_opt dirname_opt =
    match (threshold_opt, dirname_opt) with
    | None, None -> settings := None
    | _ ->
      let dirname =
        match dirname_opt with
        | None -> get_tracing_tmp_dir ()
        | Some nm -> get_tracing_dir nm
      in
      let threshold = Option.value threshold_opt ~default:1.0 in
      settings := Some (dirname, threshold)


  let trace_files time =
    match !settings with
    | None -> None
    | Some (_, threshold) when Stdlib.Float.compare time threshold < 0 -> None
    | Some (dirname, _) ->
      let nm = Printf.sprintf "slow_prob_%03d" !num_traced in
      num_traced := !num_traced + 1;
      let summ_f = open_out (dirname ^ Filename.dir_sep ^ nm ^ ".txt") in
      let smt_f = open_out (dirname ^ Filename.dir_sep ^ nm ^ ".smt2") in
      Some (summ_f, smt_f)
end

let set_slow_smt_settings = Slow_SMT_Tracing.set_settings

type query_trace_elem =
  | Push
  | Pop
  | Assert of IT.t list
  | Check of IT.t list

type solver =
  { context : Z3.context;
    incremental : Z3.Solver.solver;
    non_incremental : Z3.Solver.solver;
    query_trace : query_trace_elem list ref
  }

type expr = Z3.Expr.expr

type sort = Z3.Sort.sort

type model = Z3.context * Z3.Model.model

type model_with_q = model * (Sym.t * BT.t) list

let trace elems solver =
  if !trace_all_queries then
    solver.query_trace := elems @ !(solver.query_trace)
  else
    ()


let log_file () =
  match !log_to_temp with
  | false -> None
  | true -> Some (Filename.get_temp_dir_name () ^ "/z3_log.smt")


let logging_params () =
  match log_file () with None -> [] | Some fname -> [ ("solver.smtlib2_log", fname) ]


let no_automation_params = [ ("auto_config", "false"); ("smt.auto_config", "false") ]

let no_randomness_params () =
  let seed_str = Int.to_string !random_seed in
  [ ("sat.random_seed", seed_str);
    ("nlsat.randomize", "false");
    ("fp.spacer.random_seed", seed_str);
    ("smt.arith.random_initial_value", "false");
    ("smt.random_seed", seed_str);
    ("sls.random_offset", "false");
    ("sls.random_seed", seed_str)
  ]


let solver_params =
  [ ("smt.arith.solver", "2");
    ("smt.macro_finder", "false");
    ("smt.pull-nested-quantifiers", "true");
    ("smt.mbqi", "true");
    ("smt.ematching", "false");
    (* ("smt.arith.nl", "false"); *)
    (* ("smt.arith.nl.branching", "false"); *)
    (* ("smt.arith.nl.rounds", "0"); *)
    ("sat.smt", "true")
  ]


let rewriter_params = [ ("rewriter.expand_nested_stores", "true") ]

let model_params =
  [ ("model", "true");
    ("model.compact", "true");
    ("model.completion", "true");
    ("model.inline_def", "true");
    ("model_evaluator.completion", "true");
    ("model_evaluator.array_as_stores", "false")
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
  module BT_Table = Hashtbl.Make (BT)

  (* for translating back *)
  module Sort_Table = Hashtbl.Make (Sort_HashedType)
  module Z3Symbol_Table = Hashtbl.Make (Z3Symbol_HashedType)

  type z3sym_table_entry =
    | MemberFunc of
        { tag : Sym.t;
          member : Id.t
        }
    | StructFunc of { tag : Sym.t }
    | CompFunc of
        { bts : BT.t list;
          i : int
        }
    | TupleFunc of { bts : BT.t list }
    | RecordFunc of { mbts : BT.member_types }
    | RecordMemberFunc of
        { mbts : BT.member_types;
          member : Id.t
        }
    | DefaultFunc of { bt : BT.t }
    | DatatypeConsFunc of { nm : Sym.t }
    | DatatypeConsRecogFunc of { nm : Sym.t }
    | DatatypeAccFunc of
        { member : Id.t;
          dt : Sym.t;
          bt : BT.t
        }
    | UninterpretedVal of { nm : Sym.t }
    | Term of { it : IT.t }
    | UnsignedToSigned of int
    | SignedToUnsigned of int
  [@@deriving eq]

  (* module Z3ExprMap = Map.Make(struct type t = Z3.Expr.expr let compare =
     Z3.Expr.compare end) *)

  let bt_table = BT_Table.create 1000

  let sort_table = Sort_Table.create 1000

  let bt_id_table = BT_Table.create 1000

  let z3sym_table : z3sym_table_entry Z3Symbol_Table.t = Z3Symbol_Table.create 10000

  let string context str = Z3.Symbol.mk_string context str

  let symbol_string pfx sym = pfx ^ Sym.pp_string sym ^ "_a" ^ string_of_int (Sym.num sym)

  let prefix_symbol context pfx sym = Z3.Symbol.mk_string context (symbol_string pfx sym)

  let symbol context sym = prefix_symbol context "" sym

  let bt_id bt =
    match BT_Table.find_opt bt_id_table bt with
    | Some id -> id
    | None ->
      let id = BT_Table.length bt_id_table + 1 in
      let () = BT_Table.add bt_id_table bt id in
      id


  let bt_pp_name bt =
    let open Pp in
    match bt with
    | BT.Struct nm -> !^"struct_" ^^ Sym.pp nm
    | BT.Datatype nm -> !^"datatype_" ^^ Sym.pp nm
    | BT.Tuple [ BT.Alloc_id; BT.Integer ] -> !^"pointer"
    | BT.Tuple _ -> !^"tuple_" ^^ Pp.int (bt_id bt)
    | BT.List _ -> !^"list_" ^^ Pp.int (bt_id bt)
    | BT.Set _ -> !^"set_" ^^ Pp.int (bt_id bt)
    | BT.Map _ -> !^"map_" ^^ Pp.int (bt_id bt)
    | BT.Record mems ->
      !^"rec_"
      ^^ Pp.int (bt_id bt)
      ^^ Pp.flow_map !^"_" (fun (nm, _) -> Id.pp nm) mems
      ^^ !^"_"
      ^^ Pp.int (bt_id bt)
    | _ -> BT.pp bt


  let bt_name bt = Pp.plain (bt_pp_name bt)

  let bt_suffix_name nm bt = Pp.plain (!^nm ^^ !^"_" ^^ bt_pp_name bt)

  module ITMap = Map.Make (IT)

  let uninterp_tab = ref (ITMap.empty, 0)

  let uninterp_term context sort (it : IT.t) =
    let m, n = !uninterp_tab in
    match ITMap.find_opt it m with
    | Some z3_exp -> z3_exp
    | None ->
      let nm = "uninterp_" ^ Int.to_string n ^ "_" ^ bt_name (IT.bt it) in
      let sym = string context nm in
      let z3_exp = Z3.Expr.mk_const context sym sort in
      uninterp_tab := (ITMap.add it z3_exp m, n + 1);
      Z3Symbol_Table.add z3sym_table sym (Term { it });
      z3_exp


  let is_uninterp_bt (bt : BT.t) =
    match bt with CType -> true | List _bt -> true | _ -> false


  let tuple_field_name bts i = bt_name (Tuple bts) ^ string_of_int i

  let record_member_name bts member = Id.pp_string member ^ "_of_" ^ bt_name (Record bts)

  let accessor_name dt_name member = symbol_string "" dt_name ^ "_" ^ Id.s member

  let member_name tag id = bt_name (BT.Struct tag) ^ "_" ^ Id.s id

  let dt_recog_name context nm = prefix_symbol context "is_" nm

  let unit_value_name = bt_name Unit ^ "_v"

  let sort : Z3.context -> Global.t -> BT.t -> sort =
    fun context global ->
    let string str = string context str in
    let rec translate = function
      | Unit -> Z3.Enumeration.mk_sort_s context (bt_name Unit) [ unit_value_name ]
      | Bool -> Z3.Boolean.mk_sort context
      | Integer -> Z3.Arithmetic.Integer.mk_sort context
      | Bits (Unsigned, n) -> Z3.BitVector.mk_sort context n
      | Bits (Signed, n) ->
        (*copying/adjusting Dhruv's code for Alloc_id*)
        let bt_symbol = string (bt_name (Bits (Signed, n))) in
        let field_symbol = string ("unsigned_" ^ string_of_int n) in
        Z3Symbol_Table.add z3sym_table bt_symbol (UnsignedToSigned n);
        Z3Symbol_Table.add z3sym_table field_symbol (SignedToUnsigned n);
        Z3.Tuple.mk_sort context bt_symbol [ field_symbol ] [ sort (Bits (Unsigned, n)) ]
      | Real -> Z3.Arithmetic.Real.mk_sort context
      | Loc -> translate BT.(Tuple [ Alloc_id; Memory.uintptr_bt ])
      | Alloc_id ->
        Z3.Tuple.mk_sort
          context
          (string (bt_name Alloc_id))
          [ string "alloc_id_to_integer" ]
          [ sort (if !use_vip then BT.Integer else BT.Unit) ]
      | CType ->
        (* the ctype type is represented as an uninterpreted sort *)
        Z3.Sort.mk_uninterpreted_s context (bt_name CType)
      | List bt ->
        (* lists are represented as uninterpreted sorts *)
        Z3.Sort.mk_uninterpreted_s context (bt_name (List bt))
      | Set bt -> Z3.Set.mk_sort context (sort bt)
      | Map (abt, rbt) -> Z3.Z3Array.mk_sort context (sort abt) (sort rbt)
      | Tuple bts ->
        let bt_symbol = string (bt_name (Tuple bts)) in
        Z3Symbol_Table.add z3sym_table bt_symbol (TupleFunc { bts });
        let field_symbols =
          mapi
            (fun i _ ->
              let sym = string (tuple_field_name bts i) in
              Z3Symbol_Table.add z3sym_table sym (CompFunc { bts; i });
              sym)
            bts
        in
        let sorts = map sort bts in
        Z3.Tuple.mk_sort context bt_symbol field_symbols sorts
      | Struct tag ->
        let struct_symbol = string (bt_name (Struct tag)) in
        Z3Symbol_Table.add z3sym_table struct_symbol (StructFunc { tag });
        let layout = SymMap.find tag global.struct_decls in
        let member_symbols, member_sorts =
          map_split
            (fun (id, sct) ->
              let s = string (member_name tag id) in
              Z3Symbol_Table.add z3sym_table s (MemberFunc { tag; member = id });
              (s, sort (Memory.bt_of_sct sct)))
            (Memory.member_types layout)
        in
        Z3.Tuple.mk_sort context struct_symbol member_symbols member_sorts
      | Datatype tag -> BT_Table.find bt_table (Datatype tag)
      | Record members ->
        let bt_symbol = string (bt_name (Record members)) in
        Z3Symbol_Table.add z3sym_table bt_symbol (RecordFunc { mbts = members });
        let member_symbols =
          map
            (fun (member, _bt) ->
              let sym = string (record_member_name members member) in
              Z3Symbol_Table.add
                z3sym_table
                sym
                (RecordMemberFunc { mbts = members; member });
              sym)
            members
        in
        let member_sorts = map (fun (_, bt) -> sort bt) members in
        Z3.Tuple.mk_sort context bt_symbol member_symbols member_sorts
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


  let translate_datatypes context global =
    let translate_group to_translate =
      let to_translate = List.mapi (fun i nm -> (nm, i)) to_translate in
      let arg_sort bt =
        match bt with
        | BT.Datatype nm ->
          (match BT_Table.find_opt bt_table bt with
           | Some sort -> (Some sort, 0)
           | None ->
             (* if nm is not in BT_Table, then nm must be in the current `to_translate`
                group (otherwise the topological order would be different *)
             (None, List.assoc Sym.equal nm to_translate))
        | _ -> (Some (sort context global bt), 0)
      in
      let conv_cons dt_nm nm =
        let info = SymMap.find nm global.datatype_constrs in
        let r = List.map (fun (_, bt) -> arg_sort bt) info.c_params in
        let sym = symbol context nm in
        let is_sym = dt_recog_name context nm in
        Z3Symbol_Table.add z3sym_table sym (DatatypeConsFunc { nm });
        (* Z3Symbol_Table.add z3sym_table is_sym (DatatypeConsRecogFunc {nm}); *)
        List.iter
          (fun (member, bt) ->
            Z3Symbol_Table.add
              z3sym_table
              (string context (accessor_name dt_nm member))
              (DatatypeAccFunc { member; dt = dt_nm; bt }))
          info.c_params;
        Z3.Datatype.mk_constructor
          context
          sym
          is_sym
          (List.map
             (fun (member, _) -> string context (accessor_name dt_nm member))
             info.c_params)
          (List.map fst r)
          (List.map snd r)
      in
      let conv_dt nm =
        let info = SymMap.find nm global.datatypes in
        List.map (conv_cons nm) info.dt_constrs
      in
      let sorts =
        Z3.Datatype.mk_sorts
          context
          (List.map (fun (nm, _) -> symbol context nm) to_translate)
          (List.map (fun (nm, _) -> conv_dt nm) to_translate)
      in
      List.iter2
        (fun (nm, _) sort ->
          BT_Table.add bt_table (BT.Datatype nm) sort;
          Sort_Table.add sort_table sort (BT.Datatype nm))
        to_translate
        sorts
    in
    List.iter translate_group (Option.get global.datatype_order)


  let init global context =
    (* TODO: clear other tables? *)
    BT_Table.clear bt_table;
    Sort_Table.clear sort_table;
    let _ = sort context global BT.Integer in
    let _ = sort context global BT.Bool in
    translate_datatypes context global;
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


  let rec mk_ctz context target_sz cur_sz tm =
    assert (cur_sz >= 1);
    let target s = Z3.BitVector.mk_numeral context s target_sz in
    let eq_0 tm sz =
      Z3.Boolean.mk_eq context tm (Z3.BitVector.mk_numeral context "0" sz)
    in
    if cur_sz == 1 then
      Z3.Boolean.mk_ite context (eq_0 tm cur_sz) (target "1") (target "0")
    else (
      let top_sz = cur_sz / 2 in
      let bot_sz = cur_sz - top_sz in
      let top = Z3.BitVector.mk_extract context (cur_sz - 1) (cur_sz - top_sz) tm in
      let bot = Z3.BitVector.mk_extract context (bot_sz - 1) 0 tm in
      Z3.Boolean.mk_ite
        context
        (eq_0 bot bot_sz)
        (Z3.BitVector.mk_add
           context
           (mk_ctz context target_sz top_sz top)
           (target (Int.to_string bot_sz)))
        (mk_ctz context target_sz bot_sz bot))


  let rec mk_clz context target_sz cur_sz tm =
    assert (cur_sz >= 1);
    let target s = Z3.BitVector.mk_numeral context s target_sz in
    let eq_0 tm sz =
      Z3.Boolean.mk_eq context tm (Z3.BitVector.mk_numeral context "0" sz)
    in
    if cur_sz == 1 then
      Z3.Boolean.mk_ite context (eq_0 tm cur_sz) (target "1") (target "0")
    else (
      let top_sz = cur_sz / 2 in
      let bot_sz = cur_sz - top_sz in
      let top = Z3.BitVector.mk_extract context (cur_sz - 1) (cur_sz - top_sz) tm in
      let bot = Z3.BitVector.mk_extract context (bot_sz - 1) 0 tm in
      Z3.Boolean.mk_ite
        context
        (eq_0 top top_sz)
        (Z3.BitVector.mk_add
           context
           (mk_clz context target_sz bot_sz bot)
           (target (Int.to_string top_sz)))
        (mk_clz context target_sz top_sz top))


  let _foo = (mk_ctz, mk_clz)

  let adjust_term global : IT.t -> IT.t option =
    let struct_decls = global.struct_decls in
    let intptr_cast = cast_ Memory.uintptr_bt in
    fun it ->
      let here = Locations.other __FUNCTION__ in
      match IT.term it with
      | Const Null -> Some (pointer_ ~alloc_id:Z.zero ~addr:Z.zero here)
      | Unop (op, t1) ->
        (match op with
         | BWFFSNoSMT ->
           let intl i = int_lit_ i (IT.bt t1) here in
           Some
             (ite_
                ( eq_ (t1, intl 0) here,
                  intl 0,
                  add_ (arith_unop BW_CTZ_NoSMT t1 here, intl 1) here )
                here)
         | BWFLSNoSMT ->
           let sz = match IT.bt t1 with Bits (_sign, n) -> n | _ -> assert false in
           let intl i = int_lit_ i (IT.bt t1) here in
           Some
             (ite_
                ( eq_ (t1, intl 0) here,
                  intl 0,
                  sub_ (intl sz, arith_unop BW_CLZ_NoSMT t1 here) here )
                here)
         | _ -> None)
      | Binop (op, t1, t2) ->
        (match op with
         | Exp ->
           (match (get_num_z t1, get_num_z t2) with
            | Some z1, Some z2 when Z.fits_int z2 ->
              Some (num_lit_ (Z.pow z1 (Z.to_int z2)) (IT.bt t1) here)
            | _, _ -> assert false)
         | Min -> Some (ite_ (le_ (t1, t2) here, t1, t2) here)
         | Max -> Some (ite_ (ge_ (t1, t2) here, t1, t2) here)
         | LTPointer -> Some (lt_ (intptr_cast t1 here, intptr_cast t2 here) here)
         | LEPointer -> Some (le_ (intptr_cast t1 here, intptr_cast t2 here) here)
         | _ -> None)
      | EachI ((i1, (s, bt), i2), t) ->
        let rec aux i =
          if i <= i2 then
            IT.subst (make_subst [ (s, num_lit_ (Z.of_int i) bt here) ]) t :: aux (i + 1)
          else
            []
        in
        Some (and_ (aux i1) here)
      | StructUpdate ((t, member), v) ->
        let tag = BT.struct_bt (IT.bt t) in
        let layout = SymMap.find (struct_bt (IT.bt t)) struct_decls in
        let members = Memory.member_types layout in
        let str =
          List.map
            (fun (member', sct) ->
              let value =
                if Id.equal member member' then
                  v
                else
                  member_ ~member_bt:(Memory.bt_of_sct sct) (t, member') here
              in
              (member', value))
            members
        in
        Some (struct_ (tag, str) here)
      | RecordUpdate ((t, member), v) ->
        let members = BT.record_bt (IT.bt t) in
        let str =
          List.map
            (fun (member', bt) ->
              let value =
                if Id.equal member member' then
                  v
                else
                  IT (RecordMember (t, member'), bt, here)
              in
              (member', value))
            members
        in
        Some (IT (Record str, IT.bt t, here))
      | OffsetOf (tag, member) ->
        let decl = SymMap.find tag struct_decls in
        Some
          (int_lit_
             (Option.get (Memory.member_offset decl member))
             Memory.uintptr_bt
             here)
      | SizeOf ct -> Some (int_lit_ (Memory.size_of_ctype ct) (IT.bt it) here)
      | Aligned t ->
        let addr = pointerToIntegerCast_ t.t here in
        assert (BT.equal (IT.bt addr) (IT.bt t.align));
        Some (divisible_ (addr, t.align) here)
      (* | Representable (CT.Pointer _ as ct, t) -> *)
      (*    Some (representable struct_decls ct t here) *)
      | Representable (ct, t) -> Some (representable struct_decls ct t here)
      | Good (ct, t) -> Some (good_value struct_decls ct t here)
      | WrapI (_ity, _arg) ->
        (* unlike previously (and std.core), implemented natively using bitvector ops *)
        None
      | Apply (name, args) ->
        let def = Option.get (get_logical_function_def global name) in
        (match def.definition with
         | Def body -> Some (LogicalFunctions.open_fun def.args body args)
         | _ -> None)
      | Let ((_nm, _t1), _t2) -> Some (IT.substitute_lets it)
      | _ -> None


  let term ?(warn_lambda = true) context global : IT.t -> expr =
    let struct_decls = global.struct_decls in
    let sort bt = sort context global bt in
    let symbol sym = symbol context sym in
    let string str = string context str in
    (* let integer_to_loc_symbol = Z3.FuncDecl.get_name integer_to_loc_fundecl in *)
    let mk_unit () =
      Z3.Expr.mk_app context (Z3.Enumeration.get_const_decl (sort Unit) 0) []
    in
    let loc_to_addr l =
      Z3.Expr.mk_app context (loc_to_addr_fundecl context global) [ l ]
    in
    let loc_to_alloc_id l =
      Z3.Expr.mk_app context (loc_to_alloc_id_fundecl context global) [ l ]
    in
    let integer_to_alloc_id i =
      (* ignores i in non-VIP mode *)
      Z3.Expr.mk_app
        context
        (integer_to_alloc_id_fundecl context global)
        [ (if !use_vip then i else mk_unit ()) ]
    in
    let alloc_id_addr_to_loc id i =
      Z3.Expr.mk_app context (alloc_id_addr_to_loc_fundecl context global) [ id; i ]
    in
    let apply_matching_func sym_role fds args =
      let matching fd =
        equal_z3sym_table_entry
          sym_role
          (Z3Symbol_Table.find z3sym_table (Z3.FuncDecl.get_name fd))
      in
      let fd = List.find matching fds in
      Z3.FuncDecl.apply fd args
    in
    let mk_bv_cast context (to_bt, from_bt, x) =
      let bits_info bt =
        match BT.is_bits_bt bt with
        | Some (sign, sz) -> (BT.equal_sign sign BT.Signed, sz)
        | None -> failwith ("mk_bv_cast: non-bv type: " ^ Pp.plain (BT.pp bt))
      in
      let to_signed, to_sz = bits_info to_bt in
      let from_signed, from_sz = bits_info from_bt in
      let step1 =
        if from_signed then
          Z3.Expr.mk_app context (signed_to_unsigned_fundecl context global from_sz) [ x ]
        else
          x
      in
      let step2 =
        if to_sz == from_sz then
          step1
        else if to_sz < from_sz then
          Z3.BitVector.mk_extract context (to_sz - 1) 0 step1
        else if from_signed then
          Z3.BitVector.mk_sign_ext context (to_sz - from_sz) step1
        else
          Z3.BitVector.mk_zero_ext context (to_sz - from_sz) step1
      in
      if to_signed then
        Z3.Expr.mk_app context (unsigned_to_signed_fundecl context global to_sz) [ step2 ]
      else
        step2
    in
    let unsigned_of bt =
      match bt with
      | BT.Bits (BT.Signed, n) -> BT.Bits (BT.Unsigned, n)
      | _ -> failwith "unsigned_of: not signed"
    in
    let via_unsigned context bt op t1 t2 =
      let to_u t = mk_bv_cast context (unsigned_of bt, bt, t) in
      mk_bv_cast context (bt, unsigned_of bt, op (to_u t1) (to_u t2))
    in
    let cmp_in_unsigned context bt op t1 t2 =
      let to_u t = mk_bv_cast context (unsigned_of bt, bt, t) in
      op (to_u t1) (to_u t2)
    in
    let via_unsigned1 context bt op t1 =
      via_unsigned context bt (fun t1 _ -> op t1) t1 t1
    in
    let rec term it =
      let loc = IT.loc it in
      let bt = IT.bt it in
      let adj () =
        match adjust_term global it with
        | None ->
          Pp.debug 1 (lazy (Pp.item "Translate.term: failed to adjust_term" (IT.pp it)));
          assert false
        | Some it2 -> term it2
      in
      match IT.term it with
      | Sym s -> Z3.Expr.mk_const context (symbol s) (sort bt)
      | Const (Z z) -> Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
      | Const (Bits ((Unsigned, n), v)) ->
        Z3.BitVector.mk_numeral context (Z.to_string v) n
      | Const (Bits ((Signed, n), v)) ->
        Z3.Expr.mk_app
          context
          (unsigned_to_signed_fundecl context global n)
          [ Z3.BitVector.mk_numeral context (Z.to_string v) n ]
      | Const (Q q) -> Z3.Arithmetic.Real.mk_numeral_s context (Q.to_string q)
      | Const (Pointer { alloc_id; addr }) ->
        alloc_id_addr_to_loc
          (term (alloc_id_ alloc_id loc))
          (term (num_lit_ addr Memory.uintptr_bt loc))
      | Const (Alloc_id z) ->
        integer_to_alloc_id (Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z))
      | Const (Bool true) -> Z3.Boolean.mk_true context
      | Const (Bool false) -> Z3.Boolean.mk_false context
      | Const Unit -> mk_unit ()
      | Const (Default bt) ->
        let sym = Z3.Symbol.mk_string context ("default" ^ bt_name bt) in
        let () = Z3Symbol_Table.add z3sym_table sym (DefaultFunc { bt }) in
        Z3.Expr.mk_const context sym (sort bt)
      | Const Null -> adj ()
      | Const (CType_const _ct) -> uninterp_term context (sort bt) it
      | Unop (uop, t) ->
        (match uop with
         | Not -> Z3.Boolean.mk_not context (term t)
         | Negate ->
           (match IT.bt t with
            | BT.Bits (BT.Unsigned, _) -> Z3.BitVector.mk_neg context (term t)
            | BT.Bits (BT.Signed, _) ->
              via_unsigned1 context (IT.bt t) (Z3.BitVector.mk_neg context) (term t)
            | BT.Integer | BT.Real -> Z3.Arithmetic.mk_unary_minus context (term t)
            | _ -> failwith (__FUNCTION__ ^ ":Unop (Negate, _)"))
         | BWFFSNoSMT -> adj ()
         | BWFLSNoSMT -> adj ()
         | BW_CLZ_NoSMT ->
           (match IT.bt t with
            | BT.Bits (BT.Unsigned, sz) -> mk_clz context sz sz (term t)
            | BT.Bits (BT.Signed, sz) ->
              via_unsigned1 context (IT.bt t) (mk_clz context sz sz) (term t)
            | _ -> failwith "solver: BW_CLZ_NoSMT: not a bitwise type")
         | BW_CTZ_NoSMT ->
           (match IT.bt t with
            | BT.Bits (BT.Unsigned, sz) -> mk_ctz context sz sz (term t)
            | BT.Bits (BT.Signed, sz) ->
              via_unsigned1 context (IT.bt t) (mk_ctz context sz sz) (term t)
            | _ -> failwith "solver: BW_CTZ_NoSMT: not a bitwise type"))
      | Binop (bop, t1, t2) ->
        if BT.equal (IT.bt t1) (IT.bt t2) then
          ()
        else (
          let bt1 = BT.pp @@ IT.bt t1 in
          let bt2 = BT.pp @@ IT.bt t2 in
          let doc = Pp.(IT.pp it ^^^ parens (bt1 ^^ comma ^^^ bt2)) in
          Pp.debug 1 (lazy (Pp.item "mismatching binop" doc));
          assert false);
        let open Z3.Arithmetic in
        let module BV = Z3.BitVector in
        let bv_arith_case t ~signed ~unsigned ~int_real =
          match IT.bt t with
          | BT.Bits (BT.Signed, _) -> signed
          | BT.Bits (BT.Unsigned, _) -> unsigned
          | BT.Integer -> int_real
          | BT.Real -> int_real
          | _ -> failwith "bv_arith_case"
        in
        let l_bop f ctxt x y = f ctxt [ x; y ] in
        let via_u t op ctxt = via_unsigned ctxt (IT.bt t) (op ctxt) in
        let cmp_u t op ctxt = cmp_in_unsigned ctxt (IT.bt t) (op ctxt) in
        let fail_on str _ctxt = failwith ("solver: unexpected value type for: " ^ str) in
        (match bop with
         | Add ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_add)
              ~unsigned:BV.mk_add
              ~int_real:(l_bop mk_add))
             context
             (term t1)
             (term t2)
         | Sub ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_sub)
              ~unsigned:BV.mk_sub
              ~int_real:(l_bop mk_sub))
             context
             (term t1)
             (term t2)
         | Mul ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_mul)
              ~unsigned:BV.mk_mul
              ~int_real:(l_bop mk_mul))
             context
             (term t1)
             (term t2)
         | MulNoSMT -> make_uf "mul_uf" (IT.bt t1) [ t1; t2 ]
         | Div ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_sdiv)
              ~unsigned:BV.mk_udiv
              ~int_real:mk_div)
             context
             (term t1)
             (term t2)
         | DivNoSMT -> make_uf "div_uf" (IT.bt t1) [ t1; t2 ]
         | Exp -> adj ()
         | ExpNoSMT -> make_uf "exp_uf" (IT.bt t1) [ t1; t2 ]
         | Rem ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_srem)
              ~unsigned:BV.mk_urem
              ~int_real:Integer.mk_rem)
             context
             (term t1)
             (term t2)
         | RemNoSMT -> make_uf "rem_uf" (IT.bt t1) [ t1; t2 ]
         | Mod ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_smod)
              ~unsigned:BV.mk_urem
              ~int_real:Integer.mk_mod)
             context
             (term t1)
             (term t2)
         | ModNoSMT -> make_uf "mod_uf" (IT.bt t1) [ t1; t2 ]
         | LT ->
           (bv_arith_case
              t1
              ~signed:(cmp_u t1 BV.mk_slt)
              ~unsigned:BV.mk_ult
              ~int_real:mk_lt)
             context
             (term t1)
             (term t2)
         | LE ->
           (bv_arith_case
              t1
              ~signed:(cmp_u t1 BV.mk_sle)
              ~unsigned:BV.mk_ule
              ~int_real:mk_le)
             context
             (term t1)
             (term t2)
         | Min -> adj ()
         | Max -> adj ()
         | XORNoSMT ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_xor)
              ~unsigned:BV.mk_xor
              ~int_real:(fail_on "xor"))
             context
             (term t1)
             (term t2)
         | BWAndNoSMT ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_and)
              ~unsigned:BV.mk_and
              ~int_real:(fail_on "bw_and"))
             context
             (term t1)
             (term t2)
         | BWOrNoSMT ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_or)
              ~unsigned:BV.mk_or
              ~int_real:(fail_on "bw_or"))
             context
             (term t1)
             (term t2)
         | ShiftLeft ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_shl)
              ~unsigned:BV.mk_shl
              ~int_real:(fail_on "shift_left"))
             context
             (term t1)
             (term t2)
         | ShiftRight ->
           (bv_arith_case
              t1
              ~signed:(via_u t1 BV.mk_ashr)
              ~unsigned:BV.mk_lshr
              ~int_real:(fail_on "shift_right"))
             context
             (term t1)
             (term t2)
         | EQ -> Z3.Boolean.mk_eq context (term t1) (term t2)
         | SetMember -> Z3.Set.mk_membership context (term t1) (term t2)
         | SetUnion -> Z3.Set.mk_union context (map term [ t1; t2 ])
         | SetIntersection -> Z3.Set.mk_intersection context (map term [ t1; t2 ])
         | SetDifference -> Z3.Set.mk_difference context (term t1) (term t2)
         | Subset -> Z3.Set.mk_subset context (term t1) (term t2)
         | LTPointer -> adj ()
         | LEPointer -> adj ()
         | And -> Z3.Boolean.mk_and context (map term [ t1; t2 ])
         | Or -> Z3.Boolean.mk_or context (map term [ t1; t2 ])
         | Implies -> Z3.Boolean.mk_implies context (term t1) (term t2))
      | ITE (t1, t2, t3) -> Z3.Boolean.mk_ite context (term t1) (term t2) (term t3)
      | EachI _ -> adj ()
      | Tuple ts ->
        let constructor = Z3.Tuple.get_mk_decl (sort bt) in
        Z3.Expr.mk_app context constructor (map term ts)
      | NthTuple (n, t) ->
        let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
        Z3.Expr.mk_app context (nth destructors n) [ term t ]
      | Struct (_tag, mts) ->
        let constructor = Z3.Tuple.get_mk_decl (sort bt) in
        Z3.Expr.mk_app context constructor (map (fun (_, t) -> term t) mts)
      | StructMember (t, member) ->
        let layout = SymMap.find (struct_bt (IT.bt t)) struct_decls in
        let n = Option.get (Memory.member_number layout member) in
        let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
        Z3.Expr.mk_app context (nth destructors n) [ term t ]
      | StructUpdate _ -> adj ()
      | Record mts ->
        let constructor = Z3.Tuple.get_mk_decl (sort bt) in
        Z3.Expr.mk_app context constructor (map (fun (_, t) -> term t) mts)
      | RecordMember (t, member) ->
        let members = BT.record_bt (IT.bt t) in
        let members_i = List.mapi (fun i (m, _) -> (m, i)) members in
        let n = List.assoc Id.equal member members_i in
        let destructors = Z3.Tuple.get_field_decls (sort (IT.bt t)) in
        Z3.Expr.mk_app context (nth destructors n) [ term t ]
      | RecordUpdate _ -> adj ()
      | Cast (cbt, t) ->
        (match (IT.bt t, cbt) with
         | Bits _, Loc ->
           if BT.equal (IT.bt t) Memory.uintptr_bt then
             alloc_id_addr_to_loc (term (alloc_id_ Z.zero loc)) (term t)
           else
             term (cast_ cbt (cast_ Memory.uintptr_bt t loc) loc)
         | Loc, Bits _ ->
           (* Recall above | Loc -> translate BT.(Tuple [Alloc_id; Memory.uintptr_bt]) *)
           if BT.equal cbt Memory.uintptr_bt then
             loc_to_addr (term t)
           else
             (* But if we need to cast a pointer to any other type (e.g. signed, or of a
                different length) first we need to cast the pointer to uintptr_t, and then
                cast to the requested one *)
             term (cast_ cbt (cast_ Memory.uintptr_bt t loc) loc)
         | Loc, Alloc_id -> loc_to_alloc_id (term t)
         | Real, Integer -> Z3.Arithmetic.Real.mk_real2int context (term t)
         | Integer, Real -> Z3.Arithmetic.Integer.mk_int2real context (term t)
         | Bits _, Bits _ -> mk_bv_cast context (cbt, IT.bt t, term t)
         | _ -> assert false)
      | SizeOf _ -> adj ()
      | OffsetOf _ -> adj ()
      | MemberShift (t, tag, member) ->
        let decl = SymMap.find tag struct_decls in
        let t = term t in
        let alloc_id, addr = (loc_to_alloc_id t, loc_to_addr t) in
        let offset =
          int_lit_ (Option.get (Memory.member_offset decl member)) Memory.uintptr_bt loc
        in
        alloc_id_addr_to_loc alloc_id (Z3.BitVector.mk_add context addr (term offset))
      | ArrayShift { base; ct; index } ->
        let offset =
          mul_
            ( int_lit_ (Memory.size_of_ctype ct) Memory.uintptr_bt loc,
              cast_ Memory.uintptr_bt index loc )
            loc
        in
        let base = term base in
        let alloc_id, addr = (loc_to_alloc_id base, loc_to_addr base) in
        alloc_id_addr_to_loc alloc_id (Z3.BitVector.mk_add context addr (term offset))
      | CopyAllocId { addr; loc } ->
        let int, loc = (term addr, term loc) in
        alloc_id_addr_to_loc (loc_to_alloc_id loc) int
      | Nil ibt -> make_uf (plain (!^"nil_uf" ^^ angles (BT.pp ibt))) (List ibt) []
      | Cons (t1, t2) ->
        let ibt = IT.bt t1 in
        make_uf (plain (!^"cons_uf" ^^ angles (BT.pp ibt))) (List ibt) [ t1; t2 ]
      | NthList (i, xs, d) ->
        let args = List.map term [ i; xs; d ] in
        let nm = bt_suffix_name "nth_list" bt in
        let fdec =
          Z3.FuncDecl.mk_func_decl_s
            context
            nm
            (List.map sort (List.map IT.bt [ i; xs; d ]))
            (sort bt)
        in
        Z3.FuncDecl.apply fdec args
      | ArrayToList (arr, i, len) ->
        let args = List.map term [ arr; i; len ] in
        let list_bt = Option.get (BT.is_list_bt bt) in
        let nm = bt_suffix_name "array_to_list" list_bt in
        let fdec =
          Z3.FuncDecl.mk_func_decl_s
            context
            nm
            (List.map sort (List.map IT.bt [ arr; i; len ]))
            (sort bt)
        in
        Z3.FuncDecl.apply fdec args
      | Aligned _ -> adj ()
      | Representable _ -> adj ()
      | Good _ -> adj ()
      | WrapI (ity, arg) ->
        mk_bv_cast context (Memory.bt_of_sct (Sctypes.Integer ity), IT.bt arg, term arg)
      | MapConst (abt, t) -> Z3.Z3Array.mk_const_array context (sort abt) (term t)
      | MapSet (t1, t2, t3) -> Z3.Z3Array.mk_store context (term t1) (term t2) (term t3)
      (* | MapGet (IT (Map_op (Def ((s, bt), body)), _), arg) ->  *)
      (*    term (IT.subst (make_subst [(s, arg)]) body) *)
      | MapGet (f, arg) -> Z3.Z3Array.mk_select context (term f) (term arg)
      | MapDef ((q_s, q_bt), body) ->
        if warn_lambda then
          warn_noloc !^"generating lambda";
        (* warn (!^"generating lambda" ^^ colon ^^^ IT.pp (IT (it_, bt))); *)
        Z3.Quantifier.expr_of_quantifier
          (Z3.Quantifier.mk_lambda_const
             context
             [ term (sym_ (q_s, q_bt, loc)) ]
             (term body))
      | Apply (name, args) ->
        let def = Option.get (get_logical_function_def global name) in
        (match def.definition with
         | Def _body -> adj ()
         | _ ->
           let decl =
             Z3.FuncDecl.mk_func_decl
               context
               (symbol name)
               (List.map (fun it -> sort (IT.bt it)) args)
               (sort def.return_bt)
           in
           Z3.Expr.mk_app context decl (List.map term args))
      | Let _ -> adj ()
      | Constructor (constr, args) -> datatypeCons (constr, args)
      (* copying and adjusting Thomas's code from compile.ml *)
      | Match (matched, cases) ->
        (* let _sort = sort (IT.bt matched) in *)
        let matched = term matched in
        let cases =
          List.map
            (fun (pat, body) ->
              (* print stdout (item "pat" (pp_pattern pat)); *)
              (* print stdout (item "body" (IT.pp body)); *)
              let cond, substs = translate_case matched pat in
              let froms, tos = List.split substs in
              let body = Z3.Expr.substitute (term body) froms tos in
              (cond, body))
            cases
        in
        let rec aux = function
          | [] -> term (default_ bt loc)
          | (cond, body) :: cases -> Z3.Boolean.mk_ite context cond body (aux cases)
        in
        let result = aux cases in
        (* print stdout (item "matched" !^(Z3.Expr.to_string matched)); *)
        (* print stdout (item "result" !^(Z3.Expr.to_string result)); *)
        result
      | _ ->
        Pp.print stdout (Pp.item "smt mapping issue" (IT.pp it));
        Cerb_debug.error "todo: SMT mapping"
    (* for extreme printf-debugging and term it = Pp.debug 22 (lazy (Pp.item
       "Translate.term" (IT.pp it))); let z3_term = term1 it in Pp.debug 22 (lazy (Pp.item
       "Translate.term: done with" (Pp.typ (IT.pp it) (Pp.string (Z3.Expr.to_string
       z3_term))))); z3_term *)
    and translate_case (matched : Z3.Expr.expr) pat =
      match pat with
      | Pat (PConstructor (c_nm, args), _pbt, _) ->
        let m1 = datatypeIsCons (c_nm, matched) in
        let constr_info = SymMap.find c_nm global.datatype_constrs in
        let dt_tag = constr_info.c_datatype_tag in
        assert (
          List.for_all2
            (fun (id, _) (id', _) -> Id.equal id id')
            constr_info.c_params
            args);
        let args_conds_substs =
          List.map
            (fun (id, (Pat (_, abt, _) as apat)) ->
              let member = datatypeMember ((matched, Datatype dt_tag), (id, abt)) in
              translate_case member apat)
            args
        in
        let args_conds, args_substs = List.split args_conds_substs in
        (Z3.Boolean.mk_and context (m1 :: args_conds), List.concat args_substs)
      | Pat (PSym s, pbt, loc) ->
        let subst = (term (IT.sym_ (s, pbt, loc)), matched) in
        (Z3.Boolean.mk_true context, [ subst ])
      | Pat (PWild, _pbt, _) -> (Z3.Boolean.mk_true context, [])
    and make_uf name ret_bt args =
      let decl =
        Z3.FuncDecl.mk_func_decl
          context
          (string name)
          (List.map (fun it -> sort (IT.bt it)) args)
          (sort ret_bt)
      in
      Z3.Expr.mk_app context decl (List.map term args)
    and datatypeCons (c_nm, args) =
      (* ensure datatype added first *)
      let constr_info = SymMap.find c_nm global.datatype_constrs in
      let dt_sort = sort (Datatype constr_info.c_datatype_tag) in
      assert (
        List.for_all2 (fun (id, _) (id', _) -> Id.equal id id') constr_info.c_params args);
      let args = List.map (fun (_id, t) -> term t) args in
      apply_matching_func
        (DatatypeConsFunc { nm = c_nm })
        (Z3.Datatype.get_constructors dt_sort)
        args
    and datatypeMember ((dt_it, dt_bt), (member, bt)) =
      (* ensure datatype added first *)
      let dt_sort = sort dt_bt in
      let dt_nm = datatype_bt dt_bt in
      apply_matching_func
        (DatatypeAccFunc { member; dt = dt_nm; bt })
        (List.concat (Z3.Datatype.get_accessors dt_sort))
        [ dt_it ]
    and datatypeIsCons (c_nm, t) =
      let dt_tag = (SymMap.find c_nm global.datatype_constrs).c_datatype_tag in
      (* ensure datatype added *)
      let dt_sort = sort (Datatype dt_tag) in
      let recogs = Z3.Datatype.get_recognizers dt_sort in
      (* something's funny with these recognizers. assume in same order as constructors *)
      let info = SymMap.find dt_tag global.datatypes in
      let assocs = List.map2 (fun c_nm fd -> (c_nm, fd)) info.dt_constrs recogs in
      let fd = List.assoc Sym.equal c_nm assocs in
      Z3.FuncDecl.apply fd [ t ]
    in
    fun it -> term it


  let assumption context global c =
    let term it = term context global it in
    match c with T it -> Some (it, term it) | Forall ((_s, _bt), _body) -> None


  type reduction =
    { expr : Z3.Expr.expr;
      it : IT.t;
      qs : (Sym.t * BT.t) list;
      extra : Z3.Expr.expr list;
      smt2_doc : Pp.document Lazy.t
    }
  [@@warning "-unused-field"]

  let goal1 context global lc =
    let term it = term context global it in
    let smt2_doc = lazy !^"<to be replaced>" in
    match lc with
    | T it -> { expr = term it; it; qs = []; extra = []; smt2_doc }
    | Forall ((s, bt), it) ->
      let here = Locations.other __FUNCTION__ in
      let v_s, v = IT.fresh_same bt s here in
      let it = IT.subst (make_subst [ (s, v) ]) it in
      { expr = term it; it; qs = [ (v_s, bt) ]; extra = []; smt2_doc }


  let extra_assumptions assumptions qs =
    let loc = Locations.other __FUNCTION__ in
    List.concat_map
      (fun (s, bt) ->
        let v = sym_ (s, bt, loc) in
        LCSet.fold
          (fun lc acc ->
            match lc with
            | Forall ((s', bt'), it') when BT.equal bt bt' ->
              IT.subst (make_subst [ (s', v) ]) it' :: acc
            | _ -> acc)
          assumptions
          [])
      qs


  let goal_to_smt2_doc solver extra lc_expr =
    let check_doc = !^"(check-sat)" in
    (* it seems that Z3.Solver.to_string gives us useful setup/definitions, once
       everything is in scope, which it is in a throwaway solver instance *)
    let simple = Z3.Solver.mk_simple_solver solver.context in
    Z3.Solver.add
      simple
      (Z3.Solver.get_assertions solver.incremental
       @ extra
       @ [ Z3.Boolean.mk_not solver.context lc_expr ]);
    Pp.string (Z3.Solver.to_string simple) ^^ check_doc


  let goal solver global assumptions _pointer_facts lc =
    let g1 = goal1 solver.context global lc in
    let extra1 = extra_assumptions assumptions g1.qs in
    let extra = List.map (term solver.context global) extra1 in
    let smt2_doc = lazy (goal_to_smt2_doc solver extra g1.expr) in
    let here = Locations.other __FUNCTION__ in
    trace [ Check (IT.not_ g1.it here :: extra1) ] solver;
    { g1 with extra; smt2_doc }
end

(* taking a prefix of the simplifications listed in
   https://microsoft.github.io/z3guide/docs/strategies/simplifiers/ *)
(* z3 -simplifiers prints the list of available simplifiers*)
let simplifiers =
  [ "simplify";
    "solve-eqs";
    (* this seems to lead to very strange outcomes, and maybe shouldn't be allowed in
       incremental-mode "elim-unconstrained"; *)
    "propagate-values";
    "simplify"
  ]


let _add_simplifiers context solver =
  match List.map (Z3.Simplifier.mk_simplifier context) simplifiers with
  | s1 :: s2 :: rest ->
    Z3.Solver.add_simplifier context solver (Z3.Simplifier.and_then context s1 s2 rest)
  | [ s ] -> Z3.Solver.add_simplifier context solver s
  | [] -> solver


let make global : solver =
  Z3.Memory.reset ();
  List.iter (fun (c, v) -> Z3.set_global_param c v) (params ());
  Pp.debug
    4
    (lazy
      (Pp.item
         "Setting up Z3 with params"
         (flow_map !^" " (fun (s, v) -> !^s ^^ !^"=" ^^ !^v) (params ()))));
  let context = Z3.mk_context [] in
  Translate.init global context;
  let incremental =
    let s = Z3.Solver.mk_simple_solver context in
    let params = Z3.Params.mk_params context in
    Z3.Params.add_int params (Z3.Symbol.mk_string context "timeout") 200;
    Z3.Solver.set_parameters s params;
    s
  in
  let non_incremental = Z3.Solver.mk_solver context None in
  { context; incremental; non_incremental; query_trace = ref [] }


(* do nothing to non-incremental solver, because that is reset for every query *)
let push solver =
  Z3.Solver.push solver.incremental;
  trace [ Push ] solver


let pop solver n =
  Z3.Solver.pop solver.incremental n;
  trace (List.init n (fun _ -> Pop)) solver


let num_scopes solver = Z3.Solver.get_num_scopes solver.incremental

let add_assumption solver global lc =
  (* do nothing to non-incremental solver, because that is reset for every query *)
  match Translate.assumption solver.context global lc with
  | None -> ()
  | Some (it, sc) ->
    Z3.Solver.add solver.incremental [ sc ];
    trace [ Assert [ it ] ] solver


(* as similarly suggested by Robbert *)
let shortcut simp_ctxt lc =
  let lc = Simplify.LogicalConstraints.simp simp_ctxt lc in
  match lc with LC.T (IT (Const (Bool true), _, _)) -> `True | _ -> `No_shortcut lc


type model_state =
  | Model of Z3.context * Z3.Solver.solver * (Sym.t * LogicalSorts.t) list
  | No_model

let model_state = ref No_model

let model () =
  match !model_state with
  | No_model -> assert false
  | Model (context, z3_solver, qs) ->
    let omodel = Z3.Solver.get_model z3_solver in
    let model = Option.value_err "SMT solver did not produce a counter model" omodel in
    ((context, model), qs)


let maybe_save_slow_problem kind loc lc lc_t smt2_doc time solver =
  match Slow_SMT_Tracing.trace_files time with
  | None -> ()
  | Some (summ_f, smt2_f) ->
    let lc_doc = Pp.string (Z3.Expr.to_string lc_t) in
    Cerb_colour.without_colour
      (fun () ->
        print
          summ_f
          (item
             "Slow CN problem"
             (Pp.flow
                Pp.hardline
                [ item "time taken" (format [] (Float.to_string time));
                  item "current source location" (Locations.pp loc);
                  item "constraint" (LC.pp lc);
                  item "result" (Pp.string kind);
                  item "SMT constraint" lc_doc;
                  item
                    "solver statistics"
                    !^(Z3.Statistics.to_string (Z3.Solver.get_statistics solver))
                ])))
      ();
    output_string summ_f "\n";
    close_out summ_f;
    print smt2_f (Lazy.force smt2_doc);
    close_out smt2_f


let print_doc_to fname doc =
  let channel = open_out_gen [ Open_wronly; Open_creat ] 0o666 fname in
  print channel doc;
  close_out channel


let res_short_string = function
  | Z3.Solver.UNSATISFIABLE -> "unsat"
  | Z3.Solver.SATISFIABLE -> "sat"
  | Z3.Solver.UNKNOWN -> "unknown"


let provable ~loc ~solver ~global ~assumptions ~simp_ctxt ~pointer_facts lc =
  debug 12 (lazy (item "provable: checking constraint" (LC.pp lc)));
  debug 13 (lazy (item "context" (Context.pp_constraints assumptions)));
  Cerb_debug.begin_csv_timing ();
  let context = solver.context in
  let rtrue () =
    model_state := No_model;
    `True
  in
  let rfalse qs solver =
    model_state := Model (context, solver, qs);
    `False
  in
  match shortcut simp_ctxt lc with
  | `True ->
    Cerb_debug.end_csv_timing "Solver.provable shortcut";
    rtrue ()
  | `No_shortcut lc ->
    let existing_scs = Z3.Solver.get_assertions solver.incremental in
    let Translate.{ expr; qs; extra; smt2_doc; _ } =
      Translate.goal solver global assumptions pointer_facts lc
    in
    if !print_level >= 1 then print_doc_to "recent.smt2" (Lazy.force smt2_doc);
    let nlc = Z3.Boolean.mk_not context expr in
    let elapsed, res =
      time_f_elapsed
        (time_f_logs loc 5 "Z3(inc)" (Z3.Solver.check solver.incremental))
        (nlc :: extra)
    in
    maybe_save_slow_problem
      (res_short_string res)
      loc
      lc
      expr
      smt2_doc
      elapsed
      solver.incremental;
    (match res with
     | Z3.Solver.UNSATISFIABLE -> rtrue ()
     | Z3.Solver.SATISFIABLE -> rfalse qs solver.incremental
     | Z3.Solver.UNKNOWN ->
       let () = Z3.Solver.reset solver.non_incremental in
       let () =
         List.iter
           (fun lc -> Z3.Solver.add solver.non_incremental [ lc ])
           ((nlc :: extra) @ existing_scs)
       in
       let elapsed2, res2 =
         time_f_elapsed
           (time_f_logs loc 5 "Z3(non-inc)" (Z3.Solver.check solver.non_incremental))
           []
       in
       maybe_save_slow_problem
         (res_short_string res2)
         loc
         lc
         expr
         smt2_doc
         elapsed2
         solver.non_incremental;
       (match res2 with
        | Z3.Solver.UNSATISFIABLE -> rtrue ()
        | Z3.Solver.SATISFIABLE -> rfalse qs solver.non_incremental
        | Z3.Solver.UNKNOWN ->
          let reason = Z3.Solver.get_reason_unknown solver.non_incremental in
          failwith ("SMT solver returned 'unknown'; reason: " ^ reason)))


module Eval = struct
  open Translate

  let trace_z3_evals = ref false

  let trace_z3_eval expr evaluated =
    if !trace_z3_evals then
      Pp.debug
        8
        (lazy
          (Pp.item
             "Z3 evaluation"
             (Pp.list
                (fun expr -> Pp.string (Z3.Expr.to_string expr))
                [ expr; evaluated ])))
    else
      ()


  let is_array_sort sort =
    try Some (Z3.Z3Array.get_domain sort, Z3.Z3Array.get_range sort) with _ -> None


  let find_already_translated_sort sort =
    try Sort_Table.find sort_table sort with
    | Not_found -> failwith (Z3.Sort.to_string sort ^ "' not in Sort_Table")


  let rec z3_sort (sort : Z3.Sort.sort) =
    match is_array_sort sort with
    | Some (domain, range) -> Map (z3_sort domain, z3_sort range)
    | None -> find_already_translated_sort sort


  let eval global (context, model) to_be_evaluated =
    let unsupported expr what =
      let err = Printf.sprintf "unsupported %s. expr: %s" what (Z3.Expr.to_string expr) in
      failwith err
    in
    (* informed by this:
       https://stackoverflow.com/questions/22885457/read-func-interp-of-a-z3-array-from-the-z3-model/22918197 *)
    let rec func_interp func_decl =
      let domain = Z3.FuncDecl.get_domain func_decl in
      assert (List.length domain = 1);
      let argument_sort = List.hd domain in
      let func_interp = Option.get (Z3.Model.get_func_interp model func_decl) in
      let base_value = z3_expr (Z3.Model.FuncInterp.get_else func_interp) in
      let entries = Z3.Model.FuncInterp.get_entries func_interp in
      let loc = Locations.other __FUNCTION__ in
      List.fold_right
        (fun entry map_value ->
          let entry_args = Z3.Model.FuncInterp.FuncEntry.get_args entry in
          assert (List.length entry_args = 1);
          let index = List.hd entry_args in
          let value = z3_expr (Z3.Model.FuncInterp.FuncEntry.get_value entry) in
          map_set_ map_value (z3_expr index, value) loc)
        entries
        (const_map_ (z3_sort argument_sort) base_value loc)
    and z3_expr (expr : Z3.Expr.expr) : IT.t =
      let args = try Z3.Expr.get_args expr with _ -> [] in
      let args = List.map z3_expr args in
      let loc = Locations.other __FUNCTION__ in
      match () with
      | () when Z3.AST.is_quantifier (Z3.Expr.ast_of_expr expr) ->
        unsupported expr "quantifiers/lambdas"
      | () when Z3.Arithmetic.is_add expr ->
        List.fold_left (fun a b -> add_ (a, b) loc) (hd args) (tl args)
      | () when Z3.Boolean.is_and expr -> and_ args loc
      | () when Z3.Z3Array.is_as_array expr ->
        (* informed by this:
           https://stackoverflow.com/questions/22885457/read-func-interp-of-a-z3-array-from-the-z3-model/22918197 *)
        let as_array_func_parameter =
          List.hd (Z3.FuncDecl.get_parameters (Z3.Expr.get_func_decl expr))
        in
        let func_decl = Z3.FuncDecl.Parameter.get_func_decl as_array_func_parameter in
        func_interp func_decl
      | () when Z3.Z3Array.is_constant_array expr ->
        let abt = z3_sort (Z3.Z3Array.get_domain (Z3.Expr.get_sort expr)) in
        const_map_ abt (hd args) loc
      | () when Z3.Z3Array.is_default_array expr -> unsupported expr "z3 array default"
      | () when Z3.Set.is_difference expr -> setDifference_ (nth args 0, nth args 1) loc
      | () when Z3.Boolean.is_distinct expr -> unsupported expr "z3 is_distinct"
      | () when Z3.Arithmetic.is_idiv expr -> div_ (nth args 0, nth args 1) loc
      | () when Z3.Boolean.is_eq expr -> eq_ (nth args 0, nth args 1) loc
      | () when Z3.Boolean.is_false expr -> bool_ false loc
      | () when Z3.Arithmetic.is_ge expr -> ge_ (nth args 0, nth args 1) loc
      | () when Z3.Arithmetic.is_gt expr -> gt_ (nth args 0, nth args 1) loc
      | () when Z3.Boolean.is_implies expr -> impl_ (nth args 0, nth args 1) loc
      | () when Z3.Arithmetic.is_int_numeral expr ->
        z_ (Z3.Arithmetic.Integer.get_big_int expr) loc
      | () when Z3.BitVector.is_bv_numeral expr ->
        let s = Z3.BitVector.numeral_to_string expr in
        let z = Z.of_string s in
        num_lit_
          z
          (BT.Bits (BT.Unsigned, Z3.BitVector.get_size (Z3.Expr.get_sort expr)))
          loc
      | () when Z3.Boolean.is_ite expr -> ite_ (nth args 0, nth args 1, nth args 2) loc
      | () when Z3.Arithmetic.is_le expr -> le_ (nth args 0, nth args 1) loc
      | () when Z3.Arithmetic.is_lt expr -> lt_ (nth args 0, nth args 1) loc
      | () when Z3.Arithmetic.is_modulus expr -> mod_ (nth args 0, nth args 1) loc
      | () when Z3.Arithmetic.is_mul expr -> mul_ (nth args 0, nth args 1) loc
      | () when Z3.Boolean.is_not expr -> not_ (nth args 0) loc
      | () when Z3.Boolean.is_or expr -> or_ args loc
      | () when Z3.Arithmetic.is_rat_numeral expr ->
        q1_ (Z3.Arithmetic.Real.get_ratio expr) loc
      | () when Z3.Arithmetic.is_remainder expr -> rem_ (nth args 0, nth args 1) loc
      | () when Z3.Z3Array.is_select expr -> map_get_ (nth args 0) (nth args 1) loc
      | () when Z3.Z3Array.is_store expr ->
        map_set_ (nth args 0) (nth args 1, nth args 2) loc
      | () when Z3.Arithmetic.is_sub expr -> sub_ (nth args 0, nth args 1) loc
      | () when Z3.Set.is_subset expr -> subset_ (nth args 0, nth args 1) loc
      | () when Z3.Boolean.is_true expr -> bool_ true loc
      | () when Z3.Arithmetic.is_uminus expr ->
        let arg = nth args 0 in
        (match IT.bt arg with
         | Integer -> sub_ (int_ 0 loc, arg) loc
         | Real -> sub_ (q_ (0, 1) loc, arg) loc
         | _ -> Cerb_debug.error "illtyped index term")
      | () when Z3.AST.is_var (Z3.Expr.ast_of_expr expr) ->
        unsupported expr "variables from quantifiers/lambdas"
      | () ->
        let func_decl = Z3.Expr.get_func_decl expr in
        let func_name = Z3.FuncDecl.get_name func_decl in
        let expr_bt = z3_sort (Z3.Expr.get_sort expr) in
        (match () with
         | () when Z3.FuncDecl.equal func_decl (loc_to_addr_fundecl context global) ->
           let p = nth args 0 in
           (* fiddly in the pointer-is-bitvector case begin match IT.is_pointer p with |
              Some (_id, z) -> z_ z | _ -> pointerToIntegerCast_ p end *)
           pointerToIntegerCast_ p loc
         | ()
           when Z3.FuncDecl.equal func_decl (alloc_id_addr_to_loc_fundecl context global)
           ->
           let alloc_id =
             Option.value_err "non-wrapped alloc_id" @@ IT.is_alloc_id @@ nth args 0
           in
           let i = nth args 1 in
           (match IT.get_num_z i with
            | Some addr -> pointer_ ~alloc_id ~addr loc
            | _ -> copyAllocId_ ~addr:i ~loc:(pointer_ ~alloc_id ~addr:Z.zero loc) loc)
         | ()
           when Z3.FuncDecl.equal func_decl (integer_to_alloc_id_fundecl context global)
           ->
           let i = nth args 0 in
           (match (!use_vip, IT.is_z i) with
            | true, Some z -> alloc_id_ z loc
            | true, None -> assert false
            | false, _ -> alloc_id_ Z.zero loc)
         | () when Z3Symbol_Table.mem z3sym_table func_name ->
           (match Z3Symbol_Table.find z3sym_table func_name with
            | DefaultFunc { bt } -> default_ bt loc
            | MemberFunc { tag; member } ->
              let sd = Memory.member_types (SymMap.find tag global.struct_decls) in
              let member_bt = Memory.bt_of_sct (List.assoc Id.equal member sd) in
              member_ ~member_bt (nth args 0, member) loc
            | StructFunc { tag } ->
              let sd = Memory.members (SymMap.find tag global.struct_decls) in
              struct_ (tag, List.combine sd args) loc
            | CompFunc { bts; i } ->
              let comp_bt = List.nth bts i in
              nthTuple_ ~item_bt:comp_bt (i, nth args 0) loc
            | TupleFunc { bts = _ } -> tuple_ args loc
            | RecordFunc { mbts } ->
              IT (Record (List.combine (List.map fst mbts) args), Record mbts, loc)
            | RecordMemberFunc { mbts; member } ->
              let member_bt = List.assoc Id.equal member mbts in
              IT (RecordMember (nth args 0, member), member_bt, loc)
            | DatatypeConsFunc { nm } ->
              let info = SymMap.find nm global.datatype_constrs in
              IT
                ( Constructor (nm, List.combine (List.map fst info.c_params) args),
                  Datatype info.c_datatype_tag,
                  loc )
            | DatatypeConsRecogFunc { nm = _ } ->
              (* not supported inside CN, hopefully we shouldn't need it *)
              unsupported expr "Reconstructing Z3 term with datatype recogniser"
            | DatatypeAccFunc _ ->
              unsupported expr "Reconstructing Z3 term with datatype accessor"
              (* Simplify.IndexTerms.datatype_member_reduce (nth args 0) xs.member
                 xs.bt *)
            | UninterpretedVal { nm } -> sym_ (nm, expr_bt, loc)
            | Term { it } -> it
            | UnsignedToSigned n ->
              Simplify.IndexTerms.cast_reduce (Bits (Signed, n)) (nth args 0)
            | SignedToUnsigned n ->
              Simplify.IndexTerms.cast_reduce (Bits (Unsigned, n)) (nth args 0))
         | () when String.equal (Z3.Symbol.to_string func_name) "^" ->
           exp_ (nth args 0, nth args 1) loc
         | () when Z3.Arithmetic.is_real2int expr -> realToInt_ (nth args 0) loc
         | () when Z3.Arithmetic.is_int2real expr -> intToReal_ (nth args 0) loc
         | () when BT.equal Unit expr_bt -> unit_ loc
         (* TODO: this looks incorrect: nm will not be bound in the typing context *)
         | () when is_uninterp_bt expr_bt && List.length args == 0 ->
           (* Z3 creates unspecified consts within uninterpreted types - map to vars *)
           let nm = Sym.fresh_named (Z3.Symbol.to_string func_name) in
           Z3Symbol_Table.add z3sym_table func_name (UninterpretedVal { nm });
           sym_ (nm, expr_bt, loc)
         | () when Option.is_some (Z3.Model.get_func_interp model func_decl) ->
           assert (List.length args = 1);
           map_get_ (func_interp func_decl) (List.hd args) loc
         | () -> unsupported expr "Reconstructing unknown Z3 term")
    in
    let expr = Translate.term ~warn_lambda:false context global to_be_evaluated in
    match Z3.Model.eval model expr true with
    | None -> None
    | Some v ->
      trace_z3_eval expr v;
      Some (z3_expr v)
end

let eval = Eval.eval

let debug_solver_to_string solver =
  Pp.debug
    2
    (lazy
      (Pp.item
         "debug solver.to_string"
         (Pp.string (Z3.Solver.to_string solver.incremental))))


let debug_solver_query solver global assumptions pointer_facts lc =
  Pp.debug
    2
    (lazy
      (let Translate.{ smt2_doc; _ } =
         Translate.goal solver global assumptions pointer_facts lc
       in
       Pp.item "debug solver query" (Lazy.force smt2_doc)))
