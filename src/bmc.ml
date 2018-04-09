(*
 * TODO: Give an overview of the relevant modules
 *)

open Core
open Core_ctype
open Cthread
open Global_ocaml
open Lem_pervasives
open Mem
open Ocaml_implementation
open Ocaml_mem
open Pp_core
open Z3
open Z3.Arithmetic
open Z3.Boolean

open Bmc_analysis
open Bmc_events
open Bmc_inline
open Bmc_normalize
open Bmc_saves
open Bmc_sorts
open Bmc_utils

let initial_tid = -1

(* ========== Type definitions ========== *)

type ksym_table = (ksym, Expr.expr) Pmap.map

(* NB: all heap stuff is deprecated and replaced w/ memory model graph 
 *
 * Pointer state: 
 * For every variable of Core type pointer, 
 *    - Associate it with a set of allocs it might refer to
 *
 * Bmc_address:
 *    - Store allocation id associated with it
 *    - Sequence ctr and sequence history of expressions stored
 *    - Z3 Sort (?)
 *
 * For let x: pointer = Create...
 *    - Create a allocation id (storing values of a certain type?)
 *    - Associate x to allocation {@x}
 *    - Create a bmc_address, map @x->bmc_address
 *    - Let x be a z3 expr (Pointer @x)
 *    - Heap: map x->@x_1 where @x_1 is some unspecified Z3 symbol
 *
 * For let y: pointer = x
 *    - Associate y with set of allocs x might refer to
 *    - "y : SMT ptr sort" = x (address)
 *
 * For store (p, v)
 *    - If v is a pointer, update points-to map such that all 
 *      all allocs in allocs(p) might point to allocs(v)
 *    - For each alloc in allocs(p), 
 *      create a fresh sequence variable @p_i 
 *    - In Z3: addr(p) == @p ? @p_i = v : @p_i = @p_{i-1}
 *
 * For load (p)
 *    - lookup address variable points to, assign it current value in z3
 *
 * bmc_state:
 *    - map from address -> cur_value (int?)
 *    - pointer state: symbol -> PointerState map
 *)


type kbmc_address = {
  addr        : Address.addr;
  (*
  seq_ctr     : int ref;
  hist        : ((int, Expr.expr) Pmap.map) ref;
  *)
  sort        : Sort.sort
}

(* type kheap = (Address.addr, Expr.expr) Pmap.map *)


(* TODO: sym_table, addr_map, alias_state should not use references *)
type 'a bmc_state = {
  ctx         : context;
  file        : 'a typed_file;

  solver      : Solver.solver;
  sym_table   : ksym_table ref;
  sym_supply  : ksym_supply ref;

  (* Map from alloc -> address *)
  addr_map    : (Address.addr, kbmc_address) Pmap.map ref;

  (* Alias analysis stuff *)
  alias_state : kanalysis_state;

  (* TODO: hack for function calls 
   * Map from sym : cfunction bound in mk_eq_expr to function sym 
   * Assumes function is bound exactly once
   *)
  fn_map      : (ksym, ksym) Pmap.map ref;

  (* ------------- *)
  
  (* Map from address to Z3 symbol representing value *)
  (* heap        : (Address.addr, Expr.expr) Pmap.map; *)


  parent_tid  : (thread_id * thread_id)  Pset.set ref;
  action_map  : (action_id, bmc_paction) Pmap.map ref;

  aid_supply  : action_id ref;
  tid_supply  : thread_id ref;
  tid         : thread_id;

  (* LOCAL STATE *)
  preexec      : preexecution;
  vcs          : Expr.expr list;
  has_returned : Expr.expr; 
  z3_ret       : Expr.expr;
  ret_asserts  : Expr.expr list;
  saves        : unit saves_map
}

(* ========== BMC ========== *)

let check_solver_fun (solver: Solver.solver) 
                     (fun_list: FuncDecl.func_decl list)
                     (ret_value: Expr.expr option) =
  let status = Solver.check solver [] in
  Printf.printf "Status: %s\n" (Solver.string_of_status status);
  begin
  if status = UNKNOWN then
    Printf.printf "Unknown: %s\n" (Solver.get_reason_unknown solver)
  else if status = UNSATISFIABLE then
    begin
      print_endline "NOT SAT :)";
    end
  else
    begin 
    Printf.printf "SAT====MODEL======= :( \n";
    let model = Solver.get_model solver in
      match model with
      | Some m -> 
          Printf.printf "Model: \n%s\n" (Model.to_string m);
          print_endline "FUNC_INTERPS";
          List.iter (fun f ->
            match Model.get_func_interp m f with
            | Some interp -> 
                Printf.printf "Fun: %s\n Interp: %s\n" (FuncDecl.to_string f)
                                          (Model.FuncInterp.to_string interp);
            | None -> print_endline ("No interp for: " ^ (FuncDecl.to_string f))
          ) fun_list;
          begin
            match ret_value with
            | None -> ()
            | Some z3_ret ->
              print_endline "RET_VALUE";
              match Model.get_const_interp_e m (z3_ret) with
              | Some interp ->
                  Printf.printf "Z3_ret: %s\n" (Expr.to_string interp)
              | None -> print_endline "No interp for ret."
          end;
          Printf.printf "SAT :( \n"
      | None -> Printf.printf "No model\n"
    ;
    end
  end;
  status

let check_solver (solver: Solver.solver) =
  check_solver_fun solver [] None

(*
let get_last_seqnum (ctx: context) (bmc_address : kbmc_address) =
  (!(bmc_address.seq_ctr))
*)

(*
let mk_next_seq_symbol (ctx: context) (bmc_address : kbmc_address) =
  bmc_address.seq_ctr := succ (!(bmc_address.seq_ctr));
  (mk_sym ctx ("@" ^ (Address.to_string (bmc_address.addr)) ^ "_" ^ 
              (string_of_int (!(bmc_address.seq_ctr)))),
   get_last_seqnum(ctx) (bmc_address))
*)

let mk_next_aid (state: 'a bmc_state) =
  state.aid_supply := succ !(state.aid_supply);
  !(state.aid_supply)

let mk_next_tid (state: 'a bmc_state) =
  state.tid_supply := succ !(state.tid_supply);
  !(state.tid_supply)

let ctor_to_z3 (state: 'a bmc_state) (ctor: typed_ctor) 
               (pes: Expr.expr list) (sort: Sort.sort) =
  match ctor with
  | Cnil _ (* empty list *)
  | Ccons -> 
      assert false
  | Ctuple ->
      assert (List.length pes = Tuple.get_num_fields sort);
      let mk_decl = Tuple.get_mk_decl sort in
      FuncDecl.apply mk_decl pes
  | Carray ->
      assert false(* C array *)
  | Civmax ->
      assert false
  | Civmin ->
      assert false
  | Civsizeof ->
      assert false (* sizeof value *)
  | Civalignof ->
      assert false(* alignof value *)
  | CivCOMPL ->
      assert false (* bitwise complement *)
  | CivAND ->
      assert false (* bitwise AND *)
  | CivOR ->
      assert false (* bitwise OR *)
  | CivXOR ->
      assert false (* bitwise XOR *) 
  | Cspecified ->
      assert (List.length pes = 1);

      let expr = List.hd pes in
        (* TODO: Do generically... *)
        if (Sort.equal sort (LoadedInteger.mk_sort state.ctx)) then
          LoadedInteger.mk_loaded state.ctx expr
        else if (Sort.equal sort (LoadedPointer.mk_sort state.ctx)) then
          (
          Printf.printf "TODO: pointers\n";
          LoadedPointer.mk_loaded state.ctx expr 
          )
        else 
          assert false
  | Cunspecified (* unspecified value *) ->
      assert (List.length pes = 1);

      let expr = List.hd pes in

      if (Sort.equal sort (LoadedInteger.mk_sort state.ctx)) then
        LoadedInteger.mk_unspec state.ctx expr
      else if (Sort.equal sort (LoadedPointer.mk_sort state.ctx)) then
        LoadedPointer.mk_unspec state.ctx expr
      else
        assert false
  | Cfvfromint (* cast integer to floating value *)
  | Civfromfloat (* cast floating to integer value *) ->
      assert false

let z3_sortlist_to_tuple (ctx: context)
                         (sorts: Sort.sort list) : Sort.sort =
  let sort_to_string = "(" ^ (String.concat "," (List.map Sort.to_string sorts)) ^ ")" in
  let sort_symbol = mk_sym ctx sort_to_string in

  let sym_list = List.mapi 
      (fun i _ -> mk_sym ctx ( "#" ^ (string_of_int i))) sorts in

  Tuple.mk_sort ctx sort_symbol sym_list sorts 

(* core_base_type to z3 sort *)
let rec cbt_to_z3 (state: 'a bmc_state) (cbt : core_base_type) : Sort.sort =
  let ctx = state.ctx in
  match cbt with
   | BTy_unit  -> 
        UnitSort.mk_sort ctx
   | BTy_boolean ->
        Boolean.mk_sort ctx
   | BTy_ctype -> 
        (* TODO *)
        ctypeSort ctx
   | BTy_list _ -> assert false
   | BTy_tuple cbt_list ->
        let sort_to_string = fun t -> pp_to_string
                              (Pp_core.Basic.pp_core_base_type t) in
        let sort_name = sort_to_string cbt in
        let sort_symbol = mk_sym state.ctx sort_name in

        let sym_list = List.mapi 
            (fun i _ -> mk_sym state.ctx 
                  ( "#" ^ (string_of_int i)))
            cbt_list in
        let sort_list = List.map (fun t -> cbt_to_z3 state t) cbt_list in
        Tuple.mk_sort ctx sort_symbol sym_list sort_list 
   | BTy_object obj_type ->
       core_object_type_to_z3_sort ctx obj_type
   | BTy_loaded obj_type ->
       (* TODO do generically *)
       begin
         match obj_type with
          | OTy_integer -> 
              LoadedInteger.mk_sort ctx
          | OTy_pointer -> 
              LoadedPointer.mk_sort ctx
          | _ -> assert false
       end

let add_sym_to_sym_table (state: 'a bmc_state) (sym: ksym) (ty: core_base_type) =
  let z3_sort = cbt_to_z3 state ty in
  let z3_sym = Expr.mk_const state.ctx (symbol_to_z3 state.ctx sym) z3_sort in
  state.sym_table := Pmap.add sym z3_sym !(state.sym_table)

let pmap_lookup_or_fail key pmap =
  match Pmap.lookup key pmap with
  | None -> assert false
  | Some x -> x

let bmc_lookup_sym (sym: ksym) (state: 'a bmc_state) : Expr.expr =
  pmap_lookup_or_fail sym !(state.sym_table)

let bmc_lookup_alloc alloc (state: 'a bmc_state) : kbmc_address =
  pmap_lookup_or_fail alloc !(state.addr_map)

(*
let bmc_lookup_addr_in_heap alloc heap =
  pmap_lookup_or_fail alloc heap
*)

let initial_bmc_state (supply : ksym_supply) 
                      (file : 'a typed_file)
                      : 'a bmc_state = 
  let cfg = [ ("model", "true")
            ; ("proof", "false")
            ] in

  let ctx = mk_context cfg in
  {
    ctx = ctx;
    file = file;
    solver = Solver.mk_solver ctx None;
    sym_table = ref (Pmap.empty sym_cmp);
    sym_supply = ref supply;
    addr_map = ref (Pmap.empty Pervasives.compare);
    (* heap = Pmap.empty Pervasives.compare; *)
    alias_state = initial_analysis_state ();

    fn_map = ref (Pmap.empty sym_cmp);

    vcs = [];
    preexec = initial_preexec ();
    action_map = ref (Pmap.empty Pervasives.compare);
    parent_tid = ref (Pset.empty Pervasives.compare);
    aid_supply = ref 0;
    tid_supply = ref 0;
    tid        = 0;

    has_returned = mk_false ctx;
    z3_ret = Expr.mk_fresh_const ctx "ret_main" (LoadedInteger.mk_sort ctx);
    ret_asserts = [];
    saves = Pmap.empty sym_cmp
  }

(*
let add_func_constraints (st : bmc_state) =
  Solver.add st.solver (sizeof_ibty_goals st.ctx) ;
  Solver.add st.solver (ivmin_goals st.ctx) 
*)

let integer_value_to_z3 (ctx: context) ival =
  let maybe_ival = eval_integer_value ival in
  match maybe_ival with
  | None -> assert false
  | Some i -> Integer.mk_numeral_i ctx (Nat_big_num.to_int i)


let object_value_to_z3 (ctx: context) = function
  | OVinteger ival -> integer_value_to_z3 ctx ival
  | OVfloating _
  | OVpointer _ ->
      assert false
  | OVcfunction (Sym sym)->
      (*
      let tmp = symbol_to_int sym in
      print_endline ("XX" ^ (string_of_int tmp));
      *)
      CFunctionSort.mk_cfn ctx (Integer.mk_numeral_i ctx (symbol_to_int sym))
  | OVcfunction _ ->
     assert false 
  | OVarray _ 
  | OVstruct _
  | OVunion _ 
  | OVcomposite _ ->
      assert false

let ctype_to_z3 (ctx: context) (ctype: ctype0) =
  let _ =  (* TODO: safeguard for unimplemented stuff *)
    match ctype with
    | Void0 -> assert false
    | Basic0 (Integer i) ->
        begin
        match i with
        | Char -> assert false
        | Bool -> ()
        | Unsigned ibty (* Fall through *)
        | Signed ibty -> 
          begin
          match ibty with
          | Ichar | Short | Int_ | Long | LongLong | Intmax_t | Intptr_t -> ()
          | _ -> assert false
          end
        | _ -> assert false
        end
    | _ -> assert false
  in
  ctype_to_expr ctype ctx


let rec value_to_z3 (ctx: context) (cval: value) (typ: core_base_type) =
  match cval with
  | Vunit -> UnitSort.mk_unit ctx
  | Vtrue -> mk_true ctx
  | Vfalse -> mk_false ctx
  | Vlist (_, cvals) ->
      assert false;
  | Vtuple cvals ->
      assert false
  | Vctype ty ->
      ctype_to_z3 ctx ty      
  | Vobject oval ->
      object_value_to_z3 ctx oval
  | Vloaded lval ->
      match lval with
      | LVspecified ov  ->
          begin
          match ov with
          | OVinteger ival ->
            let iexpr = integer_value_to_z3 ctx ival in
            LoadedInteger.mk_loaded ctx iexpr
          | _ -> assert false
          end
      | LVunspecified ctyp -> 
          (* TODO*)
          begin
          match typ with
          | BTy_loaded OTy_integer -> 
              let ctyp_expr = ctype_to_z3 ctx ctyp in
              LoadedInteger.mk_unspec ctx ctyp_expr
          | _ -> assert false 
          end

let binop_to_constraints (ctx: context) (pe1: Expr.expr) (pe2: Expr.expr) = function
  | OpAdd -> Arithmetic.mk_add ctx [ pe1; pe2 ]
  | OpSub -> Arithmetic.mk_sub ctx [ pe1; pe2 ]
  | OpMul -> Arithmetic.mk_mul ctx [ pe1; pe2 ]
  | OpDiv -> Arithmetic.mk_div ctx pe1 pe2
  | OpRem_t -> assert false
  | OpRem_f -> Integer.mk_mod ctx pe1 pe2 (* TODO: Flooring remainder? *)
  | OpExp -> assert false
  | OpEq -> mk_eq ctx pe1 pe2   
  | OpLt -> Arithmetic.mk_lt ctx pe1 pe2
  | OpLe -> Arithmetic.mk_le ctx pe1 pe2 
  | OpGt -> Arithmetic.mk_gt ctx pe1 pe2
  | OpGe -> Arithmetic.mk_ge ctx pe1 pe2
  | OpAnd -> mk_and ctx [ pe1; pe2 ] 
  | OpOr -> mk_or ctx [ pe1; pe2 ]


(* TODO: add symbol to sym table somewhere else!!! 
 * Also just completely rewrite this function... 
 * *)
let mk_eq_expr (state: 'a bmc_state) (m_sym: ksym option) 
               (ty : core_base_type) (expr: Expr.expr) =
  match m_sym with
  | None -> mk_true state.ctx (* Do nothing *)
  | Some sym -> 
      let pat_sym = symbol_to_z3 state.ctx sym in
      (* TODO: case on bmc_expr instead *)
      begin
      match ty with
      | BTy_unit -> assert false
      | BTy_ctype (* Fall through *)
      | BTy_boolean -> 
          (* TODO: duplicated code *)
          let sort = cbt_to_z3 state ty in
          let expr_pat = Expr.mk_const state.ctx pat_sym sort in
          state.sym_table := Pmap.add sym expr_pat (!(state.sym_table));
          (mk_eq state.ctx expr_pat expr)
      | BTy_tuple ty_list -> 
          assert false
      | BTy_list _ -> assert false
      (*
      | BTy_object OTy_pointer -> 
              assert (Sort.equal (Expr.get_sort expr) 
                                 (PointerSort.mk_sort state.ctx));
              (* Create a new symbol for the pattern pointer *)
              let pat_sym = symbol_to_z3 state.ctx sym in
              let expr_pat = 
                  Expr.mk_const state.ctx pat_sym (PointerSort.mk_sort state.ctx)
              in
              (* Add to sym table *)
              state.sym_table := Pmap.add sym expr_pat (!(state.sym_table));

              (* Assert that get_addr expr_pat == get_addr expr *)
              mk_eq state.ctx 
                (PointerSort.get_addr state.ctx expr_pat)
                (PointerSort.get_addr state.ctx expr)   
       *)
       | BTy_object obj_type -> 
          (* TODO: duplicated *)
              let sort = cbt_to_z3 state ty in
              let expr_pat = Expr.mk_const state.ctx pat_sym sort in
              state.sym_table := Pmap.add sym expr_pat (!(state.sym_table));
              begin
              match obj_type with
              | OTy_pointer ->
                  assert (Sort.equal (Expr.get_sort expr) 
                                     (PointerSort.mk_sort state.ctx));
                  mk_eq state.ctx
                    (PointerSort.get_addr state.ctx expr_pat)
                    (PointerSort.get_addr state.ctx expr)
              | OTy_integer ->
                  mk_eq state.ctx expr_pat expr
              | OTy_cfunction _ ->
                  (* Assert cfunction type is bound only from constructed type 
                   * and not a symbol *)
                  assert (Expr.get_num_args expr = 1);
                  (* Add to fn_map 
                   * TODO: this is a hack *)
                  let sym_id = (match Expr.get_args expr with 
                                | [x] -> assert (Expr.is_numeral x);
                                         Integer.get_int x
                                | _ -> assert false) in
                  state.fn_map := Pmap.add sym (Sym.Symbol(sym_id, None))
                                  !(state.fn_map);
                  mk_eq state.ctx expr_pat expr
              | _ ->
                  assert false
              end
      | BTy_loaded cot ->
          (* TODO duplicated code: should case on bmc_expr instead maybe *)
          let pat_symbol = symbol_to_z3 state.ctx sym in
          let z3_sort = cbt_to_z3 state ty in
          let expr_pat = Expr.mk_const state.ctx pat_symbol z3_sort in
          state.sym_table := Pmap.add sym expr_pat 
                                      (!(state.sym_table));
          mk_eq state.ctx expr_pat expr
         end

let rec pattern_match (state: 'a bmc_state) (pattern: typed_pattern)
                      (expr: Expr.expr) =
   match pattern with
  | CaseBase(maybe_sym, typ) ->
      mk_true state.ctx
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      let exprList = Expr.get_args expr in
      let patConditions = List.mapi 
          (fun i pat -> pattern_match state pat ((List.nth exprList i )))
          patlist in
      mk_and state.ctx patConditions
  | CaseCtor(Cspecified, [CaseBase(maybe_sym, BTy_object OTy_integer)]) ->
      LoadedInteger.is_loaded state.ctx expr 
  | CaseCtor(Cspecified, [CaseBase(maybe_sym, BTy_object OTy_pointer)]) ->
      LoadedPointer.is_loaded state.ctx expr
  | CaseCtor(Cunspecified, _) -> 
      (* TODO: terrible... *)
      if (Sort.equal (Expr.get_sort expr) 
                     (LoadedInteger.mk_sort state.ctx)) then
        LoadedInteger.is_unspec state.ctx expr
      else if (Sort.equal (Expr.get_sort expr) 
                          (LoadedPointer.mk_sort state.ctx)) then
        LoadedPointer.is_unspec state.ctx expr
      else
        assert false
  | _ -> 
      assert false

let rec mk_eq_pattern (state: 'a bmc_state) (pattern: typed_pattern)
                      (expr: Expr.expr) =
  match pattern with
  | CaseBase(maybe_sym, typ) ->
      mk_eq_expr state maybe_sym typ expr 
  | CaseCtor(Ctuple, patlist) -> 
      (* TODO: make ty_list *)
      let exprList = Expr.get_args expr in
      assert (Expr.get_num_args expr = List.length patlist);
      let zipped = List.combine exprList patlist in
      mk_and state.ctx 
        (List.mapi (fun i (exp, pat) -> 
          mk_eq_pattern state pat 
          ((exp))) zipped
        )
  | CaseCtor(Cspecified, patlist) -> 
      begin
        match patlist with
        | ([CaseBase(maybe_sym, BTy_object OTy_integer)]) -> 
            (* Guard by ensuring expr is constructed with loaded *)
            let is_loaded = LoadedInteger.is_loaded state.ctx expr in
            let loaded_value = LoadedInteger.get_loaded_value state.ctx expr in     
            let eq_expr = mk_eq_expr state maybe_sym
                                 (BTy_object OTy_integer) 
                                 (loaded_value) in
            mk_and state.ctx [is_loaded; eq_expr]
        | ([(CaseBase(maybe_sym, BTy_object OTy_pointer))])-> 
            (* TODO: duplicated code *)
            let is_loaded = LoadedPointer.is_loaded state.ctx expr in
            let loaded_value = LoadedPointer.get_loaded_value state.ctx expr
            in
            let (eq_expr) = mk_eq_expr state maybe_sym
                                 (BTy_object OTy_pointer) 
                                 (loaded_value) in
            mk_and state.ctx [is_loaded; eq_expr]
        | _ -> assert false
    end
  | CaseCtor(Cunspecified, [CaseBase(maybe_sym, _)]) ->
      (* TODO: terrible... *)
      if (Sort.equal (Expr.get_sort expr) 
                     (LoadedInteger.mk_sort state.ctx)) then
        let is_unspec = LoadedInteger.is_unspec state.ctx expr in
        let unspec_value = LoadedInteger.get_unspec_value state.ctx expr in
        let eq_expr = mk_eq_expr state maybe_sym BTy_ctype (unspec_value) in
        mk_and state.ctx [is_unspec; eq_expr]
      else if (Sort.equal (Expr.get_sort expr) 
                          (LoadedPointer.mk_sort state.ctx)) then
        let is_unspec = LoadedPointer.is_unspec state.ctx expr in
        let unspec_value = LoadedPointer.get_unspec_value state.ctx expr in
        let eq_expr = mk_eq_expr state maybe_sym BTy_ctype (unspec_value) in
        mk_and state.ctx [is_unspec; eq_expr]
      else
        assert false
  | _ -> assert false

(* TODO: rewrite *)
let concat_vcs (state: 'a bmc_state)
               (vc1: Expr.expr list)
               (vc2: Expr.expr list)
               (guard: Expr.expr) =
  let new_vc1 = mk_implies state.ctx guard
                    (mk_and state.ctx vc1) in
  let new_vc2 = mk_implies state.ctx 
                    (mk_not state.ctx guard)
                    (mk_and state.ctx vc2) in
  [new_vc1; new_vc2 ]                  

let rec bmc_pexpr (state: 'a bmc_state) 
                  (Pexpr(_, bTy, pe) : typed_pexpr) : 
                    Expr.expr * AddressSet.t * 'a bmc_state =
  match pe with
    | PEsym sym ->
        let sym_expr = bmc_lookup_sym sym state in
        let allocs = alias_lookup_sym sym state.alias_state in
        sym_expr, allocs, state
    | PEimpl _ -> assert false
    | PEval cval ->
        (value_to_z3 state.ctx cval bTy), AddressSet.empty, state
    | PEconstrained _ ->
        assert false
    | PEundef _ ->
        let sort = cbt_to_z3 state bTy in
        let new_vcs = (mk_implies state.ctx 
                            (mk_not state.ctx state.has_returned) 
                            (mk_false state.ctx)) 
                      :: state.vcs in
        let new_state = {state with vcs = new_vcs} in
        Expr.mk_fresh_const state.ctx "undef" sort, AddressSet.empty, new_state 
    | PEerror _ -> 
        let sort = cbt_to_z3 state bTy in
        let new_vcs = (mk_implies state.ctx
                            (mk_not state.ctx state.has_returned)
                            (mk_false state.ctx)) 
                      :: state.vcs in
        let new_state = {state with vcs = new_vcs} in
        Expr.mk_fresh_const state.ctx "error" sort, AddressSet.empty, new_state 
    | PEctor (ctor, pelist) -> 
        let sort = cbt_to_z3 state bTy in
        (* TODO: state needs to be propagated. 
         * Currently assume PEs don't change  state except vcs *) 
        (* BMC each expression *)
        let empty_vc_state = ({state with vcs = []}) in
        let z3_pelist_tmp = List.map 
            (fun pe -> bmc_pexpr empty_vc_state pe) pelist in
        let new_vcs = List.concat 
            (List.map (fun (_, _, st) -> st.vcs) z3_pelist_tmp) in
        let final_vcs = state.vcs @ new_vcs in

        let z3_pelist = List.map (fun (a, _, _) -> a) z3_pelist_tmp in
        let new_state = ({state with vcs = final_vcs})  in
        let ret = ctor_to_z3 new_state ctor z3_pelist sort in

        (* Union allocs *)
        let allocs = List.fold_left (fun s (_, allocs, _) ->
          AddressSet.union s allocs) AddressSet.empty z3_pelist_tmp in

        ret, allocs, new_state 

    | PEcase (pe, caselist) -> 
        (* case pe of | pat1 -> e1 | pat2 -> e2 | pat3 -> e3 | _ ->
          * error("incomplete pattern matching") 
          *
          * pe -> z3 expr
          * convert each pat to condition for matching: 
          * e.g. - if pat = CaseBase(Some sym), true 
          *      - if pat = _, true (all CaseBase => true)
          *      - if pat = Specified(x): isSpecified pe
          *      - if pat = (a, b): true b/c  type? (TODO)
          *
          * Then convert each pat to an equality with pe
          *
          * BMC each e* with empty vcs
          *
          * Make guards with Boolean.mk_ite 
          * *)
        let (pe_z3, pe_set, state) = bmc_pexpr state pe in
        List.iter (fun (pat1, _) -> 
          alias_pattern state.alias_state pat1 pe_set) caselist;

        begin
            let pattern_guards = 
              List.map (fun (pat, _) -> pattern_match state pat pe_z3) caselist in 
            let complete_guard = mk_or state.ctx pattern_guards in
            Solver.add state.solver [ complete_guard ];

            let combined_pat_guards = 
              List.mapi (fun i expr -> 
                mk_and state.ctx 
                [ mk_not state.ctx (mk_or state.ctx (list_take i pattern_guards))
                ; expr 
                ]
                ) pattern_guards in

            let expr_eqs = List.map (fun (pat, _) -> 
              mk_eq_pattern state pat pe_z3) caselist in

            (* Match case i => expr_eq i holds *)
            let impl_eqs = List.map2 
              (fun guard eq -> mk_implies state.ctx guard eq) 
              combined_pat_guards expr_eqs in
            Solver.add state.solver impl_eqs;

            (* Now need to combine verification conditions: 
             * st1.vcs @... guarded by case match *)
            let cases_z3 = List.map 
                (fun (_, e) -> bmc_pexpr ({state with vcs = []}) e) caselist in
            let cases_vcs = (List.map (fun (_,_,s) -> mk_and state.ctx s.vcs) cases_z3) in
            let new_vcs = 
              (state.vcs @ (List.map2 (fun guard vc -> mk_implies state.ctx guard vc)
              combined_pat_guards cases_vcs)) in
            (* TODO: correctness? *)
            let ret_state = {state with vcs = new_vcs} in

            (* Now make ite, careful with cases where expressions are None *)
            let zipped = List.combine combined_pat_guards 
                        (List.map (fun (e, _, _) -> e) cases_z3) in
            let rev_filtered = List.rev zipped in

            (* Alloc ids *)
            let alloc_ret = List.fold_left (fun s (_, set, _) ->
              AddressSet.union s set) AddressSet.empty cases_z3 in

            begin
            match List.length rev_filtered with
            | 0 -> assert false
            | 1 -> 
                let (_, e) = List.hd rev_filtered in
                e, alloc_ret, ret_state
            | _ -> 
                let (_, last) = List.hd rev_filtered in
                let ite = List.fold_left (fun prev (guard, e) ->
                  mk_ite ret_state.ctx guard e prev
                ) last (List.tl rev_filtered) in

                ite, alloc_ret, ret_state
            end
        end
    | PEarray_shift _ -> assert false
    | PEmember_shift _ -> assert false
    | PEnot pe1 -> 
        let (z3_pe1, allocs, state) = bmc_pexpr state pe1 in  
          (mk_not state.ctx z3_pe1), allocs, state
    | PEop (bop, pe1, pe2) ->
        let (z3_pe1, alloc1, state1) = bmc_pexpr state pe1 in
        let (z3_pe2, alloc2, state2) = bmc_pexpr state1 pe2 in
        binop_to_constraints state2.ctx z3_pe1 z3_pe2 bop, 
            AddressSet.union alloc1 alloc2, 
            state2
    | PEstruct _
    | PEunion _ -> assert false
    | PEcall(Sym sym, _) ->
        assert false
    | PEcall _ -> 
        assert false
    (*
    | PElet (CaseBase(Some sym, pat_ty), pe1, pe2) ->
        (* TODO: switch to mk_eq_pattern *)
        let (Pexpr(pat_type, _)) = pe1 in
        let z3_sort = cbt_to_z3 state pat_type in

        let (z3_pe1, alloc1, state1) = bmc_pexpr state pe1 in
        (* Add new symbol to sym_table *)
        let pat_symbol = symbol_to_z3 state.ctx sym in
        let expr_pat = Expr.mk_const (state.ctx) pat_symbol z3_sort in
        state1.sym_table := Pmap.add sym expr_pat 
                                     (!(state1.sym_table));

        Solver.add (state1.solver) 
                            [ Boolean.mk_eq (state1.ctx) expr_pat z3_pe1 ];


        bmc_pexpr state1 pe2 
    | PElet (CaseBase(None, pat_ty), pe1, pe2) ->
        let (z3_pe1, state1) = bmc_pexpr state pe1 in
        bmc_pexpr state1 pe2
       
    | PElet (CaseCtor(ctor, patList), pe1, pe2) ->
        let (z3_pe1, state1) = bmc_pexpr state pe1 in

        let (eq_expr) = 
          mk_eq_pattern state1 (CaseCtor(ctor, patList)) 
                     z3_pe1 in

        Solver.add state1.solver [ eq_expr ];

        bmc_pexpr state1 pe2 
    *)
    | PElet (pat, pe1, pe2) ->
        let (z3_pe1, alloc1, state) = bmc_pexpr state pe1 in
        let eq_expr = mk_eq_pattern state pat z3_pe1 in
        Solver.add state.solver [ eq_expr ];

        alias_pattern state.alias_state pat alloc1;
        bmc_pexpr state pe2

    | PEif (pe1, pe2, pe3) ->
        let (z3_pe1, loc1, s1) = bmc_pexpr state pe1 in
        let (z3_pe2, loc2, s2) = bmc_pexpr ({state with vcs = []}) pe2 in
        let (z3_pe3, loc3, s3) = bmc_pexpr ({state with vcs = []}) pe3 in
        let new_vc = s1.vcs @ (concat_vcs state s2.vcs s3.vcs z3_pe1) in
        (mk_ite s3.ctx z3_pe1 z3_pe2 z3_pe3), 
          AddressSet.union loc2 loc3, 
          ({s1 with vcs = new_vc})
    | PEis_scalar _ ->
        assert false
    | PEis_integer _ ->
        assert false
    | PEis_signed _ ->
        assert false
    | PEis_unsigned _ ->
        assert false
        (*
    | PEstd (_, pe) ->
        bmc_pexpr state pe
        *)

let mk_bmc_address (addr : Address.addr) (sort: Sort.sort) =
  {addr = addr; 
   (* seq_ctr = ref 0; 
      hist = ref (Pmap.empty Pervasives.compare);
   *)
   sort = sort
  }

let rec mk_loaded_assertions ctx ty expr =
  match ty with
  | Basic0 (Integer ity) ->
      let (nmin, nmax) = integer_range impl ity in

      let lval = LoadedInteger.get_loaded_value ctx expr in
      let assertions =
        mk_and ctx 
        [ mk_ge ctx lval (Integer.mk_numeral_i ctx nmin)
        ; mk_le ctx lval (Integer.mk_numeral_i ctx nmax)
        ] in
      [mk_implies ctx
          (LoadedInteger.is_loaded ctx expr)
          assertions]
  | Basic0 _ -> assert false
  | Pointer0 _ -> 
      (* TODO: no assertions for pointer type right now... *)
      []
  | Atomic0 ctype ->
      (* TODO: not exactly correct *)
      mk_loaded_assertions ctx ctype expr
  | _ -> assert false


let rec ctype_to_sort (state: 'a bmc_state) ty =
  match ty with
  | Void0 -> assert false
  | Basic0 ty -> 
    begin
    match ty with
    (* TODO: Cases for types currently implemented for ivmin/ivmax.
     *       This is used only as a guard for unimplemented types.
     *)
    | Integer (Signed Int_)
    | Integer (Unsigned Int_) ->
        LoadedInteger.mk_sort state.ctx
    | Integer _ -> assert false
    | Floating fTy -> assert false
    end
  | Array0 _ -> assert false
  | Function0 _ -> assert false
  | Pointer0 _ -> 
      LoadedPointer.mk_sort state.ctx 
  | Atomic0 ctype -> 
      (* TODO: Not really correct. Ignoring Atomic part of type *)
      ctype_to_sort state ctype
  | Struct0 _ 
  | Union0 _
  | Builtin0 _ -> assert false

let ctype_is_atomic ty = 
  match ty with
  | Atomic0 _ -> true
  | _ -> false

let bmc_paction (state: 'a bmc_state)
                (Paction(pol, action) : 'a typed_paction) 
                : Expr.expr * AddressSet.t * 'a bmc_state =
  let Action(_, _, action_) = action in
  match action_ with
  | Create (pe1, Pexpr(_,BTy_ctype, PEval (Vctype ty)), _) ->
      let sort = ctype_to_sort state ty in

      (* Make a new memory allocation for alias analysis *)
      let new_addr = mk_new_addr state.alias_state in
      let typ = Pexpr([],BTy_ctype, PEval (Vctype ty)) in 

      alias_add_addr state.alias_state new_addr typ;
      let addr_ret = AddressSet.singleton new_addr in
      
      (* Create a new bmc address and add it to the addr_map *)
      let bmc_addr : kbmc_address = mk_bmc_address new_addr sort in
      state.addr_map :=  Pmap.add new_addr bmc_addr !(state.addr_map);
      state.alias_state.addr_set := AddressSet.add new_addr
                                   !(state.alias_state.addr_set);

      (*
      (* Set it to an initial unspecified value @a_1 *)
      let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_addr in
      (* TODO: make fresh? *)
      let initial_value = Expr.mk_const state.ctx new_sym sort in
      let new_heap = Pmap.add new_addr initial_value state.heap in
      *)

      (* Try: create a new pointer and return it instead *)
      let addr_expr = Address.mk_expr state.ctx new_addr in
      let new_ptr = PointerSort.mk_ptr state.ctx  addr_expr in

      let addr_is_atomic = Boolean.mk_val state.ctx (ctype_is_atomic ty) in

      Solver.add state.solver 
          [mk_eq state.ctx addr_is_atomic
                           (Address.is_atomic state.ctx addr_expr)];

      (* Switching to concurrency model: create an initial write action *)
      let to_store = Expr.mk_fresh_const state.ctx 
                      ("initial_" ^ (Address.to_string new_addr)) sort in
      let action = Write(mk_next_aid state, initial_tid, NA, new_ptr, to_store) in
      let paction = BmcAction(Pos, mk_not state.ctx state.has_returned, action) in
      state.action_map := Pmap.add (get_aid action) paction !(state.action_map);

      new_ptr, addr_ret, 
        {state with (* heap = new_heap; *)
                    preexec = add_initial_action (get_aid action) paction
                              state.preexec
        }

  | Create _ -> assert false
  | CreateReadOnly _ -> assert false
  | Alloc0 _ -> assert false
  | Kill pexpr ->
      let (_, allocs, state) = bmc_pexpr state pexpr in
      (*
      assert (AddressSet.cardinal allocs = 1);
      let elem = AddressSet.find_first (fun _ -> true) allocs in
      let new_heap = Pmap.remove elem state.heap in
      *)
      (* TODO: should really alter analysis_state too *)

      UnitSort.mk_unit state.ctx, 
          AddressSet.empty, state (* with heap = new_heap *)
  | Store0 (Pexpr(_,BTy_ctype, PEval (Vctype ty)), Pexpr(_,_, PEsym sym),
  p_value, mem_order) ->
      (* TODO: update comment
       * Overview:
         For each possible address, 
         if (get_addr sym == @a) @a_i = p_value; @a_i = (cur value)
         update heap: @a_i
       *)

      (* let sort = ctype_to_sort state ty in  *)
      let ptr_allocs = alias_lookup_sym sym state.alias_state in
      let (value, v_allocs, state) = bmc_pexpr state p_value in

      (* Not necessary, just for renaming purposes *)
      let to_store = Expr.mk_fresh_const state.ctx
                ("store_" ^ (symbol_to_string sym)) (Expr.get_sort value) in
      Solver.add state.solver [ mk_eq state.ctx value to_store ];

      let z3_sym = bmc_lookup_sym sym state in
      (*
      print_endline ("STORE " ^ (Expr.to_string z3_sym) ^ 
                     " " ^ (Expr.to_string to_store));
      *)

      let action = Write(mk_next_aid state, state.tid, mem_order,
                         z3_sym, to_store) in
      let paction = BmcAction(pol, mk_not state.ctx state.has_returned, action) in
      state.action_map := Pmap.add (get_aid action) paction !(state.action_map);

      print_endline (string_of_paction paction);


      (* If we are storing a C pointer, update points-to map *)
      begin
        if is_ptr_ctype (Pexpr([],BTy_ctype, PEval (Vctype ty))) then
          begin
          assert (not (AddressSet.is_empty ptr_allocs));
          assert (not (AddressSet.is_empty v_allocs));

          (* For each potential store location, add v_allocs to addr_map *)

          AddressSet.iter (fun loc ->
            print_string (Address.to_string loc);
            let prev_set = alias_lookup_alloc loc state.alias_state in
            alias_add_to_addr_map state.alias_state 
                  loc (AddressSet.union prev_set v_allocs)
          ) ptr_allocs
          end
      end;

      (* Now for each alloc in ptr_allocs, 
       * if (get_addr sym == @a) @a_i = p_value; @a_i = (cur_value)
       * update heap: @a_i
       *)

      (*
      print_endline "-----STORE ALIAS_RESULTS";
      print_ptr_map !(state.alias_state.ptr_map);
      print_addr_map !(state.alias_state.addr_map);

      print_heap state.heap; 
      print_endline ((string_of_address_set ptr_allocs) ^ " ZZZZ");
      *)

      (*
      let update = (fun alloc heap ->
          let bmc_addr = bmc_lookup_alloc alloc state in
          if (not (Sort.equal (bmc_addr.sort) sort)) then
            assert false (* or return heap *)
          else
            begin
              match Pmap.lookup alloc state.heap with
              | None -> (* addr was killed, not an option *)
                  heap
              | Some cur_value ->
              (* Create a fresh value *)
              let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_addr in
              let new_expr = Expr.mk_const state.ctx new_sym bmc_addr.sort in
              (* get_addr sym == @a *)
              let addr_eq = Boolean.mk_eq state.ctx 
                                (PointerSort.get_addr state.ctx z3_sym)
                                (Address.mk_expr state.ctx alloc) in
              (* @a_i = p_value *)
              let new_eq = Boolean.mk_eq state.ctx new_expr to_store in
              (* @a_i = (cur_value) *)
              let old_eq = Boolean.mk_eq state.ctx new_expr cur_value in
              
              let ite = Boolean.mk_ite state.ctx addr_eq new_eq old_eq in
              
              (* TODO: check if this should be guarded *)

              Solver.add state.solver [ ite ];

              Pmap.add alloc new_expr heap 
            end
        ) in
        let new_heap = AddressSet.fold update ptr_allocs state.heap in
        *)
        (UnitSort.mk_unit state.ctx), AddressSet.empty, 
            {state with (* heap = new_heap;  *)
                        preexec = add_action (get_aid action) paction 
                                  state.preexec   
            }
       
  | Store0 _ -> assert false
  | Load0 (Pexpr(_,BTy_ctype, PEval (Vctype ty)), Pexpr(_,_, PEsym sym),
           mem_order) -> 
      (* Overview: for each address, look up value in the heap.
       * Generate equation 
          (get_addr sym == addr => heap_value)
         TODO: assert that address is equal to something...
       * Return conjunction
       *)
       let sort = ctype_to_sort state ty in

       
       let z3_sym = bmc_lookup_sym sym state in
       let ret_value = Expr.mk_fresh_const state.ctx
              ("load_" ^ (symbol_to_string sym)) sort in
       assert (Sort.equal (Expr.get_sort z3_sym) 
                          (PointerSort.mk_sort state.ctx));

       (* If specified, assert it is in the range of ty*)
       (* TODO: check correctness ? *)
       Solver.add state.solver 
         (mk_loaded_assertions state.ctx ty ret_value);

      (*
       print_endline ("LOAD " ^ (Expr.to_string ret_value) ^
                      " " ^ polarity);
      *)

      let action = Read(mk_next_aid state, state.tid, mem_order,
                         z3_sym, ret_value) in
      let paction = BmcAction(pol, mk_not state.ctx state.has_returned, action) in
      state.action_map := Pmap.add (get_aid action) paction !(state.action_map);

      print_endline (string_of_paction paction);

       (* TODO: If unspecified, assert the type is ty.
        *       Not implemented (b/c recursive sorts for pointers 
        *       Also /hopefully/ not needed anywhere...??
        *)
       let ptr_allocs = alias_lookup_sym sym state.alias_state in
       (* Do alias analysis *)
       let ret_alloc = 
         begin
           if is_ptr_ctype (Pexpr([], BTy_ctype, PEval (Vctype ty))) then
             begin
               assert (not (AddressSet.is_empty ptr_allocs));

               (* Union all addr_map[loc] for loc in locs *)
               AddressSet.fold (fun loc ret ->
                 AddressSet.union (alias_lookup_alloc loc state.alias_state) ret)
                 ptr_allocs AddressSet.empty
              end
          else
            AddressSet.empty
         end in
       (*
      print_endline "-----LOAD ALIAS_RESULTS";
      print_ptr_map !(state.alias_state.ptr_map);
      print_addr_map !(state.alias_state.addr_map);

      print_heap state.heap; 
      print_endline ((string_of_address_set ptr_allocs) ^ " ZZZZ");
      *)
      (*
       let iterate = (fun alloc (expr_list, addr_list) ->
          match Pmap.lookup alloc state.heap with
          | None -> (expr_list, addr_list)
          | Some cur_value ->
          if (Sort.equal (Expr.get_sort cur_value) sort) then
            begin
              let addr_expr = Address.mk_expr state.ctx alloc in
              let addr_eq_expr = Boolean.mk_eq state.ctx
                  (PointerSort.get_addr state.ctx z3_sym)
                  addr_expr in
              let impl_expr = Boolean.mk_implies state.ctx
                  addr_eq_expr
                  (Boolean.mk_eq state.ctx ret_value cur_value) in
              (impl_expr :: expr_list, addr_eq_expr :: addr_list)
            end
          else
            assert false (* Return (expr_list, addr_list) *)
       ) in
       let (expr_eqs, addr_eqs) = AddressSet.fold iterate ptr_allocs ([], []) in

       let ret = Boolean.mk_and state.ctx expr_eqs in
       let new_vc = Boolean.mk_or state.ctx addr_eqs in
       (* TODO: CONCURRENCY *)
       print_endline "TODO: commmented out heap sequencing stuff";
       (* Solver.add state.solver [ ret ]; *)
       *)
       ret_value, ret_alloc, 
          ({state with (*vcs = (new_vc) :: state.vcs; *)
                       preexec = add_action (get_aid action) paction
                                 state.preexec}
          )
  | Load0 _
  | RMW0 _
  | Fence0 _ ->
      assert false


(* if guard then heap1 else heap2 for all addresses in alist *)
(* TODO: genrealize to n heaps with n guards *)
      (*
let merge_heaps (state: bmc_state) 
                (heap1: kheap) (heap2: kheap) 
                (guard1: Expr.expr) (guard2: Expr.expr) : kheap =
  Pmap.merge (
    fun k e1_ e2_ -> 
      let (e1, e2) = match (e1_, e2_) with
        | (Some x, Some y) -> (x, y)
        | _ -> (Printf.printf "TODO: Merge heaps properly\n"; assert false)
      in
      (* TODO: duplicated code *)
      let bmc_address = bmc_lookup_alloc k state in
      let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_address in
      (* TODO: sort should be in bmc_address *)
      assert (Sort.equal (Expr.get_sort e1) (Expr.get_sort e2));
      let sort = Expr.get_sort e1 in
      let new_expr = Expr.mk_const state.ctx new_sym sort in
      bmc_address.hist := Pmap.add seq_num new_expr (!(bmc_address.hist));
     
      (* Add equality *) 
      Solver.add state.solver 
        [ Boolean.mk_implies state.ctx guard1
            (Boolean.mk_eq state.ctx new_expr e1) ;
          Boolean.mk_implies state.ctx guard2 
            (Boolean.mk_eq state.ctx new_expr e2) 
        ];
      Some new_expr 
      ) heap1 heap2
*)
let rec bmc_expr (state: 'a bmc_state) 
                 (Expr(annot, expr_) : 'a typed_expr)
                 : Expr.expr * AddressSet.t * 'a bmc_state =
  match expr_ with
  | Epure pe ->
      bmc_pexpr state pe 
  | Ememop (PtrValidForDeref, _) ->
      print_endline "TODO: Ememop PtrValidForDeref: always true";
      mk_true state.ctx, AddressSet.empty, state
  | Ememop _ ->
      assert false
  | Eaction paction ->
      bmc_paction state paction
  | Ecase (pe, elist) ->  
      assert (List.length elist > 0);
      let (bmc_pe, pe_addr, st) = bmc_pexpr state pe in

      (* TODO: unnecessary now ? *)
      List.iter (fun (pat, _) ->
        alias_pattern state.alias_state pat pe_addr) elist;

      let pattern_guards = List.map
        (fun (pat, _) -> pattern_match st pat bmc_pe) elist in

      let complete_guard = mk_or st.ctx pattern_guards in
      Solver.add st.solver [ complete_guard ];

      let combined_pat_guards = 
        List.mapi (fun i expr ->
          mk_and st.ctx
          [ mk_not st.ctx (mk_or st.ctx (list_take i pattern_guards))
          ; expr
          ]
        ) pattern_guards in

      let expr_eqs = List.map (fun (pat, _) -> 
          mk_eq_pattern st pat bmc_pe) elist in
      let impl_eqs = List.map2 
        (fun guard eq -> mk_implies state.ctx guard eq)
        combined_pat_guards expr_eqs in
      Solver.add st.solver impl_eqs;

      let cases_z3 = List.map (fun (_, e) -> 
        bmc_expr ({st with vcs = []; 
                           preexec = initial_preexec ();
                           ret_asserts = []
                  }) e) elist in
      let cases_vcs = List.map (fun (_, _, s) -> 
          mk_and state.ctx s.vcs) cases_z3 in
      let new_vcs = st.vcs @ (List.map2 (fun guard vc -> 
          mk_implies state.ctx guard vc
        ) combined_pat_guards cases_vcs) in
      let new_ret_asserts = st.ret_asserts @ (List.map2 
        (fun guard (_, _, state) -> 
          mk_implies state.ctx guard (mk_and state.ctx state.ret_asserts)
        )
      ) combined_pat_guards cases_z3 in

      let new_has_returned = 
        mk_or st.ctx 
          (st.has_returned :: (List.map2 (fun guard (_, _, state) ->
              mk_and state.ctx [guard; state.has_returned])
              combined_pat_guards cases_z3)) in

      let alloc_ret = List.fold_left (fun s (_, set, _) ->
        AddressSet.union s set) AddressSet.empty cases_z3 in
      let guarded_preexecs = List.map2 (fun guard (_, _, state) ->
        guard_preexec state.ctx guard state.preexec 
      ) combined_pat_guards cases_z3 in
      let new_preexec = List.fold_left (fun p1 p2 ->
          merge_preexecs p1 p2
        ) st.preexec guarded_preexecs in

      let sort = Expr.get_sort (let (e, _, _) = List.hd cases_z3 in e ) in
      let ret = List.fold_right2 (fun guard (bmc_e, _, _) rest ->
        mk_ite st.ctx guard bmc_e rest
      ) pattern_guards cases_z3 (Expr.mk_fresh_const state.ctx "unmatchedCase"
      sort) in

      ret, alloc_ret, {st with vcs = new_vcs; 
                               preexec = new_preexec;
                               has_returned = new_has_returned;
                               ret_asserts = new_ret_asserts
                      }
  | Eskip -> 
      (* TODO: Unit *)
      (UnitSort.mk_unit state.ctx), AddressSet.empty, state 
  | Eproc _ -> assert false
  | Eccall (_, Pexpr(_, BTy_object (OTy_cfunction (retTy, numArgs, var)), 
                        PEsym sym), arglist)  -> 
      let sym_fn = (match Pmap.lookup sym !(state.fn_map) with
        | None -> assert false
        | Some x -> x) in
      begin
        match Pmap.lookup sym_fn state.file.funs with
        | Some (Proc(ty, params, e)) ->
            (* TODO: temporary *)
            assert (List.length params = 0);
            begin
            match bmc_normalize_fn (Proc(ty, params, e))
                  state.file !(state.sym_supply) with
            | Proc(ty2, params2, e2), supply ->
                state.sym_supply := supply;
                let sort = cbt_to_z3 state ty2 in
                let fresh_state = {state with
                    vcs = [];
                    preexec = initial_preexec ();
                    has_returned = mk_false state.ctx;
                    z3_ret = Expr.mk_fresh_const state.ctx  
                                ("ret_" ^ (symbol_to_string sym_fn)) sort;
                    ret_asserts = [];
                    saves = find_save_expr e 
                  } in


                let (bmc_call, alloc, ret_state) = 
                  bmc_expr fresh_state e2 in

                Solver.add state.solver ret_state.ret_asserts;
                print_endline "INCOMPLETE";
                (ret_state.z3_ret, alloc, state)
                
            | _ -> assert false

            end
        | _ -> assert false
      end
  | Eccall _ -> 
      assert false
  | Eunseq elist -> 
      (* return tuple of bmc values 
       * union allocs
       * merge_preexecs just by union
       * concatenate vcs
       *
       * Assumes cbt is BTy_tuple
       * Similar to ctor
       *)
      let bmc_list = List.map (fun e ->
        bmc_expr {state with vcs = []; 
                             preexec = initial_preexec ();
                             ret_asserts = []
                 } e
      ) elist in
      let expr_list = List.map (fun (expr, _, _) -> expr) bmc_list in

      let sort_list = List.map Expr.get_sort expr_list in

      let sort = z3_sortlist_to_tuple state.ctx sort_list in

      let ret = ctor_to_z3 state Ctuple expr_list sort  in
      let allocs = List.fold_left (fun set (_, alloc, _) ->
        AddressSet.union set alloc) AddressSet.empty bmc_list in
      let new_vcs = List.fold_left (fun vc (_, _, st) ->
        st.vcs @ vc 
      ) state.vcs bmc_list in
      let new_preexec = List.fold_left (fun exec (_, _, st) ->
        merge_preexecs exec st.preexec 
      ) state.preexec bmc_list in
      let new_has_returned = mk_or state.ctx (state.has_returned:: (List.map 
        (fun (_, _, st) -> st.has_returned) bmc_list)) in
      let new_ret_asserts = List.fold_left (fun l (_, _, st) ->
        st.ret_asserts @ l) state.ret_asserts bmc_list in

      ret, allocs, {state with vcs = new_vcs; 
                               preexec = new_preexec;
                               has_returned = new_has_returned;
                               ret_asserts = new_ret_asserts
                   }
  | Eindet _ -> assert false
  | Ebound (_, e1) ->
      bmc_expr state e1 
  | End [e1; e2] ->
      (* nondet sequencing: special case len(elist)=2 for now 
       * Guard vcs and heap assignments by choice points
       *
       * TODO: generalize to any elist 
       * (just have to write heap merging function really)
       *)
      let (bmc_e1, alloc1, st1) = 
        bmc_expr {state with vcs = []; 
                             preexec = initial_preexec ();
                             ret_asserts = []
                 } e1 in
      let (bmc_e2, alloc2, st2) = 
        bmc_expr {state with vcs = []; 
                             preexec = initial_preexec ();
                             ret_asserts = []
                 } e2 in

      let bmc_seq1 = Expr.mk_fresh_const state.ctx "seq" 
                      (Boolean.mk_sort state.ctx) in
      let bmc_seq2 = Expr.mk_fresh_const state.ctx "seq" 
                      (Boolean.mk_sort state.ctx) in
      let seq_xor = mk_xor state.ctx bmc_seq1 bmc_seq2  in
      Solver.add state.solver [ seq_xor ];

      let vc1 = mk_implies state.ctx bmc_seq1
                    (mk_and state.ctx st1.vcs)  in
      let vc2 = mk_implies state.ctx bmc_seq2
                    (mk_and state.ctx st2.vcs) in
      let new_vcs = vc1 :: vc2 :: state.vcs in
      (*
      let new_heap = merge_heaps state st1.heap st2.heap
                      bmc_seq1 bmc_seq2 in
      *)

      (* preexecs *)
      let preexec1 = guard_preexec state.ctx bmc_seq1 st1.preexec in
      let preexec2 = guard_preexec state.ctx bmc_seq2 st2.preexec in
      let new_preexec = merge_preexecs preexec1 preexec2 in

      let new_has_returned = mk_or state.ctx
        [ state.has_returned 
        ; mk_implies state.ctx bmc_seq1 st1.has_returned
        ; mk_implies state.ctx bmc_seq2 st2.has_returned 
        ] in
  
      let new_ret_asserts =
           (mk_implies state.ctx bmc_seq1 
                                 (mk_and state.ctx st1.ret_asserts))
        :: (mk_implies state.ctx bmc_seq2
                                 (mk_and state.ctx st2.ret_asserts))
        :: state.ret_asserts in 

      (UnitSort.mk_unit state.ctx, 
       AddressSet.union alloc1 alloc2,
       {state with vcs = new_vcs;  (* heap = new_heap; *)
                   preexec = new_preexec;
                   has_returned = new_has_returned;
                   ret_asserts = new_ret_asserts
       }
      )

  | End _ -> assert false
  | Erun (_, Symbol(i, Some s), pelist) ->
      print_endline "TODO: Erun, special casing ret";
      begin
      match Str.split (Str.regexp "_") s with
      | [name; id] ->
          if (name = "ret") && (int_of_string id = i) then
            begin
              let sym = Sym.Symbol(i, Some s) in
              let (cbt, symlist, expr) = 
                (match Pmap.lookup sym state.saves with
                 | None -> assert false
                 | Some x -> x) in
              assert (List.length symlist = List.length pelist);
              let subMap = List.fold_left2 (fun map sym pe ->
                Pmap.add sym pe map) (Pmap.empty sym_cmp) symlist pelist in
              let to_run = substitute_expr subMap expr in 

              let (ret, aset, state) = bmc_expr state to_run in
              (*
              pp_to_stdout (Pp_core.Basic.pp_expr to_run);
              print_endline "  Erun expr";
              *)
              let eq_expr = mk_implies state.ctx
                (mk_not state.ctx state.has_returned)
                (mk_eq state.ctx state.z3_ret ret) in

            (UnitSort.mk_unit state.ctx), aset, 
            { state with has_returned = mk_true state.ctx;
                         ret_asserts = eq_expr :: state.ret_asserts
            }
            end
          else
            assert false
      | _ -> assert false
      end

  | Erun _ ->
      assert false
  | Epar elist -> 
      (* TODO: Duplicated code from Eunseq *)
      (* Assume can not return in Epar? *)
      let bmc_list = List.map (fun expr ->
          bmc_expr {state with vcs = []; 
                               preexec = initial_preexec ();
                               tid = mk_next_tid state
                   } expr
        ) elist in
      let expr_list = List.map (fun (expr, _, _) -> expr) bmc_list in
      let sort_list = List.map Expr.get_sort expr_list in
      let sort = z3_sortlist_to_tuple state.ctx sort_list in
      let ret = ctor_to_z3 state Ctuple expr_list sort  in
      let allocs = List.fold_left (fun set (_, alloc, _) ->
        AddressSet.union set alloc) AddressSet.empty bmc_list in
      let new_vcs = List.fold_left (fun vc (_, _, st) ->
        st.vcs @ vc 
      ) state.vcs bmc_list in
      let new_preexec = List.fold_left (fun exec (_, _, st) ->
        merge_preexecs exec st.preexec 
      ) state.preexec bmc_list in

      List.iter (fun (_, _, st) ->
        state.parent_tid := 
            Pset.add (st.tid, state.tid) !(state.parent_tid)
      ) bmc_list;

      let new_has_returned = mk_or state.ctx (state.has_returned ::(
        List.map (fun (_, _, st) -> st.has_returned) bmc_list
      )) in 
      let new_ret_asserts = List.fold_left (fun l (_, _, st) ->
        st.ret_asserts @ l) state.ret_asserts bmc_list in

      ret, allocs, {state with vcs = new_vcs; 
                               preexec = new_preexec;
                               has_returned = new_has_returned;
                               ret_asserts = new_ret_asserts
                   }
  | Ewait _ -> assert false
  | Eif (pe, e1, e2) -> 
      let (bmc_pe, loc, st) = bmc_pexpr state pe in
      let (bmc_e1, loc1, st1) = bmc_expr 
          ({st with vcs = []; 
                    preexec = initial_preexec ();
                    ret_asserts = []
           }) e1 in
      let (bmc_e2, loc2, st2) = bmc_expr 
          ({st with vcs = [];   
                    preexec = initial_preexec ();
                    ret_asserts = []
           }) e2 in

      
      let new_vc = st.vcs @ (concat_vcs state st1.vcs st2.vcs bmc_pe) in
      (*
      let new_heap = merge_heaps st st1.heap st2.heap 
                     bmc_pe (Boolean.mk_not st.ctx bmc_pe) in
      *)

      let preexec1 = guard_preexec st.ctx bmc_pe st1.preexec in
      let preexec2 = guard_preexec st.ctx (mk_not st.ctx bmc_pe) st2.preexec in
      let new_preexec = merge_preexecs (st.preexec) 
          (merge_preexecs preexec1 preexec2) in

      let new_has_returned = mk_or st.ctx 
          [ st.has_returned
          ; mk_and st.ctx [bmc_pe ; st1.has_returned]
          ; mk_and st.ctx [(mk_not st.ctx bmc_pe); st2.has_returned]] in

      let new_ret_asserts = 
        (mk_implies st.ctx bmc_pe (mk_and st.ctx st1.ret_asserts))
        :: (mk_implies st.ctx (mk_not st.ctx bmc_pe) 
                              (mk_and st.ctx st2.ret_asserts))
        :: st.ret_asserts in

      (mk_ite state.ctx bmc_pe bmc_e1 bmc_e2),
        AddressSet.union loc1 loc2,
        {st with (* heap = new_heap; *) vcs = new_vc; 
                                        preexec = new_preexec;
                                        has_returned = new_has_returned;
                                        ret_asserts = new_ret_asserts
        }
        
  | Elet _ -> assert false
  | Easeq _ ->
      assert false
  | Ewseq (pat, e1, e2) ->
      let old_preexec = state.preexec in 
      let (ret_e1, loc1, state) = 
        bmc_expr {state with preexec = initial_preexec () } e1 in
      alias_pattern state.alias_state pat loc1;
      let eq_expr = mk_eq_pattern state pat ret_e1 in
      Solver.add state.solver [ eq_expr ];

      let (ret_e2, loc2, state2) = 
        bmc_expr {state with preexec = initial_preexec ()} e2 in

      let (exec1, exec2) = (state.preexec, state2.preexec) in

      (* Sequence all actions in state before those in state2*) 
      let new_preexec =  merge_preexecs old_preexec 
                                (merge_preexecs state.preexec state2.preexec) in
      let new_preexec = 
        {new_preexec with 
          sb = Pset.union (new_preexec.sb) 
                          (pos_cartesian_product exec1.actions
                                                 exec2.actions);
          asw = Pset.union (new_preexec.asw)
                           (asw_product exec1.actions exec2.actions
                                        !(state.parent_tid)
                           );
          hb = Pset.union (new_preexec.hb)
                          (hb_cartesian_product exec1.actions
                                                exec2.actions
                                                true
                          )
        } in 

      (ret_e2, loc2, {state2 with preexec = new_preexec})


  | Esseq (pat, e1, e2) ->
      (* TODO: mostly duplicated code from Ewseq *)
      let old_preexec = state.preexec in 
      let (ret_e1, loc1, state) = 
        bmc_expr {state with preexec = initial_preexec () } e1 in
      alias_pattern state.alias_state pat loc1;
      let eq_expr = mk_eq_pattern state pat ret_e1 in
      Solver.add state.solver [ eq_expr ];

      let (ret_e2, loc2, state2) = 
        bmc_expr {state with preexec = initial_preexec ()} e2 in

      let (exec1, exec2) = (state.preexec, state2.preexec) in

      (* Sequence all actions in state before those in state2*) 
      let new_preexec =  merge_preexecs old_preexec 
                                (merge_preexecs state.preexec state2.preexec) in
      let new_preexec = 
        {new_preexec with 
          sb = Pset.union (new_preexec.sb) 
                          (cartesian_product exec1.actions
                                             exec2.actions);
          asw = Pset.union (new_preexec.asw)
                           (asw_product exec1.actions exec2.actions
                                        !(state.parent_tid)
                           );
          hb = Pset.union (new_preexec.hb)
                          (hb_cartesian_product exec1.actions
                                                exec2.actions
                                                false
                          )


        } in
      (ret_e2, loc2, {state2 with preexec = new_preexec})


  | Esave ((Symbol (i, Some s), _), binding_list, _)  ->
      (* Special case ret *)
      (* TODO: code duplication from Erun *)
      begin
      match Str.split (Str.regexp "_") s with
      | [name; id] -> 
          if (name = "ret") && ((int_of_string id) = i) then
            begin
              let sym = Sym.Symbol(i, Some s) in
              let (cbt, symlist, expr) = 
                (match Pmap.lookup sym state.saves with
                 | None -> assert false
                 |Some x -> x) in
              assert (List.length symlist = List.length binding_list);
              let pelist = List.map (fun(_, (_, pe)) -> pe) binding_list in
              let subMap = List.fold_left2 (fun map sym pe ->
                Pmap.add sym pe map) (Pmap.empty sym_cmp) symlist pelist in
              let to_run = substitute_expr subMap expr in
              let (ret, aset, state) = bmc_expr state to_run in
              let eq_expr = mk_implies state.ctx
                (mk_not state.ctx state.has_returned)
                (mk_eq state.ctx state.z3_ret ret) in

              UnitSort.mk_unit state.ctx, AddressSet.empty, 
                { state with has_returned = mk_true state.ctx;
                             ret_asserts = eq_expr :: state.ret_asserts }
            end
          else 
            assert false
      | _ -> assert false
      end
  | Esave _ ->
      assert false

(*
(* TODO: only handles one function *)
let bmc_fun_map (state: bmc_state)
                (funs: ('a, 'b typed_fun_map_decl) Pmap.map) =
  Pmap.map (function
    | Fun (ty, params, pe) ->
        (* TODO: return vcs *)
        let (_, state1) = bmc_pexpr state pe in
        let not_vcs = List.map (fun a -> (Boolean.mk_not state1.ctx a))
                               state1.vcs 
        in
        Solver.add state1.solver [ Boolean.mk_or state1.ctx not_vcs ]
    | ProcDecl (ty, params) ->
        assert false
    | Proc (ty, params, e) ->        
        let (_, state1) = bmc_expr state e in
        Printf.printf "-----CONSTRAINTS ONLY\n";
        nheck_solver state1.solver;
        Printf.printf "-----WITH VCS \n";
        let not_vcs = List.map (fun a -> (Boolean.mk_not state1.ctx a))
                               state1.vcs
        in
        Solver.add state1.solver [ Boolean.mk_or state1.ctx not_vcs ] 
  ) funs
*)

(* NOTE: special-cased for main b/c types of pointers are unknown otherwise 
 * TODO: currently broken for args
 * *)
let initialise_param ((sym, ty): (ksym * core_base_type)) state sort =
  add_sym_to_sym_table state sym ty;
  match Pmap.lookup sym !(state.alias_state.ptr_map) with
  | Some s -> assert false (* Symbol should not exist yet *)
  | None ->
      assert (is_ptr_type ty);
      let new_addr = mk_new_addr state.alias_state in
      state.alias_state.addr_set := AddressSet.add new_addr
                          !(state.alias_state.addr_set);
      add_set state.alias_state sym (AddressSet.singleton new_addr);

      (* Create a new bmc address and add it to addr_map 
       * The sort needs to be unspecified.
       *)
      let bmc_addr =  mk_bmc_address new_addr sort in
      state.addr_map := Pmap.add new_addr bmc_addr !(state.addr_map);

      (*
      (* Set it to an initial unspecified value @a_1 *)
      let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_addr in
      let initial_value = Expr.mk_const state.ctx new_sym sort in
      let new_heap = Pmap.add new_addr initial_value state.heap in
      *)

      let ptr = bmc_lookup_sym sym state in 
      (* Concurrency model stuff: add initial write *)
      let to_store = Expr.mk_fresh_const state.ctx 
                      ("initial_" ^ (Address.to_string new_addr)) sort in
      let action = Write(mk_next_aid state, initial_tid, NA, ptr, to_store) in
      let paction = BmcAction(Pos, mk_true state.ctx, action) in
      state.action_map := Pmap.add (get_aid action) paction !(state.action_map);

      let addr_expr = Address.mk_expr state.ctx new_addr in
      let addr_is_atomic = Boolean.mk_val state.ctx (false) in

      Solver.add state.solver 
          [mk_eq state.ctx addr_is_atomic
                           (Address.is_atomic state.ctx addr_expr)];

      (* Assert address of symbol is new_addr *)
      Solver.add state.solver [ 
        mk_eq  state.ctx
          (PointerSort.get_addr state.ctx ptr)
          (addr_expr)
      ];


      {state with (* heap = new_heap; *)
                  preexec = add_initial_action (get_aid action) 
                            paction state.preexec}

let initialise_main_params params state =
  match params with
  | [] -> state
  | [p1; p2] ->
      let state = initialise_param p1 state (LoadedInteger.mk_sort state.ctx) in
      initialise_param p2 state (LoadedPointer.mk_sort state.ctx)
  | _ -> assert false

let initialise_global state sym typ expr : 'a bmc_state =
  assert (is_ptr_type typ);
  (* TODO: duplicated from Esseq *)
  let (ret, loc, state) = bmc_expr state expr in 
  let pat = CaseBase(Some sym, typ) in
  alias_pattern state.alias_state pat loc;
  let eq_expr = mk_eq_pattern state pat ret in
  Solver.add state.solver [ eq_expr ];
  state

(* TODO: make event a datatype 
 * TODO: do this in a nicer way so it's actually readable...
 * e.g. generically 
 *)
let preexec_to_z3 (state: 'a bmc_state) =
  let ctx = state.ctx in
  let preexec = state.preexec in 
  (* TODO: rewrite all this stuff... *)
  (* Make initial events *)
  let initial_event_list = set_to_list preexec.initial_actions in
  let preexec_list = set_to_list preexec.actions in
  let event_list = initial_event_list @ preexec_list in

  let action_id_to_z3_sym aid = mk_sym ctx ("#E_" ^ (string_of_int aid)) in
  let action_to_z3_sym action = action_id_to_z3_sym (aid_of_paction action) in
  let event_syms = List.map action_to_z3_sym event_list in
  let event_sort = Enumeration.mk_sort ctx 
                      (mk_sym ctx "Event") event_syms in
  (* map from aid -> z3 expr *)
  let events = Enumeration.get_consts event_sort in
  let event_map = List.fold_left2 (fun pmap action expr ->
    Pmap.add (aid_of_paction action) expr pmap)
    (Pmap.empty Pervasives.compare) event_list events in

  let mk_event_expr : action_id -> Expr.expr = (fun aid ->
    match Pmap.lookup aid event_map with | Some x -> x | None -> assert false) in
  let event_expr : bmc_paction -> Expr.expr = (fun action ->
    mk_event_expr (aid_of_paction action)) in

  let bound_0 = Quantifier.mk_bound ctx 0 event_sort in
  let bound_1 = Quantifier.mk_bound ctx 1 event_sort in
  let bound_2 = Quantifier.mk_bound ctx 2 event_sort in

  (* ====================================== *)
  (* ========== Type decls ================ *)
  (* ====================================== *)

  (* Read/write type *)
  let event_type = Enumeration.mk_sort ctx (mk_sym ctx "Event_type")
                   [ mk_sym ctx "Read"
                   ; mk_sym ctx "Write" ] in


  (* ====================================== *)
  (* ========== Event accessor decls ====== *)
  (* ====================================== *)
  (* Get the load/store value associated with the event *)
  let fn_getVal = FuncDecl.mk_fresh_func_decl ctx 
                    "getVal" [ event_sort ] (Loaded.mk_sort ctx) in
  (* Address of the event *)
  let fn_getAddr = FuncDecl.mk_fresh_func_decl ctx 
                    "getAddr" [ event_sort ] (Address.mk_sort ctx) in
  let getAddr expr = FuncDecl.apply fn_getAddr [ expr ] in
  (* Guard for the event to actually occur in control flow *)
  let fn_getGuard = FuncDecl.mk_fresh_func_decl ctx
                      "getGuard" [ event_sort ] (Boolean.mk_sort ctx) in
  let getGuard expr = FuncDecl.apply fn_getGuard [ expr ] in
  (* Thread id of the event; initial events have different id *)
  let fn_getThread = FuncDecl.mk_fresh_func_decl ctx
                      "getThread" [ event_sort ] (Integer.mk_sort ctx) in
  let getThread expr = FuncDecl.apply fn_getThread [ expr ] in
  (* Type is read or write *)
  let fn_getEventType = FuncDecl.mk_fresh_func_decl ctx
                    "getEventType" [ event_sort ] event_type in
  let read_type = Enumeration.get_const event_type 0 in
  let write_type = Enumeration.get_const event_type 1 in 
  let is_read expr = mk_eq ctx 
                          (FuncDecl.apply fn_getEventType [expr])
                          read_type in
  let is_write expr = mk_eq ctx 
                          (FuncDecl.apply fn_getEventType [expr])
                          write_type in
  (* Memory order type *)
  let memorder_type = Enumeration.mk_sort ctx (mk_sym ctx "Memorder_type")
                      [ mk_sym ctx "NA"
                      ; mk_sym ctx "Seq_cst"
                      ; mk_sym ctx "Relaxed"
                      ; mk_sym ctx "Release"
                      ; mk_sym ctx "Acquire"
                      ; mk_sym ctx "Consume"
                      ; mk_sym ctx "Acq_rel"
                      ] in
  let fn_getMemorder = FuncDecl.mk_fresh_func_decl ctx
                       "getMemorder" [ event_sort ] memorder_type in
  let na_order = Enumeration.get_const memorder_type 0 in
  let seq_cst_order = Enumeration.get_const memorder_type 1 in 
  let relaxed_order = Enumeration.get_const memorder_type 2 in 
  let release_order = Enumeration.get_const memorder_type 3 in 
  let acquire_order = Enumeration.get_const memorder_type 4 in 
  let consume_order = Enumeration.get_const memorder_type 5 in 
  let acq_rel_order = Enumeration.get_const memorder_type 6 in 
  let is_memorder memorder expr = mk_eq ctx 
            (FuncDecl.apply fn_getMemorder [expr])
            memorder in


  (* ====================================== *)
  (* ========== Rel decls ================= *)
  (* ====================================== *)
  (* SB relation, already computed; po | (I x not I )
   *)
  let fn_sb = FuncDecl.mk_fresh_func_decl ctx 
                "sb" [ event_sort; event_sort ] (Boolean.mk_sort ctx) in
  (* ASW: additional synchronizes with; thread creates/joins *)
  let fn_asw = FuncDecl.mk_fresh_func_decl ctx
                  "asw" [event_sort; event_sort ] (Boolean.mk_sort ctx) in
  (* HB: happens-before; (sb | sw)+ *)
  let fn_hb = FuncDecl.mk_fresh_func_decl ctx
                "hb" [event_sort; event_sort] (Boolean.mk_sort ctx) in

  (* events that behave like acquire: ACQ or AR or (SC and R) *)
  let fn_isAcq = FuncDecl.mk_fresh_func_decl ctx
                   "isAcq" [event_sort] (Boolean.mk_sort ctx) in
  
  (* Events that behave like release:  REL or AR or (SC and W) *)
  let fn_isRel = FuncDecl.mk_fresh_func_decl ctx
                   "isRel" [event_sort] (Boolean.mk_sort ctx) in
  (* Reads from map *)
  let fn_rf = FuncDecl.mk_fresh_func_decl ctx
                "rf" [ event_sort ] event_sort in
  let app_rf expr = FuncDecl.apply fn_rf [expr] in
  (* Modification order *)
  let fn_mo = FuncDecl.mk_fresh_func_decl ctx
                "mo" [ event_sort ] (Integer.mk_sort ctx) in
  (* From-read *)
  (*
  let fn_fr = FuncDecl.mk_fresh_func_decl ctx
                "fr" [ event_sort; event_sort ] (Boolean.mk_sort ctx) in
  *)
  (* cc-clock: clock; used to be for coherence check. Now to track hb  *)
  let fn_clock = FuncDecl.mk_fresh_func_decl ctx
                "cc-clock" [ event_sort ] (Integer.mk_sort ctx) in
  (* synchronizes with; asw or[rel] ; [A && W] ; rf; [R && A]; [acq] 
   *)
  let fn_sw = FuncDecl.mk_fresh_func_decl ctx
                "sw" [event_sort; event_sort] (Boolean.mk_sort ctx) in

  (* getInitial(e1) = initial event of location of e1 *)
  let fn_getInitial = FuncDecl.mk_fresh_func_decl ctx
                        "getInitial" [ Address.mk_sort ctx ] event_sort in
  let getInitial expr = FuncDecl.apply fn_getInitial [ expr ] in

  (* ============ Function definitions ============ *)
  (* Map each location to the initial event of the location *)
  let getInitial_asserts = List.map (fun ie ->
      mk_eq ctx (getInitial (PointerSort.get_addr ctx (location_of_paction ie))) 
                (event_expr ie)
    ) initial_event_list in

  (* Declare value funcion. 
   * Assert (symbolic) value of stores and loads
   *)
  let val_asserts = List.map (fun action -> 
    let loaded_value = Loaded.mk_loaded ctx (value_of_paction action) in
    mk_eq ctx (FuncDecl.apply fn_getVal [event_expr action]) 
                      (loaded_value)) event_list in

  (* Declare address function.
   * Assert (symbolic) addresses of stores and loads 
   *)
  let addr_asserts = List.map (fun action -> 
    let addr = PointerSort.get_addr ctx (location_of_paction action) in
    mk_eq ctx (getAddr (event_expr action))
                      addr) event_list in
  let guard_asserts = List.map (fun action ->
    mk_eq ctx (getGuard (event_expr action)) 
              (guard_of_paction action)) event_list in

  let thread_asserts = List.map (fun action ->
    mk_eq ctx (getThread (event_expr action)) 
              (Integer.mk_numeral_i ctx (thread_of_paction action))) event_list in

  (* SB relation *)
  let sb_eqs = Pset.fold (fun (a1, a2) ret ->
    let (a1_expr, a2_expr) = (mk_event_expr a1, mk_event_expr a2) in
    let expr = mk_and ctx [ mk_eq ctx bound_0 a1_expr
                          ; mk_eq ctx bound_1 a2_expr] in
    expr :: ret) preexec.sb [] in
  let init_notInit e1 e2 = 
    mk_and ctx [ mk_eq ctx (getThread e1) 
                           (Integer.mk_numeral_i ctx initial_tid)
               ; mk_not ctx (mk_eq ctx (getThread e2) 
                                       (Integer.mk_numeral_i ctx initial_tid ))
               ] in
  let sb_assert = Quantifier.expr_of_quantifier (
      Quantifier.mk_forall ctx
        [event_sort; event_sort] [mk_sym ctx "e1"; mk_sym ctx "e2"]
        (mk_eq ctx (FuncDecl.apply fn_sb [bound_0; bound_1])
                   (mk_or ctx (sb_eqs @ [init_notInit bound_0 bound_1]))
        ) None [] [] None None
    ) in

  (* additional synchronizes-with *)
  let asw_eqs = Pset.fold (fun (a1, a2) ret ->
    let (a1_expr, a2_expr) = (mk_event_expr a1, mk_event_expr a2) in
    let expr = mk_and ctx [ mk_eq ctx bound_0 a1_expr
                          ; mk_eq ctx bound_1 a2_expr] in
    expr :: ret) preexec.asw [] in
  let asw_assert = Quantifier.expr_of_quantifier (
        Quantifier.mk_forall ctx
        [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
        (mk_eq ctx (FuncDecl.apply fn_asw [bound_0; bound_1])
                   (mk_or ctx asw_eqs))
        None [] [] None None) in
  (* TODO: very slow
   * Happens-before: (sb | sw)+
   *)
  let hb_exists = Quantifier.expr_of_quantifier (
    Quantifier.mk_exists ctx
      [event_sort] [mk_sym ctx "e3"]
      (mk_and ctx [ mk_or ctx [ FuncDecl.apply fn_sb [bound_1; bound_0]
                              ; FuncDecl.apply fn_sw [bound_1; bound_0]
                              ]
                  ; FuncDecl.apply fn_hb [bound_0; bound_2]
                  ]
      ) None [] [] None None
    ) in
  let hb_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_eq ctx (FuncDecl.apply fn_hb [bound_0; bound_1])
                 (mk_or ctx [ FuncDecl.apply fn_sb [bound_0; bound_1]
                            ; FuncDecl.apply fn_sw [bound_0; bound_1]
                            ; hb_exists
                            ]
                 )
      ) None [] [] None None
    ) in
  (*
  (* TODO: computed hb = (sb | (I x not I) | sw)+
   *)
  let hb_eqs = Pset.fold (fun (a1, a2) ret ->
    let (a1_expr, a2_expr) = (mk_event_expr a1, mk_event_expr a2) in
    let expr = mk_and ctx [ mk_eq ctx bound_0 a1_expr
                          ; mk_eq ctx bound_1 a2_expr] in
    expr :: ret) preexec.hb [] in
  let hb_assert = Quantifier.expr_of_quantifier (
     Quantifier.mk_forall ctx
        [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
        (mk_eq ctx (FuncDecl.apply fn_hb [bound_0; bound_1])
                   (mk_or ctx (hb_eqs @ [init_notInit bound_0 bound_1]))
        ) None [] [] None None) in
  *)

  (* read/write? *)
  let type_asserts = List.map (fun (BmcAction(_, _, action))->
    let expr = mk_event_expr (get_aid action) in
    match action with
    | Read  _ -> is_read expr
    | Write _ -> is_write expr
    ) event_list in

  (* Memorder ? *)
  let memorder_asserts = List.map (fun paction ->
    let expr = event_expr paction in
    let memorder = 
      match memorder_of_paction paction with
      | Cmm_csem.NA  -> na_order 
      | Cmm_csem.Seq_cst -> seq_cst_order 
      | Cmm_csem.Relaxed -> relaxed_order
      | Cmm_csem.Release -> release_order
      | Cmm_csem.Acquire -> acquire_order
      | Cmm_csem.Consume -> consume_order
      | Cmm_csem.Acq_rel -> acq_rel_order in
    is_memorder memorder expr
    ) event_list in

  let isAcq_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort] [mk_sym ctx "e"]
      (mk_eq ctx (FuncDecl.apply fn_isAcq [bound_0])
                 (mk_or ctx [ is_memorder acquire_order bound_0
                            ; is_memorder acq_rel_order bound_0
                            ; mk_and ctx [ is_memorder seq_cst_order bound_0
                                         ; is_read bound_0
                                         ]
                            ]
                 )                
      ) None [] [] None None
  ) in
  let isRel_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort] [mk_sym ctx "e"]
      (mk_eq ctx (FuncDecl.apply fn_isRel [bound_0])
                 (mk_or ctx [ is_memorder release_order bound_0
                            ; is_memorder acq_rel_order bound_0
                            ; mk_and ctx [ is_memorder seq_cst_order bound_0
                                         ; is_write bound_0
                                         ]
                            ]
                 )                
      ) None [] [] None None
  ) in

  let sw_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_eq ctx (FuncDecl.apply fn_sw [bound_0; bound_1])
                 (mk_or ctx [ FuncDecl.apply fn_asw [bound_0; bound_1]
                            ; mk_and ctx [ FuncDecl.apply fn_isRel [bound_0]
                                         ; FuncDecl.apply fn_isAcq [bound_1]
                                         ; is_write bound_0
                                         ; is_read bound_1
                                         ; mk_eq ctx bound_0 (app_rf bound_1)
                                         ; mk_eq ctx (getAddr bound_0) 
                                                     (getAddr bound_1)
                                         ; Address.is_atomic ctx (getAddr bound_0)
                                         ] 
                            ]
                 )
      ) None [] [] None None
  ) in

  (* rf => guard (can only read from event that actually happens *)

  (* Reads read-from writes
   * (forall ((e E)) (=> (read e) (write (rf e))))
   *)
  let rf_write_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort] [mk_sym ctx "e"]
      (mk_implies ctx 
          (mk_and ctx [is_read bound_0; getGuard bound_0])
          (is_write (FuncDecl.apply fn_rf [bound_0]))
      ) None [] [] None None
    ) in

  (* for each read, it has the value of the event it reads from
   * and is from the same address (below missing address) 
   * and (rf e) guard is true
   * (forall ((e E)) (=> (read e)  (= (val e) (val (rf e))))) 
   *)
  let rf_well_formed_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx [event_sort] [mk_sym ctx "e"]
      (mk_implies ctx
        (mk_and ctx [is_read bound_0; getGuard bound_0]) 
        (mk_and ctx 
          [ mk_eq ctx (FuncDecl.apply fn_getAddr [bound_0]) 
                      (FuncDecl.apply fn_getAddr 
                        [ FuncDecl.apply fn_rf [bound_0] ])
          ; mk_eq ctx (FuncDecl.apply fn_getVal [bound_0])
                      (FuncDecl.apply fn_getVal
                        [ FuncDecl.apply fn_rf [bound_0]])
          ; getGuard (FuncDecl.apply fn_rf [bound_0])
          ]
        )
      ) None [] [] None None 
    ) in
  (* rf_vse_assert 
   *
   * forall e1, e2: is_write e2 and distinct (e2, rf(e1)) and 
   *                same location (e1, e2) and
   *                non-atomic-location e1
   *            =>  not (rf(e1) hb e2 and e2 hb b)
   *                && rf(e1) hb e2
   *)
  let rf_vse_subexpr = 
      mk_not ctx (mk_and ctx [FuncDecl.apply fn_hb [(app_rf bound_0); 
                                                    bound_1]
                             ;FuncDecl.apply fn_hb [bound_1; bound_0]]) in
  let rf_vse_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx 
      [event_sort; event_sort] [mk_sym ctx "e1"; mk_sym ctx "e2"]
      (mk_implies ctx
        (mk_and ctx [ getGuard bound_0
                    ; getGuard bound_1
                    ; is_read bound_0
                    ; is_write bound_1
                    ; mk_not ctx (mk_eq ctx (app_rf bound_0) bound_1)
                    ; mk_eq ctx (getAddr bound_0)
                                (getAddr bound_1)  
                    ; mk_not ctx (Address.is_atomic ctx (getAddr bound_0))
                    ]) 
        (mk_and ctx [ rf_vse_subexpr
                    ; FuncDecl.apply fn_hb [(app_rf bound_0); bound_0]]
        )
      ) None [] [] None None 
    ) in

  (* co well-formedness: 
   * each write is co-after the initial write (of 0?)
   * (Below is for single address)
   * (assert (forall ((e E)) (=> (and (write e) (not (= e ix))) (< (co ix) (co e)))))
  *)
  let mo_well_formed_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx [event_sort] [mk_sym ctx "e"]
    (mk_implies ctx 
      (mk_and ctx 
        [ is_write bound_0
        ; getGuard bound_0
        ; mk_not ctx (mk_eq ctx bound_0 (getInitial (getAddr bound_0)))
        ])
      (mk_lt ctx (FuncDecl.apply fn_mo [ getInitial (getAddr bound_0) ])
                 (FuncDecl.apply fn_mo [ bound_0 ]) 
      )
    ) None [] [] None None
  ) in
  (* assert mo of an initial event is 0 for convenience *)
  let mo_initial_asserts = List.map (fun ie ->
    mk_eq ctx (FuncDecl.apply fn_mo [event_expr ie])
              (Integer.mk_numeral_i ctx 0)) initial_event_list in

  (* any nonequal writes to the same address e1 and e2 are strictly mo-related one way or the other
   *(below is for single address )
   * Also: relates only events in atomic locations
    (forall 
       ((e1 E) (e2 E))  
       (=> (and (write e1) (write e2) (not (= e1 e2))) 
           (or (< (co e1) (co e2)) (< (co e2) (co e1)))
       )
   *)
  let mo_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx 
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_implies ctx 
        (mk_and ctx [ is_write bound_0
                    ; is_write bound_1
                    ; getGuard bound_0
                    ; getGuard bound_1
                    ; mk_not ctx (mk_eq ctx bound_0 bound_1)
                    ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                    ; Address.is_atomic ctx (getAddr bound_0)
                    ]
        )
        (mk_or ctx [ mk_lt ctx (FuncDecl.apply fn_mo [bound_0])
                               (FuncDecl.apply fn_mo [bound_1])
                   ; mk_lt ctx (FuncDecl.apply fn_mo [bound_1])
                               (FuncDecl.apply fn_mo [bound_0])
                   ]
        )
      ) None [] [] None None
  ) in
  let clock_initial_asserts = List.map (fun ie ->
    mk_eq ctx (FuncDecl.apply fn_clock [event_expr ie])
              (Integer.mk_numeral_i ctx 0)) initial_event_list in


  (* hb included in cc-clock
    (assert (forall ((e1 E) (e2 E)) (=> (po e1 e2) (< (cc-clock e1) (cc-clock e2)))))
  *)
  let hb_clock_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1" ]
      (mk_implies ctx
        (mk_and ctx [ FuncDecl.apply fn_hb [bound_0; bound_1]
                    ; getGuard bound_0
                    ; getGuard bound_1
                    ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                    ]
        )
        (mk_lt ctx (FuncDecl.apply fn_clock [bound_0])
                   (FuncDecl.apply fn_clock [bound_1])
        )
      ) None [] [] None None
  ) in

  (* rf included in cc-clock
  (assert (forall ((e E)) (=> (read e) (< (cc-clock (rf e)) (cc-clock e)))))
  *)
  (*
  let rf_clock_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort] [mk_sym ctx "e"]
      (mk_implies ctx
        (mk_and ctx [is_read bound_0; getGuard bound_0])
        (mk_lt ctx (FuncDecl.apply fn_clock [FuncDecl.apply fn_rf [ bound_0 ]])
                   (FuncDecl.apply fn_clock [bound_0])
        )
      ) None [] [] None None
  ) in
  *)

  (* fr definition: (below for single address)
    (assert (forall ((e1 E) (e2 E))  (=> (and (read e1) (write e2)) (= (fr e1 e2) (< (co (rf e1)) (co e2))))))
  *)
  (*
  let fr_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1" ]
      (mk_implies ctx
          (mk_and ctx [ is_read bound_0
                      ; is_write bound_1
                      ; getGuard bound_0
                      ; getGuard bound_1
                      ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                      ]
          )
          (mk_eq ctx (FuncDecl.apply fn_fr [bound_0; bound_1])
            (mk_lt ctx 
              (FuncDecl.apply fn_mo [ FuncDecl.apply fn_rf [bound_0]] )
              (FuncDecl.apply fn_mo [ bound_1 ])
            ) 
          )
      ) None [] [] None None
  ) in
  *)
  (*
  (* fr included in cc-clock
    (assert (forall ((e1 E) (e2 E)) (=> (and (read e1) (write e2) (fr e1 e2)) (< (cc-clock e1) (cc-clock e2)))))
  *)
  let fr_clock_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1" ]
      (mk_implies ctx
          (mk_and ctx [ is_read bound_0
                      ; is_write bound_1
                      ; getGuard bound_0
                      ; getGuard bound_1
                      ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                      ; FuncDecl.apply fn_fr [bound_0; bound_1]
                      ]
          )
          (mk_lt ctx (FuncDecl.apply fn_clock [bound_0])
                     (FuncDecl.apply fn_clock [bound_1])
          )
      ) None [] [] None None
  ) in
  *)

  (* co included in cc-clock
    (assert (! (forall ((e1 E) (e2 E)) (=> (and (write e1) (write e2) (< (co e1) (co e2))) (< (cc-clock e1) (cc-clock e2)))) :named co-included))
  *)
  (*
  let mo_included_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1" ]
      (mk_implies ctx
          (mk_and ctx [ is_write bound_0
                      ; is_write bound_1
                      ; getGuard bound_0
                      ; getGuard bound_1
                      ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                      ; mk_lt ctx (FuncDecl.apply fn_mo [bound_0])
                                  (FuncDecl.apply fn_mo [bound_1])
                      ]
          )
          (mk_lt ctx (FuncDecl.apply fn_clock [bound_0])
                     (FuncDecl.apply fn_clock [bound_1])
          )
      ) None [] [] None None
  ) in
  *)

  (* CoRR assert: Two reads ordered by hb may not read two writes that are mo in
   * the other direction 
   * forall e1, e2: isRead(e1) && isRead(e2) && hb(e1, e2) => not <mo (rf(e2), rf(e1))
   *)
  let coRR_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_implies ctx
        (mk_and ctx [ is_read bound_0
                    ; is_read bound_1
                    ; getGuard bound_0
                    ; getGuard bound_1
                    ; FuncDecl.apply fn_hb [bound_0; bound_1]
                    ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                    ]
        )
        (mk_not ctx (mk_lt ctx
                        (FuncDecl.apply fn_mo [app_rf bound_1])
                        (FuncDecl.apply fn_mo [app_rf bound_0]) 
                    )
        )
      ) None [] [] None None
  ) in

  (* CoWR assert: Forbidden to read from write that is hb-hidden by a later
   * write in modification order (in same address)
   * forall e1 e2. is_write e1 and is_read e2 and hb(e1,e2) => not <mo (rf(e2)) e1 
   *)
  let coWR_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_implies ctx
        (mk_and ctx [ is_write bound_0
                    ; is_read bound_1
                    ; getGuard bound_0
                    ; getGuard bound_1
                    ; FuncDecl.apply fn_hb [bound_0; bound_1]
                    ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                    ]
        )
        (mk_not ctx (mk_lt ctx
                        (FuncDecl.apply fn_mo [app_rf bound_1])
                        (FuncDecl.apply fn_mo [bound_0])
                    )
        )
      ) None [] [] None None
  ) in

  (* HB and MO must not disagree *)
  let coWW_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_implies ctx
        (mk_and ctx [ is_write bound_0
                    ; is_write bound_1
                    ; getGuard bound_0
                    ; getGuard bound_1
                    ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                    ; mk_lt ctx (FuncDecl.apply fn_mo [bound_0])
                                (FuncDecl.apply fn_mo [bound_1])
                    ]
        )
        (mk_not ctx (FuncDecl.apply fn_hb [bound_1; bound_0])
        )
      ) None [] [] None None
  ) in
  (* Union of RF map, HB, and MO must be acyclic *)
  let coRW_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_implies ctx
        (mk_and ctx [ is_read bound_0
                    ; is_write bound_1
                    ; getGuard bound_0
                    ; getGuard bound_1
                    ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                    ; FuncDecl.apply fn_hb [bound_0; bound_1]
                    ]
        )
        (mk_not ctx (mk_lt ctx (FuncDecl.apply fn_mo [bound_1])
                               (FuncDecl.apply fn_mo [app_rf bound_0])
                    )
        )
      ) None [] [] None None
  ) in

  (* asw included in cc-clock
   * TODO: ???
   *)
  (*
  let asw_clock_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_implies ctx
        (mk_and ctx [ getGuard bound_0
                    ; getGuard bound_1
                    ; FuncDecl.apply fn_asw [bound_0; bound_1]
                    ]
        )
        (mk_lt ctx (FuncDecl.apply fn_clock [bound_0])
                   (FuncDecl.apply fn_clock [bound_1])
        )
      ) None [] [] None None
  ) in
  *)

  (* Unseq race:
   * forall (e1, e2): 
   * (distinct and same location and one is write and same
   * thread and guard => must be sb *)
  let unseq_race_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx 
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_implies ctx
          (mk_and ctx [ mk_not ctx (mk_eq ctx bound_0 bound_1)
                      ; mk_eq ctx (getAddr bound_0)  (getAddr bound_1)
                      ; mk_or ctx [is_write bound_0; is_write bound_1]
                      ; mk_eq ctx (getThread bound_0) (getThread bound_1)
                      ; getGuard bound_0
                      ; getGuard bound_1 
                      ]
          )
          (mk_or ctx [ FuncDecl.apply fn_sb [bound_0; bound_1]
                     ; FuncDecl.apply fn_sb [bound_1; bound_0]
                     ]
          )
      ) None [] [] None None
  ) in

  (* Data race:
    * forall (e1, e2)
    * (distinct and same location and one is write and not same thread and both
    * are non-atomic =>
    * must be related by happens before
   *)
  let data_race_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort; event_sort] [mk_sym ctx "e2"; mk_sym ctx "e1"]
      (mk_implies ctx
        (mk_and ctx [ mk_not ctx (mk_eq ctx bound_0 bound_1)
                    ; mk_eq ctx (getAddr bound_0) (getAddr bound_1)
                    ; mk_or ctx [is_write bound_0; is_write bound_1]
                    ; mk_not ctx (mk_eq ctx (getThread bound_0) 
                                            (getThread bound_1))
                    ; getGuard bound_0
                    ; getGuard bound_1
                    ; mk_or ctx [ is_memorder na_order bound_0
                                ; is_memorder na_order bound_1
                                ]
                    ]
        )
        (mk_or ctx [ FuncDecl.apply fn_hb [bound_0; bound_1] 
                   ; FuncDecl.apply fn_hb [bound_1; bound_0]
                   ]
        )
      ) None [] [] None None
  ) in

  let irr_hb_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort] [mk_sym ctx "e"]
      (mk_not ctx (FuncDecl.apply fn_hb [bound_0; bound_0]))
      None [] [] None None
  ) in

  let irr_rf_assert = Quantifier.expr_of_quantifier (
    Quantifier.mk_forall ctx
      [event_sort] [mk_sym ctx "e"]
      (mk_implies ctx 
          (mk_and ctx [is_read bound_0; getGuard bound_0])
          (mk_not ctx (FuncDecl.apply fn_hb [bound_0; app_rf bound_0]))
      )
      None [] [] None None
  ) in

  let ret =   val_asserts 
            @ addr_asserts 
            @ guard_asserts
            @ type_asserts 
            @ memorder_asserts
            @ thread_asserts
            @ getInitial_asserts
            @ mo_initial_asserts
            @ clock_initial_asserts
            @ [ sb_assert  
              ; asw_assert 
              ; sw_assert
              ; isAcq_assert
              ; isRel_assert
              (*; fr_assert *)
              ; rf_write_assert 
              ; rf_well_formed_assert 
              ; mo_well_formed_assert
              ; irr_hb_assert
              ; irr_rf_assert
              ; rf_vse_assert (* NaRF *)
              ; coRR_assert  
              ; coWR_assert
              ; coWW_assert
              ; coRW_assert  
              (* coherence check for CoRW and COWW (acyclic rf, hb, mo 
               * TODO: check correctness. maybe better to isolate..
               *)
              ; mo_assert 
              ; hb_clock_assert 
              (* ; rf_clock_assert *)
              (*; fr_clock_assert *)
              (* ; mo_included_assert *)
              (* ; asw_clock_assert  *)
              ; unseq_race_assert 
              (* Comment out hb_assert and data_race_assert if too slow *)
              ; hb_assert 
              ; data_race_assert 
              ] in
  List.iter (fun s -> print_endline (Expr.to_string s)) ret;

  let func_decl_list = [ fn_getAddr
                       ; fn_getInitial
                       ; fn_getVal
                       ; fn_getGuard
                       ; fn_getThread
                       ; fn_sb
                       ; fn_rf
                       (* ; fn_fr *)
                       ; fn_mo
                       ; fn_clock
                       ] in

  ret, func_decl_list


let bmc_file (file: 'a typed_file) (supply: ksym_supply) =
  (* Do globals *)
  let initial_state = initial_bmc_state supply file in
  let state = List.fold_left (fun st (sym, typ, e) ->
    initialise_global st sym typ e) initial_state file.globs in 


  match file.main with
  | None -> failwith "ERROR: file does not have a main"
  | Some main_sym ->
      let (_, _, state1) = (
        match Pmap.lookup main_sym file.funs with
        | Some (Proc(ty, params, e)) ->
            (* Assert return type is an integer st return sort is consistant *)
            assert (ty = BTy_loaded OTy_integer);
            (* Handle parameters *)
            let state = initialise_main_params params state in
            let esaves = find_save_expr e in

            bmc_expr {state with saves = esaves} e
        | Some (Fun(ty, params, pe)) ->
            (* Handle parameters *)
            let state = initialise_main_params params state in
            bmc_pexpr state pe 
        | _ -> assert false
      ) in

      (* TODO: do properly. Need to make ASW relation correct *)
      let state1 = {state1 with preexec = 
        {state1.preexec with asw = 
          filter_asw state1.preexec.asw
                     !(state1.parent_tid)
                     state1.preexec.sb
                     !(state1.action_map)
      }} in
      (*
      print_endline "-----RET_ASSERTS2";
      List.iter (fun expr ->
        print_endline (Expr.to_string (Expr.simplify expr None));
      ) state1.ret_asserts;
      *)
      Solver.add state1.solver (List.map (fun e -> Expr.simplify e None) state1.ret_asserts);


      print_endline "-----ALIAS_RESULTS";
      print_ptr_map !(state1.alias_state.ptr_map);
      print_addr_map !(state1.alias_state.addr_map);

      print_endline "-----EVENTS";
      print_preexec state1.preexec;

      print_endline "-----EVENT STUFF";
      let (z3_preexec, funcdecl_list) = 
        (if Pset.is_empty state1.preexec.actions then 
            [], [] (* Guard st sort is well-founded *)
          else
            preexec_to_z3 state1
        ) in


      print_endline "-----CONSTRAINTS ONLY";
      assert (Solver.check state1.solver [] = SATISFIABLE);

      print_endline "-----WITH EVENTS";
      Solver.add state1.solver z3_preexec; 

      if (check_solver_fun state1.solver funcdecl_list (Some state1.z3_ret)
            = SATISFIABLE) then
        begin
          print_endline "-----WITH VCS";
          let not_vcs = List.map (fun a -> (mk_not state1.ctx a))
                                 state1.vcs
          in
          (* List.iter (fun e -> print_endline (Expr.to_string e)) not_vcs; *)
          Solver.add state1.solver [ mk_or state1.ctx not_vcs ] ;

          Printf.printf "\n-- Solver:\n%s\n" (Solver.to_string (state1.solver));
          print_endline "Checking sat";
          let _ = check_solver (state1.solver) in
          ()
        end
      else
        (* No valid execution *)
        (
          print_endline "-----NOT ALL EXECUTIONS ARE VALID IN MEMORY MODEL";
          print_endline "-----RESULT=SAT :("
        )

let (>>=) = Exception.except_bind

let run_bmc (core_file : 'a file) 
            (sym_supply: ksym_supply)    = 
  (* TODO: state monad with sym_supply *)
  print_endline "ENTER: BMC PIPELINE";
  pp_file core_file;

  print_endline "ENTER: NORMALIZING FILE";
  let (norm_file, norm_supply) = bmc_normalize_file core_file sym_supply in

  print_endline "EXIT: NORMALIZING FILE";

  (* pp_file norm_file; *)

  print_endline "Typechecking file";
  Core_typing.typecheck_program norm_file >>= fun typed_core ->
    Exception.except_return (

      (* Do not sequentialise file *)
      (* let seq_file = Core_sequentialise.sequentialise_file typed_core in
      pp_file seq_file; 
      *)

      pp_file typed_core;
      print_endline "START Z3";
      (* bmc_file seq_file norm_supply; *)
      bmc_file typed_core norm_supply;

      print_string "EXIT: BMC PIPELINE \n"
    )
