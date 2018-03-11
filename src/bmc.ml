(*
 * TODO: Give an overview of the relevant modules
 *)

open Core
open Core_ctype
open Global_ocaml
open Lem_pervasives
open Mem
open Ocaml_implementation
open Ocaml_mem
open Pp_core
open Z3
open Z3.Arithmetic

open Bmc_analysis
open Bmc_inline
open Bmc_normalize
open Bmc_sorts
open Bmc_utils

(* ========== Type definitions ========== *)

type ksym_table = (ksym, Expr.expr) Pmap.map

(* (The below is old and no longer used )
 *
 * Pointer state: 
 * For every variable of Core type pointer, 
 *    - Map it to set of addresses it refers to
 *    - int (core symbol) -> PointerState = Set of addresses
 *
 * An address consists of a unique allocation
 *    - fun: is_eq (check if same address)
 *    - map from int to symbol?
 *    - type ? 
 *
 * For let x: pointer = Create...
 *    - Create a new address
 *    - Don't insert into bmc_state?
 *    - Add it to pointer state
 *    - "x: SMT ptr sort" = address
 *
 * For let y: pointer = x
 *    - pointer state
 *    - "y : SMT ptr sort" = x (address)
 *
 * For store:
 *    - create fresh var for the address and assign it to a value
 *
 * For load:
 *    - lookup address variable points to, assign it current value in z3
 *
 * bmc_state:
 *    - map from address -> cur_value (int?)
 *    - pointer state: symbol -> PointerState map
 *)


(* "Symbol: @int_int" *)
type kbmc_address = {
  addr        : Address.addr;
  seq_ctr     : int ref;
  hist        : ((int, Expr.expr) Pmap.map) ref;
  sort        : Sort.sort
}

type kheap = (Address.addr, Expr.expr) Pmap.map

type bmc_state = {
  ctx         : context;
  solver      : Solver.solver;
  sym_table   : ksym_table ref;
  sym_supply  : ksym_supply ref;

  (*
  (* Make fresh allocations using Address.mk_fresh *)
  addr_gen    : Address.addr ref;
  *)

  (* Map from int -> address *)
  addr_map    : (Address.addr, kbmc_address) Pmap.map ref;

  (* ------------- *)
  (* Stuff from alias analysis *)
  alias_state : kanalysis_state;


  (* ------------- *)
  
  (* Map from address to Z3 symbol representing value *)
  heap        : (Address.addr, Expr.expr) Pmap.map;

  (* TODO: rethink what's a VC and what's a constraint *)
  vcs         : Expr.expr list;
}


(* PPrinters *)

(*
let print_ptr_map (map : (int, Address.addr list) Pmap.map) =
  Pmap.mapi (fun k v-> (Printf.printf "%d -> " k;
            List.iter(fun s -> Printf.printf "%s " (Address.to_string s)) v)) map
*)

let print_heap (heap: (Address.addr, Expr.expr) Pmap.map) =
  Printf.printf "HEAP\n";
  Pmap.iter (fun k v-> (Printf.printf "E: %s -> %s\n" 
                  (Address.to_string k) (Expr.to_string v))) heap ;
  Printf.printf "END_HEAP\n"


(* ========== BMC ========== *)

let check_solver (solver: Solver.solver) =
  begin
  let status = Solver.check solver [] in
  Printf.printf "Status: %s\n" (Solver.string_of_status status);
  begin
  if status = UNKNOWN then
    Printf.printf "Unknown: %s\n" (Solver.get_reason_unknown solver)
  end;
  if status != SATISFIABLE then
    Printf.printf "NOT SAT :) \n"
  else
    begin 
    Printf.printf "SAT :( \n";
    let model = Solver.get_model solver in
      match model with
      | Some m -> Printf.printf "Model: \n%s\n" (Model.to_string m)
      | None -> Printf.printf "No model\n"
    ;
    end
  end

let get_last_seqnum (ctx: context) (bmc_address : kbmc_address) =
  (!(bmc_address.seq_ctr))

let mk_next_seq_symbol (ctx: context) (bmc_address : kbmc_address) =
  bmc_address.seq_ctr := succ (!(bmc_address.seq_ctr));
  (mk_sym ctx ("@" ^ (Address.to_string (bmc_address.addr)) ^ "_" ^ 
              (string_of_int (!(bmc_address.seq_ctr)))),
   get_last_seqnum(ctx) (bmc_address))


let ctor_to_z3 (state: bmc_state) (ctor: typed_ctor) 
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


(* core_base_type to z3 sort *)
let rec cbt_to_z3 (state: bmc_state) (cbt : core_base_type) : Sort.sort =
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

let add_sym_to_sym_table (state: bmc_state) (sym: ksym) (ty: core_base_type) =
  let z3_sort = cbt_to_z3 state ty in
  let z3_sym = Expr.mk_const state.ctx (symbol_to_z3 state.ctx sym) z3_sort in
  state.sym_table := Pmap.add sym z3_sym !(state.sym_table)

let bmc_lookup_sym (sym: ksym) (state: bmc_state) : Expr.expr =
  match Pmap.lookup sym !(state.sym_table) with
  | None -> assert false
  | Some x -> x

let bmc_lookup_alloc alloc (state: bmc_state) : kbmc_address =
  match Pmap.lookup alloc !(state.addr_map) with
  | None -> assert false
  | Some addr -> addr

let bmc_lookup_addr_in_heap alloc heap =
  match Pmap.lookup alloc heap with
  | None -> assert false
  | Some x -> x


let initial_bmc_state (supply : ksym_supply) 
                      : bmc_state = 
  let cfg = [("model", "true"); ("proof", "false")] in

  let ctx = mk_context cfg in
  {
    ctx = ctx;
    solver = Solver.mk_solver ctx None;
    sym_table = ref (Pmap.empty sym_cmp);
    sym_supply = ref supply;

    (* addr_gen = ref (Address.mk_initial); *)
    addr_map = ref (Pmap.empty Pervasives.compare);

    heap = Pmap.empty Pervasives.compare;

    alias_state = initial_analysis_state ();

    vcs = []
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
  | OVpointer _
  | OVcfunction _
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
  | Vtrue -> Boolean.mk_true ctx
  | Vfalse -> Boolean.mk_false ctx
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
  | OpEq -> Boolean.mk_eq ctx pe1 pe2   
  | OpLt -> Arithmetic.mk_lt ctx pe1 pe2
  | OpLe -> Arithmetic.mk_le ctx pe1 pe2 
  | OpGt -> Arithmetic.mk_gt ctx pe1 pe2
  | OpGe -> Arithmetic.mk_ge ctx pe1 pe2
  | OpAnd -> Boolean.mk_and ctx [ pe1; pe2 ] 
  | OpOr -> Boolean.mk_or ctx [ pe1; pe2 ]


(* TODO: add symbol to sym table somewhere else!!! 
 * Also just completely rewrite this function... 
 * *)
let mk_eq_expr (state: bmc_state) (m_sym: ksym option) 
               (ty : core_base_type) (expr: Expr.expr) =
  match m_sym with
  | None -> Boolean.mk_true state.ctx (* Do nothing *)
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
          (Boolean.mk_eq state.ctx expr_pat expr)
          (*
          begin
          match bmc_expr with
          | Some expr ->
              (Boolean.mk_eq state.ctx expr_pat expr)
          | _ -> assert false
          end
          *)
      | BTy_tuple ty_list -> 
          assert false
          (*
          (* TODO: duplicate *)
          begin
          match bmc_expr with
          | Some expr ->
              let sort = cbt_to_z3 state ty in
              let expr_pat = Expr.mk_const state.ctx pat_sym sort in
              state.sym_table := Pmap.add sym_id expr_pat (!(state.sym_table));
              (Boolean.mk_eq state.ctx expr_pat expr)
          | _ -> assert false
          end
          *)
      | BTy_list _ -> assert false
      | BTy_object OTy_pointer -> 
          (* Pointer equality *)
            (*
          match bmc_expr with
          | Some expr ->
              *)
              assert (Sort.equal (Expr.get_sort expr) 
                                 (PointerSort.mk_sort state.ctx));
              (*
              let addr_list = 
                match Pmap.lookup ptr_id state.ptr_map with
                | Some z -> z
                | None -> assert false
              in
              *)
              (* Create a new symbol for the pattern pointer *)
              let pat_sym = symbol_to_z3 state.ctx sym in
              let expr_pat = 
                  Expr.mk_const state.ctx pat_sym (PointerSort.mk_sort state.ctx)
              in
              (* Add to sym table *)
              state.sym_table := Pmap.add sym expr_pat (!(state.sym_table));

              (* Assert that get_addr expr_pat == get_addr expr *)
              Boolean.mk_eq state.ctx 
                (PointerSort.get_addr state.ctx expr_pat)
                (PointerSort.get_addr state.ctx expr)   
          (*
          | _ -> assert false
          end
          *)
      | BTy_object _ -> 
          (* TODO: duplicated *)
              let sort = cbt_to_z3 state ty in
              let expr_pat = Expr.mk_const state.ctx pat_sym sort in
              state.sym_table := Pmap.add sym expr_pat (!(state.sym_table));
              (Boolean.mk_eq state.ctx expr_pat expr)
      | BTy_loaded cot ->
          (* TODO duplicated code: should case on bmc_expr instead maybe *)
          let pat_symbol = symbol_to_z3 state.ctx sym in
          let z3_sort = cbt_to_z3 state ty in
          let expr_pat = Expr.mk_const state.ctx pat_symbol z3_sort in
          state.sym_table := Pmap.add sym expr_pat 
                                      (!(state.sym_table));
          Boolean.mk_eq state.ctx expr_pat expr;
          (*
          begin
          match bmc_expr with
          | None -> Boolean.mk_true state.ctx
          | Some expr ->
              begin
              (Boolean.mk_eq state.ctx expr_pat expr)
              end
          end
          *)
        end

let rec pattern_match (state: bmc_state) (pattern: typed_pattern)
                      (expr: Expr.expr) =
  (* let expr = (match bmc_expr with | Some expr -> expr | None -> assert false)
   * in *)
  match pattern with
  | CaseBase(maybe_sym, typ) ->
      Boolean.mk_true state.ctx
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      let exprList = Expr.get_args expr in
      let patConditions = List.mapi 
          (fun i pat -> pattern_match state pat ((List.nth exprList i )))
          patlist in
      Boolean.mk_and state.ctx patConditions
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

let rec mk_eq_pattern (state: bmc_state) (pattern: typed_pattern)
                      (expr: Expr.expr) =
  match pattern with
  | CaseBase(maybe_sym, typ) ->
      mk_eq_expr state maybe_sym typ expr 
  | CaseCtor(Ctuple, patlist) -> 
      (* TODO: make ty_list *)
      let exprList = Expr.get_args expr in
      assert (Expr.get_num_args expr = List.length patlist);
      let zipped = List.combine exprList patlist in
      Boolean.mk_and state.ctx 
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
            Boolean.mk_and state.ctx [is_loaded; eq_expr]
        | ([(CaseBase(maybe_sym, BTy_object OTy_pointer))])-> 
            (* TODO: duplicated code *)
            let is_loaded = LoadedPointer.is_loaded state.ctx expr in
            let loaded_value = LoadedPointer.get_loaded_value state.ctx expr
            in
            let (eq_expr) = mk_eq_expr state maybe_sym
                                 (BTy_object OTy_pointer) 
                                 (loaded_value) in
            Boolean.mk_and state.ctx [is_loaded; eq_expr]
        | _ -> assert false
    end
  | CaseCtor(Cunspecified, [CaseBase(maybe_sym, _)]) ->
      (* TODO: terrible... *)
      if (Sort.equal (Expr.get_sort expr) 
                     (LoadedInteger.mk_sort state.ctx)) then
        let is_unspec = LoadedInteger.is_unspec state.ctx expr in
        let unspec_value = LoadedInteger.get_unspec_value state.ctx expr in
        let eq_expr = mk_eq_expr state maybe_sym BTy_ctype (unspec_value) in
        Boolean.mk_and state.ctx [is_unspec; eq_expr]
      else if (Sort.equal (Expr.get_sort expr) 
                          (LoadedPointer.mk_sort state.ctx)) then
        let is_unspec = LoadedPointer.is_unspec state.ctx expr in
        let unspec_value = LoadedPointer.get_unspec_value state.ctx expr in
        let eq_expr = mk_eq_expr state maybe_sym BTy_ctype (unspec_value) in
        Boolean.mk_and state.ctx [is_unspec; eq_expr]
      else
        assert false
  | _ -> assert false

(* TODO: mk_and for vcs for readability *)
let concat_vcs (state: bmc_state)
               (vc1: Expr.expr list)
               (vc2: Expr.expr list)
               (guard: Expr.expr) =
  let new_vc1 = List.map (fun vc -> Boolean.mk_implies state.ctx guard vc) vc1 in
  let new_vc2 = List.map (fun vc -> Boolean.mk_implies state.ctx 
                                        (Boolean.mk_not state.ctx guard) vc) vc2 in
  new_vc1 @ new_vc2


let rec bmc_pexpr (state: bmc_state) 
                  (Pexpr(bTy, pe) : typed_pexpr) : 
                    Expr.expr * AddressSet.t * bmc_state =
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
        let new_vcs = (Boolean.mk_false state.ctx) :: state.vcs in
        let new_state = {state with vcs = new_vcs} in
        Expr.mk_fresh_const state.ctx "undef" sort, AddressSet.empty, new_state 
    | PEerror _ -> 
        let sort = cbt_to_z3 state bTy in
        let new_vcs = (Boolean.mk_false state.ctx) :: state.vcs in
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
        let (pe_z3, pe_set, st1) = bmc_pexpr state pe in
        List.iter (fun (pat1, _) -> 
          alias_pattern state.alias_state pat1 pe_set) caselist;

        begin
            let pattern_guards = 
              List.map (fun (pat, _) -> pattern_match st1 pat pe_z3) caselist in 
            let complete_guard = Boolean.mk_or st1.ctx pattern_guards in
            Solver.add st1.solver [ complete_guard ];

            let combined_pat_guards = 
              List.mapi (fun i expr -> 
                Boolean.mk_and st1.ctx 
                [ Boolean.mk_not st1.ctx (Boolean.mk_or st1.ctx (list_take i pattern_guards))
                ; expr 
                ]
                ) pattern_guards in

            let expr_eqs = List.map (fun (pat, _) -> 
              mk_eq_pattern st1 pat pe_z3) caselist in

            (* Match case i => expr_eq i holds *)
            let impl_eqs = List.map2 
              (fun guard eq -> Boolean.mk_implies state.ctx guard eq) 
              combined_pat_guards expr_eqs in
            Solver.add st1.solver impl_eqs;

            (* Now need to combine verification conditions: 
             * st1.vcs @... guarded by case match *)
            let cases_z3 = List.map 
                (fun (_, e) -> bmc_pexpr ({st1 with vcs = []}) e) caselist in
            let cases_vcs = (List.map (fun (_,_,s) -> Boolean.mk_and state.ctx s.vcs) cases_z3) in
            let new_vcs = 
              (st1.vcs @ (List.map2 (fun guard vc -> Boolean.mk_implies state.ctx guard vc)
              combined_pat_guards cases_vcs)) in
            (* TODO: correctness? *)
            let ret_state = {st1 with vcs = new_vcs} in

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
                  Boolean.mk_ite state.ctx guard e prev
                ) last (List.tl rev_filtered) in

                ite, alloc_ret, ret_state
            end
        end
    | PEarray_shift _ -> assert false
    | PEmember_shift _ -> assert false
    | PEnot pe1 -> 
        let (z3_pe1, allocs, state) = bmc_pexpr state pe1 in  
          (Boolean.mk_not state.ctx z3_pe1), allocs, state
    | PEop (bop, pe1, pe2) ->
        let (z3_pe1, alloc1, state1) = bmc_pexpr state pe1 in
        let (z3_pe2, alloc2, state2) = bmc_pexpr state1 pe2 in
        binop_to_constraints state2.ctx z3_pe1 z3_pe2 bop, 
            AddressSet.union alloc1 alloc2, 
            state2
    | PEstruct _
    | PEunion _ -> assert false
    | PEcall(Sym sym, _) ->
        Printf.printf "TODO: inline function calls\n";
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
        begin
          (*
          match (maybe_pe1, maybe_pe2, maybe_pe3) with
          | (None, _, _)  (* fall through *)
          | (Some _, None, None) ->
              (* Extra vcs for debugging *)
              None, ({s1 with vcs = (Boolean.mk_false s3.ctx) :: s1.vcs}) 
          | (Some a, Some b, None) ->
              let vc_guard = a in
              let new_vc = s1.vcs @ s2.vcs in
              Some b, ({s1 with vcs = (vc_guard :: new_vc)})
          | (Some a, None, Some b) ->
              let vc_guard = Boolean.mk_not s3.ctx a in
              let new_vc = s1.vcs @ s3.vcs in
              Some b, ({s1 with vcs = (vc_guard :: new_vc)})
          | (Some a, Some b, Some c) ->
          *)
              let new_vc = s1.vcs @ (concat_vcs state s2.vcs s3.vcs z3_pe1) in
              (Boolean.mk_ite s3.ctx z3_pe1 z3_pe2 z3_pe3), 
                AddressSet.union loc2 loc3, 
                ({s1 with vcs = new_vc})
        end
    | PEis_scalar _ ->
        assert false
    | PEis_integer _ ->
        assert false
    | PEis_signed _ ->
        assert false
    | PEis_unsigned _ ->
        assert false
    | PEstd (_, pe) ->
        bmc_pexpr state pe

let mk_bmc_address (addr : Address.addr) (sort: Sort.sort) =
  {addr = addr; 
   seq_ctr = ref 0; 
   hist = ref (Pmap.empty Pervasives.compare);
   sort = sort
  }

let ctype_to_sort (state: bmc_state) ty =
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
  | Atomic0 _ -> assert false 
  | Struct0 _ 
  | Union0 _
  | Builtin0 _ -> assert false

let bmc_paction (state: bmc_state)
                (Paction(_, action) : 'a typed_paction) 
                : Expr.expr * AddressSet.t * bmc_state =
  let Action(_, _, action_) = action in
  match action_ with
  | Create (pe1, Pexpr(BTy_ctype, PEval (Vctype ty)), _) ->
      (* TODO: turns all integers into loaded integers *)
      let sort = ctype_to_sort state ty in

      (* Make a new memory allocation for alias analysis *)
      let new_addr = mk_new_addr state.alias_state in
      let typ = Pexpr(BTy_ctype, PEval (Vctype ty)) in 

      alias_add_addr state.alias_state new_addr typ;
      let addr_ret = AddressSet.singleton new_addr in
      
      (* Create a new bmc address and add it to the addr_map *)
      let bmc_addr : kbmc_address = mk_bmc_address new_addr sort in
      state.addr_map :=  Pmap.add new_addr bmc_addr !(state.addr_map);

      (* Set it to an initial unspecified value @a_1 *)
      let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_addr in
      let initial_value = Expr.mk_const state.ctx new_sym sort in
      let new_heap = Pmap.add new_addr initial_value state.heap in
      (* Try: create a new pointer and return it instead *)
      let new_ptr = PointerSort.mk_ptr state.ctx 
                    (Address.mk_expr state.ctx new_addr) in
      new_ptr, addr_ret, ({state with heap = new_heap})

  | Create _ -> assert false
  | Alloc0 _ -> assert false
  | Kill pexpr ->
      let (_, allocs, state) = bmc_pexpr state pexpr in
      assert (AddressSet.cardinal allocs = 1);
      let elem = AddressSet.find_first (fun _ -> true) allocs in
      let new_heap = Pmap.remove elem state.heap in
      UnitSort.mk_unit state.ctx, 
          AddressSet.empty, {state with heap = new_heap}
  | Store0 (Pexpr(BTy_ctype, PEval (Vctype ty)), Pexpr(_, PEstd (_, Pexpr(_, PEsym sym))), p_value, _) 
    (* Fall through *)
  | Store0 (Pexpr(BTy_ctype, PEval (Vctype ty)), Pexpr(_, PEsym sym), p_value, _) ->
      (* TODO: update comment
       * Overview:
         For each possible address, 
         if (get_addr sym == @a) @a_i = p_value; @a_i = (cur value)
         update heap: @a_i

         This is extremely naiive and generates equations for every created
         ^address. 
       *)
      let sort = ctype_to_sort state ty in 
      let ptr_allocs = alias_lookup_sym sym state.alias_state in
      let (value, v_allocs, state) = bmc_pexpr state p_value in
      let z3_sym = bmc_lookup_sym sym state in
      (* If we are storing a C pointer, update points-to map *)
      begin
        if is_ptr_ctype (Pexpr(BTy_ctype, PEval (Vctype ty))) then
          begin
          assert (not (AddressSet.is_empty ptr_allocs));
          assert (not (AddressSet.is_empty v_allocs));

          (* For each potential store location, add v_allocs to addr_map *)
          AddressSet.iter (fun loc ->
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
      let update = (fun alloc heap ->
          let bmc_addr = bmc_lookup_alloc alloc state in
          if (not (Sort.equal (bmc_addr.sort) sort)) then
            assert false (* or return heap *)
          else
            begin
              let cur_value = bmc_lookup_addr_in_heap alloc heap in
              
              (* Create a fresh value *)
              let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_addr in
              let new_expr = Expr.mk_const state.ctx new_sym bmc_addr.sort in
              (* get_addr sym == @a *)
              let addr_eq = Boolean.mk_eq state.ctx 
                                (PointerSort.get_addr state.ctx z3_sym)
                                (Address.mk_expr state.ctx alloc) in
              (* @a_i = p_value *)
              let new_eq = Boolean.mk_eq state.ctx new_expr value in
              (* @A_i = (cur_value) *)
              let old_eq = Boolean.mk_eq state.ctx new_expr cur_value in
              
              let ite = Boolean.mk_ite state.ctx addr_eq new_eq old_eq in
              
              (* TODO: check if this should be guarded *)
              Solver.add state.solver [ ite ];

              Pmap.add alloc new_expr heap 
            end
        ) in
        let new_heap = AddressSet.fold update ptr_allocs state.heap in
        (UnitSort.mk_unit state.ctx), AddressSet.empty, 
            {state with heap = new_heap}

(*
      let update = (fun addr bmc_addr heap ->
            if (not(Sort.equal (bmc_addr.sort) sort)) then
              heap
            else
              begin
                let cur_value = match (Pmap.lookup addr heap) with
                    | None -> assert false
                    | Some x -> x in
                (* Create a fresh value *)
                let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_addr in
                let new_expr = Expr.mk_const state.ctx new_sym bmc_addr.sort in
                (* get_addr sym == @a *)
                let addr_eq = Boolean.mk_eq state.ctx 
                      (PointerSort.get_addr state.ctx z3_sym)
                      (Address.mk_expr state.ctx addr) in 
                (* @a_i = p_value *)
                let new_eq = Boolean.mk_eq state.ctx new_expr value in

                (* @a_i = (cur value) *)
                let old_eq = Boolean.mk_eq state.ctx new_expr cur_value in

                let ite = Boolean.mk_ite state.ctx addr_eq new_eq old_eq in
                Solver.add state.solver [ ite ];

                (* Update heap *)
                let new_heap = Pmap.add addr new_expr heap in

               (* Return new heap *) 
                new_heap
              end
        )
      in
      let new_heap = Pmap.fold update (!(state.addr_map)) state.heap in
      (UnitSort.mk_unit state.ctx), ({state1 with heap = new_heap})
*)
       
  | Store0 _ -> assert false
  | Load0 (Pexpr(BTy_ctype, PEval (Vctype ty)), Pexpr(_, PEsym sym), _) -> 
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

       let ptr_allocs = alias_lookup_sym sym state.alias_state in
       (* Do alias analysis *)
       let ret_alloc = 
         begin
           if is_ptr_ctype (Pexpr(BTy_ctype, PEval (Vctype ty))) then
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
      print_endline "-----ALIAS_RESULTS";
      print_ptr_map !(state.alias_state.ptr_map);
      print_addr_map !(state.alias_state.addr_map);

      print_heap state.heap; 
      print_endline ((string_of_address_set ptr_allocs) ^ " ZZZZ");
       let iterate = (fun alloc (expr_list, addr_list) ->
          let cur_value = bmc_lookup_addr_in_heap alloc state.heap in
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

        (*
       let iterate = (fun addr bmc_addr (expr_list, addr_list) ->
          let cur_value = match (Pmap.lookup addr state.heap) with
              | None -> assert false
              | Some x -> x in
          if (Sort.equal (Expr.get_sort cur_value) sort) then
            begin
              let addr_expr = Address.mk_expr state.ctx addr in
              let addr_eq_expr = Boolean.mk_eq state.ctx
                  (PointerSort.get_addr state.ctx z3_sym)
                  addr_expr in
              let impl_expr = Boolean.mk_implies state.ctx 
                    addr_eq_expr 
                    (Boolean.mk_eq state.ctx ret_value cur_value) in
              (impl_expr :: expr_list, addr_eq_expr :: addr_list)
            end
          else 
            (expr_list, addr_list)
       ) in
       let (expr_eqs, addr_eqs) = Pmap.fold iterate (!(state.addr_map)) 
                                        ([], []) in
      *)
       
       let ret = Boolean.mk_and state.ctx expr_eqs in
       let new_vc = Boolean.mk_or state.ctx addr_eqs in
       Solver.add state.solver [ ret ];
       ret_value, ret_alloc, ({state with vcs = (new_vc) :: state.vcs})

  | Load0 _
  | RMW0 _
  | Fence0 _ ->
      assert false
(*
let merge_heap_list (state: bmc_state)
                    (heaps: kheap list)
                    (guards: Expr.expr list) : kheap =
  assert (List.length heaps = List.length guards);
*)


(* if guard then heap1 else heap2 for all addresses in alist *)
let merge_heaps (state: bmc_state) 
                (heap1: kheap) (heap2: kheap) 
                (guard: Expr.expr) : kheap =
  Pmap.merge (
    fun k e1_ e2_ -> 
      let (e1, e2) = match (e1_, e2_) with
        | (Some x, Some y) -> (x, y)
        | _ -> (Printf.printf "TODO: Merge heaps properly\n"; assert false)
      in
      (* TODO: duplicated code *)
      let bmc_address = 
        match Pmap.lookup k (!(state.addr_map)) with
        | Some x -> x
        | None -> assert false
      in
      let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_address in
      (* TODO: sort should be in bmc_address *)
      assert (Sort.equal (Expr.get_sort e1) (Expr.get_sort e2));
      let sort = Expr.get_sort e1 in
      let new_expr = Expr.mk_const state.ctx new_sym sort in
      bmc_address.hist := Pmap.add seq_num new_expr (!(bmc_address.hist));
     
      (* Add equality *) 
      Solver.add state.solver 
        [ Boolean.mk_implies state.ctx guard 
            (Boolean.mk_eq state.ctx new_expr e1) ;
          Boolean.mk_implies state.ctx (Boolean.mk_not state.ctx guard)
            (Boolean.mk_eq state.ctx new_expr e2) 
        ];
      Some new_expr 
      ) heap1 heap2

let rec bmc_expr (state: bmc_state) 
                 (Expr(annot, expr_) : 'a typed_expr)
                 : Expr.expr * AddressSet.t * bmc_state =
  match expr_ with
  | Epure pe ->
      bmc_pexpr state pe 
  | Ememop (PtrValidForDeref, _) ->
      Printf.printf "TODO: Ememop PtrValidForDeref: currently always true\n";
      (Boolean.mk_true state.ctx), AddressSet.empty, state
  | Ememop _ ->
      assert false
  | Eaction paction ->
      bmc_paction state paction

  | Ecase (pe, ((pat1, e1) :: (pat2, e2) :: [])) -> 
      Printf.printf "TODO: Ecase";
      (* TODO... painful... special case for now, 
       * copied from more general PEcase code. merging heap stuff. *)
      let caselist = [(pat1, e1); (pat2, e2)] in
      let (maybe_pe, pe_set, st)  = bmc_pexpr state pe in

      (* Alias alloc patterns *)
      List.iter (fun (pat1, _) -> 
        alias_pattern state.alias_state pat1 pe_set) caselist;

      let pattern_guards = List.map 
          (fun (pat, _) -> pattern_match st pat maybe_pe) caselist in 
      let complete_guard = Boolean.mk_or st.ctx pattern_guards in

      Solver.add st.solver [ complete_guard ];

      let combined_pat_guards = 
        List.mapi (fun i expr -> 
          Boolean.mk_and st.ctx 
          [ Boolean.mk_not st.ctx (Boolean.mk_or st.ctx (list_take i pattern_guards))
          ; expr 
          ]
          ) pattern_guards in


      (* Length = 2 *)
      let expr_eqs = List.map (fun (pat, _) -> mk_eq_pattern st pat maybe_pe) caselist in
      let impl_eqs = List.map2 
        (fun guard eq -> Boolean.mk_implies state.ctx guard eq) 
        combined_pat_guards expr_eqs in

      Solver.add st.solver impl_eqs;

      let cases_z3 = List.map 
        (fun (_, e) -> bmc_expr ({st with vcs = []}) e) caselist in
      let cases_vcs = (List.map (fun (e, _, s) -> Boolean.mk_and state.ctx s.vcs) cases_z3) in
      let new_vcs = (st.vcs @ (List.map2 (fun guard vc -> Boolean.mk_implies state.ctx guard vc) combined_pat_guards cases_vcs)) in

      let guard = List.hd combined_pat_guards in

      let alloc_ret = List.fold_left (fun s (_, set, _) ->
        AddressSet.union s set) AddressSet.empty cases_z3 in
      

      let ((bmc_e1, _, st1),(bmc_e2, _, st2)) = match cases_z3 with
        | [x; y] -> (x, y)
        | _ -> assert false
      in

      begin
        (*
        match (bmc_e1, bmc_e2) with
        | (None, None) -> 
            let new_heap = merge_heaps st st1.heap st2.heap guard in
            None, ({st with vcs = new_vcs; heap = new_heap})
        | (Some a1, Some a2) -> 
            *)
            let new_heap = merge_heaps st st1.heap st2.heap guard in
            
            (Boolean.mk_ite st.ctx guard bmc_e1 bmc_e2),
              alloc_ret,
             ({st with heap = new_heap; vcs = new_vcs})
        (*
        | (Some a1, None) -> 
            Printf.printf "TODOa: Do Ecase properly\n";
            Some a1, ({st with heap = st1.heap; vcs = new_vcs})
        | (None, Some a2) ->
            (Printf.printf "TODOb: Do ECase properly\n"; assert false)
        *)
      end

  | Ecase _ ->  
      Printf.printf "TODO2: Do ECase properly \n"; 
      assert false
  | Eskip -> 
      (* TODO: Unit *)
      (UnitSort.mk_unit state.ctx), AddressSet.empty, state 
  | Eproc _ -> assert false
  | Eccall _  -> assert false
  | Eunseq _ -> assert false
  | Eindet _ -> assert false
  | Ebound (_, e1) ->
      print_endline "TODO: bound in Ebound ignored";
      bmc_expr state e1 
  | End _ ->
      (* nondeterministic sequencing: create disjoint choice points
       * guard verification conditions and heap assignments by choice points
       *
       * TODO: length elist=2 for now, rewrite later
       *)
      (*
      let bmc_elist = List.map (fun e -> 
        (bmc_expr state e, 
         Expr.mk_fresh_const state.ctx "seq" (Boolean.mk_sort state.ctx))) in
      let seq_xor = Boolean.mk_xor state.ctx (List.map (fun (_, seq) -> seq)) in

      (* Assert exactly one sequence occured *)
      Solver.add state.solver [seq_xor];

      let new_vcs = List.map (fun ((_, st'), guard) -> 
        Boolean.mk_implies st'.ctx guard (Boolean.mk_and st'.ctx st'.vcs)) in

      let new_heap = 
      *)

      (* 
      assert (List.length elist = 2);
      Printf.printf "TODO: ND sequencing. Currently only elist of length two\n";
      let bmc_elist = List.mapi (fun i e -> bmc_expr state e) in 
      *)
      Printf.printf "TODO ND sequencing: currrently treated as undef\n";
      let new_vcs = (Boolean.mk_false state.ctx) :: state.vcs in
      let new_state = {state with vcs = new_vcs} in
      (UnitSort.mk_unit state.ctx), AddressSet.empty, new_state
  | Erun (_, Symbol(i, Some s), _) ->
      Printf.printf "TODO: Erun, special casing ret by ignoring it\n";
      begin
      match Str.split (Str.regexp "_") s with
      | [name; id] ->
          if (name = "ret") && (int_of_string id = i) then
            (UnitSort.mk_unit state.ctx), AddressSet.empty, state
          else
            assert false
      | _ -> assert false
      end

  | Erun _ ->
      assert false
  | Epar _
  | Ewait _ -> assert false
  | Eif (pe, e1, e2) -> 
      let (bmc_pe, loc, st) = bmc_pexpr state pe in
      let (bmc_e1, loc1, st1) = bmc_expr ({st with vcs = []}) e1 in
      let (bmc_e2, loc2, st2) = bmc_expr ({st with vcs = []}) e2 in

      Printf.printf "TODO: only heap/vcs are updated after Eif\n";
      
        (*
      let ret = 
        (* TODO: special cased; inconsistent with PEif *)
        match (maybe_pe, bmc_e1, bmc_e2) with
        | (None, _, _) ->
            None, st
        | (Some pexpr, None, None) -> 
          let new_vc = st.vcs @ (concat_vcs state st1.vcs st2.vcs pexpr) in
          let new_heap = merge_heaps st st1.heap st2.heap pexpr in

          (* Return state conditional upon which store occurred *)
          (* TODO: record which addresses each state may have changed *) 
          (* TODO: ptr_map *)
          None, ({st with heap = new_heap; vcs = new_vc})
        | (Some pexpr, Some e1, Some e2) -> 
            (* TODO: duplicated *)
        *)
          let new_vc = st.vcs @ (concat_vcs state st1.vcs st2.vcs bmc_pe) in
          let new_heap = merge_heaps st st1.heap st2.heap bmc_pe in
          (Boolean.mk_ite state.ctx bmc_pe bmc_e1 bmc_e2),
            AddressSet.union loc1 loc2,
            ({st with heap = new_heap; vcs = new_vc})
        (*
        | (Some pexpr, Some e1, None) -> 
          let new_vc = st.vcs @ (concat_vcs state st1.vcs st2.vcs pexpr) in
          let new_heap = st1.heap in
            Some e1, ({st with heap = new_heap; vcs = new_vc})
        | (Some pexpr, None, Some e2) -> 
          let new_vc = st.vcs @ (concat_vcs state st1.vcs st2.vcs pexpr) in
          let new_heap = st2.heap in
            Some e2, ({st with heap = new_heap; vcs = new_vc})

      in 
      ret    
      *)
  | Elet _ -> assert false
  | Easeq _ ->
      assert false
  (*
  | Ewseq (CaseBase(sym, typ), e1, e2) ->
      let (ret_e1, state1) = bmc_expr state e1 in
      let (eq_expr) = mk_eq_pattern state1 (CaseBase(sym, typ)) ret_e1 in
      Solver.add state1.solver [ eq_expr ];

      bmc_expr state1 e2
  | Ewseq (CaseCtor(ctor, patList), e1, e2) -> 
      Printf.printf "TODO: Ewseq\n";
      let (ret_e1, state1) = bmc_expr state e1 in
      let (eq_expr) = mk_eq_pattern state1 (CaseCtor(ctor, patList)) ret_e1 in

      Solver.add state1.solver [ eq_expr ];

      bmc_expr state1 e2
      
  | Esseq (CaseBase(sym, typ), e1, e2) ->
      let (ret_e1, state1) = bmc_expr state e1 in
      let (eq_expr ) = mk_eq_pattern state1 (CaseBase(sym, typ)) ret_e1 in
      Solver.add state1.solver [ eq_expr ];
      bmc_expr state1 e2
  | Esseq _  ->
      assert false
  *)
  | Ewseq (pat, e1, e2) (* TODO: Fall through for now *)
  | Esseq (pat, e1, e2) ->
      let (ret_e1, loc1, state) = bmc_expr state e1 in
      alias_pattern state.alias_state pat loc1;
      let eq_expr = mk_eq_pattern state pat ret_e1 in
      Solver.add state.solver [ eq_expr ];
      bmc_expr state e2

  | Esave ((Symbol (i, Some s), _), _, _)  ->
      (* Special case ret *)
      begin
      match Str.split (Str.regexp "_") s with
      | [name; id] -> 
          begin
            if (name = "ret") && ((int_of_string id) = i) then
               (print_endline "TODO: Esave ret, currently ignored";
                UnitSort.mk_unit state.ctx, AddressSet.empty, state)
            else 
              assert false
          end
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
        check_solver state1.solver;
        Printf.printf "-----WITH VCS \n";
        let not_vcs = List.map (fun a -> (Boolean.mk_not state1.ctx a))
                               state1.vcs
        in
        Solver.add state1.solver [ Boolean.mk_or state1.ctx not_vcs ] 
  ) funs
*)
let initialise_param ((sym, ty): (ksym * core_base_type)) state =
  add_sym_to_sym_table state sym ty;
  match Pmap.lookup sym !(state.alias_state.ptr_map) with
  | Some s -> assert false (* Symbol should not exist yet *)
  | None ->
     (* TODO: does not work if arg is a C pointer ? *) 
      if is_ptr_type ty then (* duplicated from Create *)
        begin
          let new_addr = mk_new_addr state.alias_state in
          state.alias_state.addr_set := AddressSet.add new_addr
                              !(state.alias_state.addr_set);
          add_set state.alias_state sym (AddressSet.singleton new_addr);

          (* Create a new bmc address and add it to addr_map *)
          let sort = cbt_to_z3 state ty in
          let bmc_addr =  mk_bmc_address new_addr sort in
          state.addr_map := Pmap.add new_addr bmc_addr !(state.addr_map);

          (* Set it to an initial unspecified value @a_1 *)
          let (new_sym, seq_num) = mk_next_seq_symbol state.ctx bmc_addr in
          let initial_value = Expr.mk_const state.ctx new_sym sort in
          let new_heap = Pmap.add new_addr initial_value state.heap in
          ({state with heap = new_heap})
        end
    else 
      state

let bmc_file (file: 'a typed_file) (supply: ksym_supply) =
  match file.main with
  | None -> failwith "ERROR: file does not have a main"
  | Some main_sym ->
      let (_, _, state1) = (
        let initial_state = initial_bmc_state supply in
        match Pmap.lookup main_sym file.funs with
        | Some (Proc(ty, params, e)) ->
            (* Handle parameters *)
            let state = List.fold_left (fun st param ->
                initialise_param param st) initial_state params in
              (*
            let _ = analyse_expr analysis_state e in

            print_ptr_map !(analysis_state.ptr_map);
            print_addr_map !(analysis_state.addr_map);
            *)
            bmc_expr state e
        | Some (Fun(ty, params, pe)) ->
            (* Handle parameters *)

            let state = List.fold_left (fun st param ->
                initialise_param param st) initial_state params in
                        (*
            let _ = analyse_pexpr analysis_state pe in

            print_ptr_map !(analysis_state.ptr_map);
            print_addr_map !(analysis_state.addr_map);

            let initial_state = initial_bmc_state supply analysis_state in
            *)
            bmc_pexpr state pe 
        | _ -> assert false
      ) in

      print_endline "-----ALIAS_RESULTS";
      print_ptr_map !(state1.alias_state.ptr_map);
      print_addr_map !(state1.alias_state.addr_map);


      Printf.printf "-----CONSTRAINTS ONLY\n";
      check_solver state1.solver;
      Printf.printf "-----WITH VCS \n";
      let not_vcs = List.map (fun a -> (Boolean.mk_not state1.ctx a))
                             state1.vcs
      in
      Solver.add state1.solver [ Boolean.mk_or state1.ctx not_vcs ] ;

      Printf.printf "\n-- Solver:\n%s\n" (Solver.to_string (state1.solver));
      Printf.printf "Checking sat\n";
      check_solver (state1.solver)

let (>>=) = Exception.except_bind

let run_bmc (core_file : 'a file) 
            (sym_supply: ksym_supply)    = 
  (* TODO: state monad with sym_supply *)
  print_string "ENTER: BMC PIPELINE \n";
  pp_file core_file;

  print_string "ENTER: NORMALIZING FILE\n";
  let (norm_file, norm_supply) = bmc_normalize_file core_file sym_supply in

  print_string "EXIT: NORMALIZING FILE\n";


  print_string "Typechecking file\n";
  Core_typing.typecheck_program norm_file >>= fun typed_core ->
    Exception.except_return (

      print_string "HERE\n";
      let seq_file = Core_sequentialise.sequentialise_file typed_core in
      pp_file seq_file;
      bmc_file seq_file norm_supply;

      print_string "EXIT: BMC PIPELINE \n"
    )

