(*
 * BMC STUFF
 *
 * BMC_utils:
 *    - pretty printers
 * BMC_normalize: 
 *    - normalize core file
 *)

open Core
open Lem_pervasives
open Z3
open Z3.Arithmetic

open Mem
open Ocaml_mem
open Bmc_utils
open Bmc_normalize
open Bmc_sorts

open Pp_core
(* ========== Type definitions ========== *)

type ksym_table = (int, Expr.expr) Pmap.map

(* Pointer state: 
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

module type AddressType =
  sig
    type addr
    val is_eq: addr -> addr -> bool

    (* Given previous addr, make a new one *)
    val mk_fresh: addr ref -> addr
    val mk_sort: context -> Sort.sort
    val mk_initial: addr
    val to_string: addr -> string
  end 

module IntAddress : AddressType = 
  struct
    type addr = int
    let is_eq = (==)
    let mk_fresh st = (let ret = succ !st in (st := ret; ret))
    let mk_sort = Integer.mk_sort
    let mk_initial = 0
    let to_string = string_of_int
  end

module Address = (IntAddress : AddressType)

(* "Symbol: @int_int" *)
type kbmc_address = {
  addr        : Address.addr;
  seq_ctr     : int ref;
  hist        : ((int, Expr.expr) Pmap.map) ref;
}

type bmc_state = {
  ctx         : context;
  solver      : Solver.solver;
  sym_table   : ksym_table ref;
  sym_supply  : ksym_supply ref;

  (* Make fresh allocations using Address.mk_fresh *)
  addr_gen    : Address.addr ref;

  (* Map from int -> address *)
  addr_map    : (Address.addr, kbmc_address) Pmap.map ref;

  (* ------------- *)
  
  (* Map from address to Z3 symbol representing value *)
  heap        : (Address.addr, Expr.expr) Pmap.map;

  (* Map from Core symbol to set of addresses *)
  ptr_map     : (int, Address.addr list) Pmap.map;

  vcs         : Expr.expr list;
}

type bmc_ret = 
  | BmcAddress of kbmc_address
  | BmcZ3Expr  of Expr.expr option
  | BmcTODO
  | BmcNone

(* PPrinters *)

let print_ptr_map (map : (int, Address.addr list) Pmap.map) =
  Pmap.mapi (fun k v-> (Printf.printf "%d -> " k;
            List.iter(fun s -> Printf.printf "%s " (Address.to_string s)) v)) map


(* ========== BMC ========== *)

let symbol_to_z3 (ctx: context) (sym: ksym) =
  match sym with
  | Symbol (num, Some str) ->
      mk_sym ctx ((string_of_int num) ^ "_" ^ str)
  | Symbol (num, None) ->
      mk_sym ctx ((string_of_int num) ^ "_" ^ "a")

let get_last_seqnum (ctx: context) (bmc_address : kbmc_address) =
  (!(bmc_address.seq_ctr))

let mk_next_seq_symbol (ctx: context) (bmc_address : kbmc_address) =
  bmc_address.seq_ctr := succ (!(bmc_address.seq_ctr));
  mk_sym ctx ("@" ^ (Address.to_string (bmc_address.addr)) ^ "_" ^ 
              (string_of_int (!(bmc_address.seq_ctr))))


let ctor_to_z3 (state: bmc_state) (ctor: typed_ctor) 
               (pes: Expr.expr list) (sort: Sort.sort) =
  match ctor with
  | Cnil _ (* empty list *)
  | Ccons -> 
      assert false
  | Ctuple ->
      (* sort should be a tuple sort *)
      assert (List.length pes = Tuple.get_num_fields sort);
      let mk_decl = Tuple.get_mk_decl sort in
      FuncDecl.apply mk_decl pes

  | Carray (* C array *)
  | Civmax (* max integer value *)
  | Civmin (* min integer value *)
  | Civsizeof (* sizeof value *)
  | Civalignof (* alignof value *)
  | CivCOMPL (* bitwise complement *)
  | CivAND (* bitwise AND *)
  | CivOR (* bitwise OR *)
  | CivXOR (* bitwise XOR *)
  | Cspecified (* non-unspecified loaded value *)
  | Cunspecified (* unspecified value *)
  | Cfvfromint (* cast integer to floating value *)
  | Civfromfloat (* cast floating to integer value *) ->
      assert false

(* core_base_type to z3 sort *)
let rec cbt_to_z3 (state: bmc_state) (cbt : core_base_type) : Z3.Sort.sort =
  let ctx = state.ctx in
  match cbt with
   | BTy_unit  -> 
        UnitSort.mk_sort ctx
   | BTy_boolean ->
        Boolean.mk_sort ctx
   | BTy_ctype 
   | BTy_list _ -> assert false
   | BTy_tuple (cbt_list) ->
        let (new_sym, supply1) = Sym.fresh (!(state.sym_supply)) in
        state.sym_supply := supply1;
        let sort_to_string = fun t -> pp_to_string
                              (Pp_core.Basic.pp_core_base_type t) in
        let sort_name = sort_to_string cbt in
        let sort_symbol = mk_sym state.ctx sort_name in

        let sym_list = List.mapi 
            (fun i v -> mk_sym state.ctx 
                  ( "#" ^ (string_of_int i)))
            (*      ((sort_to_string v) ^ "_" ^ (string_of_int i))) *)
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
          | _ -> assert false
       end

                       

let initial_bmc_state (supply : ksym_supply) : bmc_state = 
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = mk_context cfg in
  {
    ctx = ctx;
    solver = Solver.mk_solver ctx None;
    sym_table = ref (Pmap.empty Pervasives.compare);
    sym_supply = ref supply;

    addr_gen = ref (Address.mk_initial);
    addr_map = ref (Pmap.empty Pervasives.compare);

    heap = Pmap.empty Pervasives.compare;
    ptr_map = Pmap.empty Pervasives.compare;

    vcs = []
  }
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

let rec value_to_z3 (ctx: context) (cval: value) =
  match cval with
  | Vunit -> UnitSort.mk_unit ctx
  | Vtrue -> Boolean.mk_true ctx
  | Vfalse -> Boolean.mk_false ctx
  | Vlist (_, cvals) ->
      assert false;
  | Vtuple cvals ->
      assert false
  | Vctype ty ->
      assert false
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
      | LVunspecified _ -> assert false

let binop_to_constraints (ctx: context) (pe1: Expr.expr) (pe2: Expr.expr) = function
  | OpAdd -> Arithmetic.mk_add ctx [ pe1; pe2 ]
  | OpSub -> Arithmetic.mk_sub ctx [ pe1; pe2 ]
  | OpMul -> Arithmetic.mk_mul ctx [ pe1; pe2 ]
  | OpDiv -> Arithmetic.mk_div ctx pe1 pe2
  | OpRem_t 
  | OpRem_f 
  | OpExp -> assert false;
  | OpEq -> Boolean.mk_eq ctx pe1 pe2   
  | OpLt -> Arithmetic.mk_lt ctx pe1 pe2
  | OpLe -> Arithmetic.mk_le ctx pe1 pe2 
  | OpGt -> Arithmetic.mk_gt ctx pe1 pe2
  | OpGe -> Arithmetic.mk_ge ctx pe1 pe2
  | OpAnd -> Boolean.mk_and ctx [ pe1; pe2 ] 
  | OpOr -> Boolean.mk_or ctx [ pe1; pe2 ]


let mk_eq_expr (state: bmc_state) (m_sym: ksym option) 
               (ty : core_base_type) (bmc_expr : bmc_ret) =
  match m_sym with
  | None -> state (* Do nothing *)
  | Some sym -> 
      let sym_id = symbol_to_int sym in
      let pat_sym = symbol_to_z3 state.ctx sym in
      begin
      match ty with
      | BTy_unit -> assert false
      | BTy_boolean -> assert false
      | BTy_ctype -> assert false
      | BTy_list _ -> assert false
      | BTy_tuple ty_list -> 
          (* TODO: duplicate *)
          begin
          match bmc_expr with
          | BmcZ3Expr (Some expr) ->
              let sort = cbt_to_z3 state ty in
              let expr_pat = Expr.mk_const state.ctx pat_sym sort in
              state.sym_table := Pmap.add sym_id expr_pat (!(state.sym_table));
              Solver.add state.solver [ Boolean.mk_eq state.ctx expr_pat expr];
              state
          | _ -> assert false
          end
      | BTy_object OTy_pointer -> 
          (* Pointer equality *)
          begin
          match bmc_expr with
          | BmcAddress addr -> 
              (* let x: pointer = Create... *)
              (* TODO: Z3 equality of address *)

              (* Add symbol to sym_table: x -> Pointer x *)
              let expr_pat = PointerSort.mk_ptr state.ctx 
                                  (PointerSort.mk_addr state.ctx sym_id) in
              state.sym_table := Pmap.add sym_id expr_pat (!(state.sym_table));
              (* Map sym_id to address *)
              ({state with ptr_map = (Pmap.add sym_id [ addr.addr ]
                                      state.ptr_map)})
          | BmcZ3Expr (Some expr) ->
              if Sort.equal (Expr.get_sort expr) (PointerSort.mk_sort state.ctx)
              then 
                begin
                  let ptr_id = PointerSort.get_addr expr in
                  let addr_list = 
                    match Pmap.lookup ptr_id state.ptr_map with
                    | Some z -> z
                    | None -> assert false
                  in
                  (* TODO: duplicated code from BmcAddress. Do earlier *)
                  let sym_id = symbol_to_int sym in
                  let pat_sym = symbol_to_z3 state.ctx sym in
                  let expr_pat = PointerSort.mk_ptr state.ctx 
                                      (PointerSort.mk_addr state.ctx sym_id) in
                  state.sym_table := Pmap.add sym_id expr_pat (!(state.sym_table));
                  (* Only changed line *)
                  ({state with ptr_map = (Pmap.add sym_id addr_list
                                          state.ptr_map)})
                end 
              else
                assert false
          | _ -> assert false
          end
      | BTy_object _ -> 
          (* TODO: duplicated *)
          begin
          match bmc_expr with
          | BmcZ3Expr (Some expr) ->
              let sort = cbt_to_z3 state ty in
              let expr_pat = Expr.mk_const state.ctx pat_sym sort in
              state.sym_table := Pmap.add sym_id expr_pat (!(state.sym_table));
              Solver.add state.solver [ Boolean.mk_eq state.ctx expr_pat expr];
              state
          | _ -> assert false
          end
      | BTy_loaded cot ->
          (* TODO duplicated code: should case on bmc_expr instead maybe *)
          let pat_symbol = symbol_to_z3 state.ctx sym in
          let z3_sort = cbt_to_z3 state ty in
          let expr_pat = Expr.mk_const state.ctx pat_symbol z3_sort in
          state.sym_table := Pmap.add (symbol_to_int sym) expr_pat 
                                      (!(state.sym_table));
          begin
          match bmc_expr with
          | BmcZ3Expr None -> state
          | BmcZ3Expr (Some expr) ->
              begin
              Solver.add state.solver [ Boolean.mk_eq state.ctx expr_pat expr];
              state
              end
          | _ -> assert false
          end
        end

let rec mk_eq_pattern (state: bmc_state) (pattern: typed_pattern)
                      (ty: core_base_type) (bmc_expr: bmc_ret) =
  match pattern with
  | CaseBase(maybe_sym, typ) ->
      mk_eq_expr state maybe_sym typ bmc_expr
  | CaseCtor(ctor, patlist) -> 
      match ctor with
      | Cnil _
      | Ccons -> 
          assert false
      | Ctuple ->
          begin
          match ty with
          | BTy_tuple ty_list -> 
              assert (List.length ty_list = List.length patlist);
              let z3_sort = cbt_to_z3 state ty in
              let indices = List.mapi (fun i v -> i) ty_list in
              let zipped = List.combine ty_list patlist in
              let fields = Tuple.get_field_decls z3_sort in
              let expr = (
                match bmc_expr with
                | BmcZ3Expr (Some expr) -> expr
                | _ -> assert false 
              ) in
              let get_field i = 
                FuncDecl.apply (List.nth fields i) [ expr ] in

              assert (List.length fields = List.length patlist);

              List.fold_left2 (fun s (ty, pat) i ->
                mk_eq_pattern s pat ty 
                  (BmcZ3Expr (Some (get_field i))
              )) state zipped indices;
          | _ -> assert false
          end
      | Carray (* C array *)
      | Civmax (* max integer value *)
      | Civmin (* min integer value *)
      | Civsizeof (* sizeof value *)
      | Civalignof (* alignof value *)
      | CivCOMPL (* bitwise complement *)
      | CivAND (* bitwise AND *)
      | CivOR (* bitwise OR *)
      | CivXOR (* bitwise XOR *)
      | Cspecified (* non-unspecified loaded value *)
      | Cunspecified (* unspecified value *)
      | Cfvfromint (* cast integer to floating value *)
      | Civfromfloat (* cast floating to integer value *) ->
          assert false

let rec bmc_pexpr (state: bmc_state) 
                  (Pexpr(bTy, pe) as pexpr : typed_pexpr) =
  let (z_pe, state') = match pe with
    | PEsym sym ->
        pp_to_stdout (Pp_core.Basic.pp_pexpr pexpr);
        Printf.printf "\n";
        let sym_expr = 
          match Pmap.lookup (symbol_to_int sym) (!(state.sym_table)) with
          | Some z -> z
          | None -> assert false
        in
        Some sym_expr, state
    | PEimpl _ -> assert false
    | PEval cval ->
        (Some (value_to_z3 state.ctx cval), state)
    | PEconstrained _ ->
        assert false
    | PEundef _ ->
        let new_vcs = (Boolean.mk_false state.ctx) :: state.vcs in
        let new_state = {state with vcs = new_vcs} in
        None, new_state
    | PEerror _ -> assert false
    | PEctor (ctor, pelist) -> 
        let sort = cbt_to_z3 state bTy in
        (* assert pelist just consists of pesyms *)
        let _ = List.iter 
                (fun pe -> match pe with
                           | Pexpr(_, PEsym sym) -> ()
                           | _ -> assert false )
                pelist in
        (* TODO: state needs to be propagated *) 
        (* Should just be a lookup *)
        let z3_pelist = List.map (fun pe -> 
          match (bmc_pexpr state pe) with
          | (None, _) -> assert false
          | (Some x, _) -> x 
          ) pelist in

        let ret = ctor_to_z3 state ctor z3_pelist sort in
        Some ret,  state
    | PEcase (pe1, patlist) -> 
        let (maybe_pe1) = bmc_pexpr state pe1 in 
        assert false
    | PEarray_shift _ -> assert false
    | PEmember_shift _ -> assert false
    | PEnot pe1 -> 
        let (maybe_pe1, state1) = bmc_pexpr state pe1 in  
        begin
          match maybe_pe1 with
          | Some x -> Some (Boolean.mk_not state.ctx x), state1
          | _ -> None, state1
        end
    | PEop (bop, pe1, pe2) ->
        let (maybe_pe1, state1) = bmc_pexpr state pe1 in
        let (maybe_pe2, state2) = bmc_pexpr state1 pe2 in
        begin
          match (maybe_pe1, maybe_pe2) with
          | (Some x, Some y) ->
              Some (binop_to_constraints (state2.ctx) x y bop), state2
          | _ -> None, state2
        end
    | PEstruct _
    | PEunion _ -> assert false
    | PEcall (Sym (Symbol(_, Some "conv_loaded_int")), (typ :: pe :: [])) -> 
        (* TODO: special case conv_loaded_int *)
        (* TODO: range check *)
        bmc_pexpr state pe 
    | PEcall (_, args) -> assert false
    | PElet (CaseBase(Some sym, pat_ty), pe1, pe2) ->
        let (Pexpr(pat_type, _)) = pe1 in
        let z3_sort = cbt_to_z3 state pat_type in
        let (maybe_pe1, state1) = bmc_pexpr state pe1 in

        (* Add new symbol to sym_table *)
        let pat_symbol = symbol_to_z3 state.ctx sym in
        let expr_pat = Expr.mk_const (state.ctx) pat_symbol z3_sort in
        state1.sym_table := Pmap.add (symbol_to_int sym) expr_pat 
                                     (!(state1.sym_table));

        begin
          match maybe_pe1 with
          | Some pe -> Solver.add (state1.solver) 
                                  [ Boolean.mk_eq (state1.ctx) expr_pat pe ]
          | None -> ()
        end;

        let (maybe_pe2, state2) = bmc_pexpr state1 pe2 in
        maybe_pe2, state2
    | PElet (CaseBase(None, pat_ty), pe1, pe2) ->
        assert false
    | PElet (CaseCtor(ctor, patList), pe1, pe2) ->
        let (Pexpr(pat_type, _)) = pe1 in
        let z3_sort = cbt_to_z3 state pat_type in
        let (maybe_pe1, state1) = bmc_pexpr state pe1 in
        let state2 = mk_eq_pattern state1 (CaseCtor(ctor, patList)) 
                     pat_type (BmcZ3Expr maybe_pe1) in
        bmc_pexpr state2 pe2
    | PEif (pe1, pe2, pe3) ->
        let (maybe_pe1, s1) = bmc_pexpr state pe1 in
        let (maybe_pe2, s2) = bmc_pexpr ({state with vcs = []}) pe2 in
        let (maybe_pe3, s3) = bmc_pexpr ({state with vcs = []}) pe3 in
        begin
          match (maybe_pe1, maybe_pe2, maybe_pe3) with
          | (Some a, Some b, Some c) ->
              let new_vc2 = List.map (fun vc -> Boolean.mk_implies s2.ctx a vc) 
                                     s2.vcs in
              let new_vc3 = List.map (fun vc -> Boolean.mk_implies s3.ctx
                                                (Boolean.mk_not s3.ctx a) vc)
                                     s3.vcs in
              let new_vc = s1.vcs @ new_vc2 @ new_vc3 in
              Some (Boolean.mk_ite s3.ctx a b c), ({s3 with vcs = new_vc})
          | _ -> assert false (* TODO *)
        end
    | PEis_scalar _
    | PEis_integer _
    | PEis_signed _
    | PEis_unsigned _
    | PEstd _ ->
      assert false
  in
    z_pe, state'




let mk_bmc_address (addr : Address.addr) =
  {addr = addr; seq_ctr = ref 0; hist = ref (Pmap.empty Pervasives.compare)}

let bmc_paction (state: bmc_state)
                (Paction(_, action) as paction : 'a typed_paction) =
  let Action(_, _, action_) = action in
  match action_ with
  | Create _ ->
      (* Create a new addr *)
      let addr = Address.mk_fresh state.addr_gen in
      let bmc_addr : kbmc_address = mk_bmc_address addr in
      (* Add address to addr_map *)
      state.addr_map :=  Pmap.add addr bmc_addr (!(state.addr_map));
      BmcAddress bmc_addr, state
  | Alloc0 _ ->
      assert false
  | Kill _ ->
      BmcTODO, state
  | Store0 (_, Pexpr(_, PEsym sym), p_value, _) ->
      (* Look up symbol in ptr_map *)
      (* Look up address in addr_map *)
      let addr = 
        match Pmap.lookup (symbol_to_int sym) (state.ptr_map) with
        | Some (addr :: []) -> addr (* TODO: assume singleton address *)
        | _ -> assert false
      in   
      (* Generate new seq variable *)
      let bmc_address =
        match Pmap.lookup addr (!(state.addr_map)) with
        | Some x -> x
        | None -> assert false
      in
      let new_sym = mk_next_seq_symbol state.ctx bmc_address in
      let seq_num = get_last_seqnum state.ctx bmc_address in
      (* Add to history *)
      (* TODO: Type is wrong *)
      let Pexpr(typ, _) = p_value in
      let z3_sort = cbt_to_z3 state typ in
      let expr_pat = Expr.mk_const state.ctx new_sym z3_sort in
      bmc_address.hist := Pmap.add seq_num expr_pat (!(bmc_address.hist));

      (* Update heap *)
      let new_heap = Pmap.add addr expr_pat state.heap in
      let (expr_value, state1) = bmc_pexpr state p_value in

      begin
      match expr_value with
      | None -> assert false
      | Some v -> Solver.add state1.solver 
                  [ Boolean.mk_eq state1.ctx expr_pat v]
      end;
      BmcNone,  {state1 with heap = new_heap}
  | Store0 _ -> assert false
  | Load0 (_, Pexpr(_, PEsym sym), _) -> 
      let sym_id = symbol_to_int sym in
      let addr = 
        match Pmap.lookup sym_id state.ptr_map with
        | Some (addr :: []) -> addr
        | _ -> assert false
      in
      Printf.printf "Addr: %s\n" (Address.to_string addr);
      let heap_value = 
        match Pmap.lookup addr state.heap with
        | Some x -> x
        | None -> assert false
      in
      BmcZ3Expr (Some heap_value), state
  | Load0 _
  | RMW0 _
  | Fence0 _ ->
      assert false

let rec bmc_expr (state: bmc_state) 
                 (Expr(annot, expr_) as expr: 'a typed_expr) =
  let (z_e, state') = match expr_ with
  | Epure pe ->
      let (maybe_ret1, state1)  = bmc_pexpr state pe in
      BmcZ3Expr (maybe_ret1), state1
  | Ememop _ ->
      assert false
  | Eaction paction ->
      bmc_paction state paction
  | Ecase _
  | Eskip
  | Eproc _
  | Eccall _ 
  | Eunseq _ -> assert false
  | Eindet _ -> assert false
  | Ebound (_, e1) ->
      (* TODO: bound ignored *)
      bmc_expr state e1 
  | End _
  | Erun _
  | Epar _
  | Ewait _ 
  | Eif _ 
  | Elet _ 
  | Easeq _ ->
      assert false
  | Ewseq (CaseBase(sym, typ), e1, e2) ->
      let (ret_e1, state1) = bmc_expr state e1 in
      let state2 = mk_eq_pattern state1 (CaseBase(sym, typ)) typ ret_e1 in
      Printf.printf "HERE\n";
      Printf.printf "%s\n" (Solver.to_string state2.solver);
      Printf.printf "THERE\n";
      bmc_expr state2 e2
  | Ewseq _ -> assert false
  | Esseq (CaseBase(sym, typ), e1, e2) ->
      let (ret_e1, state1) = bmc_expr state e1 in
      let state2 = mk_eq_pattern state1 (CaseBase(sym, typ)) typ ret_e1 in
      (Printf.printf "EEK: %s\n" (Solver.to_string state2.solver));
      bmc_expr state2 e2
  | Esseq _  ->
      assert false
  | Esave _  ->
      BmcTODO, state
  in 
    Printf.printf "%s\n" (Solver.to_string state'.solver);
    (z_e, state')


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
        let not_vcs = List.map (fun a -> (Boolean.mk_not state1.ctx a))
                               state1.vcs
        in
        Solver.add state1.solver [ Boolean.mk_or state1.ctx not_vcs ] 
  ) funs


let bmc_file (file: 'a typed_file) (supply: ksym_supply) =
  let initial_state = initial_bmc_state supply in
  bmc_fun_map initial_state file.funs;
  (* TODO globals *)
  Printf.printf "\n-- Solver:\n%s\n" (Solver.to_string (initial_state.solver));
  Printf.printf "Checking sat\n";
  begin
  if (Solver.check (initial_state.solver) []) != SATISFIABLE then
    Printf.printf "NOT SAT :) \n"
  else
    begin 
    Printf.printf "SAT :( \n";
    let model = Solver.get_model (initial_state.solver) in
      match model with
      | Some m -> Printf.printf "Model: \n%s\n" (Model.to_string m)
      | None -> Printf.printf "No model\n"
    ;
    end
  end

let run_bmc (core_file : 'a typed_file) 
            (sym_supply: ksym_supply)    = 
  print_string "ENTER: BMC PIPELINE \n";
  pp_file core_file;
  let (normalized_file, supply1) = normalize_file core_file sym_supply in
  pp_file normalized_file;

  print_string "Done normalization\n";
  bmc_file normalized_file supply1; 

  print_string "EXIT: BMC PIPELINE \n";
