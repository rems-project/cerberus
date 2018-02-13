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

module type Address =
  sig
    type addr
    val is_eq: addr -> addr -> bool

    (* Given previous addr, make a new one *)
    val mk_fresh: addr -> addr
    val mk_sort: context -> Sort.sort
  end

module IntAddress : Address = 
  struct
    type addr = int
    let is_eq = (==)
    let mk_fresh = succ
    let mk_sort = Integer.mk_sort
  end

type bmc_state = {
  ctx         : context;
  solver      : Solver.solver;
  sym_table   : ksym_table ref;

  vcs         : Expr.expr list;
}


(* ========== BMC ========== *)

let symbol_to_z3 (ctx: context) (sym: Sym.sym) =
  match sym with
  | Symbol (num, Some str) ->
      mk_sym ctx ((string_of_int num) ^ "_" ^ str)
  | Symbol (num, None) ->
      mk_sym ctx ((string_of_int num) ^ "_" ^ "a")


(* core_base_type to z3 sort *)
let cbt_to_z3 (ctx: context) (cbt : core_base_type) : Z3.Sort.sort =
  match cbt with
   | BTy_unit  -> 
        UnitSort.mk_sort ctx
   | BTy_boolean ->
        Boolean.mk_sort ctx
   | BTy_ctype 
   | BTy_list _ 
   | BTy_tuple _ ->
        assert false
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

let initial_bmc_state (_ : unit) : bmc_state = 
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = mk_context cfg in
  {
    ctx = ctx;
    solver = Solver.mk_solver ctx None;
    sym_table = ref (Pmap.empty Pervasives.compare);
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


let rec bmc_pexpr (state: bmc_state) 
                  (Pexpr(bTy, pe) as pexpr : typed_pexpr) =
  let (z_pe, state') = match pe with
    | PEsym sym ->
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
    | PEerror _ 
    | PEctor _
    | PEcase _
    | PEarray_shift _
    | PEmember_shift _ 
    | PEnot _ -> assert false
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
    | PEunion _
    | PEcall _ -> 
        assert false
    | PElet (CaseBase(Some sym, pat_ty), pe1, pe2) ->
        let z3_sort = cbt_to_z3 (state.ctx) pat_ty in
        let (maybe_pe1, state1) = bmc_pexpr state pe1 in

        (* Add new symbol to sym_table *)
        let pat_symbol = symbol_to_z3 state.ctx sym in
        let expr_pat = Expr.mk_const (state.ctx) pat_symbol z3_sort in
        state1.sym_table := Pmap.add (symbol_to_int sym) expr_pat 
                                     (!(state1.sym_table));

        let (maybe_pe2, state2) = bmc_pexpr state1 pe2 in
        begin
          match maybe_pe1 with
          | Some pe -> Solver.add (state2.solver) 
                                  [ Boolean.mk_eq (state2.ctx) expr_pat pe ]
          | None -> ()
        end;
        maybe_pe2, state2
    | PElet (CaseBase(None, pat_ty), pe1, pe2) ->
        assert false
    | PElet (_, pe1, pe2) ->
        assert false
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
    
let rec bmc_expr (state: bmc_state) 
                 (Expr(annot, expr_) as expr: 'a typed_expr) =
  let (z_e, state') = match expr_ with
  | Epure _
  | Ememop _ 
  | Eaction _
  | Ecase _
  | Eskip
  | Eproc _
  | Eccall _
  | Eunseq _
  | Eindet _ 
  | Ebound _
  | End _
  | Erun _
  | Epar _
  | Ewait _ 
  | Eif _ 
  | Elet _ 
  | Easeq _ 
  | Ewseq _ ->
      assert false
  | Esseq (pat, e1, e2) ->
      assert false
  | Esave _  ->
    assert false
  in (z_e, state')


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


let bmc_file (file: 'a typed_file) =
  let initial_state = initial_bmc_state () in
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
  let (normalized_file, _) = normalize_file core_file sym_supply in
  pp_file normalized_file;

  print_string "Done normalization\n";
  bmc_file normalized_file; 

  print_string "EXIT: BMC PIPELINE \n";
