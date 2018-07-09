open Bmc_utils
open Z3
open Z3.Arithmetic
open Z3.Boolean

open Core
open Ocaml_mem 
open Printf

(* =========== GLOBALS =========== *)

(* Z3 context config *)
let g_z3_ctx_cfg = [ ("model", "true")  (* Generate model *)
                   ; ("proof", "false") (* Disable proof generation *)
                   ]
let g_ctx = mk_context g_z3_ctx_cfg

let g_z3_solver_logic_opt = None        (* Logic used by the solver *)
let g_solver      = Solver.mk_solver g_ctx g_z3_solver_logic_opt

(* true => use bit vector representation *)
let g_bv = false

(* =========== TYPES =========== *)
type bmc_ret = {
  expr              : Expr.expr;
  assume            : Expr.expr list;
  vcs               : Expr.expr list;
}

(* =========== PPRINTERS =========== *)
let pp_bmc_ret (bmc_ret: bmc_ret) =
  sprintf ">>Expr: %s\n>>Assume:%s\n>>VCs:%s\n"
          (Expr.to_string bmc_ret.expr)
          (List.fold_left (fun s expr -> s ^ "\n>>>>" ^ (Expr.to_string expr))
                          "" bmc_ret.assume
          )
          (List.fold_left (fun s expr -> s ^ "\n>>>>" ^ (Expr.to_string expr))
                          "" bmc_ret.vcs
          )

(* =========== SOME MONAD FUN =========== *)

module BmcM = struct
  type sym_table_ty = (sym_ty, Expr.expr) Pmap.map

  type bmc_state = {
    file         : unit typed_file;
    sym_supply   : sym_supply_ty;

    sym_table    : sym_table_ty;
  }


  (* =========== MONADIC FUNCTIONS =========== *)
  type 'a eff =
    Eff of (bmc_state -> 'a * bmc_state)

  let return (a: 't) : 't eff = Eff (fun st -> (a, st))

  let bind ((Eff ma): 'a eff) (f: 'a -> 'b eff) : 'b eff =
    Eff begin
      fun st ->
        let (a, st') = ma st in
        let Eff mb = f a in
        mb st'
    end

  let (>>=) = bind

  let (>>) m m' = bind m (fun _ -> bind m' (fun x' -> return x'))

  let run : bmc_state -> 'a eff -> 'a * bmc_state =
    fun st (Eff ma) -> ma st

  let sequence ms =
    List.fold_right (
      fun m m' -> 
      m  >>= fun x  -> 
      m' >>= fun xs ->
      return (x :: xs)
    ) ms (return [])

  let sequence_ ms = List.fold_right (>>) ms (return ())
  let mapM  f ms = sequence (List.map f ms)
  let mapM_ f ms = sequence_ (List.map f ms)

  let get : bmc_state eff =
    Eff (fun st -> (st, st))

  let put (st' : bmc_state) : unit eff =
    Eff (fun _ -> ((), st'))


  (* =========== STATE ACCESSORS =========== *)
  let get_sym_table : sym_table_ty eff =
    get >>= fun st -> return st.sym_table

  let lookup_sym (sym: sym_ty) : Expr.expr eff =
    get_sym_table >>= fun sym_table ->
    return (Pmap.find sym sym_table)

  let update_sym_table new_table : unit eff =
    get >>= fun st ->
      put {st with sym_table = new_table}

  let add_sym_to_sym_table (sym: sym_ty) (expr: Expr.expr) 
                           : unit eff =
    get_sym_table >>= fun sym_table ->
    update_sym_table (Pmap.add sym expr sym_table)


  (* =========== STATE INIT =========== *)
  let mk_initial_state (file       : unit typed_file)  
                       (sym_supply : sym_supply_ty)
                       : bmc_state =
    { file        = file
    ; sym_supply  = sym_supply

    ; sym_table   = Pmap.empty sym_cmp
    }
end

let (>>=) = BmcM.bind


(* =========== CUSTOM SORTS =========== *)
module UnitSort = struct
  let mk_sort = 
    Datatype.mk_sort_s g_ctx "unit"
      [ Datatype.mk_constructor_s g_ctx "unit" 
                                  (Symbol.mk_string g_ctx "isUnit")
                                  [] [] []
      ]

  let mk_unit =
    let constructors = Datatype.get_constructors mk_sort in
    Expr.mk_app g_ctx (List.hd constructors) []

end


(* =========== CORE TYPES -> Z3 SORTS =========== *)
let cot_to_z3 (cot: core_object_type) : Sort.sort =
  match cot with
  | OTy_integer ->
      if g_bv then assert false
      else Integer.mk_sort g_ctx
  | OTy_pointer -> assert false
  | OTy_floating 
  | OTy_array _
  | OTy_struct _
  | OTy_cfunction _ 
  | OTy_union _ ->
      assert false

let cbt_to_z3 (cbt: core_base_type) : Sort.sort =
  match cbt with
  | BTy_unit    -> UnitSort.mk_sort
  | BTy_boolean -> Boolean.mk_sort g_ctx
  | BTy_ctype ->
      assert false
  | BTy_list _ -> assert false
  | BTy_tuple cbt_list ->
      assert false
  | BTy_object obj_type ->
      cot_to_z3 obj_type
  | BTy_loaded obj_type ->
      assert false

let binop_to_z3 (binop: binop) (arg1: Expr.expr) (arg2: Expr.expr)
                : Expr.expr =
  if g_bv then assert false
  else begin
    match binop with
    | OpAdd   -> Arithmetic.mk_add g_ctx [arg1; arg2]
    | OpSub   -> Arithmetic.mk_sub g_ctx [arg1; arg2]
    | OpMul   -> Arithmetic.mk_mul g_ctx [arg1; arg2]
    | OpDiv   -> Arithmetic.mk_div g_ctx arg1 arg2
    | OpRem_t -> assert false
    | OpRem_f -> assert false
    | OpExp   -> assert false
    | OpEq    -> mk_eq g_ctx arg1 arg2
    | OpLt    -> Arithmetic.mk_lt g_ctx arg1 arg2
    | OpLe    -> Arithmetic.mk_le g_ctx arg1 arg2
    | OpGt    -> Arithmetic.mk_gt g_ctx arg1 arg2
    | OpGe    -> Arithmetic.mk_ge g_ctx arg1 arg2
    | OpAnd   -> mk_and g_ctx [arg1; arg2]
    | OpOr    -> mk_or  g_ctx [arg1; arg2]
  end

let integer_value_to_z3 (ival: Ocaml_mem.integer_value) : Expr.expr =
  (* TODO: check which is the correct ival->big num function *)
  match eval_integer_value ival with
  | None -> assert false
  | Some i ->
      if g_bv then
        assert false
      else
        Integer.mk_numeral_s g_ctx (Nat_big_num.to_string i)


let object_value_to_z3 (oval: object_value) : Expr.expr =
  match oval with
  | OVinteger ival -> integer_value_to_z3 ival
  | OVfloating _
  | OVpointer _
  | OVcfunction _
  | OVarray _
  | OVstruct _
  | OVunion _
  | OVcomposite _ ->
      assert false

let value_to_z3 (value: value)
                : Expr.expr =
  match value with
  | Vunit  -> UnitSort.mk_unit
  | Vtrue  -> mk_true g_ctx
  | Vfalse -> mk_false g_ctx
  | Vlist _
  | Vtuple _
  | Vctype _ ->
      assert false
  | Vobject oval ->
      object_value_to_z3 oval
  | Vloaded _ ->
      assert false


(* =========== SYMBOL TABLE MAINTENANCE FUNCTIONS =========== *)
let symbol_to_fresh_z3_const (sym: ksym) (sort: Sort.sort) : Expr.expr =
  Expr.mk_fresh_const g_ctx (symbol_to_string sym) sort

let add_sym_to_sym_table (sym: ksym) (ty: core_base_type) 
                         : unit BmcM.eff =
  let z3_sort = cbt_to_z3 ty in
  let z3_sym = symbol_to_fresh_z3_const sym z3_sort in
  BmcM.add_sym_to_sym_table sym z3_sym

let initialise_param ((sym, ty) : sym_ty * core_base_type) 
                     : unit BmcM.eff =
  assert (not (is_core_ptr_bty ty));
  dprintf "Initialising param: %s %s\n" 
          (symbol_to_string sym) 
          (pp_to_string (Pp_core.Basic.pp_core_base_type ty));
  (* TODO: do not handle pointers for now.
   *       Pointers: need to do a create maybe. *)
  add_sym_to_sym_table sym ty

let rec add_pattern_to_sym_table (pattern: typed_pattern) 
                                 : unit BmcM.eff =
  match pattern with
  | CaseBase(None, _) -> 
      BmcM.return () (* Do nothing; wildcard => no symbol *)
  | CaseBase(Some sym, ty) ->
      add_sym_to_sym_table sym ty
  | CaseCtor _ ->
      assert false

(* =========== Z3 LET BINDINGS =========== *)
let mk_let_binding (maybe_sym: sym_ty option)
                   (expr: Expr.expr) 
                   : Expr.expr BmcM.eff =
  match maybe_sym with
  | None -> BmcM.return (mk_true g_ctx)
  | Some sym -> 
      BmcM.lookup_sym sym >>= fun sym_expr ->
      BmcM.return (mk_eq g_ctx sym_expr expr)

let rec mk_let_bindings (pat: typed_pattern) (expr: Expr.expr) 
                        : Expr.expr BmcM.eff =
  match pat with
  | CaseBase(maybe_sym, _) ->
      mk_let_binding maybe_sym expr
  | CaseCtor(_, _) ->
      assert false

(* =========== MODEL CHECKING FUNCTIONS =========== *)
let rec bmc_pexpr (Pexpr(annot, bTy, pe) as pexpr: typed_pexpr) :
                  bmc_ret BmcM.eff =
  match pe with
  | PEsym sym ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      BmcM.return { expr   = sym_expr
                  ; assume = []
                  ; vcs    = []
                  }
  | PEimpl _ ->
      assert false
  | PEval cval ->
      BmcM.return { expr        = value_to_z3 cval 
                  ; assume      = []
                  ; vcs         = [] 
                  }
  | PEconstrained _
  | PEundef _
  | PEerror _
  | PEctor _
  | PEcase _
  | PEarray_shift _
  | PEmember_shift _
  | PEmemberof _ 
  | PEnot _ ->
      assert false
  | PEop (binop, pe1, pe2) ->
      bmc_pexpr pe1 >>= fun res1 ->
      bmc_pexpr pe2 >>= fun res2 ->
      BmcM.return { expr   = binop_to_z3 binop res1.expr res2.expr 
                  ; assume = res1.assume @ res2.assume
                  ; vcs    = res1.vcs @ res2.vcs
                  }
  | PEstruct _
  | PEunion _
  | PEcall _ ->
      assert false
  | PElet (pat, pe1, pe2) ->
      bmc_pexpr pe1                 >>= fun res1 ->
      add_pattern_to_sym_table pat  >>= fun () ->
      mk_let_bindings pat res1.expr >>= fun let_binding ->
      bmc_pexpr pe2                 >>= fun res2 ->
      BmcM.return { expr    = res2.expr
                  ; assume  = let_binding::(res1.assume @ res2.assume)
                  ; vcs     = res1.vcs @ res2.vcs
                  } 
  | PEif _
  | PEis_scalar _
  | PEis_integer _ 
  | PEis_signed _
  | PEis_unsigned _ ->
      assert false


let bmc_file (file              : unit typed_file)
             (sym_supply        : sym_supply_ty)
             (function_to_check : sym_ty) =
  (* Create an initial model checking state *)
  let initial_state : BmcM.bmc_state = 
    BmcM.mk_initial_state file sym_supply in

  (* TODO: temporarily assume there are no globals *)
  assert (List.length file.globs = 0);

  let to_run = 
    match Pmap.lookup function_to_check file.funs with
    | Some (Proc (_, ty, params, e)) ->
        assert false

    | Some (Fun (ty, params, pe)) ->
        BmcM.mapM_ initialise_param params >>= fun () ->
        bmc_pexpr pe

    | _ -> failwith "Function to check must be a Core Proc or Fun"
  in 
  let (result, new_state) = BmcM.run initial_state to_run in

  print_endline "====FINAL BMC_RET";
  print_string (pp_bmc_ret result);

  (* TODO: assert and track based on annotation *)
  (* TODO: multiple expressions or one expression? *)

  (* Assumptions *)
  Solver.assert_and_track
    g_solver
    (Expr.simplify (mk_and g_ctx result.assume) None)
    (Expr.mk_fresh_const g_ctx "assume" (Boolean.mk_sort g_ctx));

  (* VCs *)
  Solver.assert_and_track 
    g_solver 
    (Expr.simplify (mk_not g_ctx (mk_and g_ctx result.vcs)) None)
    (Expr.mk_fresh_const g_ctx "negated_vcs" (Boolean.mk_sort g_ctx));

  print_endline "====FINAL SOLVER";
  print_endline (Solver.to_string g_solver);

  match Solver.check g_solver [] with
  | UNKNOWN ->
      printf "STATUS: unknown. Reason: %s\n" 
             (Solver.get_reason_unknown g_solver)
  | UNSATISFIABLE ->
      print_endline "STATUS: unsatisfiable :)"
  | SATISFIABLE ->
      print_endline "STATUS: satisfiable"


(* Main bmc function: typechecks and sequentialises file.
 * The symbol supply is used to ensure fresh symbols when renaming.      
 *)
let bmc (core_file  : unit file)
        (sym_supply : sym_supply_ty) = 

  match Core_typing.typecheck_program core_file with
    | Result typed_core -> 
        begin
          let sequentialised_core = 
            Core_sequentialise.sequentialise_file typed_core in

          pp_file sequentialised_core;
          bmc_debug_print 1 "START: model checking";
          match sequentialised_core.main with
          | None -> 
              (* Currently only check main function *)
              failwith "ERROR: fail does not have a main"
          | Some main_sym ->
              bmc_file sequentialised_core sym_supply main_sym
        end
    | Exception msg -> 
        printf "Typechecking error: %s\n" (Pp_errors.to_string msg)
