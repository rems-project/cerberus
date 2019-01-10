open Bmc_common
open Bmc_conc
open Bmc_globals
open Bmc_monad
open Bmc_sorts
open Bmc_substitute
open Bmc_types
open Bmc_utils
open Z3
open Z3.Arithmetic

open AilTypes
open Annot
open Core
open Core_aux
open Ocaml_mem
open Printf
open Util

open Bmc_incremental

module BmcM = struct
  type state_ty = {
    file        : unit typed_file;
    sym_supply  : sym_supply_ty;
    fn_to_check : sym_ty;
    ail_opt     : GenTypes.genTypeCategory AilSyntax.ail_program option;

    inline_pexpr_map : (int, typed_pexpr) Pmap.map option;
    inline_expr_map  : (int, unit typed_expr) Pmap.map option;

    sym_expr_table   : (sym_ty, Expr.expr) Pmap.map option;

    expr_map         : (int, Expr.expr) Pmap.map option;
    case_guard_map   : (int, Expr.expr list) Pmap.map option;
    action_map       : (int, BmcZ3.intermediate_action) Pmap.map option;

    drop_cont_map    : (int, Expr.expr) Pmap.map option;

    bindings         : (Expr.expr list) option;
    vcs              : (BmcVC.vc list) option;

    ret_expr         : Expr.expr option;
    ret_bindings     : (Expr.expr list) option;

    (* Memory stuff *)
    mem_bindings     : (Expr.expr list) option;
  }

  include EffMonad(struct type state = state_ty end)

  let mk_initial_state file sym_supply fn_to_check ail_opt =
    { file        = file
    ; sym_supply  = sym_supply
    ; fn_to_check = fn_to_check
    ; ail_opt     = ail_opt
    ; inline_pexpr_map = None
    ; inline_expr_map  = None
    ; sym_expr_table   = None
    ; expr_map         = None
    ; case_guard_map   = None
    ; action_map       = None
    ; drop_cont_map    = None
    ; bindings         = None
    ; vcs              = None
    ; ret_expr         = None
    ; ret_bindings     = None
    ; mem_bindings     = None
    }

  (* ===== Transformations/analyses ==== *)
  let do_inlining : unit eff =
    get >>= fun st ->
    let initial_state = BmcInline.mk_initial st.file in
    let (file, final_state) =
      BmcInline.run initial_state (BmcInline.inline st.file st.fn_to_check) in
    put {st with file = file;
                 inline_pexpr_map = Some final_state.inline_pexpr_map;
                 inline_expr_map = Some final_state.inline_expr_map}

  let do_ssa : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcSSA.mk_initial st.sym_supply st.file
                        (Option.get st.inline_pexpr_map)
                        (Option.get st.inline_expr_map) in
    let (file, final_state) =
      BmcSSA.run initial_state (BmcSSA.ssa st.file st.fn_to_check) in
    put {st with file = file;
                 sym_supply = final_state.sym_supply;
                 inline_pexpr_map = Some final_state.inline_pexpr_map;
                 inline_expr_map  = Some final_state.inline_expr_map;
                 sym_expr_table   = Some final_state.sym_expr_table;
        }

  (* Convert to SMT expressions *)
  let do_z3 : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcZ3.mk_initial st.file
                      (Option.get st.inline_pexpr_map)
                      (Option.get st.inline_expr_map)
                      (Option.get st.sym_expr_table) in
    let (file, final_state) =
      BmcZ3.run initial_state (BmcZ3.z3_file st.file st.fn_to_check) in
    put {st with file = file;
                 expr_map       = Some final_state.expr_map;
                 case_guard_map = Some final_state.case_guard_map;
                 action_map     = Some final_state.action_map;
        }

  (* Compute drop continuation table *)
  let do_drop_cont : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcDropCont.mk_initial (Option.get st.inline_pexpr_map)
                             (Option.get st.inline_expr_map)
                             (Option.get st.case_guard_map) in
    let (_, final_state) =
      BmcDropCont.run initial_state
                      (BmcDropCont.drop_cont_file st.file st.fn_to_check) in
    put {st with drop_cont_map = Some final_state.drop_cont_map}


  (* Compute let bindings *)
  let do_bindings : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcBind.mk_initial (Option.get st.inline_pexpr_map)
                         (Option.get st.inline_expr_map)
                         (Option.get st.sym_expr_table)
                         (Option.get st.case_guard_map)
                         (Option.get st.expr_map)
                         (Option.get st.action_map) in
    let (bindings, _) =
      BmcBind.run initial_state
                  (BmcBind.bind_file st.file st.fn_to_check) in
    let simplified_bindings =
      List.map (fun e -> Expr.simplify e None) bindings in

    put { st with bindings = Some simplified_bindings }

  (* Compute verification conditions *)
  let do_vcs : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcVC.mk_initial (Option.get st.inline_pexpr_map)
                       (Option.get st.inline_expr_map)
                       (Option.get st.sym_expr_table)
                       (Option.get st.case_guard_map)
                       (Option.get st.expr_map)
                       (Option.get st.action_map)
                       (Option.get st.drop_cont_map) in
    let (vcs, _) =
      BmcVC.run initial_state
                (BmcVC.vcs_file st.file st.fn_to_check) in
    let simplified_vcs =
      List.map (fun (e, dbg) -> (Expr.simplify e None, dbg)) vcs in

    put { st with vcs = Some simplified_vcs}

  let do_ret_cond : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcRet.mk_initial (Option.get st.inline_expr_map)
                        (Option.get st.expr_map)
                        (Option.get st.case_guard_map)
                        (Option.get st.drop_cont_map) in
    let ((ret_expr, bindings), _) =
      BmcRet.run initial_state
                 (BmcRet.do_file st.file st.fn_to_check) in
    let simplified_bindings =
      List.map (fun e -> Expr.simplify e None) bindings in
    put {st with ret_expr = Some ret_expr;
                 ret_bindings = Some simplified_bindings}

  (* Compute memory bindings using sequential mode *)
  let do_seq_mem : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcSeqMem.mk_initial (Option.get st.inline_expr_map)
                           (Option.get st.expr_map)
                           (Option.get st.action_map)
                           (Option.get st.case_guard_map)
                           (Option.get st.drop_cont_map) in
    let (bindings, _) =
      BmcSeqMem.run initial_state
                    (BmcSeqMem.do_file st.file st.fn_to_check) in
    let simplified_bindings =
      List.map (fun e -> Expr.simplify e None) bindings in
    put { st with mem_bindings = Some simplified_bindings }

  (* TODO: temporary for testing; get actions *)
  let do_conc_actions : (bmc_action list * aid_rel list ) eff =
    get >>= fun st ->
    let initial_state =
      BmcConcActions.mk_initial (Option.get st.inline_expr_map)
                                (Option.get st.expr_map)
                                (Option.get st.action_map)
                                (Option.get st.case_guard_map)
                                (Option.get st.drop_cont_map) in
    let ((actions, po, assertions), _) =
      BmcConcActions.run initial_state
                         (BmcConcActions.do_file st.file st.fn_to_check) in
    put { st with mem_bindings = Some assertions } >>
    return (actions, po)

  (* ===== Getters/setters ===== *)
  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file

  (* ===== Extract stuff from model *)
  let find_satisfied_vcs (model: Model.model) (vcs: BmcVC.vc list)
                         : BmcVC.vc list =
    List.filter (fun (expr, dbg) ->
      match Model.eval model expr false with
      | Some b -> Boolean.is_false b
      | None -> assert false
    ) vcs
end

let initialise_solver (solver: Solver.solver) =
  bmc_debug_print 1 "Initialising solver.";
  Solver.add solver ImplFunctions.all_asserts;
  let params = Params.mk_params g_ctx in
  Params.add_bool params (mk_sym "macro_finder") g_macro_finder;
  Solver.set_parameters solver params

let bmc_file (file              : unit typed_file)
             (sym_supply        : sym_supply_ty)
             (fn_to_check       : sym_ty)
             (ail_opt: GenTypes.genTypeCategory AilSyntax.ail_program option) =
  let initial_state : BmcM.state =
    BmcM.mk_initial_state file sym_supply fn_to_check ail_opt in
  initialise_solver g_solver;
  let (>>=) = BmcM.(>>=) in
  let (>>) = BmcM.(>>) in

  let all_phases =
    BmcM.do_inlining  >>
    BmcM.do_ssa       >>
    BmcM.do_z3        >>
    BmcM.do_drop_cont >>
    BmcM.do_bindings  >>
    BmcM.do_vcs       >>
    BmcM.do_ret_cond  >>
    (*BmcM.do_seq_mem   >>*)

    (* TODO: temporary *)
    BmcM.do_conc_actions >>= fun (actions,po) ->
    List.iter (fun a -> print_endline (pp_bmcaction a)) actions;
    print_endline "PROGRAM ORDER";
    List.iter (fun (a,b) -> printf "%d,%d\n" a b) po;

    BmcM.get_file >>= fun file ->
    if !!bmc_conf.debug_lvl >= 3 then pp_file file;
    BmcM.return () in
  let (_, final_state) = BmcM.run initial_state all_phases in
  (* Print bindings *)
  bmc_debug_print 5 "====BINDINGS";
  List.iter (fun e -> bmc_debug_print 5 (Expr.to_string e))
            (Option.get final_state.bindings);
  bmc_debug_print 5 "====VCS";
  List.iter (fun (e, _) -> bmc_debug_print 5 (Expr.to_string e))
            (Option.get final_state.vcs);
  bmc_debug_print 5 "====MEM_BINDINGS";
  List.iter (fun e -> bmc_debug_print 5 (Expr.to_string e))
            (Option.get final_state.mem_bindings);
  bmc_debug_print 5 "====RET_BINDINGS";
  List.iter (fun e -> bmc_debug_print 5 (Expr.to_string e))
            (Option.get final_state.ret_bindings);

  (* Add bindings *)
  Solver.add g_solver (Option.get final_state.bindings);
  Solver.add g_solver (Option.get final_state.mem_bindings);
  Solver.add g_solver (Option.get final_state.ret_bindings);
  let ret_value =
    begin match Solver.check g_solver [] with
    | SATISFIABLE ->
        print_endline "Checkpoint passed: bindings are SAT";
        let model = Option.get (Solver.get_model g_solver) in
        Model.eval model (Option.get final_state.ret_expr) false
    | UNSATISFIABLE ->
        failwith "ERROR: Bindings unsatisfiable. Should always be sat."
    | UNKNOWN ->
        failwith (sprintf "ERROR: status unknown. Reason: %s"
                          (Solver.get_reason_unknown g_solver))
    end in

  let vcs = List.map fst (Option.get final_state.vcs) in
  Solver.assert_and_track
    g_solver
    (Expr.simplify (mk_not (mk_and vcs)) None)
    (Expr.mk_fresh_const g_ctx "negated_vcs" boolean_sort);
  bmc_debug_print 1 "==== Checking VCS";
  begin match Solver.check g_solver [] with
  | SATISFIABLE ->
      begin
      print_endline "OUTPUT: satisfiable";
      if !!bmc_conf.output_model then
        begin
        let model = Option.get (Solver.get_model g_solver) in
        print_endline (Model.to_string model);
        (* TODO: print this out independently of --bmc_output_model*)
        let satisfied_vcs =
          BmcM.find_satisfied_vcs model (Option.get final_state.vcs) in
        List.iter (fun (expr, dbg) ->
          printf "%s: %s\n" (BmcVC.vc_debug_to_str dbg) (Expr.to_string expr)
        ) satisfied_vcs;
        end
      end
  | UNSATISFIABLE ->
      print_endline "OUTPUT: unsatisfiable! No errors found. :)";
      assert (is_some ret_value);
      printf "Return value: %s\n" (Expr.to_string (Option.get ret_value))
  | UNKNOWN ->
      printf "OUTPUT: unknown. Reason: %s\n"
             (Solver.get_reason_unknown g_solver)
  end

(* Find f_name in function map, returning the Core symbol *)
let find_function (f_name: string)
                  (fun_map: unit typed_fun_map) =
  let is_f_name = (fun (sym, decl) ->
      match sym with
      | Sym.Symbol(i, Some s) -> String.equal s f_name
      | _ -> false
    ) in
  match (List.find_opt is_f_name (Pmap.bindings_list fun_map)) with
  | Some (sym, _) -> sym
  | None -> failwith ("ERROR: file does not have the function " ^ f_name)

(* Main bmc function: typechecks and sequentialises file.
 * The symbol supply is used to ensure fresh symbols when renaming.
 *)
let bmc (core_file  : unit file)
        (sym_supply : sym_supply_ty)
        (ail_opt    : GenTypes.genTypeCategory AilSyntax.ail_program option) =
  match Core_typing.typecheck_program core_file with
  | Result typed_core -> begin
      let core_to_check =
          if !!bmc_conf.sequentialise then
            Core_sequentialise.sequentialise_file typed_core
          else
            typed_core in
        if !!bmc_conf.debug_lvl >= 2 then
          pp_file core_to_check;

        bmc_debug_print 1 "START: model checking";
        let fn_sym = find_function !!bmc_conf.fn_to_check core_to_check.funs in
        bmc_file core_to_check sym_supply fn_sym ail_opt
    end
    | Exception msg ->
        printf "Typechecking error: %s\n" (Pp_errors.to_string msg)
