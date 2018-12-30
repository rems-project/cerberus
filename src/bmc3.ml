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

    bindings         : (Expr.expr list) option;
    vcs              : (BmcVC.vc list) option;
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
    ; bindings         = None
    ; vcs              = None
    }

  (* ===== Transformations/analyses ==== *)
  let do_inlining : unit eff =
    get >>= fun st ->
    let initial_state = BmcInline.mk_initial st.file in
    let (file, final_state) =
      BmcInline.run initial_state (BmcInline.inline st.file st.fn_to_check) in
    put {st with file = file;
                 inline_pexpr_map = Some (final_state.inline_pexpr_map);
                 inline_expr_map = Some (final_state.inline_expr_map)}

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
                       (Option.get st.action_map) in
    let (vcs, _) =
      BmcVC.run initial_state
                (BmcVC.vcs_file st.file st.fn_to_check) in
    let simplified_vcs =
      List.map (fun (e, dbg) -> (Expr.simplify e None, dbg)) vcs in

    put { st with vcs = Some simplified_vcs}

  (* ===== Getters/setters ===== *)
  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file
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
    BmcM.do_inlining >>
    BmcM.do_ssa      >>
    BmcM.do_z3       >>
    BmcM.do_bindings >>
    BmcM.get_file >>= fun file ->
    pp_file file;
    BmcM.do_vcs      >>
    BmcM.return () in
  let (_, final_state) = BmcM.run initial_state all_phases in
  (* Print bindings *)
  print_endline "====BINDINGS";
  List.iter print_expr (Option.get final_state.bindings);
  print_endline "====VCS";
  List.iter (fun (e, _) -> print_expr e) (Option.get final_state.vcs);
  assert false

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
