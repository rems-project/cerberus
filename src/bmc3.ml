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
    fn_to_check : sym_ty;
    ail_opt     : GenTypes.genTypeCategory AilSyntax.ail_program option;

    inline_pexpr_map : (int, typed_pexpr) Pmap.map option;
    inline_expr_map  : (int, unit typed_expr) Pmap.map option;
    fn_call_map      : (int, sym_ty) Pmap.map option;

    sym_expr_table   : (sym_ty, Expr.expr) Pmap.map option;

    expr_map         : (int, Expr.expr) Pmap.map option;
    case_guard_map   : (int, Expr.expr list) Pmap.map option;
    action_map       : (int, BmcZ3.intermediate_action) Pmap.map option;
    param_actions    : (BmcZ3.intermediate_action option) list option;
    alloc_meta       : (alloc, allocation_metadata) Pmap.map option;
    prov_syms        : (Expr.expr * (Expr.expr * Core_ctype.ctype0)) list option;

    drop_cont_map    : (int, Expr.expr) Pmap.map option;

    bindings         : (Expr.expr list) option;
    assumes          : ((Location_ocaml.t option * Expr.expr) list) option;
    vcs              : (BmcVC.vc list) option;

    ret_expr         : Expr.expr option;
    ret_bindings     : (Expr.expr list) option;

    (* Memory stuff *)
    mem_bindings     : (Expr.expr list) option;

    (* Concurrency only *)
    preexec            : preexec option;
    (*memory_module      : (module MemoryModel) option;*)
    extract_executions : (Expr.expr -> (alloc, allocation_metadata) Pmap.map option
                          -> string * string list * bool) option;
  }

  include EffMonad(struct type state = state_ty end)

  let mk_initial_state file fn_to_check ail_opt =
    { file        = file
    ; fn_to_check = fn_to_check
    ; ail_opt     = ail_opt
    ; inline_pexpr_map = None
    ; inline_expr_map  = None
    ; fn_call_map      = None
    ; sym_expr_table   = None
    ; expr_map         = None
    ; case_guard_map   = None
    ; action_map       = None
    ; param_actions    = None
    ; alloc_meta       = None
    ; prov_syms        = None
    ; drop_cont_map    = None
    ; bindings         = None
    ; assumes          = None
    ; vcs              = None
    ; ret_expr         = None
    ; ret_bindings     = None
    ; mem_bindings     = None
    ; preexec          = None
    (*; memory_module    = None*)
    ; extract_executions = None
    }

  (* ===== Transformations/analyses ==== *)
  let do_inlining : unit eff =
    get >>= fun st ->
    let initial_state = BmcInline.mk_initial st.file in
    let (file, final_state) =
      BmcInline.run initial_state (BmcInline.inline st.file st.fn_to_check) in
    bmc_debug_print 7 "Done BmcInline phase";
    put {st with file = file;
                 inline_pexpr_map = Some final_state.inline_pexpr_map;
                 inline_expr_map  = Some final_state.inline_expr_map;
                 fn_call_map      = Some final_state.fn_call_map;
        }

  let do_ssa : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcSSA.mk_initial st.file
                        (Option.get st.inline_pexpr_map)
                        (Option.get st.inline_expr_map) in
    let (file, final_state) =
      BmcSSA.run initial_state (BmcSSA.ssa st.file st.fn_to_check) in

    bmc_debug_print 7 "Done BmcSSA phase";
    put {st with file = file;
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
    bmc_debug_print 7 "Done BmcZ3 phase";
    put {st with file = file;
                 expr_map       = Some final_state.expr_map;
                 case_guard_map = Some final_state.case_guard_map;
                 action_map     = Some final_state.action_map;
                 param_actions  = Some final_state.param_actions;
                 alloc_meta     = Some final_state.alloc_meta_map;
                 prov_syms      = Some final_state.prov_syms;
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

    bmc_debug_print 7 "Done BmcDropCont phase";
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
                         (Option.get st.action_map)
                         (Option.get st.alloc_meta) in
    let ((bindings, assumes), _) =
      BmcBind.run initial_state
                  (BmcBind.bind_file st.file st.fn_to_check) in
    let simplified_bindings =
      List.map (fun e -> Expr.simplify e None) bindings in
    let simplified_assumes =
      List.map (fun (loc,e) -> (loc, Expr.simplify e None)) assumes in

    bmc_debug_print 7 "Done BmcBind phase";
    put { st with bindings = Some simplified_bindings;
                  assumes  = Some simplified_assumes;
        }

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

    bmc_debug_print 7 "Done BmcVC phase";
    put { st with vcs = Some simplified_vcs}

  let do_ret_cond : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcRet.mk_initial st.file
                        (Option.get st.inline_expr_map)
                        (Option.get st.fn_call_map)
                        (Option.get st.expr_map)
                        (Option.get st.case_guard_map)
                        (Option.get st.drop_cont_map) in
    let ((ret_expr, bindings), _) =
      BmcRet.run initial_state
                 (BmcRet.do_file st.file st.fn_to_check) in
    let simplified_bindings =
      List.map (fun e -> Expr.simplify e None) bindings in

    bmc_debug_print 7 "Done BmcRet phase";
    put {st with ret_expr = Some ret_expr;
                 ret_bindings = Some simplified_bindings}

  (* Compute memory bindings using sequential mode *)
  let do_seq_mem : unit eff =
    get >>= fun st ->
    let initial_state =
      BmcSeqMem.mk_initial st.file
                           (Option.get st.inline_expr_map)
                           (Option.get st.sym_expr_table)
                           (Option.get st.expr_map)
                           (Option.get st.action_map)
                           (Option.get st.param_actions)
                           (Option.get st.case_guard_map)
                           (Option.get st.drop_cont_map)
                           (Option.get st.alloc_meta)
                           (Option.get st.prov_syms) in
    let (bindings, _) =
      BmcSeqMem.run initial_state
                    (BmcSeqMem.do_file st.file st.fn_to_check) in
    let simplified_bindings =
      List.map (fun e -> Expr.simplify e None) bindings in

    bmc_debug_print 7 "Done BmcSeqMem phase";
    put { st with mem_bindings = Some simplified_bindings }

  (* TODO: temporary for testing; get actions *)
  let do_conc_actions : unit eff =
    get >>= fun st ->
    (*let memory_module = (module C11MemoryModel : MemoryModel) in*)
    let initial_state =
      BmcConcActions.mk_initial st.file
                                (Option.get st.inline_pexpr_map)
                                (Option.get st.inline_expr_map)
                                (Option.get st.sym_expr_table)
                                (Option.get st.action_map)
                                (Option.get st.param_actions)
                                (Option.get st.case_guard_map)
                                (Option.get st.drop_cont_map)
                                (Option.get st.alloc_meta)
                                (Option.get st.prov_syms)
                                (*memory_module*) in
    let ((preexec, assertions, extract_executions), _) =
      BmcConcActions.run initial_state
                         (BmcConcActions.do_file st.file st.fn_to_check) in

    bmc_debug_print 7 "Done BmcConcActions phase";
    put { st with mem_bindings  = Some assertions;
                  preexec       = Some preexec;
                  (*memory_module = Some memory_module;*)
                  extract_executions = extract_executions;
        }

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
             (fn_to_check       : sym_ty)
             (ail_opt: GenTypes.genTypeCategory AilSyntax.ail_program option) =
  let initial_state : BmcM.state =
    BmcM.mk_initial_state file fn_to_check ail_opt in
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

    (if !!bmc_conf.concurrent_mode then
      BmcM.do_conc_actions
    else
      BmcM.do_seq_mem
    ) >>

    BmcM.get_file >>= fun file ->
    if !!bmc_conf.debug_lvl > 3 then pp_file file;
    BmcM.return () in
  let (_, final_state) = BmcM.run initial_state all_phases in
  (* Print bindings *)

  if !!bmc_conf.debug_lvl >= 5 then begin
    print_endline "====BINDINGS";
    List.iter (fun e -> print_endline (Expr.to_string e))
              (Option.get final_state.bindings);
    print_endline "====VCS";
    List.iter (fun (e, _) -> print_endline (Expr.to_string e))
              (Option.get final_state.vcs);
    print_endline "====MEM_BINDINGS";
    List.iter (fun e -> print_endline (Expr.to_string e))
              (Option.get final_state.mem_bindings);
    print_endline "====RET_BINDINGS";
    List.iter (fun e -> print_endline (Expr.to_string e))
              (Option.get final_state.ret_bindings);
  end;
  (* TODO: Output this in the dot graph *)
  if !!bmc_conf.debug_lvl > 3 then
  ( print_endline "====ALLOCATION PREFIXES";
    Pmap.iter (fun alloc meta ->
      printf "%d: %s\n" alloc (prefix_to_string (get_metadata_prefix meta)))
      (Option.get final_state.alloc_meta)
  );

  bmc_debug_print 3 "ADDING BINDINGS";
  (* Add bindings *)
  Solver.add g_solver (Option.get final_state.bindings);
  Solver.add g_solver (Option.get final_state.ret_bindings);
  Solver.push g_solver;
  bmc_debug_print 3 "START FIRST CHECK WITHOUT MEMORY ACTIONS";
  begin match Solver.check g_solver [] with
  | SATISFIABLE ->
      bmc_debug_print 1 "Checkpoint passed: bindings w/o mem constraints are SAT"
  | UNSATISFIABLE ->
      failwith ("ERROR: Bindings unsatisfiable. Should always be sat.")
  | UNKNOWN ->
      failwith (sprintf "ERROR: status unknown. Reason: %s"
                        (Solver.get_reason_unknown g_solver))
  end;
  Solver.add g_solver (Option.get final_state.mem_bindings);
  bmc_debug_print 3 "START FIRST CHECK WITH MEMORY ACTIONS";
  begin match Solver.check g_solver [] with
  | SATISFIABLE ->
      bmc_debug_print 1 "Checkpoint passed: bindings are SAT"
  | UNSATISFIABLE ->
      failwith ("ERROR: Bindings unsatisfiable. Should always be sat.")
  | UNKNOWN ->
      failwith (sprintf "ERROR: status unknown. Reason: %s"
                        (Solver.get_reason_unknown g_solver))
  end;
  (* Add __BMC_ASSUMES *)
  let (constraints, bool_constants) =
    let assumes = Option.get final_state.assumes in
    (List.map snd assumes
    ,List.map (fun (loc_opt,_) ->
        let loc_string = match loc_opt with
                         | Some loc -> Location_ocaml.location_to_string loc
                         | None -> "unknown_location"  in
        mk_fresh_const loc_string boolean_sort) assumes
    ) in
  Solver.assert_and_track_l g_solver constraints bool_constants;

  let error_opt =
    begin match Solver.check g_solver [] with
    | SATISFIABLE ->
        bmc_debug_print 1 "Checkpoint passed: assumes are SAT";
        None
    | UNSATISFIABLE ->
        let unsat_core = Solver.get_unsat_core g_solver in
        (* TODO: Lazy hack to pretty print strings *)
        let unsat_locations = List.map (fun e ->
          let e_str = Expr.to_string e in
          let r_index = String.rindex_opt e_str '!' in
          let l_index = String.index_opt e_str '|' in
          match (l_index, r_index) with
          | Some l, Some r ->
              String.sub e_str (l+1) (r - l - 1)
          | _ -> e_str
        ) unsat_core in
        let error_msg = (sprintf "The __BMC_ASSUMEs at [%s] cannot be true."
                                 (String.concat "," unsat_locations)) in
        print_endline error_msg;
        Some (`Unknown error_msg)
    | UNKNOWN ->
        let error_msg = sprintf "ERROR: status unknown. Reason %s"
                        (Solver.get_reason_unknown g_solver) in
        Some (`Unknown error_msg)
    end
  in
  (* TODO: Do this in a nicer way (option monad!) *)
  if is_some error_opt then
    Option.get error_opt (* Exit cleanly *)
  else begin
    let model = Option.get (Solver.get_model g_solver) in
    (if (!!bmc_conf.debug_lvl >= 7) then
      begin
        print_endline "BINDING MODEL:";
        print_endline (Model.to_string model)
      end);
    let ret_value = Model.eval model (Option.get final_state.ret_expr) false in
    (* Extract executions *)
    let (exec_output_str, dots, race_free) =
      (if !!bmc_conf.concurrent_mode && !!bmc_conf.find_all_execs &&
          (is_some final_state.extract_executions) then
        (Option.get final_state.extract_executions) (*g_solver
                                  (Option.get final_state.memory_model)*)
                                  (Option.get final_state.ret_expr)
                                  (final_state.alloc_meta)
       else
        ("",[], true))
    in
    (* Check for races *)
    if not race_free then
      begin
      (* We can skip the VC check; races are UB *)
      (* TODO: give more informative output *)
      print_endline "Error(s) found:";
      let output = "UB found: race exists" in
      print_endline output;
      `Satisfiable(output, dots)
      end
    else begin
      (* Actually check for VCS *)
      let vcs = List.map fst (Option.get final_state.vcs) in
      Solver.assert_and_track
        g_solver
        (Expr.simplify (mk_not (mk_and vcs)) None)
        (Expr.mk_fresh_const g_ctx "negated_vcs" boolean_sort);
      bmc_debug_print 1 "==== Checking VCS";
      begin match Solver.check g_solver [] with
      | SATISFIABLE ->
        begin
          print_endline "Error(s) found:";
          let model = Option.get (Solver.get_model g_solver) in
          let str_model = Model.to_string model in
          let satisfied_vcs =
            BmcM.find_satisfied_vcs model (Option.get final_state.vcs) in

          let vc_str = String.concat "\n"
              (List.map (fun (expr, dbg) -> BmcVC.vc_debug_to_str dbg)
                        satisfied_vcs) in
          print_endline vc_str;

          if !!bmc_conf.output_model then
            begin
            print_endline str_model;
            (* TODO: print this out independently of --bmc_output_model*)
            end;
        let output = sprintf "UB found:\n%s\n\n%s\n\nModel:\n%s" vc_str exec_output_str str_model in

        `Satisfiable (output, dots)
        end
      | UNSATISFIABLE ->
          print_endline "No errors found. :)";
          assert (is_some ret_value);
          (* TODO: there could be multiple return values ... *)
          let str_ret_value =
            if (List.length dots > 0) then
              exec_output_str
            else
              (let ret = sprintf "Possible return value: %s\n" (Expr.to_string (Option.get ret_value)) in
               print_endline ret; ret) in

          (*let str_ret_value = Expr.to_string (Option.get ret_value) in
          printf "Possible return value: %s\n" str_ret_value;*)
          `Unsatisfiable (str_ret_value, dots)
      | UNKNOWN ->
          let str_error = Solver.get_reason_unknown g_solver in
          printf "OUTPUT: unknown. Reason: %s\n" str_error;
          `Unknown str_error
      end
    end
  end

(* Find f_name in function map, returning the Core symbol *)
let find_function (f_name: string)
                  (fun_map: unit typed_fun_map) =
  let is_f_name = (fun (sym, decl) ->
      match sym with
      | Sym.Symbol(_, i, Some s) -> String.equal s f_name
      | _ -> false
    ) in
  match (List.find_opt is_f_name (Pmap.bindings_list fun_map)) with
  | Some (sym, _) -> sym
  | None -> failwith ("ERROR: file does not have the function " ^ f_name)

(* Main bmc function: typechecks and sequentialises file.
 * The symbol supply is used to ensure fresh symbols when renaming.
 *)
let bmc (core_file  : unit file)
        (ail_opt    : GenTypes.genTypeCategory AilSyntax.ail_program option) =
  match Core_typing.typecheck_program core_file with
  | Result typed_core -> begin
      let t = Sys.time() in
      let core_to_check =
          if !!bmc_conf.sequentialise then
            Core_sequentialise.sequentialise_file typed_core
          else
            typed_core in
        if !!bmc_conf.debug_lvl > 3 then
          pp_file core_to_check;

        bmc_debug_print 1 "START: model checking";
        let fn_sym = find_function !!bmc_conf.fn_to_check core_to_check.funs in
        let ret = bmc_file core_to_check fn_sym ail_opt in
        bmc_debug_print 1 (sprintf "BMC execution time: %fs\n"
                                   (Sys.time() -. t));
        ret
    end
    | Exception msg ->
        let str_err = Pp_errors.to_string msg in
        printf "Typechecking error: %s\n" str_err;
        `Unknown str_err
