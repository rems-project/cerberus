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

(* TODO: Clean up modules *)
open Bmc_analysis
open Bmc_conc_types
open Bmc_events
open Bmc_globals
open Bmc_inline
open Bmc_normalize
open Bmc_pp_conc
open Bmc_saves
open Bmc_sorts
open Bmc_utils

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

  (* TODO: hack for outputting source symbols for locations *)
  src_ptr_map : (int, ksym) Pmap.map ref;

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
  (* has_returned : Expr.expr;  *)
  z3_ret       : Expr.expr;
  (* ret_asserts  : Expr.expr list; *)
  saves        : unit saves_map;
  depth        : int
}

type 'a bmc_ret = {
  expr        : Expr.expr;
  allocs      : AddressSet.t;
  vcs         : Expr.expr list;
  preexec     : preexecution;
  ret_asserts : Expr.expr list;
  returned    : Expr.expr;
  state       : 'a bmc_state
}

type exec_fns = {
  event_sort  : Sort.sort;

  event_type : Sort.sort; (* read/write *)
  read_type  : Expr.expr;
  write_type : Expr.expr;

  memorder_type : Sort.sort;
  na_order      : Expr.expr;
  seq_cst_order : Expr.expr;
  relaxed_order : Expr.expr;
  release_order : Expr.expr;
  acquire_order : Expr.expr;
  consume_order : Expr.expr;
  acq_rel_order : Expr.expr;

  asw          : FuncDecl.func_decl;
  hb           : FuncDecl.func_decl;
  mo           : FuncDecl.func_decl;
  rf           : FuncDecl.func_decl;
  sb           : FuncDecl.func_decl;
  sw           : FuncDecl.func_decl;

  (* hb, isAcq, isRel, clock, getInitial *)

  (* TODO: generalize this. Location is atomic *)
  is_atomic    : Expr.expr -> Expr.expr;

  getAddr      : FuncDecl.func_decl;
  getAid       : FuncDecl.func_decl;
  getEventType : FuncDecl.func_decl;
  getGuard     : FuncDecl.func_decl;
  getMemOrder  : FuncDecl.func_decl;
  getThread    : FuncDecl.func_decl;
  getVal       : FuncDecl.func_decl;

  (* Race assertions *)
  unseq_race   : Expr.expr;
  data_race    : Expr.expr;
}

type model_execution = {
  preexecution : pre_execution;
  witness      : execution_witness;
  derived_data : execution_derived_data;
  
  z3_asserts   : Expr.expr;

  retOpt       : Expr.expr option;
}
let get_memorder (memorder : Expr.expr) (fns : exec_fns) =
  if (Expr.equal memorder fns.na_order) then
    NA
  else if (Expr.equal memorder fns.seq_cst_order) then
    Seq_cst
  else if (Expr.equal memorder fns.relaxed_order) then
    Relaxed
  else if (Expr.equal memorder fns.release_order) then
    Release
  else if (Expr.equal memorder fns.acquire_order) then
    Acquire
  else if (Expr.equal memorder fns.consume_order) then
    Consume
  else if (Expr.equal memorder fns.acq_rel_order) then
    Acq_rel
  else
    assert false

let cartesian l l' = 
  List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)

let lbool_to_bool = function
  | Z3enums.L_TRUE -> true
  | Z3enums.L_FALSE -> false
  | _ -> assert false

let extract_executions (model: Model.model)
                       (fns : exec_fns) 
                       (ctx : context) 
                       (retOpt: Expr.expr option) 
                       (src_ptr_map : (int, ksym) Pmap.map) =  
  let apply = FuncDecl.apply in
  let events = Enumeration.get_consts fns.event_sort in

  let interp expr = 
    (match Model.eval model expr false with
     | None -> assert false
     | Some e -> e) in
  print_endline "EXTRACTING EXECUTIONS";

  let pp_value (value: Expr.expr) =
    if (Loaded.is_loaded ctx value) then
      begin
      match Expr.get_args value with
      | [v] -> 
          if (Sort.equal (Expr.get_sort v) (LoadedInteger.mk_sort ctx) &&
              Expr.is_numeral (List.hd (Expr.get_args v))) then 
            Expr.to_string (List.hd (Expr.get_args v))
          else
            Expr.to_string value
      | _ -> assert false
      end
    else
      Expr.to_string value 
  in 

  (* Get actions *)
  let all_actions = 
    List.map getOptVal
    (List.filter is_some 
      (List.map (fun event ->
        let loc = Integer.get_int (interp (apply fns.getAddr [event])) in
        let aid = Integer.get_int (interp (apply fns.getAid [event])) in
        let event_type = interp (apply fns.getEventType [ event]) in
        let guarded = Boolean.get_bool_value(interp (apply fns.getGuard [event])) in
        let memorder = get_memorder (interp (apply fns.getMemOrder [event])) fns in
        let tid = Integer.get_int (interp (apply fns.getThread [event])) in
        let value = pp_value(interp(apply fns.getVal [event])) in

        let loc_val = match Pmap.lookup loc src_ptr_map with
          | None -> ConcreteLoc loc
          | Some (Symbol(_, Some str)) -> SymbolicLoc str
          | Some _ -> ConcreteLoc loc in

        match (tid=g_initial_tid),guarded with 
        | true, _ -> None
        | _, L_TRUE -> 
            if (Expr.equal event_type fns.read_type) then
              Some (Load (aid, tid, memorder, loc_val, Flexible value))
            else if (Expr.equal event_type fns.write_type) then
              Some (Store (aid, tid, memorder, loc_val, Flexible value))
            else
              assert false
        | _, L_FALSE -> None
        | _, L_UNDEF -> assert false 
      ) events)) in

  let quadratic_actions = cartesian all_actions all_actions in

  let action_map : (action_id, action) Pmap.map = 
    List.fold_left (fun map action ->
      Pmap.add (aid_of action) action map) 
      (Pmap.empty Pervasives.compare) all_actions in

  let event_map  : (action_id, Expr.expr) Pmap.map = 
    List.fold_left (fun map event ->
      let aid = Integer.get_int (interp (apply fns.getAid [event])) in
      Pmap.add aid event map
    ) (Pmap.empty Pervasives.compare) events in

  let location_kinds = List.fold_left (fun map action ->
    let event = Pmap.find (aid_of action) event_map in
    let loc = (apply fns.getAddr [event]) in
    print_endline (Expr.to_string loc);
    match lbool_to_bool (Boolean.get_bool_value (interp (fns.is_atomic loc))) with
    | true -> 
        Pmap.add (getOptVal (loc_of action)) Atomic map
    | false ->
        Pmap.add (getOptVal (loc_of action)) Non_Atomic map
  ) (Pmap.empty Pervasives.compare) all_actions in

  let all_tids = List.fold_left (fun set action ->
    Pset.add (tid_of action) set
  ) (Pset.empty Pervasives.compare) all_actions in

  let sb = List.filter (fun (a1, a2) ->
    let event1 = Pmap.find (aid_of a1) event_map in
    let event2 = Pmap.find (aid_of a2) event_map in
    let is_sb = lbool_to_bool(Boolean.get_bool_value 
                  (interp (apply fns.sb [event1; event2]))) in
    (tid_of a1 <> g_initial_tid) &&
    (tid_of a2 <> g_initial_tid) &&
    is_sb
  ) (quadratic_actions) in

  let asw = List.filter (fun (a1, a2) ->
    let event1 = Pmap.find (aid_of a1) event_map in
    let event2 = Pmap.find (aid_of a2) event_map in
    let is_asw = lbool_to_bool (Boolean.get_bool_value 
                  (interp (apply fns.asw [event1; event2]))) in
    (tid_of a1 <> g_initial_tid) &&
    (tid_of a2 <> g_initial_tid) &&
    is_asw
  ) (quadratic_actions) in

  let hb = List.filter (fun (a1, a2) ->
    let event1 = Pmap.find (aid_of a1) event_map in
    let event2 = Pmap.find (aid_of a2) event_map in
    let is_hb = lbool_to_bool(Boolean.get_bool_value 
                  (interp (apply fns.hb [event1; event2]))) in
    (tid_of a1 <> g_initial_tid) &&
    (tid_of a2 <> g_initial_tid) &&
    is_hb
  ) (quadratic_actions) in

  let preexecution : pre_execution = 
    { actions = all_actions
    ; threads = Pset.elements all_tids
    ; lk = location_kinds
    ; sb = sb
    ; asw = asw
    } in

  pp_preexecution preexecution;

  let rf = List.map getOptVal
    (List.filter (function
     | None -> false
     | Some (a1, a2) ->
       match a2 with
       | Load _ -> true
       | _ -> false
  ) (List.map (fun a1 ->
      let event1 = Pmap.find (aid_of a1) event_map in
      let event2 = (interp (apply fns.rf [event1])) in
      let aid2 = Integer.get_int (interp (apply fns.getAid [event2])) in
      
      if (Pmap.mem aid2 action_map) then
        Some (Pmap.find aid2 action_map, a1)
      else
        None
    ) all_actions)) in

  let mo = List.filter (fun (a1, a2) ->
    let event1 = Pmap.find (aid_of a1) event_map in
    let event2 = Pmap.find (aid_of a2) event_map in
    let mo1    = Integer.get_int (interp (apply fns.mo [event1])) in
    let mo2    = Integer.get_int (interp (apply fns.mo [event2])) in
    let is_atomic = (match Pmap.find (getOptVal(loc_of a1)) location_kinds with
                     | Atomic -> true | _ -> false) in

    (tid_of a1 <> g_initial_tid) &&
    (tid_of a2 <> g_initial_tid) &&
    (loc_of a1 = loc_of a2) &&
    (is_atomic) &&
    (is_write a1 && is_write a2) &&
    (mo1 < mo2)
  ) (quadratic_actions) in

  let sw = List.filter (fun (a1, a2) ->
    let event1 = Pmap.find (aid_of a1) event_map in
    let event2 = Pmap.find (aid_of a2) event_map in
    let is_sw = lbool_to_bool(Boolean.get_bool_value 
                  (interp (apply fns.sw [event1; event2]))) in
    (tid_of a1 <> g_initial_tid) &&
    (tid_of a2 <> g_initial_tid) &&
    is_sw
  ) (quadratic_actions) in

  let witness : execution_witness = 
    { rf = rf;
      mo = mo;
    } in
  pp_witness witness;

  let guard_assert = mk_and ctx (List.map (fun event ->
    let guarded = (interp (apply fns.getGuard[event])) in
    mk_eq ctx (apply fns.getGuard[event]) guarded
  ) events) in
  let rf_assert = mk_and ctx (List.map (fun (a1,a2) ->
    let event1 = Pmap.find (aid_of a1) event_map in
    let event2 = Pmap.find (aid_of a2) event_map in
    mk_eq ctx (apply fns.rf [event2]) (event1) 
  ) rf) in
  let mo_assert = mk_and ctx (List.map (fun (a1, a2) ->
    let event1 = Pmap.find (aid_of a1) event_map in
    let event2 = Pmap.find (aid_of a2) event_map in
    mk_lt ctx (apply fns.mo [event1]) (apply fns.mo [event2]) 
  ) mo) in
  
  (* unsequenced race *)
  let unsequenced_race = List.filter (fun (a1, a2) ->
    (a1 <> a2) &&
    (loc_of a1 = loc_of a2) &&
    (is_write a1 || is_write a2) &&
    (tid_of a1 = tid_of a2) &&
    (tid_of a1 <> g_initial_tid) &&
    (not (List.exists (fun (x,y) -> 
      (x = a1 && y = a2) || (x = a2 && y = a1)) sb))
  ) quadratic_actions in

  let data_race = List.filter (fun (a1,a2) ->
    (a1 <> a2) &&
    (loc_of a1 = loc_of a2) &&
    (is_write a1 || is_write a2) &&
    (tid_of a1 <> tid_of a2) &&
    (not (is_atomic_action a1 && is_atomic_action a2)) &&
    (not (List.exists (fun(x,y) ->
      (x = a1 && y = a2) || (x = a2 && y = a1)) hb))
  ) quadratic_actions in

  let derived_data = {
    derived_relations = [
      ("sw", sw);
(*      ("hb", hb)  *)
    ];
    undefined_behaviour = [("ur", Two unsequenced_race)
                          ;("dr", Two data_race)]
    } in
  (*
  let dot_str = pp_dot () (ppmode_default_web, 
              (preexecution, Some witness, None)) in
  save_to_file g_dot_file dot_str;
  *)

  let retValueO = match retOpt with
    | None -> None
    | Some ret -> Some (interp ret) in

  let ret : model_execution =
    { preexecution = preexecution;
      witness = witness;
      derived_data = derived_data;
      z3_asserts = mk_and ctx [guard_assert; rf_assert; mo_assert];
      retOpt = retValueO
    } in
  ret

let get_all_executions (solver : Solver.solver)
                       (fns    : exec_fns)
                       (ctx    : context)
                       (retOpt : Expr.expr option) 
                       (src_ptr_map : (int, ksym) Pmap.map)
                       =
  Solver.push solver;

  let rec aux solver ret =
    if Solver.check solver [] = SATISFIABLE then
      let model = getOptVal (Solver.get_model solver) in
      let execution = extract_executions model fns ctx retOpt src_ptr_map in
      (* Assert not *)
      Solver.add solver [mk_not ctx execution.z3_asserts];
      aux solver (execution :: ret)
    else
      ret
  in 
  let execs = aux solver [] in
  let race_free = List.fold_left (fun acc exec ->
    if (List.for_all (fun (_, p) ->
            match p with
            | One _ -> true
            | Two [] -> true
            | _ -> false) exec.derived_data.undefined_behaviour) then
        acc + 1
    else acc) 0 execs in

  Printf.printf "# of consistent executions: %d\n" (List.length execs);
  Printf.printf "# race free: %d\n" (race_free);
  match retOpt with
  | None -> ();
  | Some _ ->
    List.iter (fun exec ->
      match exec.retOpt with
      | None -> ()
      | Some x -> print_string ((Expr.to_string x) ^ " ");
      ) execs;
  print_endline "";
  
  List.iteri (fun i exec ->
    let dot_str = pp_dot () (ppmode_default_web,
                      (exec.preexecution, Some exec.witness, 
                       Some (exec.derived_data))) in
    let filename = Printf.sprintf "%s_%d.dot" g_dot_file i in
    save_to_file filename dot_str;
  ) execs;

  Solver.pop solver 1



(* ========== BMC ========== *)

let check_solver_fun (solver: Solver.solver) 
                     (ret_value: Expr.expr option) =
  let status = Solver.check solver [] in
  Printf.printf "Status: %s\n" (Solver.string_of_status status);
  match status with
  | UNKNOWN ->
      Printf.printf "Unknown: %s\n" (Solver.get_reason_unknown solver);
      status
  | UNSATISFIABLE ->
      print_endline "NOT SAT :)";
      status
  | SATISFIABLE ->
    print_endline "SAT====MODEL======= :(";
    match Solver.get_model solver with
    | Some m -> 
        (* Printf.printf "Model: \n%s\n" (Model.to_string m); *)
        begin
          match ret_value with
          | None -> ()
          | Some z3_ret ->
            print_endline "RET_VALUE";
            match Model.eval m z3_ret false with
            | Some interp ->
                Printf.printf "Z3_ret: %s\n" (Expr.to_string interp)
            | None -> print_endline "No interp for ret."
        end;
        print_endline "SAT :( \n";
        status
    | None -> print_endline "No model"; status

let check_solver (solver: Solver.solver) =
  check_solver_fun solver None

let expr_is_sort (expr: Expr.expr) (sort: Sort.sort) 
                 : bool =
  Sort.equal (Expr.get_sort expr) sort

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

let ctor_to_z3 (ctx: context) (ctor: typed_ctor) 
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
        if (Sort.equal sort (LoadedInteger.mk_sort ctx)) then
          LoadedInteger.mk_loaded ctx expr
        else if (Sort.equal sort (LoadedPointer.mk_sort ctx)) then
          LoadedPointer.mk_loaded ctx expr 
        else 
          assert false
  | Cunspecified (* unspecified value *) ->
      assert (List.length pes = 1);
      let expr = List.hd pes in
      if (Sort.equal sort (LoadedInteger.mk_sort ctx)) then
        LoadedInteger.mk_unspec ctx expr
      else if (Sort.equal sort (LoadedPointer.mk_sort ctx)) then
        LoadedPointer.mk_unspec ctx expr
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
let rec cbt_to_z3 (ctx: context) (cbt : core_base_type) : Sort.sort =
  match cbt with
   | BTy_unit  -> 
        UnitSort.mk_sort ctx
   | BTy_boolean ->
        Boolean.mk_sort ctx
   | BTy_ctype -> 
        ctypeSort ctx
   | BTy_list _ -> assert false
   | BTy_tuple cbt_list ->
        let sort_to_string = fun t -> pp_to_string
                              (Pp_core.Basic.pp_core_base_type t) in
        let sort_name = sort_to_string cbt in
        let sort_symbol = mk_sym ctx sort_name in

        let sym_list = List.mapi 
            (fun i _ -> mk_sym ctx 
                  ( "#" ^ (string_of_int i)))
            cbt_list in
        let sort_list = List.map (fun t -> cbt_to_z3 ctx t) cbt_list in
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
  let z3_sort = cbt_to_z3 state.ctx ty in
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
    src_ptr_map = ref (Pmap.empty Pervasives.compare);
    (* heap = Pmap.empty Pervasives.compare; *)
    alias_state = initial_analysis_state ();

    fn_map = ref (Pmap.empty sym_cmp);

    action_map = ref (Pmap.empty Pervasives.compare);
    parent_tid = ref (Pset.empty Pervasives.compare);
    aid_supply = ref 0;
    tid_supply = ref 0;
    tid        = 0;

    z3_ret = Expr.mk_fresh_const ctx "ret_main" (LoadedInteger.mk_sort ctx);
    saves = Pmap.empty sym_cmp;
    depth = 0
  }

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
  | Vlist _ ->
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
 * *)
let mk_eq_expr (state: 'a bmc_state) (m_sym: ksym option) 
               (ty : core_base_type) (expr: Expr.expr) =
  match m_sym with
  | None -> mk_true state.ctx (* Do nothing *)
  | Some sym -> 
      let pat_sym = symbol_to_z3 state.ctx sym in
      let sort = cbt_to_z3 state.ctx ty in
      let expr_pat = Expr.mk_const state.ctx pat_sym sort in
      state.sym_table := Pmap.add sym expr_pat (!(state.sym_table));

      begin
      match ty with
      | BTy_unit -> assert false
      | BTy_ctype (* Fall through *)
      | BTy_boolean -> 
          mk_eq state.ctx expr_pat expr
      | BTy_tuple _ -> 
          assert false
      | BTy_list _ -> assert false
      | BTy_object obj_type -> 
              begin
              match obj_type with
              | OTy_pointer ->
                  assert (Sort.equal (Expr.get_sort expr) 
                                     (PointerSort.mk_sort state.ctx));
                  (* Hack to map source code symbol -> location *)
                  let addr_expr = 
                    Expr.simplify (PointerSort.get_addr state.ctx expr) None in
                  if (Expr.is_numeral addr_expr) then
                    begin
                      let addr = Integer.get_int addr_expr in
                      let src_sym = match Pmap.lookup addr !(state.src_ptr_map) with
                      | None -> sym
                      | Some s -> s
                      in
                      state.src_ptr_map := Pmap.add addr src_sym
                                           !(state.src_ptr_map)
                    end;
                  
                  (* TODO: hack to assign locations to symbols in program *)
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
          mk_eq state.ctx expr_pat expr
      end

(* Return a Z3 boolean expr representing condition for pattern match *)
let rec pattern_match (ctx: context) 
                      (pattern: typed_pattern)
                      (expr: Expr.expr) =
   match pattern with
  | CaseBase(_, _) ->
      mk_true ctx
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      let exprList = Expr.get_args expr in
      let patConditions = 
        List.map2 (fun expr pat -> pattern_match ctx pat expr) 
                  exprList patlist in
      mk_and ctx patConditions
  | CaseCtor(Cspecified, [CaseBase(maybe_sym, BTy_object OTy_integer)]) ->
      LoadedInteger.is_loaded ctx expr 
  | CaseCtor(Cspecified, [CaseBase(maybe_sym, BTy_object OTy_pointer)]) ->
      LoadedPointer.is_loaded ctx expr
  | CaseCtor(Cunspecified, _) -> 
      if (expr_is_sort expr (LoadedInteger.mk_sort ctx)) then
        LoadedInteger.is_unspec ctx expr
      else if (expr_is_sort expr (LoadedPointer.mk_sort ctx)) then
        LoadedPointer.is_unspec ctx expr
      else
        assert false
  | _ -> 
      assert false

let rec mk_eq_pattern (state: 'a bmc_state) 
                      (pattern: typed_pattern)
                      (expr: Expr.expr) =
  match pattern with
  | CaseBase(maybe_sym, typ) ->
      mk_eq_expr state maybe_sym typ expr 
  | CaseCtor(Ctuple, patlist) -> 
      let exprList = Expr.get_args expr in
      assert (Expr.get_num_args expr = List.length patlist);
      mk_and state.ctx 
        (List.map2 
           (fun exp pat -> mk_eq_pattern state pat exp)
           exprList patlist 
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
let concat_vcs (ctx: context)
               (vc1: Expr.expr list)
               (vc2: Expr.expr list)
               (guard: Expr.expr) =
  let new_vc1 = mk_implies ctx guard
                    (mk_and ctx vc1) in
  let new_vc2 = mk_implies ctx 
                    (mk_not ctx guard)
                    (mk_and ctx vc2) in
  [new_vc1; new_vc2 ]                  

let rec bmc_pexpr (state: 'a bmc_state) 
                  (Pexpr(_, bTy, pe) : typed_pexpr) : 
                    'a bmc_ret = 
  match pe with
    | PEsym sym ->
        let sym_expr = bmc_lookup_sym sym state in
        let allocs = alias_lookup_sym sym state.alias_state in
        { expr   = sym_expr
        ; allocs = allocs
        ; vcs = []
        ; preexec = initial_preexec ()
        ; ret_asserts = []
        ; returned = mk_false state.ctx
        ; state  = state
        }
    | PEimpl _ -> assert false
    | PEval cval ->
        { expr = value_to_z3 state.ctx cval bTy
        ; allocs = AddressSet.empty
        ; vcs = []
        ; preexec = initial_preexec ()
        ; ret_asserts = []
        ; returned = mk_false state.ctx
        ; state = state
        }
    | PEconstrained _ -> assert false
    | PEundef _ ->
        let sort = cbt_to_z3 state.ctx bTy in
          (*
        let new_vc = mk_false state.ctx in
          (mk_implies state.ctx 
                           (mk_not state.ctx state.has_returned) 
                           (mk_false state.ctx)) in
          *)
        { expr = Expr.mk_fresh_const state.ctx "undef" sort
        ; allocs = AddressSet.empty
        ; vcs = [ mk_false state.ctx ]
        ; preexec = initial_preexec ()
        ; ret_asserts = []
        ; returned = mk_false state.ctx
        ; state = state
        }
    | PEerror _ -> 
        let sort = cbt_to_z3 state.ctx bTy in
        (*
        let new_vc = (mk_implies state.ctx
                           (mk_not state.ctx state.has_returned)
                           (mk_false state.ctx)) in 
        *)
        { expr = Expr.mk_fresh_const state.ctx "error" sort
        ; allocs = AddressSet.empty
        ; vcs = [ mk_false state.ctx ]
        ; preexec = initial_preexec ()
        ; ret_asserts = []
        ; returned = mk_false state.ctx
        ; state = state
        }
    | PEctor (ctor, pelist) -> 
        let sort = cbt_to_z3 state.ctx bTy in
        let bmc_pelist = List.map 
            (fun pe -> bmc_pexpr state pe) pelist in
        let z3_pelist = List.map (fun res -> res.expr) bmc_pelist in

        (* Union allocs *)
        let allocs = List.fold_left (fun s res ->
          AddressSet.union s res.allocs) AddressSet.empty bmc_pelist in
        { expr = ctor_to_z3 state.ctx ctor z3_pelist sort
        ; allocs = allocs
        ; vcs = List.concat (List.map (fun res -> res.vcs) bmc_pelist) 
        ; preexec = initial_preexec ()
        ; ret_asserts = []
        ; returned = mk_false state.ctx
        ; state = state
        }

    | PEcase (pe, caselist) -> 
        (* case pe of | pat1 -> e1 | pat2 -> e2 | pat3 -> e3 | _ ->
          *
          * pe -> z3 expr
          * convert each pat to condition for matching: 
          * e.g. - if pat = CaseBase(Some sym), true 
          *      - if pat = _, true (all CaseBase => true)
          *      - if pat = Specified(x): isSpecified pe
          *      - if pat = (a, b): true b/c  type? (TODO)
          *
          * Then convert each pat to an equality with pe
          * BMC each e* with empty vcs
          * Make guards with Boolean.mk_ite 
          * *)
        let bmc_pe = bmc_pexpr state pe in

        List.iter (fun (pat1, _) -> 
          alias_pattern state.alias_state pat1 bmc_pe.allocs) caselist;

        let pattern_guards = 
          List.map (fun (pat, _) -> pattern_match state.ctx pat bmc_pe.expr) caselist in 
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
          mk_eq_pattern state pat bmc_pe.expr) caselist in

        (* Match case i => expr_eq i holds *)
        let impl_eqs = List.map2 
          (fun guard eq -> mk_implies state.ctx guard eq) 
          combined_pat_guards expr_eqs in
        Solver.add state.solver impl_eqs;

        (* Now need to combine verification conditions: 
         * st1.vcs @... guarded by case match *)
        let cases_z3 = List.map 
            (fun (_, e) -> bmc_pexpr bmc_pe.state e) caselist in
        let cases_vcs = (List.map (fun res -> mk_and state.ctx res.vcs) cases_z3) in
        let new_vcs = 
          ((List.map2 (fun guard vc -> mk_implies state.ctx guard vc)
          combined_pat_guards cases_vcs)) in
        (* TODO: correctness? *)

        (* Now make ite, careful with cases where expressions are None *)
        let zipped = List.combine combined_pat_guards 
                    (List.map (fun res -> res.expr) cases_z3) in
        let rev_filtered = List.rev zipped in

        (* Alloc ids *)
        let alloc_ret = List.fold_left (fun s res ->
          AddressSet.union s res.allocs) AddressSet.empty cases_z3 in

        begin
        match List.length rev_filtered with
        | 0 -> assert false
        | 1 -> 
            let (_, e) = List.hd rev_filtered in
            { expr = e
            ; allocs = alloc_ret
            ; vcs = bmc_pe.vcs @ new_vcs
            ; preexec = initial_preexec ()
            ; ret_asserts = []
            ; returned = mk_false state.ctx
            ; state = bmc_pe.state 
            }
        | _ -> 
            let (_, last) = List.hd rev_filtered in
            let ite = List.fold_left (fun prev (guard, e) ->
              mk_ite state.ctx guard e prev
            ) last (List.tl rev_filtered) in
            { expr = ite
            ; allocs = alloc_ret
            ; vcs = bmc_pe.vcs @ new_vcs
            ; preexec = initial_preexec ()
            ; ret_asserts = []
            ; returned = mk_false state.ctx
            ; state = bmc_pe.state 
            }
        end
    | PEarray_shift _ -> assert false
    | PEmember_shift _ -> assert false
    | PEnot pe1 -> 
        let res = bmc_pexpr state pe1 in  
        { res with expr = mk_not state.ctx res.expr }
    | PEop (bop, pe1, pe2) ->
        let res1 = bmc_pexpr state pe1 in
        let res2 = bmc_pexpr res1.state pe2 in
        { expr = binop_to_constraints state.ctx res1.expr res2.expr bop
        ; allocs = AddressSet.union res1.allocs res2.allocs
        ; vcs = res1.vcs @ res2.vcs
        ; preexec = initial_preexec ()
        ; ret_asserts = []
        ; returned = mk_false state.ctx
        ; state = res2.state
        }
    | PEstruct _
    | PEunion _ -> assert false
    | PEcall(Sym sym, _) ->
        assert false
    | PEcall _ -> 
        assert false
    | PElet (pat, pe1, pe2) ->
        let res1 = bmc_pexpr state pe1 in
        let eq_expr = mk_eq_pattern res1.state pat res1.expr in
        Solver.add res1.state.solver [ eq_expr ];
        alias_pattern res1.state.alias_state pat res1.allocs;
        let res2 = bmc_pexpr state pe2 in
        { expr = res2.expr
        ; allocs = res2.allocs
        ; vcs = res1.vcs @ res2.vcs
        ; preexec = initial_preexec ()
        ; ret_asserts = []
        ; returned = mk_false state.ctx
        ; state = res2.state
        }

    | PEif (pe1, pe2, pe3) ->
        let res1 = bmc_pexpr state pe1 in
        let res2 = bmc_pexpr state pe2 in
        let res3 = bmc_pexpr state pe3 in
        let new_vc = res1.vcs @ (concat_vcs state.ctx res2.vcs
                                       res3.vcs res1.expr) in
        { expr = mk_ite state.ctx res1.expr res2.expr res3.expr
        ; allocs = AddressSet.union res2.allocs res3.allocs
        ; vcs = new_vc
        ; preexec = initial_preexec ()
        ; ret_asserts = []
        ; returned = mk_false state.ctx
        ; state = res1.state
        }
    | PEis_scalar _ 
    | PEis_integer _ 
    | PEis_signed _ 
    | PEis_unsigned _ ->
        assert false

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
    | Floating _ -> assert false
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
                : 'a bmc_ret =
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
      let action = Write(mk_next_aid state, g_initial_tid, NA, new_ptr, to_store) in
      let paction = BmcAction(Pos, mk_true state.ctx, action) in
      state.action_map := Pmap.add (get_aid action) paction !(state.action_map);

      { expr = new_ptr
      ; allocs = addr_ret
      ; vcs = []
      ; preexec = add_initial_action (get_aid action) paction (initial_preexec ())
      ; ret_asserts = []
      ; returned = mk_false state.ctx
      ; state (* with heap = new_heap *)
      }

  | Create _ -> assert false
  | CreateReadOnly _ -> assert false
  | Alloc0 _ -> assert false
  | Kill pexpr ->
      let res = bmc_pexpr state pexpr in
      (*
      assert (AddressSet.cardinal allocs = 1);
      let elem = AddressSet.find_first (fun _ -> true) allocs in
      let new_heap = Pmap.remove elem state.heap in
      *)
      (* TODO: should really alter analysis_state too *)
      { expr = UnitSort.mk_unit state.ctx
      ; allocs = AddressSet.empty
      ; vcs = res.vcs
      ; preexec = res.preexec
      ; ret_asserts = res.ret_asserts
      ; returned = res.returned 
      ; state = res.state (* with heap = new heap *)
      }
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
      let res_value = bmc_pexpr state p_value in
      (* (value, v_allocs, state) = bmc_pexpr state p_value in
      *)

      (* Not necessary, just for renaming purposes *)
      let to_store = Expr.mk_fresh_const state.ctx
                ("store_" ^ (symbol_to_string sym)) 
                (Expr.get_sort res_value.expr) in
      Solver.add state.solver [ mk_eq state.ctx res_value.expr to_store ];

      let z3_sym = bmc_lookup_sym sym state in

      let action = Write(mk_next_aid state, state.tid, mem_order,
                         z3_sym, to_store) in
      let paction = BmcAction(pol, mk_true state.ctx, action) in
      state.action_map := Pmap.add (get_aid action) paction !(state.action_map);

      print_endline (string_of_paction paction);


      (* If we are storing a C pointer, update points-to map *)
      begin
        if is_ptr_ctype (Pexpr([],BTy_ctype, PEval (Vctype ty))) then
          begin
          assert (not (AddressSet.is_empty ptr_allocs));
          assert (not (AddressSet.is_empty res_value.allocs));

          (* For each potential store location, add v_allocs to addr_map *)

          AddressSet.iter (fun loc ->
            print_string (Address.to_string loc);
            let prev_set = alias_lookup_alloc loc state.alias_state in
            alias_add_to_addr_map state.alias_state 
                  loc (AddressSet.union prev_set res_value.allocs)
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
      { expr = UnitSort.mk_unit state.ctx
      ; allocs = AddressSet.empty
      ; vcs = res_value.vcs
      ; preexec = add_action (get_aid action) paction (initial_preexec ())
      ; ret_asserts = []
      ; returned = mk_false state.ctx 
      ; state = res_value.state
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

      let action = Read(mk_next_aid state, state.tid, mem_order,
                         z3_sym, ret_value) in
      let paction = BmcAction(pol, mk_true state.ctx, action) in
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
      { expr = ret_value
      ; allocs = ret_alloc
      ; vcs = []
      ; preexec = add_action (get_aid action) paction (initial_preexec ())
      ; ret_asserts = []
      ; returned = mk_false state.ctx 
      ; state = state
      }

      (*
       ret_value, ret_alloc, 
          ({state with (*vcs = (new_vc) :: state.vcs; *)
                       preexec = add_action (get_aid action) paction
                                 state.preexec}
          )
      *)
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
                 : 'a bmc_ret =
  match expr_ with
  | Epure pe ->
      bmc_pexpr state pe 
  | Ememop (PtrValidForDeref, _) ->
      print_endline "TODO: Ememop PtrValidForDeref: always true";
      { expr = mk_true state.ctx
      ; vcs = []
      ; allocs = AddressSet.empty
      ; preexec = initial_preexec ()
      ; ret_asserts = []
      ; returned = mk_false state.ctx
      ; state = state
      }
  | Ememop _ ->
      assert false
  | Eaction paction ->
      bmc_paction state paction
  | Ecase (pe, elist) ->  
      assert (List.length elist > 0);
      (* let (bmc_pe, pe_addr, st) = bmc_pexpr state pe in *)
      let res_pe = bmc_pexpr state pe in

      List.iter (fun (pat, _) ->
        alias_pattern state.alias_state pat res_pe.allocs) elist;

      let pattern_guards = List.map
        (fun (pat, _) -> pattern_match state.ctx pat res_pe.expr) elist in

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
          mk_eq_pattern state pat res_pe.expr) elist in
      let impl_eqs = List.map2 
        (fun guard eq -> mk_implies state.ctx guard eq)
        combined_pat_guards expr_eqs in
      Solver.add state.solver impl_eqs;

      let cases_z3 = List.map (fun (_, e) -> 
        bmc_expr res_pe.state e) elist in
      let cases_vcs = List.map (fun res -> 
          mk_and state.ctx res.vcs) cases_z3 in
      let new_vcs = (List.map2 (fun guard vc -> 
          mk_implies state.ctx guard vc
        ) combined_pat_guards cases_vcs) in
      let new_ret_asserts = res_pe.ret_asserts @ (List.map2 
        (fun guard res -> 
          mk_implies state.ctx guard (mk_and state.ctx res.ret_asserts)
        )
      ) combined_pat_guards cases_z3 in

      assert (is_false res_pe.returned);
      let new_has_returned = 
        mk_or state.ctx 
          (List.map2 (fun guard res ->
              mk_and state.ctx [guard; res.returned])
              combined_pat_guards cases_z3) in

      let alloc_ret = List.fold_left (fun s res ->
        AddressSet.union s res.allocs) AddressSet.empty cases_z3 in
      let guarded_preexecs = List.map2 (fun guard res ->
        guard_preexec state.ctx guard res.preexec 
      ) combined_pat_guards cases_z3 in
      let new_preexec = List.fold_left (fun p1 p2 ->
          merge_preexecs p1 p2
        ) res_pe.preexec guarded_preexecs in

      let sort = Expr.get_sort (let res = List.hd cases_z3 in res.expr) in
      let ret = List.fold_right2 (fun guard res rest ->
        mk_ite state.ctx guard res.expr rest
      ) pattern_guards cases_z3 (Expr.mk_fresh_const state.ctx "unmatchedCase"
      sort) in

      { expr = ret
      ; allocs = alloc_ret
      ; vcs = res_pe.vcs @ new_vcs
      ; preexec = new_preexec
      ; ret_asserts = new_ret_asserts
      ; returned = new_has_returned
      ; state = state
      }
  | Eskip -> 
      { expr = UnitSort.mk_unit state.ctx
      ; allocs = AddressSet.empty
      ; vcs = []
      ; preexec = initial_preexec ()
      ; ret_asserts = []
      ; returned = mk_false state.ctx
      ; state = state
      }
  | Eproc _ -> assert false
  | Eccall (_, Pexpr(_, BTy_object (OTy_cfunction (retTy, numArgs, var)), 
                        PEsym sym), arglist)  ->
      let sym_fn = Pmap.find sym !(state.fn_map) in
      begin
      match Pmap.lookup sym_fn state.file.funs with
      | None -> assert false
      | Some (Fun _) -> assert false
      | Some (ProcDecl _) -> assert false
      | Some (Proc(ty, params, e)) -> 
         begin
           if (state.depth >= g_max_function_depth) then
             let sort = cbt_to_z3 state.ctx ty in
             (*
             let new_vcs = (mk_implies state.ctx
                (mk_not state.ctx state.has_returned)
                (mk_false state.ctx)) in
              *)
             { expr = Expr.mk_fresh_const state.ctx "ccallBound" sort
             ; allocs = AddressSet.empty
             ; vcs = [ mk_false state.ctx ]
             ; preexec = initial_preexec ()
             ; ret_asserts = []
             ; returned = mk_false state.ctx
             ; state = state
             }
           else
             begin
               let bmc_args = List.map (fun pe -> 
                 bmc_pexpr state pe) arglist in
               let vcs = (List.concat (
                 List.map (fun res -> res.vcs) bmc_args)) in 
               match bmc_normalize_fn (Proc(ty, params, e)) state.file
                                      !(state.sym_supply) with
               | Proc(ty2, params2, e2),supply ->
                  assert (List.length arglist = List.length params2);
                  state.sym_supply := supply;
                  let eq_exprs = List.map2 (fun (sym1, ty) res ->
                    mk_eq_expr state (Some sym1) ty res.expr) params2 bmc_args in
                  Solver.add state.solver eq_exprs;
                  let sort = cbt_to_z3 state.ctx ty2 in
                  let fresh_state = {state with
                      z3_ret = Expr.mk_fresh_const state.ctx  
                                  ("ret_" ^ (symbol_to_string sym_fn)) sort;
                      saves = find_save_expr e ;
                      depth = state.depth + 1
                    } in
                  let res_call = bmc_expr fresh_state e2 in
                  (*
                  (bmc_call, alloc, ret_state) = 
                    bmc_expr fresh_state e2 in
                  *)
                  (*
                  let guarded_preexec = guard_preexec state.ctx
                      (mk_not state.ctx state.has_returned) res_call.preexec in
                  *)
                  (*
                  let new_preexec =
                    merge_preexecs state.preexec guarded_preexec in 
                  let (exec1, exec2) = (state.preexec, res_call.preexec) in
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
                  *)

                  Solver.add state.solver res_call.ret_asserts;
                  { expr = res_call.state.z3_ret
                  ; allocs = res_call.allocs
                  ; vcs = res_call.vcs @ vcs
                  ; preexec = res_call.preexec
                  ; ret_asserts = []
                  ; returned = mk_false state.ctx
                  ; state = state
                  }
               | _ -> assert false
             end
         end 
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
      assert (not g_sequentialise);

      let bmc_list = List.map (fun e -> bmc_expr state e) elist in
      let expr_list = List.map (fun res -> res.expr) bmc_list in
      let sort_list = List.map Expr.get_sort expr_list in

      let sort = z3_sortlist_to_tuple state.ctx sort_list in

      let ret = ctor_to_z3 state.ctx Ctuple expr_list sort  in
      let allocs = List.fold_left (fun set res ->
        AddressSet.union set res.allocs) AddressSet.empty bmc_list in
      let new_vcs = List.concat (List.map (fun res -> res.vcs) bmc_list) in
      let new_preexec = List.fold_left (fun exec res ->
        merge_preexecs exec res.preexec 
      ) (initial_preexec ()) bmc_list in
      let new_has_returned = mk_or state.ctx (List.map 
        (fun res -> res.returned) bmc_list) in
      let new_ret_asserts = List.concat (
        List.map (fun res -> res.ret_asserts) bmc_list) in
      { expr = ret
      ; allocs = allocs
      ; vcs = new_vcs
      ; preexec = new_preexec
      ; ret_asserts = new_ret_asserts
      ; returned = new_has_returned
      ; state = state
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
      let res1 = bmc_expr state e1 in
      let res2 = bmc_expr state e2 in

      let bmc_seq1 = Expr.mk_fresh_const state.ctx "seq" 
                      (Boolean.mk_sort state.ctx) in
      let bmc_seq2 = Expr.mk_fresh_const state.ctx "seq" 
                      (Boolean.mk_sort state.ctx) in
      let seq_xor = mk_xor state.ctx bmc_seq1 bmc_seq2  in
      Solver.add state.solver [ seq_xor ];

      let vc1 = mk_implies state.ctx bmc_seq1
                    (mk_and state.ctx res1.vcs)  in
      let vc2 = mk_implies state.ctx bmc_seq2
                    (mk_and state.ctx res2.vcs) in
      let new_vcs = [ vc1 ; vc2 ]  in
      (*
      let new_heap = merge_heaps state st1.heap st2.heap
                      bmc_seq1 bmc_seq2 in
      *)
      (* preexecs *)
      let preexec1 = guard_preexec state.ctx bmc_seq1 res1.preexec in
      let preexec2 = guard_preexec state.ctx bmc_seq2 res2.preexec in
      let new_preexec = merge_preexecs preexec1 preexec2 in

      let new_has_returned = mk_or state.ctx
        [ mk_and state.ctx [bmc_seq1 ; res1.returned ]
        ; mk_and state.ctx [bmc_seq2 ; res2.returned ]
        ] in
  
      let new_ret_asserts =
        [
           (mk_implies state.ctx bmc_seq1 
                                 (mk_and state.ctx res1.ret_asserts))
        ;  (mk_implies state.ctx bmc_seq2
                                 (mk_and state.ctx res2.ret_asserts))
        ] in

      { expr = UnitSort.mk_unit state.ctx
      ; allocs = AddressSet.union res1.allocs res2.allocs
      ; vcs = new_vcs
      ; preexec = new_preexec
      ; ret_asserts = new_ret_asserts
      ; returned = new_has_returned
      ; state = state (* with  heap = new_heap; *)
      }

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

              let res_run = bmc_expr state to_run in
              (* (ret, aset, state) = bmc_expr state to_run in *)
              let eq_expr = mk_implies state.ctx
                (mk_not state.ctx res_run.returned)
                (mk_eq state.ctx res_run.state.z3_ret res_run.expr) in
            { expr = UnitSort.mk_unit state.ctx
            ; allocs = res_run.allocs
            ; vcs = res_run.vcs
            ; preexec = res_run.preexec 
            ; ret_asserts = eq_expr :: res_run.ret_asserts 
            ; returned = mk_true state.ctx
            ; state = res_run.state
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
      assert (not g_sequentialise);

      let bmc_list = List.map (fun expr ->
          bmc_expr {state with tid = mk_next_tid state } expr
        ) elist in
      let expr_list = List.map (fun res -> res.expr) bmc_list in
      let sort_list = List.map Expr.get_sort expr_list in
      let sort = z3_sortlist_to_tuple state.ctx sort_list in
      let ret = ctor_to_z3 state.ctx Ctuple expr_list sort  in
      let allocs = List.fold_left (fun set res ->
        AddressSet.union set res.allocs) AddressSet.empty bmc_list in
      let new_vcs = List.concat (List.map (fun res -> res.vcs) bmc_list) in
      let new_preexec = List.fold_left (fun exec res ->
        merge_preexecs exec res.preexec 
      ) (initial_preexec ()) bmc_list in

      List.iter (fun res ->
        state.parent_tid := 
            Pset.add (res.state.tid, state.tid) !(state.parent_tid)
      ) bmc_list;

      let new_has_returned = mk_or state.ctx (
        List.map (fun res -> res.returned) bmc_list
      ) in 
      let new_ret_asserts = List.concat (
        List.map (fun res -> res.ret_asserts) bmc_list) in

      { expr = ret
      ; allocs = allocs
      ; vcs = new_vcs
      ; preexec = new_preexec
      ; ret_asserts = new_ret_asserts
      ; returned = new_has_returned
      ; state = state
      }
  | Ewait _ -> assert false
  | Eif (pe, e1, e2) -> 
      let res_pe = bmc_pexpr state pe in
      let res_e1 = bmc_expr res_pe.state e1 in
      let res_e2 = bmc_expr res_pe.state e2 in
      
      let new_vc = res_pe.vcs @ 
                  (concat_vcs state.ctx res_e1.vcs res_e2.vcs 
                              res_pe.expr) in
      (*
      let new_heap = merge_heaps st st1.heap st2.heap 
                     bmc_pe (Boolean.mk_not st.ctx bmc_pe) in
      *)

      let preexec1 = guard_preexec state.ctx res_pe.expr res_e1.preexec in
      let preexec2 = guard_preexec state.ctx (mk_not state.ctx res_pe.expr) res_e2.preexec in
      let new_preexec = (merge_preexecs preexec1 preexec2) in

      let new_has_returned = mk_or state.ctx 
          [ mk_and state.ctx [res_pe.expr; res_e1.returned]
          ; mk_and state.ctx [mk_not state.ctx res_pe.expr; res_e2.returned]] in

      let new_ret_asserts = 
        (mk_implies state.ctx res_pe.expr (mk_and state.ctx res_e1.ret_asserts))
        :: (mk_implies state.ctx (mk_not state.ctx res_pe.expr) 
                              (mk_and state.ctx res_e2.ret_asserts))
        :: res_pe.ret_asserts in
      { expr = mk_ite state.ctx res_pe.expr res_e1.expr res_e2.expr
      ; allocs = AddressSet.union res_e1.allocs res_e2.allocs
      ; vcs = new_vc
      ; preexec = new_preexec
      ; ret_asserts = new_ret_asserts
      ; returned = new_has_returned
      ; state = res_pe.state (* with (* heap = new_heap; *) *)
      }
        
  | Elet _ -> assert false
  | Easeq _ ->
      assert false
  | Ewseq (pat, e1, e2) ->
      let bmc_e1 = bmc_expr state e1 in
      alias_pattern state.alias_state pat bmc_e1.allocs;
      let eq_expr = mk_eq_pattern state pat bmc_e1.expr in
      Solver.add state.solver [ eq_expr ];

      let bmc_e2 = bmc_expr bmc_e1.state e2 in

      let (exec1, exec2) = (bmc_e1.preexec,
                           {bmc_e2.preexec with 
                              actions = guard_actions state.ctx
                                          (mk_not state.ctx bmc_e1.returned)
                                          bmc_e2.preexec.actions}) in

      (* Sequence all actions in state before those in state2*) 
      let new_preexec = merge_preexecs exec1 exec2 in 
      let new_preexec = 
        {new_preexec with 
          sb = Pset.union (new_preexec.sb) 
                          (pos_cartesian_product exec1.actions
                                                 exec2.actions);
          asw = Pset.union (new_preexec.asw)
                           (asw_product exec1.actions exec2.actions
                                        !(bmc_e1.state.parent_tid)
                           );
          (*
          hb = Pset.union (new_preexec.hb)
                          (hb_cartesian_product exec1.actions
                                                exec2.actions
                                                true
                          )
          *)
        } in
      let new_vcs = (mk_or state.ctx [ bmc_e1.returned
                                     ; mk_and state.ctx bmc_e2.vcs])
                    :: bmc_e1.vcs
         in
      let new_ret_asserts = bmc_e1.ret_asserts @ (List.map (fun ret_assert ->
        mk_implies state.ctx (mk_not state.ctx bmc_e1.returned)
                             ret_assert
      ) bmc_e2.ret_asserts) in
      { expr = bmc_e2.expr
      ; allocs = bmc_e2.allocs
      ; vcs = new_vcs
      ; preexec = new_preexec
      ; ret_asserts = new_ret_asserts
      ; returned = mk_or state.ctx [bmc_e1.returned; bmc_e2.returned]
      ; state = bmc_e2.state
      }

  | Esseq (pat, e1, e2) ->
      (* TODO: mostly duplicated code from Ewseq *)
      let bmc_e1 = bmc_expr state  e1 in
      alias_pattern state.alias_state pat bmc_e1.allocs ;
      let eq_expr = mk_eq_pattern state pat bmc_e1.expr in
      Solver.add state.solver [ eq_expr ];

      let bmc_e2 = bmc_expr bmc_e1.state e2 in
      let (exec1, exec2) = (bmc_e1.preexec,
                           {bmc_e2.preexec with 
                              actions = guard_actions state.ctx
                                          (mk_not state.ctx bmc_e1.returned)
                                          bmc_e2.preexec.actions}) in

      (* Sequence all actions in state before those in state2*) 
      let new_preexec = merge_preexecs exec1 exec2 in
      let new_preexec = 
        {new_preexec with 
          sb = Pset.union (new_preexec.sb) 
                          (cartesian_product exec1.actions
                                             exec2.actions);
          asw = Pset.union (new_preexec.asw)
                           (asw_product exec1.actions exec2.actions
                                        !(bmc_e1.state.parent_tid)
                           );
          (*
          hb = Pset.union (new_preexec.hb)
                          (hb_cartesian_product exec1.actions
                                                exec2.actions
                                                false
                          )
          *)
        } in
      let new_vcs = (mk_or state.ctx [ bmc_e1.returned
                                     ; mk_and state.ctx bmc_e2.vcs])
                    :: bmc_e1.vcs
         in
      let new_ret_asserts = bmc_e1.ret_asserts @ (List.map (fun ret_assert ->
        mk_implies state.ctx (mk_not state.ctx bmc_e1.returned)
                             ret_assert
      ) bmc_e2.ret_asserts) in
      { expr = bmc_e2.expr
      ; allocs = bmc_e2.allocs
      ; vcs = new_vcs
      ; preexec = new_preexec
      ; ret_asserts = new_ret_asserts
      ; returned = mk_or state.ctx [bmc_e1.returned; bmc_e2.returned]
      ; state = bmc_e2.state
      }

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
              let bmc_run = bmc_expr state to_run in
              let eq_expr = mk_implies state.ctx
                (mk_not state.ctx bmc_run.returned)
                (mk_eq state.ctx bmc_run.state.z3_ret bmc_run.expr) in

              { expr = UnitSort.mk_unit state.ctx
              ; allocs = AddressSet.empty
              ; vcs = bmc_run.vcs
              ; preexec = bmc_run.preexec
              ; ret_asserts = eq_expr :: bmc_run.ret_asserts
              ; returned = mk_true state.ctx
              ; state = bmc_run.state
              }
            end
          else 
            assert false
      | _ -> assert false
      end
  | Esave _ ->
      assert false

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
      let action = Write(mk_next_aid state, g_initial_tid, NA, ptr, to_store) in
      let paction = BmcAction(Pos, mk_true state.ctx, action) in
      state.action_map := Pmap.add (get_aid action) paction !(state.action_map);

      let addr_expr = Address.mk_expr state.ctx new_addr in
      let addr_is_atomic = Boolean.mk_val state.ctx false in

      Solver.add state.solver 
          [mk_eq state.ctx addr_is_atomic
                           (Address.is_atomic state.ctx addr_expr)];

      (* Assert address of symbol is new_addr *)
      Solver.add state.solver [ 
        mk_eq  state.ctx
          (PointerSort.get_addr state.ctx ptr)
          (addr_expr)
      ];
      { expr = ptr
      ; allocs = AddressSet.singleton new_addr
      ; vcs = []
      ; preexec = add_initial_action (get_aid action) paction (initial_preexec ()) 
      ; ret_asserts = []
      ; returned = mk_false state.ctx
      ; state
      }

let initialise_main_params params state =
  match params with
  | [] -> initial_preexec (), state
  | [p1; p2] ->
      let res1 = initialise_param p1 state (LoadedInteger.mk_sort state.ctx) in
      let res2 = initialise_param p2 state (LoadedPointer.mk_sort state.ctx) in
      merge_preexecs res1.preexec res2.preexec, state
  | _ -> assert false

let initialise_global state sym typ expr : 'a bmc_state =
  assert (is_ptr_type typ);
  print_endline "TODO: sb global preexec";
  (* TODO: duplicated from Esseq *)
  let res = bmc_expr state expr in 
  let pat = CaseBase(Some sym, typ) in
  alias_pattern state.alias_state pat res.allocs;
  let eq_expr = mk_eq_pattern state pat res.expr in
  Solver.add state.solver [ eq_expr ];
  res.state

(* TODO: make event a datatype 
 * TODO: do this in a nicer way so it's actually readable...
 * e.g. generically 
 *)
let preexec_to_z3 (state: 'a bmc_state) (preexec: preexecution) =
  let ctx = state.ctx in
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
  (* Get the action_id associated with the event *)
  let fn_getAid = FuncDecl.mk_fresh_func_decl ctx 
                    "getAid" [ event_sort ] (Integer.mk_sort ctx) in
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
                "hb-clock" [ event_sort ] (Integer.mk_sort ctx) in
  (* synchronizes with; asw or[rel] ; [A && W] ; rf; [R && A]; [acq] 
   *)
  let fn_sw = FuncDecl.mk_fresh_func_decl ctx
                "sw" [event_sort; event_sort] (Boolean.mk_sort ctx) in

  (* getInitial(e1) = initial event of location of e1 *)
  let fn_getInitial = FuncDecl.mk_fresh_func_decl ctx
                        "getInitial" [ Address.mk_sort ctx ] event_sort in
  let getInitial expr = FuncDecl.apply fn_getInitial [ expr ] in

  (* ============ Function definitions ============ *)
  (* aid_asserts *)
  let aid_asserts = List.map (fun action -> 
    let aid = aid_of_paction action in
    mk_eq ctx (FuncDecl.apply fn_getAid [event_expr action])
                      (Integer.mk_numeral_i ctx aid)) event_list in

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
              (Expr.simplify (guard_of_paction action) None)) event_list in

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
                           (Integer.mk_numeral_i ctx g_initial_tid)
               ; mk_not ctx (mk_eq ctx (getThread e2) 
                                       (Integer.mk_numeral_i ctx g_initial_tid ))
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
                 (mk_and ctx 
                   [
                    mk_or ctx [ FuncDecl.apply fn_sb [bound_0; bound_1]
                              ; FuncDecl.apply fn_sw [bound_0; bound_1]
                              ; hb_exists
                              ]
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
                      ; mk_not ctx 
                          (mk_and ctx [mk_eq ctx bound_0 
                                                 (getInitial (getAddr bound_0))
                                      ;mk_eq ctx bound_1
                                                 (getInitial (getAddr bound_1))
                                      ])
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
   * distinct and same location and one is write and not same thread and i
   * (not both are atomic = either is non-atomic)
   * =>
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
            @ aid_asserts
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
              (* Comment out hb_assert and data_race_assert if too slow *)
              ; hb_assert 
              (*
              ; data_race_assert 
              ; unseq_race_assert 
              *)
              ] in
  List.iter (fun s -> print_endline (Expr.to_string s)) ret;

  let fns : exec_fns = 
    { event_sort = event_sort;

      event_type = event_type;
      read_type = read_type;
      write_type = write_type;

      memorder_type = memorder_type;
      na_order = na_order;
      seq_cst_order = seq_cst_order;
      relaxed_order = relaxed_order;
      release_order = release_order;
      acquire_order = acquire_order;
      consume_order = consume_order;
      acq_rel_order = acq_rel_order;

      asw = fn_asw;
      hb  = fn_hb;
      mo  = fn_mo;
      rf  = fn_rf;
      sb  = fn_sb;
      sw  = fn_sw;

      is_atomic = Address.is_atomic ctx;

      getAddr = fn_getAddr;
      getAid  = fn_getAid;
      getEventType = fn_getEventType;
      getGuard = fn_getGuard;
      getMemOrder = fn_getMemorder;
      getThread = fn_getThread;
      getVal    = fn_getVal;

      unseq_race = unseq_race_assert;
      data_race = data_race_assert;
    } in

  ret, Some fns 


let bmc_file (file: 'a typed_file) (supply: ksym_supply) =
  (* Do globals *)
  let initial_state = initial_bmc_state supply file in
  let state = List.fold_left (fun st (sym, typ, e) ->
    initialise_global st sym typ e) initial_state file.globs in 

  match file.main with
  | None -> failwith "ERROR: file does not have a main"
  | Some main_sym ->
      let result = (
        match Pmap.lookup main_sym file.funs with
        | Some (Proc(ty, params, e)) ->
            (* Handle parameters *)
            print_endline "TODO: sequence globals preexecs!";
            let preexecs, state = initialise_main_params params state in
            let esaves = find_save_expr e in
            print_endline "SAVES";  
            print_saves_map esaves;

            let result = 
              if (ty = BTy_loaded OTy_integer) then
                bmc_expr {state with saves = esaves} e
              else if (ty = BTy_object OTy_integer)  then
                bmc_expr 
                  {state with 
                      saves = esaves;
                      z3_ret = Expr.mk_fresh_const state.ctx
                                 "ret_main" (Integer.mk_sort state.ctx) } e
              else
                assert false in
            let (exec1, exec2) = (preexecs, result.preexec) in
            let new_preexec = merge_preexecs exec1 exec2 in
            let new_preexec = 
                  {new_preexec with 
                    sb = Pset.union (new_preexec.sb) 
                                    (cartesian_product exec1.actions
                                                       exec2.actions);
                    asw = Pset.union (new_preexec.asw)
                                     (asw_product exec1.actions exec2.actions
                                                  !(result.state.parent_tid)
                                     );
                    (*
                    hb = Pset.union (new_preexec.hb)
                                    (hb_cartesian_product exec1.actions
                                                          exec2.actions
                                                          false
                                    )
                    *)
                  } in
            let result_expr = 
              if (expr_is_sort result.expr (UnitSort.mk_sort state.ctx)) then
                result.state.z3_ret
              else
                result.expr in
            { expr = result_expr
            ; allocs = result.allocs
            ; vcs = result.vcs (* TODO: globals *)
            ; preexec = new_preexec
            ; ret_asserts = result.ret_asserts
            ; returned = result.returned
            ; state = result.state
            }
        | Some (Fun(ty, params, pe)) ->
            (* Handle parameters *)
            print_endline "Fun disabled for now; check return consistent";
            assert false;

            let _, state = initialise_main_params params state in
            bmc_pexpr state pe 
        | _ -> assert false
      ) in
      let state1 = result.state in

      (* TODO: do properly. Need to make ASW relation correct *)
      let preexec = {result.preexec with
          asw = filter_asw result.preexec.asw
                !(state1.parent_tid)
                result.preexec.sb
                !(state1.action_map)
            } in
      Solver.add state1.solver (List.map (fun e -> Expr.simplify e None) result.ret_asserts);


      print_endline "-----ALIAS_RESULTS";
      print_ptr_map !(state1.alias_state.ptr_map);
      print_addr_map !(state1.alias_state.addr_map);

      print_endline "-----EVENTS";
      print_preexec preexec;

      print_endline "-----EVENT STUFF";
      let (z3_preexec, funcDecls) = 
        (if Pset.is_empty preexec.actions then 
            [], None (* Guard st sort is well-founded *)
          else
            preexec_to_z3 state1 preexec
        ) in

      print_endline "-----CONSTRAINTS ONLY";
      assert (Solver.check state1.solver [] = SATISFIABLE);

      print_endline "-----WITH EVENTS";
      Solver.add state1.solver z3_preexec; 

      if (check_solver_fun state1.solver (Some result.expr)
            = SATISFIABLE) then
        begin
          let check_vcs = (match funcDecls with
            | None -> print_endline "No memory actions"; true
            | Some fns ->
                get_all_executions state1.solver fns state1.ctx 
                                   (Some result.expr) !(state.src_ptr_map);
                print_endline "-----WITH RACE CHECKS";
                Solver.add state1.solver [fns.unseq_race; fns.data_race];
                if (Solver.check state1.solver [] = SATISFIABLE) then
                  (print_endline "All consistent executions are race free.";
                   true)
                else
                  (print_endline "Not all consistent executions are race free.";
                   print_endline "-----RESULT=SAT :(";
                   false
                  )
          ) in

          match check_vcs with
          | true ->
            print_endline "-----WITH VCS";
            let not_vcs = List.map (fun a -> (mk_not state1.ctx a))
                                   result.vcs
            in
            Solver.add state1.solver [ mk_or state1.ctx not_vcs ] ;
            (* Printf.printf "\n-- Solver:\n%s\n" (Solver.to_string
             * (state1.solver)); *)
            print_endline "Checking sat";
            let _ = check_solver (state1.solver) in
            ()
          | false -> ()
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

      let core_to_check = 
        if g_sequentialise then 
          Core_sequentialise.sequentialise_file typed_core 
        else
          typed_core
      in
      pp_file core_to_check;

      print_endline "START Z3";
      (* bmc_file seq_file norm_supply; *)
      bmc_file core_to_check norm_supply;

      print_string "EXIT: BMC PIPELINE \n"
    )
