open Bmc_globals
open Bmc_sorts
open Bmc_types
open Bmc_utils
open Core
open Printf
open Util
open Z3
open Z3.Arithmetic

type bmc_action =
  | BmcAction of polarity * guard * action

type preexec = {
  actions         : bmc_action list;
  initial_actions : bmc_action list;

  sb              : (bmc_action * bmc_action) list;
  asw             : (bmc_action * bmc_action) list;
}

(* ========== BMC ACTIONS ============= *)
let initial_tid = -1

let has_addr (BmcAction(_, _, a): bmc_action) = match a with
  | Load _
  | Store _
  | RMW _ -> true
  | _ -> false

let has_rval (BmcAction(_, _, a): bmc_action) =
  is_read a

let has_wval (BmcAction(_, _, a): bmc_action) =
  is_write a

let get_action (BmcAction(_, _, action): bmc_action) =
  action

let get_memorder (BmcAction (_, _, action): bmc_action) =
  memorder_of_action action

let tid_of_bmcaction (bmcaction: bmc_action) =
  tid_of_action (get_action bmcaction)

let aid_of_bmcaction (bmcaction: bmc_action) =
  aid_of_action (get_action bmcaction)

let addr_of_bmcaction (bmcaction: bmc_action) =
  PointerSort.get_addr (addr_of_action (get_action bmcaction))

let guard_of_bmcaction (BmcAction(_, g, _) : bmc_action) = g

let is_pos_action (BmcAction(pol, _, _): bmc_action) = match pol with
  | Pos -> true
  | Neg -> false

let is_rmw (a: bmc_action) = match get_action a with
  | RMW _ -> true
  | _ -> false


let bmc_action_cmp (BmcAction(_, _, a1)) (BmcAction(_, _, a2)) =
  compare (aid_of_action a1) (aid_of_action a2)

(* ===== PREEXECS ===== *)

type bmcaction_rel = bmc_action * bmc_action

let mk_initial_preexec : preexec =
  { actions         = []
  ; initial_actions = []
  ; sb              = []
  ; asw             = []
  }

let find_rel ((a,b): bmcaction_rel) (xs: bmcaction_rel list) =
  is_some (List.find_opt (
    fun (x,y) -> (aid_of_bmcaction a = aid_of_bmcaction x)
              && (aid_of_bmcaction b = aid_of_bmcaction y)) xs)

let find_erel ((a,b): Expr.expr * Expr.expr)
              (xs: (Expr.expr * Expr.expr) list) =
  is_some (List.find_opt (
    fun (x,y) -> (Expr.equal a x) && (Expr.equal b y)) xs)

let add_action action (preexec: preexec) : preexec =
  {preexec with actions = action::preexec.actions}

let add_initial_action action (preexec: preexec) : preexec =
  {preexec with initial_actions = action::preexec.initial_actions}

let guard_action (guard: Expr.expr) (BmcAction(pol, g, action): bmc_action) =
  BmcAction(pol, mk_and [guard;g], action)

let guard_preexec (guard: Expr.expr) (preexec: preexec) =
  {preexec with actions = List.map (guard_action guard) preexec.actions}

let combine_preexecs (preexecs: preexec list) =
  List.fold_left (fun acc preexec ->
    { actions         = preexec.actions @ acc.actions
    ; initial_actions = preexec.initial_actions @ acc.initial_actions
    ; sb              = preexec.sb @ acc.sb
    ; asw             = preexec.asw @ acc.asw
    }) mk_initial_preexec preexecs

let compute_sb (xs: bmc_action list) (ys: bmc_action list) : bmcaction_rel list =
  let cp = cartesian_product xs ys in
  List.filter (fun (x,y) -> tid_of_bmcaction x = tid_of_bmcaction y) cp

let compute_maximal (actions: bmc_action list)
                    (rel: bmcaction_rel list)
                    : aid list =
  let candidates = List.map aid_of_bmcaction actions in
  let not_maximal = List.map (fun (a, _) -> aid_of_bmcaction a) rel in
  List.filter (fun x -> not (List.mem x not_maximal)) candidates

let compute_minimal (actions: bmc_action list)
                    (rel: bmcaction_rel list)
                    : aid list =
  let candidates = List.map aid_of_bmcaction actions in
  let not_minimal = List.map (fun (_, b) -> aid_of_bmcaction b) rel in
  List.filter (fun x -> not (List.mem x not_minimal)) candidates

(* Computes Cartesian products of xs and ys, filtered such that
 * (x,y) in result => (tid x, tid y) or (tid y, tid x) in parent_tids.
 *
 * Also only add the maximal actions of xs and minimal actions of ys
 * based on the sb relations.
 *
 * The result overapproximates the relation:
 * e.g. (a,x) and (b,x) may both be in the result even if (a,b) in sb.
 *
 * filter_asw should be called on the result.
 * *)
let compute_asw (xs: bmc_action list)
                (ys: bmc_action list)
                (sb_xs: bmcaction_rel list)
                (sb_ys: bmcaction_rel list)
                (parent_tids: (tid, tid) Pmap.map)
                : bmcaction_rel list =
  let cp = cartesian_product xs ys in
  let (maximal, minimal) = (compute_maximal xs sb_xs,
                            compute_minimal ys sb_ys) in
  List.filter (fun (x,y) ->
    let (tid_x, tid_y) = (tid_of_bmcaction x, tid_of_bmcaction y) in
    let (aid_x, aid_y) = (aid_of_bmcaction x, aid_of_bmcaction y) in
    let p1 = (match Pmap.lookup tid_x parent_tids with (* (x,y) *)
              | Some a -> tid_y = a | _ -> false) in
    let p2 = (match Pmap.lookup tid_y parent_tids with (* (y,x) *)
              | Some a -> tid_x = a | _ -> false) in
    if p1 || p2 then (* check x is maximal, y is minimal *)
      List.mem aid_x maximal && List.mem aid_y minimal
    else false
    ) cp

let filter_asw (asw: bmcaction_rel list)
               (sb : bmcaction_rel list)
               : bmcaction_rel list =
  List.filter (fun (a,b) ->
    List.for_all (fun (x,y) ->
      (* a == x: (a,b) and (a,y) in asw => not sb (b,y) *)
      let fst_test = (aid_of_bmcaction a = aid_of_bmcaction x)
                  && (find_rel (b,y) sb) in
      (* b == y: (a, b) and (x,b) in asw => not sb (a,x) *)
      let snd_test = (aid_of_bmcaction b = aid_of_bmcaction y)
                  && (find_rel (a,x) sb) in
      (not fst_test) && (not snd_test)
    ) asw
  ) asw

(* ===== PPRINTERS ===== *)
let string_of_memory_order = function
  | Cmm_csem.NA      -> "NA"
  | Cmm_csem.Seq_cst -> "seq_cst"
  | Cmm_csem.Relaxed -> "relaxed"
  | Cmm_csem.Release -> "release"
  | Cmm_csem.Acquire -> "acquire"
  | Cmm_csem.Consume -> "consume"
  | Cmm_csem.Acq_rel -> "acq_rel"

let string_of_polarity = function
  | Pos -> "+"
  | Neg -> "-"

let pp_action (a: action) =
  match a with
  | Load(aid,tid,memorder,loc,rval) ->
      sprintf "Load(%d,%d,%s,%s,%s)"
              aid tid (string_of_memory_order memorder)
              (Expr.to_string loc) (Expr.to_string rval)
  | Store(aid, tid, memorder,loc,wval) ->
      sprintf "Store(%d,%d,%s,%s,%s)"
              aid tid (string_of_memory_order memorder)
              (Expr.to_string loc) (Expr.to_string wval)
  | _ -> assert false

let pp_bmcaction (BmcAction(pol, guard, action): bmc_action) =
  sprintf "Action(%s,%s,%s)"
          (*(string_of_polarity pol)*) ""
          (*(Expr.to_string guard)*)   ""
          (pp_action action)

let pp_actionrel ((a,b): bmcaction_rel) =
  sprintf "(%d,%d)" (aid_of_action (get_action a))
                    (aid_of_action (get_action b))

let pp_actionrel_list (xs : bmcaction_rel list) =
  String.concat "\n" (List.map pp_actionrel xs)

let pp_preexec (preexec: preexec) =
  sprintf ">>Initial:\n%s\n>>Actions:\n%s\n>>SB:\n%s\nASW:\n%s"
          (String.concat "\n" (List.map pp_bmcaction preexec.initial_actions))
          (String.concat "\n" (List.map pp_bmcaction preexec.actions))
          "" ""
          (*
          (pp_actionrel_list preexec.sb)
          (pp_actionrel_list preexec.asw)
          *)


(* ===== memory model ===== *)


module type MemoryModel = sig
  type z3_memory_model
  val add_assertions : Solver.solver -> z3_memory_model -> unit

  val compute_executions : preexec -> z3_memory_model
  val extract_executions : Solver.solver -> z3_memory_model -> Expr.expr -> unit
end

module C11MemoryModel : MemoryModel = struct
  type func_decl_ty = string * Sort.sort list * Sort.sort

  type decls = {
    (* Accessors *)
    aid     : FuncDecl.func_decl;
    guard   : FuncDecl.func_decl;
    etype   : FuncDecl.func_decl;
    memord  : FuncDecl.func_decl;
    addr    : FuncDecl.func_decl;
    rval    : FuncDecl.func_decl;
    wval    : FuncDecl.func_decl;

    sb      : FuncDecl.func_decl;
    asw     : FuncDecl.func_decl;
    mo_clk  : FuncDecl.func_decl;

    rf_inv  : FuncDecl.func_decl;

    rs      : FuncDecl.func_decl;
    rmw_dag : FuncDecl.func_decl;
    sw      : FuncDecl.func_decl;
    hb      : FuncDecl.func_decl;
  }

  type fn_apps = {
    getAid    : Expr.expr -> Expr.expr;
    getGuard  : Expr.expr -> Expr.expr;
    getEType  : Expr.expr -> Expr.expr;
    getAddr   : Expr.expr -> Expr.expr;
    getMemord : Expr.expr -> Expr.expr;
    getRval   : Expr.expr -> Expr.expr;
    getWval   : Expr.expr -> Expr.expr;

    isRead    : Expr.expr -> Expr.expr;
    isWrite   : Expr.expr -> Expr.expr;

    sb        : Expr.expr * Expr.expr -> Expr.expr;
    asw       : Expr.expr * Expr.expr -> Expr.expr;

    mo_clk   : Expr.expr -> Expr.expr;
    mo       : Expr.expr * Expr.expr -> Expr.expr;
    rf_inv   : Expr.expr -> Expr.expr;
    rf       : Expr.expr * Expr.expr -> Expr.expr;

    rmw_dag  : Expr.expr * Expr.expr -> Expr.expr;
    rs       : Expr.expr * Expr.expr -> Expr.expr;

    fr       : Expr.expr * Expr.expr -> Expr.expr;
    eco      : Expr.expr * Expr.expr -> Expr.expr;
    sw       : Expr.expr * Expr.expr -> Expr.expr;
    hb       : Expr.expr * Expr.expr -> Expr.expr;
  }

  type assertions = {
    aid            : Expr.expr list;
    guard          : Expr.expr list;
    etype          : Expr.expr list;
    addr           : Expr.expr list;
    memord         : Expr.expr list;
    rval           : Expr.expr list;
    wval           : Expr.expr list;

    sb             : Expr.expr list;
    asw            : Expr.expr list;

    rmw_dag        : Expr.expr list;
    rs             : Expr.expr list;
    sw             : Expr.expr list;
    hb             : Expr.expr list;

    well_formed_rf : Expr.expr list;
    well_formed_mo : Expr.expr list;

    coherence      : Expr.expr list;
  }

  type execution = {
    z3_asserts     : Expr.expr;
    ret            : Expr.expr;

    preexec        : preexec2;
    witness        : witness;
    exdd           : execution_derived_data;

    race_free      : bool;
  }

  type z3_memory_model = {
    event_sort : Sort.sort; (* Enum of memory actions *)
    event_type : Sort.sort; (* Type of memory actions: eg load/store *)

    event_map  : (aid, Expr.expr) Pmap.map;
    action_map : (aid, action) Pmap.map;

    decls      : decls;
    fns        : fn_apps;
    assertions : Expr.expr list;
  }

  let add_assertions solver model = Solver.add solver model.assertions

  (* ==== Helper aliases ==== *)
  let mk_decl = mk_fresh_func_decl
  let apply = FuncDecl.apply

  let mk_forall arglist symlist expr : Expr.expr =
    Quantifier.expr_of_quantifier (Quantifier.mk_forall g_ctx
      arglist symlist expr None [] [] None None)

  (* ==== Type definitions ==== *)
  let mk_event_sort (actions: bmc_action list) =
    Enumeration.mk_sort g_ctx
      (mk_sym "Event")
      (List.map (fun a -> mk_sym (sprintf "#E_%d" (aid_of_bmcaction a)))
                actions)

  let mk_event_type =
    Enumeration.mk_sort g_ctx (mk_sym "EventType")
                        [ mk_sym "Load"
                        ; mk_sym "Store"
                        ; mk_sym "RMW"
                        ; mk_sym "Fence"
                        ; mk_sym "Lock"
                        ; mk_sym "Unlock"
                        ]

  let load_etype  = List.nth (Enumeration.get_consts mk_event_type) 0
  let store_etype = List.nth (Enumeration.get_consts mk_event_type) 1
  let rmw_etype   = List.nth (Enumeration.get_consts mk_event_type) 2
  let fence_etype = List.nth (Enumeration.get_consts mk_event_type) 3

  let action_to_event_type (BmcAction(_,_,a): bmc_action) : Expr.expr =
    match a with
    | Load  _ -> load_etype
    | Store _ -> store_etype
    | RMW   _ -> rmw_etype
    | Fence _ -> fence_etype

  let mk_memord_type =
    Enumeration.mk_sort g_ctx (mk_sym "MemordType")
                        [ mk_sym "NA"
                        ; mk_sym "Seq_cst"
                        ; mk_sym "Relaxed"
                        ; mk_sym "Release"
                        ; mk_sym "Acquire"
                        ; mk_sym "Acq_rel"
                        ]

  let na_memord      = List.nth (Enumeration.get_consts mk_memord_type) 0
  let sc_memord      = List.nth (Enumeration.get_consts mk_memord_type) 1
  let rlx_memord     = List.nth (Enumeration.get_consts mk_memord_type) 2
  let rel_memord     = List.nth (Enumeration.get_consts mk_memord_type) 3
  let acq_memord     = List.nth (Enumeration.get_consts mk_memord_type) 4
  let acq_rel_memord = List.nth (Enumeration.get_consts mk_memord_type) 5

  let action_to_memord (BmcAction(_,_,a): bmc_action) : Expr.expr =
    match memorder_of_action a with
    | NA      -> na_memord
    | Seq_cst -> sc_memord
    | Relaxed -> rlx_memord
    | Release -> rel_memord
    | Acquire -> acq_memord
    | Acq_rel -> acq_rel_memord
    | Consume -> assert false

  let mk_decls (events: Sort.sort) : decls =
    { aid     = mk_decl "aid"     [events]        (Integer.mk_sort g_ctx)
    ; guard   = mk_decl "guard"   [events]        boolean_sort
    ; etype   = mk_decl "etype"   [events]        mk_event_type
    ; addr    = mk_decl "addr"    [events]        AddressSort.mk_sort
    ; memord  = mk_decl "memord"  [events]        mk_memord_type
    ; rval    = mk_decl "rval"    [events]        Loaded.mk_sort
    ; wval    = mk_decl "wval"    [events]        Loaded.mk_sort

    ; sb      = mk_decl "sb"      [events;events] boolean_sort
    ; asw     = mk_decl "asw"     [events;events] boolean_sort
    ; mo_clk  = mk_decl "mo_clk"  [events]        (Integer.mk_sort g_ctx)

    ; rf_inv  = mk_decl "rf_inv"  [events]        events

    ; rs      = mk_decl "rs"      [events;events] boolean_sort
    ; rmw_dag = mk_decl "rmw_dag" [events;events] boolean_sort
    ; sw      = mk_decl "sw"      [events;events] boolean_sort
    ; hb      = mk_decl "hb"      [events;events] boolean_sort
    }

  let mk_fn_apps (decls: decls) : fn_apps =
    let getGuard  = (fun e -> apply decls.guard  [e]) in
    let getEtype  = (fun e -> apply decls.etype  [e]) in
    let getAddr   = (fun e -> apply decls.addr   [e]) in
    let getMemord = (fun e -> apply decls.memord [e]) in
    let getRval   = (fun e -> apply decls.rval   [e]) in
    let getWval   = (fun e -> apply decls.wval   [e]) in

    let isRead  = (fun e -> mk_or [mk_eq (getEtype e) load_etype
                                  ;mk_eq (getEtype e) rmw_etype]) in
    let isWrite = (fun e -> mk_or [mk_eq (getEtype e) store_etype
                                  ;mk_eq (getEtype e) rmw_etype]) in

    let sb     = (fun (e1,e2) -> apply decls.sb  [e1;e2]) in
    let asw    = (fun (e1,e2) -> apply decls.asw [e1;e2]) in

    let mo_clk = (fun e -> apply decls.mo_clk [e]) in
    let mo     = (fun (e1,e2) -> mk_and [mk_lt g_ctx (mo_clk e1) (mo_clk e2)
                                        ;isWrite e1
                                        ;isWrite e2
                                        ;mk_eq (getAddr e1) (getAddr e2)
                                        ]) in
    let rf_inv = (fun e -> apply decls.rf_inv [e]) in
    let rf     = (fun (e1,e2) -> mk_and [isRead e2
                                        ;mk_eq (rf_inv e2) e1
                                        ;]) in

    let rmw_dag = (fun (e1,e2) -> apply decls.rmw_dag [e1;e2]) in
    let rs      = (fun (e1,e2) -> apply decls.rs      [e1;e2]) in
    (* let fr = (rf^-1 ; mo) \ id *)
    let fr     = (fun (e1,e2) -> mk_and [isRead e1
                                        ;mk_not (mk_eq e1 e2)
                                        ;mo (rf_inv(e1), e2)
                                        ]) in
    (* let eco = rf | mo | fr | mo ; rf | fr ; rf *)
    let eco    = (fun (e1,e2) ->
                    mk_or [rf (e1,e2)
                          ;mo (e1,e2)
                          ;fr (e1,e2)
                          ;mk_and [isRead e2; mo (e1,rf_inv(e2))]
                          ;mk_and [isRead e2; fr (e1,rf_inv(e2))]
                          ]
                 ) in
    let sw     = (fun (e1,e2) -> apply decls.sw [e1;e2]) in

    { getAid    = (fun e -> apply decls.aid [e])
    ; getGuard  = getGuard
    ; getEType  = getEtype
    ; getAddr   = getAddr
    ; getMemord = getMemord
    ; getRval   = getRval
    ; getWval   = getWval

    ; isRead    = isRead
    ; isWrite   = isWrite

    ; sb        = sb
    ; asw       = asw
    ; mo_clk    = mo_clk
    ; mo        = mo
    ; rf_inv    = rf_inv
    ; rf        = rf
    ; rmw_dag   = rmw_dag
    ; rs        = rs

    ; fr        = fr
    ; eco       = eco
    ; sw        = sw
    ; hb        = (fun (e1,e2) -> apply decls.hb [e1;e2])
    }

  let compute_executions (exec: preexec) : z3_memory_model =
    let all_actions = exec.initial_actions @ exec.actions in
    let prod_actions = cartesian_product all_actions all_actions in

    let event_sort = mk_event_sort all_actions in
    let event_type = mk_event_type in

    let all_events = Enumeration.get_consts event_sort in
    let prod_events = cartesian_product all_events all_events in

    (* Map from aid to corresponding Z3 event *)
    let event_map = List.fold_left2 (fun acc action z3expr ->
      Pmap.add (aid_of_bmcaction action) z3expr acc)
      (Pmap.empty Pervasives.compare) all_actions all_events in

    let z3action (action: bmc_action) : Expr.expr =
      Pmap.find (aid_of_bmcaction action) event_map in
    let decls :decls = mk_decls event_sort in
    let fns : fn_apps = mk_fn_apps decls in

    (* ==== Define accessors ==== *)
    let aid_asserts = List.map (fun action ->
      mk_eq (fns.getAid (z3action action))
            (Integer.mk_numeral_i g_ctx (aid_of_bmcaction action))
      ) all_actions in

    let guard_asserts = List.map (fun action ->
      mk_eq (fns.getGuard (z3action action))
            (Expr.simplify (guard_of_bmcaction action) None)
      ) all_actions in

    let type_asserts = List.map (fun action ->
      mk_eq (fns.getEType (z3action action))
            (action_to_event_type action)
      ) all_actions in

    let addr_asserts = List.map (fun action ->
      mk_eq (fns.getAddr (z3action action))
            (addr_of_bmcaction action)
    ) (List.filter has_addr all_actions) in

    let memord_asserts = List.map (fun action ->
      mk_eq (fns.getMemord (z3action action))
            (action_to_memord action)
    ) all_actions in

    let rval_asserts = List.map (fun action ->
      mk_eq (fns.getRval (z3action action))
            (Loaded.mk_expr (Expr.simplify (rval_of_action (get_action action))
                                           None))
      ) (List.filter has_rval all_actions) in

    let wval_asserts = List.map (fun action ->
      mk_eq (fns.getWval (z3action action))
            (Loaded.mk_expr (Expr.simplify (wval_of_action (get_action action))
                                           None))
    ) (List.filter has_wval all_actions) in

    (* ==== Preexecution relations ==== *)
    let sb_asserts =
      let sb_with_initial =
        cartesian_product (exec.initial_actions) (exec.actions)
        @ exec.sb in
      let not_sb =
        List.filter (fun p -> not (find_rel p sb_with_initial)) prod_actions in
      (List.map (fun (a,b) -> (mk_eq (fns.sb (z3action a, z3action b)) mk_true))
                sb_with_initial)
     @(List.map (fun (a,b) -> mk_eq (fns.sb (z3action a, z3action b)) mk_false)
                not_sb) in

    let asw_asserts =
      let not_asw =
        List.filter (fun p -> not (find_rel p exec.asw)) prod_actions in
      (List.map (fun (a,b) ->
        mk_eq (fns.asw (z3action a, z3action b)) mk_true)
                exec.asw)
      @ (List.map (fun (a,b) ->
        mk_eq (fns.asw (z3action a, z3action b)) mk_false) not_asw) in

    (* [RMW];rf^t;[RMW] *)
    let rmw_dag_asserts =
      let rmws = List.map z3action (List.filter is_rmw all_actions) in
      let candidates = cartesian_product rmws rmws in

      let not_rel = List.filter
        (fun p -> not (find_erel p candidates)) prod_events in
      List.map (fun (a,b) ->
        let inductive_def = (fun c ->
          mk_and [fns.getGuard c; fns.rf (a,c); fns.rmw_dag(c,b)]) in
        mk_and [fns.getGuard a
               ;fns.getGuard b
               ;mk_or [fns.rf (a,b); mk_or (List.map inductive_def rmws)]
               ]
      ) candidates
      @ List.map (fun (a,b) -> mk_eq (fns.rmw_dag (a,b)) mk_false) not_rel in

    (* let rs = [W] ; (sb & loc)? ; [W & ~NA] ; rf* *)
    let rs_asserts =
      let writes = List.filter has_wval all_actions in
      let atomic_writes = List.filter (fun a -> is_atomic (get_action a))
                                      writes in
      (*let rmws = List.filter is_rmw atomic_writes in*)

      let candidates = cartesian_product writes atomic_writes in
      let not_rel =
        List.filter (fun p -> not (find_rel p candidates)) prod_actions in
      (*[W] ; (sb & loc)? ; [W & ~NA] ;*)
      let sb_write (x,y) =
        let (ex,ey) = (z3action x, z3action y) in
        let same_thread = mk_bool (tid_of_bmcaction x = tid_of_bmcaction y) in
        mk_and [fns.getGuard ex; fns.getGuard ey
               ;mk_or [mk_eq ex ey
                      ;mk_and [same_thread
                              ;fns.sb (ex,ey)
                              ;mk_eq (fns.getAddr ex) (fns.getAddr ey)
                              ]
                      ]
               ] in
      List.map (fun (a,b) ->
        let def =
          match is_rmw b with
          | true ->
              let exists_def = (fun c -> mk_and
                [sb_write (a,c); fns.rmw_dag (z3action c, z3action b)]) in
              mk_or [sb_write (a,b)
                    ;mk_or (List.map exists_def atomic_writes)]
          | false -> sb_write (a,b)
        in
        mk_eq (fns.rs (z3action a, z3action b)) def
      ) candidates
      @ List.map (fun (a,b) -> mk_eq (fns.rs (z3action a, z3action b)) mk_false)
                 not_rel in

    let sw_asserts =
      let atomic_writes =
        List.filter (fun a -> match get_memorder a with
                              | Release | Acq_rel | Seq_cst -> has_wval a
                              | _ -> false) all_actions in
      let atomic_reads =
        List.filter (fun a -> match get_memorder a with
                              | Acquire | Acq_rel | Seq_cst -> has_rval a
                              | _ -> false) all_actions in
      let candidates = cartesian_product atomic_writes atomic_reads in
      let not_rel =
        List.filter (fun p -> not (find_rel p candidates)) prod_actions in

      List.map (fun (a,b) ->
        let (ea,eb) = (z3action a, z3action b) in
        let def =
          mk_and [fns.getGuard ea; fns.getGuard eb
                 ;mk_or [fns.asw (ea,eb)
                        ;fns.rs (ea, fns.rf_inv(eb))
                        ]
                 ] in
        mk_eq (fns.sw (ea,eb)) def
      ) candidates
      @ List.map (fun (a,b) ->
          let (ea,eb) = (z3action a, z3action b) in
          mk_eq (fns.sw (ea,eb)) (fns.asw (ea,eb))) not_rel in

    let hb_asserts =
      List.map (fun (a,b) ->
        let inductive_def = (fun c ->
          mk_and [fns.getGuard c
                 ;mk_or [fns.sb (a,c); fns.sw (a,c)]
                 ;fns.hb (c,b)
                 ]) in
        mk_eq (fns.hb (a,b))
              (mk_and [fns.getGuard a; fns.getGuard b
                      ;mk_or [fns.sb(a,b); fns.sw(a,b)
                             ;mk_or (List.map inductive_def all_events)
                             ]
                      ])
      ) prod_events in

    (*
    let sb_asserts =
      let sb_with_initial =
        cartesian_product (exec.initial_actions) (exec.actions)
        @ exec.sb in
      let sb_eqs = List.map (fun (a,b) ->
        mk_and [mk_eq e0 (z3action a)
               ;mk_eq e1 (z3action b)]) sb_with_initial in
      mk_forall [event_sort; event_sort] [mk_sym "e0"; mk_sym "e1"]
                (mk_eq (fns.sb (e0,e1)) (mk_or sb_eqs)) in
    *)

    (* ==== Well formed assertions ==== *)

    (* ∀e. isRead(e) ∧ guard(e) => isWrite(rf(e)) ∧ same_addr ∧ same_val *)
    let well_formed_rf = List.map (fun action ->
      let e = z3action action in
      mk_implies (fns.getGuard e)
                 (mk_and [fns.isWrite (fns.rf_inv e)
                         ;mk_eq (fns.getAddr e) (fns.getAddr (fns.rf_inv e))
                         ;mk_eq (fns.getRval e) (fns.getWval (fns.rf_inv e))
                         ;fns.getGuard (fns.rf_inv e)
                         ])
    ) (List.filter has_rval all_actions) in

    let well_formed_mo =
      let writes = List.filter has_wval all_actions in
      List.map (fun (w1,w2) ->
        let (e1,e2) = (z3action w1, z3action w2) in
        mk_implies (mk_and [fns.getGuard e1
                           ;fns.getGuard e2
                           ;mk_not (mk_eq e1 e2)
                           ;mk_eq (fns.getAddr e1) (fns.getAddr e2)
                           ])
                  (mk_not (mk_eq (fns.mo_clk e1) (fns.mo_clk e2)))
      ) (cartesian_product writes writes) in

    (* ==== coherence ==== *)
    (* irreflexive (hb ; eco?) as coh *)
    let coherence = List.map (fun (e1,e2) ->
      mk_not (mk_and [fns.getGuard e1
                     ;fns.getGuard e2
                     ;fns.hb  (e1,e2)
                     ;mk_or [mk_eq e1 e2; fns.eco (e2,e1)]
                     ])
    ) (cartesian_product all_events all_events) in

    { event_sort = event_sort
    ; event_type = event_type

    ; event_map  = event_map
    ; action_map = List.fold_left (fun acc a ->
                      Pmap.add (aid_of_bmcaction a) (get_action a) acc)
                      (Pmap.empty Pervasives.compare) all_actions

    ; decls      = decls
    ; fns        = fns

    ; assertions = aid_asserts
                 @ guard_asserts
                 @ type_asserts
                 @ addr_asserts
                 @ memord_asserts
                 @ rval_asserts
                 @ wval_asserts

                 @ sb_asserts
                 @ asw_asserts
                 @ rmw_dag_asserts
                 @ rs_asserts
                 @ sw_asserts
                 @ hb_asserts

                 @ well_formed_rf
                 @ well_formed_mo

                 @ coherence
    }

  let extract_execution (model    : Model.model)
                        (mem      : z3_memory_model)
                        (ret_value: Expr.expr)
                        : execution =
    let interp (expr: Expr.expr) = Option.get (Model.eval model expr false) in
    let fns = mem.fns in
    let proj_fst = (fun (p1,p2) -> (fst p1, fst p2))  in
    let get_bool (b: Expr.expr) = match Boolean.get_bool_value b with
       | L_TRUE -> true
       | L_FALSE -> false
       | _ -> assert false in
    let get_relation rel (p1,p2) = get_bool (interp (rel (snd p1, snd p2))) in

    (* ==== Compute preexecution ==== *)
    let action_events = List.fold_left (fun acc (aid, action) ->
      let event = Pmap.find aid mem.event_map in
      if tid_of_action action = initial_tid then acc
      else if (Boolean.get_bool_value (interp (fns.getGuard event))
               = L_TRUE) then
        let new_action = match action with
          | Load (aid,tid,memorder,loc,rval) ->
              let loc = interp (fns.getAddr event) in
              let rval = interp (fns.getRval event) in
              Load(aid,tid,memorder,loc,rval)
          | Store(aid,tid,memorder,loc,wval) ->
              let loc = interp (fns.getAddr event) in
              let wval = interp (fns.getWval event) in
              Store(aid,tid,memorder,loc,wval)
          | RMW  (aid,tid,memorder,loc,rval,wval) ->
              let loc = interp (fns.getAddr event) in
              let rval = interp (fns.getRval event) in
              let wval = interp (fns.getWval event) in
              RMW(aid,tid,memorder,loc,rval,wval)
          | Fence _ ->
              action
        in (new_action, event) :: acc
      else acc
    ) [] (Pmap.bindings_list mem.action_map) in

    let actions = List.map fst action_events in
    let events = List.map snd action_events in
    let prod = cartesian_product action_events action_events in

    let threads = Pset.elements (
        List.fold_left (fun acc (a, _) -> Pset.add (tid_of_action a) acc)
                       (Pset.empty compare) action_events) in

    let sb = List.filter (get_relation fns.sb) prod in
    let asw = List.filter (get_relation fns.asw) prod in

    let preexec : preexec2 =
      { actions = actions
      ; threads = threads
      ; sb      = List.map proj_fst sb
      ; asw     = List.map proj_fst asw
      } in

    (* ==== Compute witness ===== *)

    let rf = List.filter (get_relation fns.rf) prod in
    let mo = List.filter (get_relation fns.mo) prod in

    let witness : witness =
      { rf = List.map proj_fst rf
      ; mo = List.map proj_fst mo
      ; sc = [] (* TODO *)
      } in

    (* ==== Derived data ==== *)
    let sw = List.filter (get_relation fns.sw) prod in

    let data_race = List.filter (fun ((a1,e1),(a2,e2)) ->
      (aid_of_action a1 <> aid_of_action a2)               &&
      (Expr.equal (addr_of_action a1) (addr_of_action a2)) &&
      (is_write a1 || is_write a2)                         &&
      (tid_of_action a1 <> tid_of_action a2)               &&
      (not (is_atomic a1 && is_atomic a2))   &&
      (not (get_relation fns.hb ((a1,e1),(a2,e2))
            || get_relation fns.hb ((a2,e2),(a1,e1))))
    ) prod in

    let unseq_race = List.filter (fun ((a1,e1),(a2,e2)) ->
      (aid_of_action a1 <> aid_of_action a2)                &&
      (Expr.equal (addr_of_action a1) (addr_of_action a2))  &&
      (is_write a1 || is_write a2)                          &&
      (tid_of_action a1 = tid_of_action a2)                 &&
      (tid_of_action a1 <> initial_tid)                     &&
      (not (get_relation fns.sb ((a1,e1),(a2,e2))
            || get_relation fns.sb ((a2,e2),(a1,e1))))
    ) prod in

    let execution_derived_data =
      { derived_relations = [("sw", List.map proj_fst sw)]
      ; undefined_behaviour =
            [("dr",Two (List.map (fun (e1,e2) -> (fst e1, fst e2)) data_race))
            ;("ur",Two (List.map (fun (e1,e2) -> (fst e1, fst e2)) unseq_race))
            ]
      } in

    (* ===== Assert uniqueness of execution ===== *)
    let guard_asserts = List.map (fun event ->
         mk_eq (fns.getGuard event) (interp (fns.getGuard event))
      ) events in
    let rf_asserts = List.map (fun ((_,e1),(_,e2)) ->
        mk_eq (fns.rf (e1,e2)) mk_true
      ) rf in
    let mo_asserts = List.map (fun ((_,e1),(_,e2)) ->
        mk_eq (fns.mo (e1,e2)) mk_true
      ) mo in
    (*
    print_endline "RF";
    List.iter (fun ((_,e1),(_,e2)) ->
      printf "%s->%s\n" (Expr.to_string e1) (Expr.to_string e2)) rf;

    print_endline "MO";
    List.iter (fun ((_,e1),(_,e2)) ->
      printf "%s->%s\n" (Expr.to_string e1) (Expr.to_string e2)) rf;
    *)

    let ret = interp ret_value in
    printf "RET_VALUE: %s\n" (Expr.to_string ret);

    { z3_asserts = mk_and (List.concat [guard_asserts; rf_asserts; mo_asserts])
    ; ret = ret

    ; preexec = preexec
    ; witness = witness
    ; exdd    = execution_derived_data

    ; race_free = (List.length data_race = 0) && (List.length unseq_race = 0)
    }

  let extract_executions (solver   : Solver.solver)
                         (mem      : z3_memory_model)
                         (ret_value: Expr.expr)
                         : unit =
    Solver.push solver;
    let rec aux ret =
      if Solver.check solver [] = SATISFIABLE then
        let model = Option.get (Solver.get_model solver) in
        let execution = extract_execution model mem ret_value in
        Solver.add solver [mk_not execution.z3_asserts];
        aux (execution :: ret)
      else
        ret
    in
    let executions = aux [] in
    let num_races =
        (List.length (List.filter (fun e -> not e.race_free) executions)) in
    printf "# consistent executions: %d\n" (List.length executions);
    printf "# executions with races: %d\n" num_races;

    printf "Return values: %s\n"
           (String.concat ", " (List.map
              (fun e -> Expr.to_string e.ret) executions));
    List.iteri (fun i exec ->
      let dot_str = pp_dot () (ppmode_default_web,
                        (exec.preexec, Some exec.witness,
                         Some (exec.exdd))) in
      let filename = Printf.sprintf "%s_%d.dot" "graph" i in
      save_to_file filename dot_str;
    ) executions;

    Solver.pop solver 1
end

module BmcMem = C11MemoryModel
