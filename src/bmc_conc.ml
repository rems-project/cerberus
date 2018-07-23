open Bmc_globals
open Bmc_sorts
open Bmc_utils
open Core
open Printf
open Util
open Z3
open Z3.Arithmetic

type aid = int
type tid = int

type z3_location = Expr.expr
type z3_value    = Expr.expr
type guard       = Expr.expr

type memory_order = Cmm_csem.memory_order

type action =
  | Load  of aid * tid * memory_order * z3_location * z3_value
  | Store of aid * tid * memory_order * z3_location * z3_value
  | RMW   of aid * tid * memory_order * z3_location * z3_value * z3_value
  | Fence of aid * tid * memory_order

type bmc_action =
  | BmcAction of polarity * guard * action

let aid_of_action (a: action) = match a with
  | Load  (aid, _, _, _, _)
  | Store (aid, _, _, _, _)
  | RMW   (aid, _, _, _, _, _)
  | Fence (aid, _, _) ->
      aid

let tid_of_action (a: action) = match a with
  | Load  (_, tid, _, _, _)
  | Store (_, tid, _, _, _)
  | RMW   (_, tid, _, _, _, _)
  | Fence (_, tid, _) ->
      tid

let addr_of_action (a: action) = match a with
  | Load  (_, _, _, l, _)
  | Store (_, _, _, l, _)
  | RMW   (_, _, _, l, _, _) -> l
  | Fence (_, _, _) -> assert false

let has_addr (BmcAction(_, _, a): bmc_action) = match a with
  | Load _
  | Store _
  | RMW _ -> true
  | _ -> false

let has_rval (BmcAction(_, _, a): bmc_action) = match a with
  | Load _ | RMW _ -> true
  | _ -> false

let has_wval (BmcAction(_, _, a): bmc_action) = match a with
  | Store _ | RMW _ -> true
  | _ -> false


let rval_of_action (a: action) = match a with
  | Load (_, _, _, _, v)
  | RMW (_, _, _, _, v, _) -> v
  | _ -> assert false

let wval_of_action (a: action) = match a with
  | Store (_, _, _, _, v)
  | RMW   (_, _, _, _, _, v) -> v
  | _ -> assert false

let get_action (BmcAction(_, _, action): bmc_action) =
  action

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

let bmc_action_cmp (BmcAction(_, _, a1)) (BmcAction(_, _, a2)) =
  compare (aid_of_action a1) (aid_of_action a2)

(* ===== PREEXECS ===== *)

type action_rel = bmc_action * bmc_action

type preexec = {
  actions         : bmc_action list;
  initial_actions : bmc_action list;

  sb              : action_rel list;
  asw             : action_rel list;
}

let mk_initial_preexec : preexec =
  { actions         = []
  ; initial_actions = []
  ; sb              = []
  ; asw             = []
  }

let find_rel ((a,b): action_rel) (xs: action_rel list) =
  is_some (List.find_opt (
    fun (x,y) -> (aid_of_bmcaction a = aid_of_bmcaction x)
              && (aid_of_bmcaction b = aid_of_bmcaction y)) xs)

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

let compute_sb (xs: bmc_action list) (ys: bmc_action list) : action_rel list =
  let cp = cartesian_product xs ys in
  List.filter (fun (x,y) -> tid_of_bmcaction x = tid_of_bmcaction y) cp

let compute_maximal (actions: bmc_action list)
                    (rel: action_rel list)
                    : aid list =
  let candidates = List.map aid_of_bmcaction actions in
  let not_maximal = List.map (fun (a, _) -> aid_of_bmcaction a) rel in
  List.filter (fun x -> not (List.mem x not_maximal)) candidates

let compute_minimal (actions: bmc_action list)
                    (rel: action_rel list)
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
                (sb_xs: action_rel list)
                (sb_ys: action_rel list)
                (parent_tids: (tid, tid) Pmap.map)
                : action_rel list =
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

let filter_asw (asw: action_rel list)
               (sb : action_rel list)
               : action_rel list =
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

let pp_actionrel ((a,b): action_rel) =
  sprintf "(%d,%d)" (aid_of_action (get_action a))
                    (aid_of_action (get_action b))

let pp_actionrel_list (xs : action_rel list) =
  String.concat "\n" (List.map pp_actionrel xs)

let pp_preexec (preexec: preexec) =
  sprintf ">>Initial:\n%s\n>>Actions:\n%s\n>>SB:\n%s\nASW:\n%s"
          (String.concat "\n" (List.map pp_bmcaction preexec.initial_actions))
          (String.concat "\n" (List.map pp_bmcaction preexec.actions))
          (pp_actionrel_list preexec.sb)
          (pp_actionrel_list preexec.asw)


(* ===== memory model ===== *)

type z3_memory_model = {
  event_sort : Sort.sort; (* Enum of memory actions *)
  event_type : Sort.sort; (* Type of memory actions: eg load/store *)

  assertions : Expr.expr list;
}

module type MemoryModel = sig
  val compute_executions : preexec -> z3_memory_model
end

module C11MemoryModel : MemoryModel = struct
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

  type func_decl_ty = string * Sort.sort list * Sort.sort

  type decls = {
    (* Accessors *)
    guard  : FuncDecl.func_decl;
    etype  : FuncDecl.func_decl;
    addr   : FuncDecl.func_decl;
    rval   : FuncDecl.func_decl;
    wval   : FuncDecl.func_decl;

    sb     : FuncDecl.func_decl;
    mo_clk : FuncDecl.func_decl;

    rf_inv : FuncDecl.func_decl;
  }

  let mk_decls (events: Sort.sort) : decls =
    { guard  = mk_decl "guard"  [events]        boolean_sort
    ; etype  = mk_decl "etype"  [events]        mk_event_type
    ; addr   = mk_decl "addr"   [events]        AddressSort.mk_sort
    ; rval   = mk_decl "rval"   [events]        Loaded.mk_sort
    ; wval   = mk_decl "wval"   [events]        Loaded.mk_sort

    ; sb     = mk_decl "sb"     [events;events] boolean_sort
    ; mo_clk = mk_decl "mo_clk" [events]        (Integer.mk_sort g_ctx)

    ; rf_inv = mk_decl "rf_inv" [events]        events
    }

  type fn_apps = {
    getGuard : Expr.expr -> Expr.expr;
    getEType : Expr.expr -> Expr.expr;
    getAddr  : Expr.expr -> Expr.expr;
    getRval  : Expr.expr -> Expr.expr;
    getWval  : Expr.expr -> Expr.expr;

    isRead   : Expr.expr -> Expr.expr;
    isWrite  : Expr.expr -> Expr.expr;

    sb       : Expr.expr * Expr.expr -> Expr.expr;

    mo_clk   : Expr.expr -> Expr.expr;
    mo       : Expr.expr * Expr.expr -> Expr.expr;
    rf_inv   : Expr.expr -> Expr.expr;
    rf       : Expr.expr * Expr.expr -> Expr.expr;

    fr       : Expr.expr * Expr.expr -> Expr.expr;
    eco      : Expr.expr * Expr.expr -> Expr.expr;
    hb       : Expr.expr * Expr.expr -> Expr.expr;

  }

  let mk_fn_apps (decls: decls) : fn_apps =
    let getGuard = (fun e -> apply decls.guard [e]) in
    let getEtype = (fun e -> apply decls.etype [e]) in
    let getAddr  = (fun e -> apply decls.addr  [e]) in
    let getRval  = (fun e -> apply decls.rval  [e]) in
    let getWval  = (fun e -> apply decls.wval  [e]) in

    let isRead  = (fun e -> mk_or [mk_eq (getEtype e) load_etype
                                  ;mk_eq (getEtype e) rmw_etype]) in
    let isWrite = (fun e -> mk_or [mk_eq (getEtype e) store_etype
                                  ;mk_eq (getEtype e) rmw_etype]) in

    let sb     = (fun (e1,e2) -> apply decls.sb [e1;e2]) in

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

    { getGuard = getGuard
    ; getEType = getEtype
    ; getAddr  = getAddr
    ; getRval  = getRval
    ; getWval  = getWval

    ; isRead   = isRead
    ; isWrite  = isWrite

    ; sb       = sb
    ; mo_clk   = mo_clk
    ; mo       = mo
    ; rf_inv   = rf_inv
    ; rf       = rf

    ; fr       = fr
    ; eco      = eco
    ; hb       = if g_single_threaded then sb else assert false
    }

   type assertions = {
    guard          : Expr.expr list;
    etype          : Expr.expr list;
    addr           : Expr.expr list;
    rval           : Expr.expr list;
    wval           : Expr.expr list;

    sb             : Expr.expr list;

    well_formed_rf : Expr.expr list;
    well_formed_mo : Expr.expr list;

    coherence      : Expr.expr list;

  }

  let compute_executions (exec: preexec) : z3_memory_model =
    let all_actions = exec.initial_actions @ exec.actions in
    let prod_actions = cartesian_product all_actions all_actions in

    let event_sort = mk_event_sort all_actions in
    let event_type = mk_event_type in

    let all_events = Enumeration.get_consts event_sort in

    (* Map from aid to corresponding Z3 event *)
    let event_map = List.fold_left2 (fun acc action z3expr ->
      Pmap.add (aid_of_bmcaction action) z3expr acc)
      (Pmap.empty Pervasives.compare) all_actions all_events in

    let expr_of_action (action: bmc_action) : Expr.expr =
      Pmap.find (aid_of_bmcaction action) event_map in
    let decls :decls = mk_decls event_sort in
    let fns : fn_apps = mk_fn_apps decls in


    (* ==== Helper functions ==== *)
    (*
    let e0 = Quantifier.mk_bound g_ctx 0 event_sort in
    let e1 = Quantifier.mk_bound g_ctx 1 event_sort in
    let e2 = Quantifier.mk_bound g_ctx 2 event_sort in
    *)

    (* ==== Define accessors ==== *)

    let guard_asserts = List.map (fun action ->
      mk_eq (fns.getGuard (expr_of_action action))
            (Expr.simplify (guard_of_bmcaction action) None))
      all_actions in

    let type_asserts = List.map (fun action ->
      mk_eq (fns.getEType (expr_of_action action))
            (action_to_event_type action)
      ) all_actions in

    let addr_asserts = List.map (fun action ->
      mk_eq (fns.getAddr (expr_of_action action))
            (addr_of_bmcaction action)
    ) (List.filter has_addr all_actions) in

    let rval_asserts = List.map (fun action ->
      mk_eq (fns.getRval (expr_of_action action))
            (Loaded.mk_expr (Expr.simplify (rval_of_action (get_action action))
                                           None))
      ) (List.filter has_rval all_actions) in

    let wval_asserts = List.map (fun action ->
      mk_eq (fns.getWval (expr_of_action action))
            (Loaded.mk_expr (Expr.simplify (wval_of_action (get_action action))
                                           None))
    ) (List.filter has_wval all_actions) in

    (* ==== Preexecution relations ==== *)
    let sb_asserts =
      let sb_with_initial =
        cartesian_product (exec.initial_actions) (exec.actions)
        @ exec.sb in
      let not_sb =
        List.filter (fun (x,y) -> not (find_rel (x,y) sb_with_initial))
                    prod_actions in
      (List.map (fun (a,b) ->
        let (ea,eb) = (expr_of_action a, expr_of_action b) in
                   (mk_eq (fns.sb (ea, eb)) mk_true)) sb_with_initial)
     @(List.map (fun (a,b) ->
        let (ea,eb) = (expr_of_action a, expr_of_action b) in
                   mk_eq (fns.sb (ea, eb)) mk_false)
        not_sb) in
    (*
    let sb_asserts =
      let sb_with_initial =
        cartesian_product (exec.initial_actions) (exec.actions)
        @ exec.sb in
      let sb_eqs = List.map (fun (a,b) ->
        mk_and [mk_eq e0 (expr_of_action a)
               ;mk_eq e1 (expr_of_action b)]) sb_with_initial in
      mk_forall [event_sort; event_sort] [mk_sym "e0"; mk_sym "e1"]
                (mk_eq (fns.sb (e0,e1)) (mk_or sb_eqs)) in
  *)

    (* ==== Well formed assertions ==== *)

    (* ∀e. isRead(e) ∧ guard(e) => isWrite(rf(e)) ∧ same_addr ∧ same_val *)
    let well_formed_rf = List.map (fun action ->
      let e = expr_of_action action in
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
        let (e1,e2) = (expr_of_action w1, expr_of_action w2) in
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

    ; assertions = guard_asserts
                 @ type_asserts
                 @ addr_asserts
                 @ rval_asserts
                 @ wval_asserts

                 @ sb_asserts

                 @ well_formed_rf
                 @ well_formed_mo

                 @ coherence
    }
end

module BmcMem = C11MemoryModel
