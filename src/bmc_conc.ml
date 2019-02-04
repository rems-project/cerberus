open Bmc_cat
open Bmc_common
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

  po              : (bmc_action * bmc_action) list;
  asw             : (bmc_action * bmc_action) list;
  rmw             : (bmc_action * bmc_action) list;

  (* dependencies *)
  addr            : (bmc_action * bmc_action) list;
  data            : (bmc_action * bmc_action) list;
  ctrl            : (bmc_action * bmc_action) list;
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

let is_atomic_bmcaction (bmcaction: bmc_action) =
  is_atomic (get_action bmcaction)

let get_memorder (BmcAction (_, _, action): bmc_action) =
  memorder_of_action action

let tid_of_bmcaction (bmcaction: bmc_action) =
  tid_of_action (get_action bmcaction)

let aid_of_bmcaction (bmcaction: bmc_action) =
  aid_of_action (get_action bmcaction)

(* Base address *)
let addr_of_bmcaction (bmcaction: bmc_action) =
  PointerSort.get_addr (addr_of_action (get_action bmcaction))

let ctype_of_bmcaction(bmcaction: bmc_action) : ctype =
  ctype_of_action (get_action bmcaction)

let size_of_bmcaction(bmcaction: bmc_action) (file: unit typed_file) : int =
  PointerSort.type_size (ctype_of_bmcaction bmcaction) file

let max_addr_of_bmcaction (bmcaction: bmc_action) (file: unit typed_file) =
  let base_addr = addr_of_bmcaction bmcaction in
  let size = size_of_bmcaction bmcaction file in
  assert (size > 0);
  PointerSort.shift_index_by_n base_addr (int_to_z3 (size - 1))

let is_initial_bmcaction (bmcaction: bmc_action) =
  tid_of_bmcaction bmcaction = initial_tid

let guard_of_bmcaction (BmcAction(_, g, _) : bmc_action) = g

let is_pos_action (BmcAction(pol, _, _): bmc_action) = match pol with
  | Pos -> true
  | Neg -> false

let is_rmw (a: bmc_action) = match get_action a with
  | RMW _ -> true
  | _ -> false

let is_fence_action (BmcAction(_,_,a): bmc_action) =
  is_fence a


let bmcaction_cmp (BmcAction(_, _, a1)) (BmcAction(_, _, a2)) =
  compare (aid_of_action a1) (aid_of_action a2)

(* ===== PREEXECS ===== *)

type bmcaction_rel = bmc_action * bmc_action
type aid_rel = aid * aid

let mk_initial_preexec : preexec =
  { actions         = []
  ; initial_actions = []
  ; po              = []
  ; asw             = []
  ; rmw             = []
  ; addr            = []
  ; data            = []
  ; ctrl            = []
  }

let aid_of_bmcaction_rel ((a1,a2): bmcaction_rel) =
  (aid_of_bmcaction a1, aid_of_bmcaction a2)

let find_rel ((a,b): bmcaction_rel) (xs: bmcaction_rel list) =
  is_some (List.find_opt (
    fun (x,y) -> (aid_of_bmcaction a = aid_of_bmcaction x)
              && (aid_of_bmcaction b = aid_of_bmcaction y)) xs)

let find_erel ((a,b): Expr.expr * Expr.expr)
              (xs: (Expr.expr * Expr.expr) list) =
  is_some (List.find_opt (
    fun (x,y) -> (Expr.equal a x) && (Expr.equal b y)) xs)

let not_related (relation: 'a list)
                (candidates: 'a list)
                (contains: 'a -> 'a list -> bool) =
  List.filter (fun p -> not (contains p relation)) candidates

let add_action action (preexec: preexec) : preexec =
  {preexec with actions = action::preexec.actions}

let add_initial_action action (preexec: preexec) : preexec =
  {preexec with initial_actions = action::preexec.initial_actions}

let guard_action (guard: Expr.expr) (BmcAction(pol, g, action): bmc_action) =
  BmcAction(pol, mk_and [guard;g], action)

let guard_preexec (guard: Expr.expr) (preexec: preexec) =
  {preexec with actions = List.map (guard_action guard) preexec.actions}

(*let combine_preexecs (preexecs: preexec list) =
  List.fold_left (fun acc preexec ->
    { actions         = preexec.actions @ acc.actions
    ; initial_actions = preexec.initial_actions @ acc.initial_actions
    ; po              = preexec.po @ acc.po
    ; asw             = preexec.asw @ acc.asw
    ; rmw             = preexec.rmw @ acc.rmw
    }) mk_initial_preexec preexecs *)

let compute_po (xs: bmc_action list) (ys: bmc_action list) : bmcaction_rel list =
  let cp = cartesian_product xs ys in
  List.filter (fun (x,y) -> tid_of_bmcaction x = tid_of_bmcaction y) cp

(*let combine_preexecs_and_po (p1: preexec) (p2: preexec) =
  let combined = combine_preexecs [p1;p2] in
  let extra_po = compute_po p1.actions p2.actions in
  {combined with po = extra_po @ combined.po}
*)

(*let compute_maximal (actions: bmc_action list)
                    (rel: bmcaction_rel list)
                    : aid list =
  let candidates = List.map aid_of_bmcaction actions in
  let not_maximal = List.map (fun (a, _) -> aid_of_bmcaction a) rel in
  List.filter (fun x -> not (List.mem x not_maximal)) candidates
  *)

(*let compute_minimal (actions: bmc_action list)
                    (rel: bmcaction_rel list)
                    : aid list =
  let candidates = List.map aid_of_bmcaction actions in
  let not_minimal = List.map (fun (_, b) -> aid_of_bmcaction b) rel in
  List.filter (fun x -> not (List.mem x not_minimal)) candidates
  *)

(* Computes Cartesian products of xs and ys, filtered such that
 * (x,y) in result => (tid x, tid y) or (tid y, tid x) in parent_tids.
 *
 * Also only add the maximal actions of xs and minimal actions of ys
 * based on the po relations.
 *
 * The result overapproximates the relation:
 * e.g. (a,x) and (b,x) may both be in the result even if (a,b) in po.
 *
 * filter_asw should be called on the result.
 *
 * TODO: buggy -- can miss relation. Let's just add everything.
 * *)
(*let compute_asw (xs: bmc_action list)
                (ys: bmc_action list)
                (po_xs: bmcaction_rel list)
                (po_ys: bmcaction_rel list)
                (parent_tids: (tid, tid) Pmap.map)
                : bmcaction_rel list =
  let cp = cartesian_product xs ys in
  let (maximal, minimal) = (compute_maximal xs po_xs,
                            compute_minimal ys po_ys) in
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
*)
(*
let filter_asw (asw: bmcaction_rel list)
               (po : bmcaction_rel list)
               : bmcaction_rel list =
  List.filter (fun (a,b) ->
    List.for_all (fun (x,y) ->
      (* a == x: (a,b) and (a,y) in asw => not po (b,y) *)
      let fst_test = (aid_of_bmcaction a = aid_of_bmcaction x)
                  && (find_rel (b,y) po) in
      (* b == y: (a, b) and (x,b) in asw => not po (a,x) *)
      let snd_test = (aid_of_bmcaction b = aid_of_bmcaction y)
                  && (find_rel (a,x) po) in
      (not fst_test) && (not snd_test)
    ) asw
  ) asw
*)
(* ===== PPRINTERS ===== *)
let string_of_memory_order = function
  | C_mem_order mo ->
      (match mo with
       | Cmm_csem.NA      -> "NA"
       | Cmm_csem.Seq_cst -> "seq_cst"
       | Cmm_csem.Relaxed -> "relaxed"
       | Cmm_csem.Release -> "release"
       | Cmm_csem.Acquire -> "acquire"
       | Cmm_csem.Consume -> assert false
       | Cmm_csem.Acq_rel -> "acq_rel"
      )
  | Linux_mem_order mo ->
      (match mo with
       | Linux.Once      -> "once"
       | Linux.Acquire0  -> "linux_acquire"
       | Linux.Release0  -> "linux_release"
       | Linux.Rmb       -> "rmb"
       | Linux.Wmb       -> "wmb"
       | Linux.Mb        -> "mb"
       | Linux.RbDep     -> "rbdep"
       | Linux.RcuLock   -> "rculock"
       | Linux.RcuUnlock -> "rcuunlock"
       | Linux.SyncRcu   -> "syncrcu" )


let string_of_polarity = function
  | Pos -> "+"
  | Neg -> "-"

let pp_action (a: action) =
  match a with
  | Load(aid,tid,memorder,loc,rval,_) ->
      sprintf "Load(%d,%d,%s,%s,%s)"
              aid tid (string_of_memory_order memorder)
              (Expr.to_string loc) (Expr.to_string rval)
  | Store(aid,tid,memorder,loc,wval,_) ->
      sprintf "Store(%d,%d,%s,%s,%s)"
              aid tid (string_of_memory_order memorder)
              (Expr.to_string loc) (Expr.to_string wval)
  | RMW(aid,tid,memorder,loc,rval,wval,_) ->
      sprintf "RMW(%d,%d,%s,%s,%s,%s)"
              aid tid (string_of_memory_order memorder)
              (Expr.to_string loc) (Expr.to_string wval) (Expr.to_string rval)
  | Fence(aid,tid,memorder) ->
      sprintf "F(%d,%d,%s)"
              aid tid (string_of_memory_order memorder)

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
  sprintf ">>Initial:\n%s\n>>Actions:\n%s\n>>PO:\n%s\nASW:\n%s\nAddr:\n%s\nData:\n%s\nCtrl:\n%s\n"
          (String.concat "\n" (List.map pp_bmcaction preexec.initial_actions))
          (String.concat "\n" (List.map pp_bmcaction preexec.actions))
          (*"" ""*)
          (pp_actionrel_list preexec.po)
          (pp_actionrel_list preexec.asw)
          (pp_actionrel_list preexec.addr)
          (pp_actionrel_list preexec.data)
          (pp_actionrel_list preexec.ctrl)



(* ===== memory model ===== *)
module type MemoryModel = sig
  type z3_memory_model
  val add_assertions : Solver.solver -> z3_memory_model -> unit
  val get_assertions : z3_memory_model -> Expr.expr list

  val compute_executions : preexec -> (unit typed_file) -> z3_memory_model
  val extract_executions : Solver.solver -> z3_memory_model -> Expr.expr
                           -> (alloc, allocation_metadata) Pmap.map option
                           -> string * string list * bool
end

module MemoryModelCommon = struct
  let mk_event_sort (actions: bmc_action list) =
    Enumeration.mk_sort g_ctx
      (mk_sym "Event")
      (List.map (fun a -> mk_sym (sprintf "#E_%d" (aid_of_bmcaction a)))
                actions)

  (* EVENT TYPES *)
  let mk_event_type =
    Enumeration.mk_sort g_ctx (mk_sym "EventType")
                        [ mk_sym "Load"
                        ; mk_sym "Store"
                        ; mk_sym "RMW"
                        ; mk_sym "Fence"
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

  (* MEMORY ORDER TYPE *)
  let mk_memord_type =
    Enumeration.mk_sort g_ctx (mk_sym "MemordType")
                        [ mk_sym "NA"
                        ; mk_sym "Seq_cst"
                        ; mk_sym "Relaxed"
                        ; mk_sym "Release"
                        ; mk_sym "Acquire"
                        ; mk_sym "Acq_rel"
                        ; mk_sym "Linux_once"
                        ; mk_sym "Linux_acquire"
                        ; mk_sym "Linux_release"
                        ; mk_sym "Linux_rmb"
                        ; mk_sym "Linux_wmb"
                        ; mk_sym "Linux_mb"
                        ; mk_sym "Linux_rbdep"
                        ; mk_sym "Linux_rculock"
                        ; mk_sym "Linux_rcuunlock"
                        ; mk_sym "Linux_syncrcu"
                        ]

  let na_memord      = List.nth (Enumeration.get_consts mk_memord_type) 0
  let sc_memord      = List.nth (Enumeration.get_consts mk_memord_type) 1
  let rlx_memord     = List.nth (Enumeration.get_consts mk_memord_type) 2
  let rel_memord     = List.nth (Enumeration.get_consts mk_memord_type) 3
  let acq_memord     = List.nth (Enumeration.get_consts mk_memord_type) 4
  let acq_rel_memord = List.nth (Enumeration.get_consts mk_memord_type) 5

  let linux_once_memord = List.nth (Enumeration.get_consts mk_memord_type) 6
  let linux_acquire_memord = List.nth (Enumeration.get_consts mk_memord_type) 7
  let linux_release_memord = List.nth (Enumeration.get_consts mk_memord_type) 8
  let linux_rmb_memord = List.nth (Enumeration.get_consts mk_memord_type) 9
  let linux_wmb_memord = List.nth (Enumeration.get_consts mk_memord_type) 10
  let linux_mb_memord = List.nth (Enumeration.get_consts mk_memord_type) 11
  let linux_rbdep_memord = List.nth (Enumeration.get_consts mk_memord_type) 12

  let action_to_memord (BmcAction(_,_,a): bmc_action) : Expr.expr =
    match memorder_of_action a with
    | C_mem_order mo ->
      begin match mo with
      | NA      -> na_memord
      | Seq_cst -> sc_memord
      | Relaxed -> rlx_memord
      | Release -> rel_memord
      | Acquire -> acq_memord
      | Acq_rel -> acq_rel_memord
      | Consume -> assert false
      end
    | Linux_mem_order mo ->
        Linux.(begin match mo with
        | Once     -> linux_once_memord
        | Acquire0 -> linux_acquire_memord
        | Release0 -> linux_release_memord
        | Rmb      -> linux_rmb_memord
        | Wmb      -> linux_wmb_memord
        | Mb       -> linux_mb_memord
        | RbDep    -> linux_rbdep_memord
        | _        -> assert false
        end)

  (* BUILT IN DECLARATIONS *)
  type builtin_decls = {
    aid      : FuncDecl.func_decl;
    tid      : FuncDecl.func_decl;
    guard    : FuncDecl.func_decl;
    etype    : FuncDecl.func_decl;
    memord   : FuncDecl.func_decl;
    addr     : FuncDecl.func_decl;
    addr_max : FuncDecl.func_decl;
    rval     : FuncDecl.func_decl;
    wval     : FuncDecl.func_decl;

    rf_inv   : FuncDecl.func_decl;
    same_loc : FuncDecl.func_decl;

    co_clk   : FuncDecl.func_decl;

    po       : FuncDecl.func_decl;
    asw      : FuncDecl.func_decl;

    addr_dep : FuncDecl.func_decl;
    data_dep : FuncDecl.func_decl;
    ctrl_dep : FuncDecl.func_decl;

  }

  let apply = FuncDecl.apply
  let mk_decl = mk_fresh_func_decl

  let mk_decls (events: Sort.sort) : builtin_decls =
    { aid      = mk_decl "aid"      [events] (Integer.mk_sort g_ctx)
    ; tid      = mk_decl "tid"      [events] (Integer.mk_sort g_ctx)
    ; guard    = mk_decl "guard"    [events] boolean_sort
    ; etype    = mk_decl "etype"    [events] mk_event_type
    ; addr     = mk_decl "addr"     [events] PointerSort.mk_addr_sort
    ; addr_max = mk_decl "addr_max" [events] PointerSort.mk_addr_sort
    ; memord   = mk_decl "memord"   [events] mk_memord_type
    ; rval     = mk_decl "rval"     [events] Loaded.mk_sort
    ; wval     = mk_decl "wval"     [events] Loaded.mk_sort

    ; rf_inv   = mk_decl "rf_inv"   [events] events
    ; same_loc = mk_decl "same_loc" [events; events] boolean_sort

    ; co_clk   = mk_decl "co_clk"   [events] (Integer.mk_sort g_ctx)

    ; po       = mk_decl "po"       [events;events] boolean_sort
    ; asw      = mk_decl "asw"      [events;events] boolean_sort

    ; addr_dep = mk_decl "addr_dep" [events;events] boolean_sort
    ; data_dep = mk_decl "data_dep" [events;events] boolean_sort
    ; ctrl_dep = mk_decl "ctrl_dep" [events;events] boolean_sort
    }

  type builtin_fnapps = {
    getAid     : Expr.expr -> Expr.expr;
    getTid     : Expr.expr -> Expr.expr;
    getGuard   : Expr.expr -> Expr.expr;
    getEtype   : Expr.expr -> Expr.expr;
    getAddr    : Expr.expr -> Expr.expr;
    getAddrMax : Expr.expr -> Expr.expr;
    getMemord  : Expr.expr -> Expr.expr;
    getRval    : Expr.expr -> Expr.expr;
    getWval    : Expr.expr -> Expr.expr;

    isRead     : Expr.expr -> Expr.expr;
    isWrite    : Expr.expr -> Expr.expr;
    same_loc   : Expr.expr * Expr.expr -> Expr.expr;

    internal   : Expr.expr * Expr.expr -> Expr.expr;
    ext        : Expr.expr * Expr.expr -> Expr.expr;

    rf_inv     : Expr.expr -> Expr.expr;
    rf         : Expr.expr * Expr.expr -> Expr.expr;

    rfi        : Expr.expr * Expr.expr -> Expr.expr;
    rfe        : Expr.expr * Expr.expr -> Expr.expr;

    co_clk     : Expr.expr -> Expr.expr;
    co         : Expr.expr * Expr.expr -> Expr.expr;

    po         : Expr.expr * Expr.expr -> Expr.expr;
    po_loc     : Expr.expr * Expr.expr -> Expr.expr;
    asw        : Expr.expr * Expr.expr -> Expr.expr;

    addr_dep   : Expr.expr * Expr.expr -> Expr.expr;
    data_dep   : Expr.expr * Expr.expr -> Expr.expr;
    ctrl_dep   : Expr.expr * Expr.expr -> Expr.expr;

  }

  let mk_fn_apps (decls: builtin_decls) : builtin_fnapps =
    let getAid     = (fun e -> apply decls.aid      [e]) in
    let getTid     = (fun e -> apply decls.tid      [e]) in
    let getGuard   = (fun e -> apply decls.guard    [e]) in
    let getEtype   = (fun e -> apply decls.etype    [e]) in
    let getAddr    = (fun e -> apply decls.addr     [e]) in
    let getAddrMax = (fun e -> apply decls.addr_max [e]) in
    let getMemord  = (fun e -> apply decls.memord   [e]) in
    let getRval    = (fun e -> apply decls.rval     [e]) in
    let getWval    = (fun e -> apply decls.wval     [e]) in
    let isRead     = (fun e -> mk_or [mk_eq (getEtype e) load_etype
                                     ;mk_eq (getEtype e) rmw_etype]) in
    let isWrite    = (fun e -> mk_or [mk_eq (getEtype e) store_etype
                                     ;mk_eq (getEtype e) rmw_etype]) in
    (* TODO: hack. Ensure load address \subseteq store address *)
    (* TODO: dangerous. not an equivalence relation *)
    let same_loc   = (fun (e1,e2) -> apply decls.same_loc [e1;e2]) in

    let internal   = (fun (e1,e2) -> mk_eq (getTid e1) (getTid e2)) in
    let ext        = (fun (e1,e2) -> mk_not (mk_eq (getTid e1) (getTid e2))) in

    let rf_inv = (fun e -> apply decls.rf_inv [e]) in
    let rf     = (fun (e1,e2) -> mk_and [isRead e2
                                        ;mk_eq (rf_inv e2) e1
                                        ]) in
    let rfi    = (fun (e1,e2) -> mk_and [rf (e1,e2)
                                        ;internal (e1,e2)]) in
    let rfe    = (fun (e1,e2) -> mk_and [rf (e1,e2)
                                        ;ext (e1,e2)]) in

    let co_clk = (fun e -> apply decls.co_clk [e]) in

    let po     = (fun (e1,e2) -> apply decls.po [e1;e2]) in
    let po_loc = (fun (e1,e2) -> mk_and [po (e1,e2)
                                        ;same_loc (e1,e2)]) in

    { getAid     = getAid
    ; getTid     = getTid
    ; getGuard   = getGuard
    ; getEtype   = getEtype
    ; getAddr    = getAddr
    ; getAddrMax = getAddrMax
    ; getMemord  = getMemord
    ; getRval    = getRval
    ; getWval    = getWval

    ; isRead    = isRead
    ; isWrite   = isWrite
    ; same_loc  = same_loc

    ; internal  = internal
    ; ext       = ext

    ; rf        = rf
    ; rf_inv    = rf_inv
    ; rfi       = rfi
    ; rfe       = rfe

    ; co_clk    = co_clk
    ; co        = (fun (e1,e2) -> mk_and [mk_lt g_ctx (co_clk e1) (co_clk e2)
                                         ;isWrite e1
                                         ;isWrite e2
                                         ;same_loc (e1,e2)
                                         ])

    ; po        = po
    ; po_loc    = po_loc
    ; asw       = (fun (e1,e2) -> apply decls.asw [e1;e2])

    ; addr_dep  = (fun (e1,e2) -> apply decls.addr_dep [e1;e2])
    ; data_dep  = (fun (e1,e2) -> apply decls.data_dep [e1;e2])
    ; ctrl_dep  = (fun (e1,e2) -> apply decls.ctrl_dep [e1;e2])
    }

  type ret =
    { event_sort : Sort.sort
    ; event_map  : (aid, Expr.expr) Pmap.map
    ; decls      : builtin_decls
    ; fns        : builtin_fnapps
    ; assertions : Expr.expr list

    ; po_assert       : Expr.expr list
    ; asw_assert      : Expr.expr list
    ; addr_assert     : Expr.expr list
    ; data_assert     : Expr.expr list
    ; ctrl_assert     : Expr.expr list
    ; well_formed_rf  : Expr.expr list
    ; well_formed_co  : Expr.expr list
    ; co_init         : Expr.expr list
    }

  let gen_all_assertions (ret: ret) =
    let common =
        ret.po_assert
      @ ret.asw_assert
      @ ret.well_formed_rf
      @ ret.well_formed_co
      @ ret.co_init
      @ ret.assertions in
    if g_parse_from_model then
        ret.addr_assert
      @ ret.data_assert
      @ ret.ctrl_assert
      @ common
    else common

  let initialise (exec: preexec) (file: unit typed_file) =
    let all_actions = exec.initial_actions @ exec.actions in
    let prod_actions = cartesian_product all_actions all_actions in
    bmc_debug_print 3 (sprintf "# actions: %d" (List.length all_actions));
    List.iter (fun a -> bmc_debug_print 5 (pp_bmcaction a)) all_actions;

    let event_sort = mk_event_sort all_actions in
    let all_events = Enumeration.get_consts event_sort in
    (* Map from aid to corresponding Z3 event *)
    let event_map = List.fold_left2 (fun acc action z3expr ->
      Pmap.add (aid_of_bmcaction action) z3expr acc)
      (Pmap.empty Pervasives.compare) all_actions all_events in
    let z3action (action: bmc_action) : Expr.expr =
      Pmap.find (aid_of_bmcaction action) event_map in
    let decls = mk_decls event_sort in
    let fns = mk_fn_apps decls in

    let writes = List.filter has_wval all_actions in
    let reads = List.filter has_rval all_actions in

    let aid_asserts = List.map (fun action ->
      mk_eq (fns.getAid (z3action action))
            (Integer.mk_numeral_i g_ctx (aid_of_bmcaction action))
      ) all_actions in

    let tid_asserts = List.map (fun action ->
      mk_eq (fns.getTid (z3action action))
            (Integer.mk_numeral_i g_ctx (tid_of_bmcaction action))
      ) all_actions in

    let guard_asserts = List.map (fun action ->
      mk_eq (fns.getGuard (z3action action))
            (Expr.simplify (guard_of_bmcaction action) None)
      ) all_actions in

    let type_asserts = List.map (fun action ->
      mk_eq (fns.getEtype (z3action action)) (action_to_event_type action)
      ) all_actions in

    let addr_asserts = List.map (fun action ->
      mk_eq (fns.getAddr (z3action action)) (addr_of_bmcaction action)
    ) (List.filter has_addr all_actions) in

    let addr_max_asserts = List.map (fun action ->
      mk_eq (fns.getAddrMax (z3action action)) (max_addr_of_bmcaction action file)
    ) (List.filter has_addr all_actions) in

    let memord_asserts = List.map (fun action ->
      mk_eq (fns.getMemord (z3action action)) (action_to_memord action)
    ) all_actions in

    let rval_asserts = List.map (fun action ->
      mk_eq (fns.getRval (z3action action))
            (Loaded.mk_expr (Expr.simplify (rval_of_action (get_action action))
                                           None))
      ) reads in

    let wval_asserts = List.map (fun action ->
      mk_eq (fns.getWval (z3action action))
            (Loaded.mk_expr (Expr.simplify (wval_of_action (get_action action))
                                           None))
    ) writes in

    (* Doing it this way is faster *)
    (* TODO: dangerous. not an equivalence relation *)
    (* TODO: Disgusting and hacky *)
    let same_loc_asserts =
      let mk_same_loc = (fun (a,b) -> fns.same_loc (z3action a, z3action b)) in
      let get_addr a = fns.getAddr (z3action a) in
      let get_addr_max a = fns.getAddrMax (z3action a) in
      (* Read pairs *)
      let r_r = cartesian_product reads reads in
      (* Write pairs *)
      let w_w = cartesian_product writes writes in
      (* Write/Read pairs *)
      let w_r = cartesian_product writes reads in
      (* Read/write pairs *)
      let r_w = cartesian_product reads writes in

      let candidates = r_r @ w_w @ w_r @ r_w in
      let not_rel = not_related candidates prod_actions find_rel in
      (List.map (fun (r1,r2) -> mk_eq (mk_same_loc (r1,r2))
                                      (mk_eq (get_addr r1) (get_addr r2)))
                r_r) @
      (List.map (fun (w1,w2) ->
        mk_eq (mk_same_loc (w1,w2))
              (mk_or [PointerSort.addr_subset (get_addr w1)
                                              (get_addr w2) (get_addr_max w2)
                     ;PointerSort.addr_subset (get_addr w2)
                                              (get_addr w1) (get_addr_max w1)
                     ])
      ) w_w) @
      (List.map (fun (w,r) ->
        mk_eq (mk_same_loc (w,r))
              (PointerSort.addr_subset (get_addr r) (get_addr w) (get_addr_max w))
      ) w_r) @
      (List.map (fun (r,w) ->
        mk_eq (mk_same_loc (r,w))
              (PointerSort.addr_subset (get_addr r) (get_addr w) (get_addr_max w))
      ) r_w) @
      (List.map (fun (a,b) -> mk_eq (mk_same_loc (a,b)) mk_false) not_rel) in


    (* ==== Well formed assertions ==== *)
    (* TODO: value equality; we assume e is a read with a single addr \subseteq
     * write *)
    let well_formed_rf = List.map (fun action ->
      let e = z3action action in
      let read_addr = PointerSort.get_index_from_addr (addr_of_bmcaction action) in
      let write_base = PointerSort.get_index_from_addr (fns.getAddr (fns.rf_inv e)) in
      let diff = binop_to_z3 OpSub read_addr write_base in
      let sizeof_read = size_of_bmcaction action file in
      let index = binop_to_z3 OpDiv diff (int_to_z3 sizeof_read) in

      let indexed_wval =
          Loaded.get_ith_in_loaded_2 index (fns.getWval (fns.rf_inv e)) in
      mk_implies (fns.getGuard e)
                 (mk_and [fns.isWrite (fns.rf_inv e)
                         ;fns.same_loc (e, fns.rf_inv e)
                         (*;mk_eq (fns.getRval e) (fns.getWval (fns.rf_inv e))*)
                         ;mk_eq (fns.getRval e) indexed_wval
                         ;fns.getGuard (fns.rf_inv e)
                         ])
      ) reads in

    let well_formed_co =
      List.map (fun (w1,w2) ->
        let (e1,e2) = (z3action w1, z3action w2) in
        mk_implies (mk_and [fns.getGuard e1
                           ;fns.getGuard e2
                           ;mk_not (mk_eq e1 e2)
                           ;fns.same_loc(e1,e2)
                           ])
                  (mk_not (mk_eq (fns.co_clk e1) (fns.co_clk e2)))
      ) (cartesian_product writes writes) in

    let co_init =
      List.map (fun e ->
        mk_eq (fns.co_clk (z3action e)) (Integer.mk_numeral_i g_ctx 0))
      exec.initial_actions
      @ List.map (fun e ->
          mk_gt g_ctx (fns.co_clk (z3action e)) (Integer.mk_numeral_i g_ctx 0))
        exec.actions
    in

    let asserts_from_relation rel fn =
      let mk_rel = (fun (a,b) -> fn (z3action a, z3action b)) in
      let not_rel = not_related rel prod_actions find_rel in
        (List.map (fun (a,b) -> mk_eq (mk_rel (a,b)) mk_true) rel)
      @ (List.map (fun (a,b) -> mk_eq (mk_rel (a,b)) mk_false) not_rel) in


    (* ==== po assert ==== *)
    (*let po_asserts =
      let mk_po = (fun (a,b) -> fns.po (z3action a, z3action b)) in
      let not_po = not_related exec.po prod_actions find_rel in
        (List.map (fun (a,b) -> mk_eq (mk_po (a,b)) mk_true) exec.po)
      @ (List.map (fun (a,b) -> mk_eq (mk_po (a,b)) mk_false) not_po) in*)
    let po_asserts = asserts_from_relation exec.po fns.po in
    let asw_asserts = asserts_from_relation exec.asw fns.asw in
    let addr_dep_asserts = asserts_from_relation exec.addr fns.addr_dep in
    let data_dep_asserts = asserts_from_relation exec.data fns.data_dep in
    let ctrl_dep_asserts = asserts_from_relation exec.ctrl fns.ctrl_dep in

    (* ==== asw assert ==== *)
    (* TODO: code duplication *)
    (*let asw_asserts =
      let mk_asw = (fun (a,b) -> fns.asw (z3action a, z3action b)) in
      let not_asw = not_related exec.asw prod_actions find_rel in
        (List.map (fun (a,b) -> mk_eq (mk_asw (a,b)) mk_true) exec.asw)
      @ (List.map (fun (a,b) -> mk_eq (mk_asw (a,b)) mk_false) not_asw) in*)



    { event_sort = event_sort
    ; event_map  = event_map
    ; decls      = decls
    ; fns        = fns

    ; assertions =   aid_asserts
                   @ tid_asserts
                   @ guard_asserts
                   @ type_asserts
                   @ addr_asserts
                   @ addr_max_asserts
                   @ memord_asserts
                   @ rval_asserts
                   @ wval_asserts
                   @ same_loc_asserts

    ; po_assert      = po_asserts
    ; asw_assert     = asw_asserts
    ; addr_assert    = addr_dep_asserts
    ; data_assert    = data_dep_asserts
    ; ctrl_assert    = ctrl_dep_asserts
    ; well_formed_rf = well_formed_rf
    ; well_formed_co = well_formed_co
    ; co_init        = co_init
    }

  type execution = {
    z3_asserts     : Expr.expr;
    ret            : Expr.expr;

    preexec        : preexec2;
    witness        : witness;
    exdd           : execution_derived_data;

    race_free      : bool;
    loc_pprinting  : (Expr.expr, string) Pmap.map;
  }

  let extract_executions
      (solver: Solver.solver)
      (mem: 'a)
      (extract_execution: Model.model -> 'a -> Expr.expr
                          -> (alloc, allocation_metadata) Pmap.map option
                          -> execution)
      (ret_value: Expr.expr)
      (metadata_opt : (alloc, allocation_metadata) Pmap.map option)
      : string * string list * bool =

    Solver.push solver;
    let rec aux ret =
      if Solver.check solver [] = SATISFIABLE then
        let model = Option.get (Solver.get_model solver) in
        let execution = extract_execution model mem ret_value metadata_opt in
        Solver.add solver [mk_not execution.z3_asserts];
        aux (execution :: ret)
      else
        ret
    in
    let executions = aux [] in
    let num_races =
        (List.length (List.filter (fun e -> not e.race_free) executions)) in
    let output_str =
      sprintf "# consistent executions: %d\n# executions with races: %d\nReturn values: %s\n"
               (List.length executions)
               num_races
               (String.concat ", " (List.map
                  (fun e -> Expr.to_string e.ret) executions)) in
    (*
    printf "# consistent executions: %d\n" (List.length executions);
    printf "# executions with races: %d\n" num_races;

    printf "Return values: %s\n"
           (String.concat ", " (List.map
              (fun e -> Expr.to_string e.ret) executions));
    *)
    print_endline (output_str);
    let dots = List.fold_left (fun acc exec ->
      if (List.length exec.preexec.actions > 0) then
        Kevin.pp_dot exec.loc_pprinting (exec.preexec, exec.witness, exec.exdd) :: acc
         (* pp_dot () (ppmode_default_web,
                     (exec.preexec, Some exec.witness,
                      Some (exec.exdd)), Some exec.loc_pprinting) :: acc*)
      else acc
      ) [] executions in
    (* TODO: we probably don't want this anymore: *)
    if !!bmc_conf.output_model then
      List.iteri (fun i dot ->
        let filename = sprintf "%s_%d.dot" "graph" i in
        save_to_file filename dot
        ) dots;
    Solver.pop solver 1;
    (output_str,dots, num_races = 0)

  let get_address_ranges (data: (int * allocation_metadata) list)
                         (interp: Expr.expr -> Expr.expr option)
                         : (int * (int * int) option * Sym.prefix) list =
    List.map (fun (alloc,metadata) ->
      let addr_base = get_metadata_base metadata in
      let addr_size = get_metadata_size metadata in
      let addr_min = PointerSort.get_index_from_addr addr_base in
      let addr_max = binop_to_z3 OpAdd addr_min (int_to_z3 (addr_size - 1)) in
      let prefix = get_metadata_prefix metadata in
      match (interp addr_min, interp addr_max) with
      | Some min , Some max ->
          if (Arithmetic.is_int min && Arithmetic.is_int max) then
            (alloc,Some (Integer.get_int min, Integer.get_int max),prefix)
          else
            (alloc,None, prefix)
      | _ -> (alloc,None, prefix)
    ) data

  let loc_to_string (loc: Expr.expr)
                    (ranges: (int * ((int * int) option) * Sym.prefix) list)
                    : string =
    match Expr.get_args loc with
    | [a1] ->
        if (Arithmetic.is_int a1) then
          let addr = Integer.get_int a1 in
          match (List.find_opt (fun (alloc, range_opt, prefix) ->
            if range_opt = None then false
            else
              let (addr_min, addr_max) = Option.get range_opt in
              (addr_min <= addr && addr <= addr_max)
            ) ranges) with
          | Some (alloc, Some (min, max), prefix) ->
              sprintf "%s{%d}"  (prefix_to_string_short prefix)
                                (addr - min)
          | _ -> Expr.to_string loc
        else Expr.to_string loc
    | _ ->
        Expr.to_string loc

end


module C11MemoryModel : MemoryModel = struct
  open MemoryModelCommon

  type func_decl_ty = string * Sort.sort list * Sort.sort

  type decls = {
    (* Accessors *)
    aid      : FuncDecl.func_decl;
    guard    : FuncDecl.func_decl;
    etype    : FuncDecl.func_decl;
    memord   : FuncDecl.func_decl;
    addr     : FuncDecl.func_decl;
    rval     : FuncDecl.func_decl;
    wval     : FuncDecl.func_decl;

    rf_inv   : FuncDecl.func_decl;

    sb       : FuncDecl.func_decl;
    asw      : FuncDecl.func_decl;

    rs       : FuncDecl.func_decl;
    rf_dag   : FuncDecl.func_decl;
    sw       : FuncDecl.func_decl;
    hb       : FuncDecl.func_decl;

    sc_clk   : FuncDecl.func_decl;
    sc       : FuncDecl.func_decl;
    psc_base : FuncDecl.func_decl;
    psc_f    : FuncDecl.func_decl;


    sbrf_clk : FuncDecl.func_decl;
  }

  type fn_apps = {
    getAid    : Expr.expr -> Expr.expr;
    getGuard  : Expr.expr -> Expr.expr;
    getEtype  : Expr.expr -> Expr.expr;
    getAddr   : Expr.expr -> Expr.expr;
    getMemord : Expr.expr -> Expr.expr;
    getRval   : Expr.expr -> Expr.expr;
    getWval   : Expr.expr -> Expr.expr;

    isRead    : Expr.expr -> Expr.expr;
    isWrite   : Expr.expr -> Expr.expr;
    same_loc  : Expr.expr * Expr.expr -> Expr.expr;

    rf_inv   : Expr.expr -> Expr.expr;
    rf       : Expr.expr * Expr.expr -> Expr.expr;

    sb        : Expr.expr * Expr.expr -> Expr.expr;
    asw       : Expr.expr * Expr.expr -> Expr.expr;

    co_clk   : Expr.expr -> Expr.expr;
    mo       : Expr.expr * Expr.expr -> Expr.expr;

    rf_dag   : Expr.expr * Expr.expr -> Expr.expr;
    rs       : Expr.expr * Expr.expr -> Expr.expr;

    fr       : Expr.expr * Expr.expr -> Expr.expr;
    eco      : Expr.expr * Expr.expr -> Expr.expr;
    sw       : Expr.expr * Expr.expr -> Expr.expr;
    hb       : Expr.expr * Expr.expr -> Expr.expr;

    sc_clk   : Expr.expr -> Expr.expr;
    sc       : Expr.expr * Expr.expr -> Expr.expr;
    psc_base : Expr.expr * Expr.expr -> Expr.expr;
    psc_f    : Expr.expr * Expr.expr -> Expr.expr;

    sbrf_clk : Expr.expr -> Expr.expr;
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

    rf_dag         : Expr.expr list;
    rs             : Expr.expr list;
    sw             : Expr.expr list;
    hb             : Expr.expr list;

    sc_clk         : Expr.expr list;

    well_formed_rf : Expr.expr list;
    well_formed_mo : Expr.expr list;
    mo_init        : Expr.expr list;

    coherence      : Expr.expr list;
    atomic1        : Expr.expr list;
    atomic2        : Expr.expr list;

    sbrf_clk       : Expr.expr list;
  }

  (*
  type execution = {
    z3_asserts     : Expr.expr;
    ret            : Expr.expr;

    preexec        : preexec2;
    witness        : witness;
    exdd           : execution_derived_data;

    race_free      : bool;
  }
*)

  type z3_memory_model = {
    event_sort : Sort.sort; (* Enum of memory actions *)
    event_type : Sort.sort; (* Type of memory actions: eg load/store *)

    event_map  : (aid, Expr.expr) Pmap.map;
    action_map : (aid, action) Pmap.map;

    decls      : decls;
    fns        : fn_apps;
    assertions : Expr.expr list;
  }

  let add_assertions solver model =
    Solver.add solver model.assertions

  let get_assertions model = model.assertions

  (* ==== Helper aliases ==== *)

  let mk_forall arglist symlist expr : Expr.expr =
    Quantifier.expr_of_quantifier (Quantifier.mk_forall g_ctx
      arglist symlist expr None [] [] None None)

  (* ==== Type definitions ==== *)
  let mk_decls (events: Sort.sort)
               (builtin: MemoryModelCommon.builtin_decls) : decls =
    { aid      = builtin.aid
    ; guard    = builtin.guard
    ; etype    = builtin.etype
    ; addr     = builtin.addr
    ; memord   = builtin.memord
    ; rval     = builtin.rval
    ; wval     = builtin.wval

    ; rf_inv   = builtin.rf_inv

    ; sb       = mk_decl "sb"       [events;events] boolean_sort
    ; asw      = mk_decl "asw"      [events;events] boolean_sort

    ; rs       = mk_decl "rs"       [events;events] boolean_sort
    ; rf_dag   = mk_decl "rf_dag"   [events;events] boolean_sort
    ; sw       = mk_decl "sw"       [events;events] boolean_sort
    ; hb       = mk_decl "hb"       [events;events] boolean_sort

    ; sc_clk   = mk_decl "sc_clk"   [events]        (Integer.mk_sort g_ctx)
    ; sc       = mk_decl "sc"       [events;events] boolean_sort
    ; psc_base = mk_decl "psc_base" [events;events] boolean_sort
    ; psc_f    = mk_decl "psc_f"    [events;events] boolean_sort

    ; sbrf_clk = mk_decl "sbrf_clk" [events]        (Integer.mk_sort g_ctx)
    }

  let mk_fn_apps (decls: decls)
                 (builtin: MemoryModelCommon.builtin_fnapps) : fn_apps =
    let getGuard  = builtin.getGuard in
    let getEtype  = builtin.getEtype in
    let getAddr   = builtin.getAddr in
    let getMemord = builtin.getMemord in
    let getRval   = builtin.getRval in
    let getWval   = builtin.getWval in
    let isRead    = builtin.isRead in
    let isWrite   = builtin.isWrite in
    let same_loc  = builtin.same_loc in

    let rf_inv = builtin.rf_inv in
    let rf     = builtin.rf in

    let sb     = (fun (e1,e2) -> apply decls.sb  [e1;e2]) in
    let asw    = (fun (e1,e2) -> apply decls.asw [e1;e2]) in

    let co_clk = builtin.co_clk in
    let mo     = (fun (e1,e2) -> mk_and [mk_lt g_ctx (co_clk e1) (co_clk e2)
                                        ;isWrite e1
                                        ;isWrite e2
                                        ;same_loc (e1,e2)
                                        ]) in

    let rf_dag  = (fun (e1,e2) -> apply decls.rf_dag  [e1;e2]) in
    let rs      = (fun (e1,e2) -> apply decls.rs      [e1;e2]) in
    (* let fr = (rf^-1 ; mo) \ id *)
    let fr     = (fun (e1,e2) -> mk_and [isRead e1
                                        ;mk_not (mk_eq e1 e2)
                                        ;mo (rf_inv(e1), e2)
                                        ;same_loc (e1,e2)
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
    let sc_clk = (fun e -> apply decls.sc_clk [e]) in
    let sc     = (fun (e1,e2) -> mk_and [mk_lt g_ctx (sc_clk e1) (sc_clk e2)
                                        ;mk_eq (getMemord e1) sc_memord
                                        ;mk_eq (getMemord e2) sc_memord
                                        ]) in
    let psc_base = (fun (e1,e2) -> apply decls.psc_base [e1;e2]) in
    let psc_f    = (fun (e1,e2) -> apply decls.psc_f [e1;e2]) in

    let sbrf_clk = (fun e -> apply decls.sbrf_clk [e]) in

    { getAid    = builtin.getAid
    ; getGuard  = getGuard
    ; getEtype  = getEtype
    ; getAddr   = getAddr
    ; getMemord = getMemord
    ; getRval   = getRval
    ; getWval   = getWval

    ; isRead    = isRead
    ; isWrite   = isWrite
    ; same_loc  = same_loc

    ; sb        = sb
    ; asw       = asw
    ; co_clk    = co_clk
    ; mo        = mo
    ; rf_inv    = rf_inv
    ; rf        = rf
    ; rf_dag    = rf_dag
    ; rs        = rs

    ; fr        = fr
    ; eco       = eco
    ; sw        = sw
    ; hb        = (fun (e1,e2) -> apply decls.hb [e1;e2])
    ; sc_clk    = sc_clk
    ; sc        = sc
    ; psc_base  = psc_base
    ; psc_f     = psc_f
    ; sbrf_clk  = sbrf_clk
    }

  let compute_executions (exec: preexec) (file: unit typed_file) : z3_memory_model =
    let all_actions = exec.initial_actions @ exec.actions in
    let prod_actions = cartesian_product all_actions all_actions in
    let writes = List.filter has_wval all_actions in
    let reads = List.filter has_rval all_actions in
    let atomic_writes = List.filter is_atomic_bmcaction writes in
    let fences = List.filter is_fence_action all_actions in
    let is_sc a = get_memorder a = (C_mem_order Seq_cst) in
    let sc_actions = List.filter is_sc all_actions in

    let initialised = MemoryModelCommon.initialise exec file in
    let event_sort = initialised.event_sort in
    let event_type = mk_event_type in
    let all_events = Enumeration.get_consts event_sort in
    let prod_events = cartesian_product all_events all_events in

    (* Map from aid to corresponding Z3 event *)
    let event_map = initialised.event_map in
    let z3action (action: bmc_action) =
      Pmap.find (aid_of_bmcaction action) event_map in

    let decls: decls = mk_decls event_sort (initialised.decls) in
    let fns: fn_apps = mk_fn_apps decls (initialised.fns) in

    (* ==== Define accessors ==== *)
    let accessor_assertions = initialised.assertions in
    (*
    let aid_asserts = List.map (fun action ->
      mk_eq (fns.getAid (z3action action))
            (Integer.mk_numeral_i g_ctx (aid_of_bmcaction action))
      ) all_actions in

    let guard_asserts = List.map (fun action ->
      mk_eq (fns.getGuard (z3action action))
            (Expr.simplify (guard_of_bmcaction action) None)
      ) all_actions in

    let type_asserts = List.map (fun action ->
      mk_eq (fns.getEtype (z3action action))
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
  *)

    (* ==== Preexecution relations ==== *)
    let sb_asserts =
      let sb_with_initial = cartesian_product
          (exec.initial_actions)
          (List.filter (fun a -> has_rval a || has_wval a) exec.actions)
        @ exec.po in
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

    (*[W & ~NA] ; rf* *)
    let rf_dag_asserts =
      let rmws = (List.map z3action (List.filter is_rmw reads)) in
      let candidates = cartesian_product (List.map z3action atomic_writes)
                                         (List.map z3action reads) in
      let not_rel = not_related candidates prod_events find_erel in
      List.map (fun (a,b) ->
        let inductive_def = (fun c ->
          mk_and [fns.getGuard c; fns.rf (a,c); fns.rf_dag(c,b)]) in
        mk_eq (fns.rf_dag(a,b))
              (mk_and [fns.getGuard a
                      ;fns.getGuard b
                      ;mk_or [mk_eq a b
                             ;fns.rf(a,b)
                             ;mk_or (List.map inductive_def rmws)]])
      ) candidates
      @ List.map (fun (a,b) -> mk_eq (fns.rf_dag (a,b)) mk_false) not_rel in

    (* let rs = [W] ; (sb & loc)? ; [W & ~NA] ; rf* *)
    let rs_asserts =
      let atomic_writes =
        List.map z3action (List.filter is_atomic_bmcaction writes) in
      let candidate_tails = List.map z3action reads @ atomic_writes in
      let candidates = cartesian_product (List.map z3action writes)
                                         candidate_tails in
      let not_rel = not_related candidates prod_events find_erel in
      List.map (fun (a,b) ->
        let exists_sb =
          (fun c -> mk_and [fns.getGuard c
                           ;fns.sb (a,c)
                           ;fns.rf_dag(c,b)
                           ;fns.same_loc(a,c)
                           ]) in
        mk_eq (fns.rs (a,b))
              (mk_and [fns.getGuard a
                      ;fns.getGuard b
                      ;mk_or ((mk_eq a b)::((fns.rf_dag(a,b))
                             ::(List.map exists_sb atomic_writes)))
                      ])
      ) candidates
      @ List.map (fun (a,b) -> mk_eq (fns.rs (a,b)) mk_false)
                 not_rel in

    (*let sw = [REL | ACQ_REL | SC] ; ([F] ; sb)? ; rs ; rf ; [R & ~NA]
     *         ; (sb ; [F])? ; [ACQ | ACQ_REL | SC] *)
    let sw_asserts =
      let candidate_heads =
        let sync_write_order = (fun action ->
          let mo = get_memorder action in
          (mo = C_mem_order Release ||
           mo = C_mem_order Acq_rel ||
           mo = C_mem_order Seq_cst)) in
        List.filter sync_write_order (fences @ writes) in
      let candidate_tails =
        let sync_read_order = (fun action ->
          let mo = get_memorder action in
          (mo = C_mem_order Acquire ||
           mo = C_mem_order Acq_rel ||
           mo = C_mem_order Seq_cst)) in
        List.filter sync_read_order (fences @ reads) in
      let candidates = cartesian_product candidate_heads candidate_tails in
      let not_rel = not_related candidates prod_actions find_rel in
      let f_sb_w = List.fold_left (fun acc (a,b) ->
        if is_fence_action a && has_wval b then
          match Pmap.lookup a acc with
          | Some l -> Pmap.add a (z3action b :: l) acc
          | None   -> Pmap.add a [z3action b] acc
        else acc
      ) (Pmap.empty bmcaction_cmp) exec.po in
      let r_sb_f = List.fold_left (fun acc (a,b) ->
        if has_rval a && is_atomic_bmcaction a && is_fence_action b then
          match Pmap.lookup b acc with
          | Some l -> Pmap.add b (z3action a :: l) acc
          | None   -> Pmap.add b [z3action a] acc
        else acc
      ) (Pmap.empty bmcaction_cmp) exec.po in
      List.map (fun (a,b) ->
        let (ea,eb) = (z3action a, z3action b) in
        let f_sb_a = match Pmap.lookup a f_sb_w with
                     | Some l -> l | None -> [] in
        let sb_f_b = match Pmap.lookup b r_sb_f with
                     | Some l -> l | None -> [] in
        let def_fsb = (fun fsb ->
          mk_and [fns.getGuard fsb
                 ;mk_or[fns.rs(fsb, fns.rf_inv(eb))
                       ;mk_or (List.map (fun sbf ->
                         mk_and [fns.getGuard sbf
                                ;fns.rs(fsb, fns.rf_inv(sbf))]
                        ) sb_f_b)]
                 ]
        ) in
        mk_eq (fns.sw (ea,eb))
              (mk_and [fns.getGuard ea; fns.getGuard eb
                      ;mk_or [fns.asw(ea,eb)
                             ;fns.rs(ea,fns.rf_inv(eb))
                             ;mk_or (List.map def_fsb f_sb_a)
                             ]
                      ])
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

    (* ==== SC assertions ==== *)
    (* TODO: simplify relation *)
    let psc_base_asserts =
      (*
      let rel_cmp (x1,x2) (y1,y2) =
        if Expr.equal x1 y1 then
          Expr.compare x2 y2
        else Expr.compare x1 y1 in
      *)
      (* sb_neq_loc;hb *)
      let comp1 e1 e2 = mk_or (List.map (fun (x,y) ->
        mk_and [fns.getGuard x; fns.getGuard y
               ;fns.hb(e1,x);fns.sb(x,y);fns.sb(y,e2)
               ;mk_not (fns.same_loc(x,e1))
               ;mk_not (fns.same_loc (y,e2))
               ]) prod_events) in
      (*
      let scb_map = List.fold_left (fun acc (e1,e2) ->
        Pmap.add (e1,e2)
                 (mk_or [fns.sb (e1,e2)
                        ;comp1 e1 e2
                        ;mk_and [fns.hb(e1,e2)
                                ;fns.same_loc (e1,e2)]
                        ;fns.mo (e1,e2)
                        ;fns.fr (e1,e2)
                        ]) acc
      ) (Pmap.empty rel_cmp) prod_events in
    *)
      let scb (e1,e2) =
            (mk_or [fns.sb (e1,e2)
                        ;comp1 e1 e2
                        ;mk_and [fns.hb(e1,e2)
                                ;fns.same_loc (e1,e2)]
                        ;fns.mo (e1,e2)
                        ;fns.fr (e1,e2)
                        ]) in
        (*Pmap.find (e1,e2) scb_map in*)

      List.map (fun (a1,a2) ->
        (*let scb =  sb | sb_neq_loc ; hb ; sb_neq_loc | hb & loc | mo | fr*)
        let (e1,e2) = (z3action a1, z3action a2) in
        let singular_fences =
          mk_or (List.map (fun x ->
            let fhb_scb e_tl =
              if is_fence_action a1 then mk_and [fns.hb(e1,x); scb(x,e_tl)]
              else mk_false in
            let scb_hbf e_hd =
              if is_fence_action a2 then mk_and [scb(e_hd,x); fns.hb(x,e2)]
              else mk_false in
            mk_and [fns.getGuard x
                   ;mk_or [fhb_scb e2;scb_hbf e1]
                   ]) all_events) in
        let double_fences =
          if is_fence_action a1 && is_fence_action a2 then
            mk_or (List.map (fun (x,y) ->
              mk_and [fns.getGuard x; fns.getGuard y
                     ;fns.hb(e1,x);scb(x,y);fns.hb(y,e2)]
            ) (cartesian_product all_events all_events))
          else mk_false in
        mk_implies
          (mk_and [fns.getGuard e1;fns.getGuard e2
                  ;mk_or[scb (e1,e2)
                        ;singular_fences
                        ;double_fences
                        ]
                  ])
          (mk_lt g_ctx (fns.sc_clk e1) (fns.sc_clk e2))
      ) (cartesian_product sc_actions sc_actions) in

    let psc_f_asserts =
      let sc_fences = List.map z3action (List.filter is_sc fences) in
      let candidates = cartesian_product sc_fences sc_fences in
      List.map (fun (f1,f2) ->
        let hb_eco_hb = mk_or (List.map (fun (e1,e2) ->
          mk_and [fns.getGuard e1
                 ;fns.getGuard e2
                 ;fns.hb(f1,e1); fns.eco(e1,e2); fns.hb(e2,f2)]
          ) prod_events) in
        mk_implies
          (mk_and [fns.getGuard f1; fns.getGuard f2
                  ;mk_or [fns.hb(f1,f2)
                         ;hb_eco_hb
                         ]
                  ])
          (mk_lt g_ctx (fns.sc_clk f1) (fns.sc_clk f2))
      ) candidates in

    (* ==== Well formed assertions ==== *)

    (* ∀e. isRead(e) ∧ guard(e) => isWrite(rf(e)) ∧ same_addr ∧ same_val *)
    (*
    let well_formed_rf = List.map (fun action ->
      let e = z3action action in
      mk_implies (fns.getGuard e)
                 (mk_and [fns.isWrite (fns.rf_inv e)
                         ;fns.same_loc (e, fns.rf_inv e)
                         ;mk_eq (fns.getRval e) (fns.getWval (fns.rf_inv e))
                         ;fns.getGuard (fns.rf_inv e)
                         ])
    ) (List.filter has_rval all_actions) in
    *)
    let well_formed_rf = initialised.well_formed_rf in

    let well_formed_mo = initialised.well_formed_co in

    (*
      List.map (fun (w1,w2) ->
        let (e1,e2) = (z3action w1, z3action w2) in
        mk_implies (mk_and [fns.getGuard e1
                           ;fns.getGuard e2
                           ;mk_not (mk_eq e1 e2)
                           ;fns.same_loc(e1,e2)
                           ])
                  (mk_not (mk_eq (fns.mo_clk e1) (fns.mo_clk e2)))
      ) (cartesian_product writes writes) in
    *)

    let mo_init = initialised.co_init in
      (*List.map (fun e ->
        mk_eq (fns.mo_clk (z3action e)) (Integer.mk_numeral_i g_ctx 0))
    exec.initial_actions in *)

    (* ==== coherence ==== *)
    (* irreflexive (hb ; eco?) as coh *)
    let coherence = List.map (fun (e1,e2) ->
      mk_not (mk_and [fns.getGuard e1
                     ;fns.getGuard e2
                     ;fns.hb  (e1,e2)
                     ;mk_or [mk_eq e1 e2; fns.eco (e2,e1)]
                     ])
    ) (cartesian_product all_events all_events) in

    (* ==== atomicity ==== *)
    (* irreflexive eco as atomic1 *)
    let atomic1 = List.map (fun e ->
        mk_not (mk_and [fns.getGuard e;fns.eco (e,e)])
      ) all_events in
    let atomic2 = List.map (fun (e1,e2) ->
        mk_not (mk_and [fns.getGuard e1
                       ;fns.getGuard e2
                       ;fns.fr(e1,e2)
                       ;fns.mo(e2,e1)
                       ])
      ) prod_events in

    (* irreflexive (fr ; mo) as atomic2 *)

    (* sb_rf *)
    let sbrf_clk = List.map (fun (e1,e2) ->
      mk_implies (mk_and [fns.getGuard e1
                         ;fns.getGuard e2
                         ;mk_or[fns.sb (e1,e2); fns.rf(e1,e2)]
                         ])
                 (mk_lt g_ctx (fns.sbrf_clk e1) (fns.sbrf_clk e2))
    ) prod_events in


    { event_sort = event_sort
    ; event_type = event_type

    ; event_map  = event_map
    ; action_map = List.fold_left (fun acc a ->
                      Pmap.add (aid_of_bmcaction a) (get_action a) acc)
                      (Pmap.empty Pervasives.compare) all_actions

    ; decls      = decls
    ; fns        = fns

    ; assertions = accessor_assertions
                  (*aid_asserts
                 @ guard_asserts
                 @ type_asserts
                 @ addr_asserts
                 @ memord_asserts
                 @ rval_asserts
                 @ wval_asserts*)

                 @ sb_asserts
                 @ asw_asserts
                 @ rf_dag_asserts
                 @ rs_asserts
                 @ sw_asserts
                 @ hb_asserts

                 @ psc_base_asserts
                 @ psc_f_asserts

                 @ well_formed_rf
                 @ mo_init
                 @ well_formed_mo

                 @ coherence

                 @ atomic1
                 @ atomic2

                 @ sbrf_clk
    }

  let extract_execution (model    : Model.model)
                        (mem      : z3_memory_model)
                        (ret_value: Expr.expr)
                        (metadata_opt : (alloc, allocation_metadata) Pmap.map option)
                        : execution =
    let interp (expr: Expr.expr) = Option.get (Model.eval model expr false) in
    let fns = mem.fns in
    let proj_fst = (fun (p1,p2) -> (fst p1, fst p2))  in
    let get_bool (b: Expr.expr) = match Boolean.get_bool_value b with
       | L_TRUE -> true
       | L_FALSE -> false
       | _ -> false in
    let get_relation rel (p1,p2) = get_bool (interp (rel (snd p1, snd p2))) in

    let ranges =
      if is_some metadata_opt then
        MemoryModelCommon.get_address_ranges
            (Pmap.bindings_list (Option.get metadata_opt))
            (fun expr -> Model.eval model expr false)
      else
        []
    in

    (* ==== Compute preexecution ==== *)
    let action_events = List.fold_left (fun acc (aid, action) ->
      let event = Pmap.find aid mem.event_map in
      (*if tid_of_action action = initial_tid then acc*)
      if (Boolean.get_bool_value (interp (fns.getGuard event))
               = L_TRUE) then
        let new_action = match action with
          | Load (aid,tid,memorder,loc,rval,ctype) ->
              let loc = interp (fns.getAddr event) in
              let rval = interp (fns.getRval event) in
              Load(aid,tid,memorder,loc,rval,ctype)
          | Store(aid,tid,memorder,loc,wval,ctype) ->
              let loc = interp (fns.getAddr event) in
              let wval = interp (fns.getWval event) in
              Store(aid,tid,memorder,loc,wval,ctype)
          | RMW (aid,tid,memorder,loc,rval,wval,ctype) ->
              let loc = interp (fns.getAddr event) in
              let rval = interp (fns.getRval event) in
              let wval = interp (fns.getWval event) in
              RMW(aid,tid,memorder,loc,rval,wval,ctype)
          | Fence _ ->
              action
        in (new_action, event) :: acc
      else acc
    ) [] (Pmap.bindings_list mem.action_map) in

    let loc_pprinting = List.fold_left (fun base (action,_) ->
      match action with
      | Load (_,_,_,loc,_,_) (* fall through *)
      | Store(_,_,_,loc,_,_) (* fall through *)
      | RMW(_,_,_,loc,_,_,_) ->
          Pmap.add loc (MemoryModelCommon.loc_to_string loc ranges) base
      | Fence _ ->
          base
      ) (Pmap.empty Expr.compare) (action_events) in

    let not_initial action = (tid_of_action action <> initial_tid) in
    let remove_initial rel =
      List.filter (fun (x,y) -> not_initial x && not_initial y)
                  rel in

    let actions = List.map fst action_events in
    let noninitial_actions = List.filter not_initial actions in
    let events = List.map snd action_events in
    let prod = cartesian_product action_events action_events in

    let threads = Pset.elements (
        List.fold_left (fun acc a -> Pset.add (tid_of_action a) acc)
                       (Pset.empty compare) noninitial_actions) in

    let sb = List.filter (get_relation fns.sb) prod in
    let asw = List.filter (get_relation fns.asw) prod in

    let preexec : preexec2 =
      { actions = noninitial_actions
      ; threads = threads
      ; sb      = remove_initial (List.map proj_fst sb)
      ; asw     = remove_initial (List.map proj_fst asw)
      } in

    (* ==== Compute witness ===== *)

    let rf = List.filter (get_relation fns.rf) prod in
    let mo = List.filter (get_relation fns.mo) prod in
    let sc = List.filter (get_relation fns.sc) prod in

    let witness : witness =
      { rf = remove_initial (List.map proj_fst rf)
      ; mo = remove_initial (List.map proj_fst mo)
      ; sc = remove_initial (List.map proj_fst sc)
      } in

    (* ==== Derived data ==== *)
    (* TODO: fix output/definition of sw *)
    let sw = List.filter (get_relation fns.sw) prod in
    let hb = List.filter (get_relation fns.hb) prod in
    (*let rs = List.filter (get_relation fns.rs) prod in*)

    let data_race = List.filter (fun ((a1,e1),(a2,e2)) ->
      (aid_of_action a1 <> aid_of_action a2)               &&
      (is_write a1 || is_write a2)                         &&
      (get_relation fns.same_loc ((a1,e1),(a2,e2)))        &&
      (tid_of_action a1 <> tid_of_action a2)               &&
      (not (is_atomic a1 && is_atomic a2))                 &&
      (not (get_relation fns.hb ((a1,e1),(a2,e2))
            || get_relation fns.hb ((a2,e2),(a1,e1))))
    ) prod in

    if not (List.length data_race = 0) then
      bmc_debug_print 4
        (String.concat "\n" (List.map (fun ((_,e1),(_,e2)) ->
          sprintf "%s->%s" (Expr.to_string e1) (Expr.to_string e2))
          data_race));

    let unseq_race = List.filter (fun ((a1,e1),(a2,e2)) ->
      (aid_of_action a1 <> aid_of_action a2)                &&
      (is_write a1 || is_write a2)                          &&
      (get_relation fns.same_loc ((a1,e1),(a2,e2)))         &&
      (tid_of_action a1 = tid_of_action a2)                 &&
      (tid_of_action a1 <> initial_tid)                     &&
      (not (get_relation fns.sb ((a1,e1),(a2,e2))
            || get_relation fns.sb ((a2,e2),(a1,e1))))
    ) prod in

    let execution_derived_data =
      { derived_relations = [(*("sw", List.map proj_fst sw)*)
                            (*;("rs", List.map proj_fst rs)*)
                             ("hb", remove_initial (List.map proj_fst hb))
                            ]
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

    let ret = interp ret_value in
    bmc_debug_print 4 (sprintf "RET_VALUE: %s\n" (Expr.to_string ret));

    { z3_asserts = mk_and (List.concat [guard_asserts; rf_asserts; mo_asserts])
    ; ret = ret

    ; preexec = preexec
    ; witness = witness
    ; exdd    = execution_derived_data

    ; race_free = (List.length data_race = 0) && (List.length unseq_race = 0)
    ; loc_pprinting = loc_pprinting
    }

  let extract_executions (solver   : Solver.solver)
                         (mem      : z3_memory_model)
                         (ret_value: Expr.expr)
                         (metadata_opt : (alloc, allocation_metadata) Pmap.map option)
                         : string * string list * bool =
    MemoryModelCommon.extract_executions
      solver mem extract_execution ret_value metadata_opt
      (*
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
      if (List.length exec.preexec.actions > 0) then
        begin
        let dot_str =
          pp_dot () (ppmode_default_web,
                          (exec.preexec, Some exec.witness,
                           Some (exec.exdd))) in
        let filename = sprintf "%s_%d.dot" "graph" i in
        save_to_file filename dot_str
        end
    ) executions;

    Solver.pop solver 1
    *)
end

module GenericModel (M: CatModel) : MemoryModel = struct
  open MemoryModelCommon
  type decl_map = (CatFile.id, FuncDecl.func_decl) Pmap.map
  type fn_map = (CatFile.id, (Expr.expr * Expr.expr) -> Expr.expr) Pmap.map

  type z3_memory_model =
    { event_sort   : Sort.sort
    ; actions      : bmc_action list
    ; events       : Expr.expr list
    ; prod_actions : (bmc_action * bmc_action) list

    ; event_map    : (aid, Expr.expr) Pmap.map
    ; action_map   : (aid, action) Pmap.map

    ; z3action     : bmc_action -> Expr.expr

    ; builtin_fns   : MemoryModelCommon.builtin_fnapps
    ; builtin_decls : MemoryModelCommon.builtin_decls
    ; fns           : fn_map
    ; decls         : decl_map
    ; assertions    : (Expr.expr list) option
    (*; undefs        : (string option * (Expr.expr list)) list*)
    (* TODO *)
    }

  let add_assertions solver model =
    match model.assertions with
    | Some assertions -> Solver.add solver assertions
    | None            -> assert false

  let get_assertions model =
    match model.assertions with
    | Some assertions -> assertions
    | None -> assert false

  let lookup_id (id: CatFile.id) (fns: fn_map) =
    match Pmap.lookup id fns with
    | Some fn -> fn
    | None ->
        failwith (sprintf "Unknown id in memory model: %s"
                          (CatFile.pprint_id id))

  let baseset_to_filter (set: CatFile.base_set) (a: bmc_action) =
    match set with
    | BaseSet_U -> true
    | BaseSet_R -> has_rval a
    | BaseSet_W -> has_wval a
    | BaseSet_M -> has_rval a || has_wval a
    | BaseSet_A -> is_atomic_bmcaction a
    | BaseSet_I -> is_initial_bmcaction a
    | BaseSet_F -> is_fence_action a
    | BaseSet_NA  -> get_memorder a = C_mem_order NA
    | BaseSet_RLX -> get_memorder a = C_mem_order Relaxed
    | BaseSet_REL -> get_memorder a = C_mem_order Release
    | BaseSet_ACQ -> get_memorder a = C_mem_order Acquire
    | BaseSet_ACQ_REL -> get_memorder a = C_mem_order Acq_rel
    | BaseSet_SC      -> get_memorder a = C_mem_order Seq_cst
    | BaseSet_Rmb      -> get_memorder a = Linux_mem_order Rmb
    | BaseSet_Wmb      -> get_memorder a = Linux_mem_order Wmb
    | BaseSet_LinuxAcquire -> get_memorder a = Linux_mem_order Acquire0
    | BaseSet_LinuxRelease -> get_memorder a = Linux_mem_order Release0


  (* TODO: rename all this... *)
  let rec set_to_filter (set: CatFile.set) (a: bmc_action) =
    match set with
    | Set_base base -> baseset_to_filter base a
    | Set_union (s1,s2) ->
        (set_to_filter s1 a) || (set_to_filter s2 a)
    | Set_intersection (s1,s2) ->
        (set_to_filter s1 a) && (set_to_filter s2 a)
    | Set_difference (s1,s2) ->
        (set_to_filter s1 a) && (not (set_to_filter s2 a))
    | Set_not s ->
        not (set_to_filter s a)

  let id_to_z3 (model: z3_memory_model)
               (id: CatFile.id)
               ((a,b) : bmc_action * bmc_action)
               : Expr.expr =
    let (ea,eb) = (model.z3action a, model.z3action b) in
    match id with
    | Id s ->
        (lookup_id id model.fns) (ea,eb)
    | BaseId baseid ->
        begin
        match baseid with
        | BaseId_rf     -> model.builtin_fns.rf (ea,eb)
        | BaseId_rf_inv -> model.builtin_fns.rf (eb,ea)
        | BaseId_co     -> model.builtin_fns.co (ea,eb)
        | BaseId_id     -> mk_eq ea eb
        | BaseId_asw    -> model.builtin_fns.asw (ea,eb)
        | BaseId_po     -> model.builtin_fns.po (ea,eb)
        | BaseId_loc    -> model.builtin_fns.same_loc (ea,eb)
        | BaseId_int    -> model.builtin_fns.internal (ea,eb)
        | BaseId_ext    -> model.builtin_fns.ext (ea,eb)
        | BaseId_rfi    -> model.builtin_fns.rfi (ea,eb)
        | BaseId_rfe    -> model.builtin_fns.rfe (ea,eb)
        | BaseId_po_loc -> model.builtin_fns.po_loc (ea,eb)
        | BaseId_addr_dep -> model.builtin_fns.addr_dep (ea,eb)
        | BaseId_ctrl_dep -> model.builtin_fns.ctrl_dep (ea,eb)
        | BaseId_data_dep -> model.builtin_fns.data_dep (ea,eb)
        end

  (* === Expr -> boolean *)
  let rec simple_expr_to_z3 (model: z3_memory_model)
                            (expr: CatFile.simple_expr)
                            ((a,b): bmc_action * bmc_action)
                            : Expr.expr =
    let z3action = model.z3action in
    let (ea,eb) = (z3action a, z3action b) in
    match expr with
    | Eid id -> id_to_z3 model id (a,b)
    | Einverse expr ->
        simple_expr_to_z3 model expr (b,a)
    | Eunion (e1,e2) ->
        mk_or [simple_expr_to_z3 model e1 (a,b)
              ;simple_expr_to_z3 model e2 (a,b)]
    | Eintersection (e1,e2) ->
        mk_and [simple_expr_to_z3 model e1 (a,b)
               ;simple_expr_to_z3 model e2 (a,b)]
    | Esequence (e1,e2) ->
        mk_or (List.map (fun x ->
                mk_and [model.builtin_fns.getGuard (z3action x)
                       ;simple_expr_to_z3 model e1 (a,x)
                       ;simple_expr_to_z3 model e2 (x,b)
                       ]
              ) model.actions)
    | Edifference (e1,e2) ->
        mk_and [ simple_expr_to_z3 model e1 (a,b)
               ; mk_not (simple_expr_to_z3 model e2 (a,b))]
    | Eset set ->
        mk_bool ((aid_of_bmcaction a = aid_of_bmcaction b)
                 && (set_to_filter set a))
    | Eprod (set1,set2) ->
        mk_bool ((set_to_filter set1 a) && (set_to_filter set2 b))
    | Eoptional expr ->
        mk_or [simple_expr_to_z3 model expr (a,b); mk_eq ea eb]

  let expr_to_z3 (model: z3_memory_model)
                 (id: CatFile.id)
                 (expr: CatFile.expr)
                 ((a,b) : bmc_action * bmc_action) =
    let z3action = model.z3action in
    let (ea,eb) = (z3action a, z3action b) in
    let getGuard = model.builtin_fns.getGuard in
    let condition = begin match expr with
    | Esimple e ->
        simple_expr_to_z3 model e (a,b)
    | Eplus e ->
        mk_or [simple_expr_to_z3 model e (a,b)
              ;simple_expr_to_z3 model (Esequence(e, Eid id)) (a,b)]
    | Estar e ->
        mk_or [simple_expr_to_z3 model e (a,b)
              ;mk_eq ea eb
              ;simple_expr_to_z3 model (Esequence(e, Eid id)) (a,b)]
    end in
    mk_and [condition
           ;getGuard ea
           ;getGuard eb]

  (* TODO: clarify type of binding *)
  let mk_assertion (s, (hd,tl), expr) (model: z3_memory_model) =
    let id = CatFile.Id s in
    let fn = lookup_id id model.fns in
    let candidates =
      let candidate_heads = List.filter (set_to_filter hd) model.actions in
      let candidate_tails = List.filter (set_to_filter tl) model.actions in
      cartesian_product candidate_heads candidate_tails in
    let z3action = model.z3action in
    let not_rel = not_related candidates model.prod_actions find_rel in
      List.map (fun (a,b) -> mk_eq (fn (z3action a,z3action b))
                             (expr_to_z3 model id expr (a,b)))
               candidates
    @ List.map (fun (a,b) -> mk_eq (fn (z3action a,z3action b)) mk_false)
               not_rel

  let mk_constraint ((s_opt, constr): string option * CatFile.constraint_expr)
                    (model: z3_memory_model)
                    : Expr.expr list =
    let getGuard = model.builtin_fns.getGuard in
    let z3action = model.z3action in
    let event_sort = model.event_sort in
    match constr with
    | Irreflexive expr ->
        List.map (fun a ->
          mk_not (mk_and [getGuard (z3action a)
                         ;simple_expr_to_z3 model expr (a,a)
                         ])
        ) model.actions
    | Acyclic expr ->
        let clk_name =
          match s_opt with | Some s -> s | None -> "acyclic_clk" in
        let clk_decl = mk_decl clk_name [event_sort] (Integer.mk_sort g_ctx) in
        let clk_fn event = Expr.mk_app g_ctx clk_decl [event] in
        List.map (fun (a,b) ->
          let (ea,eb) = (z3action a, z3action b) in
          mk_implies (mk_and [getGuard ea
                             ;getGuard eb
                             ;simple_expr_to_z3 model expr (a,b)
                             ])
                     (mk_lt g_ctx (clk_fn ea) (clk_fn eb))
        ) model.prod_actions
    | Empty expr ->
        List.map (fun (a,b) ->
          let (ea,eb) = (z3action a, z3action b) in
          mk_implies (mk_and [getGuard ea; getGuard eb])
                     (mk_not (simple_expr_to_z3 model expr (a,b)))
          ) model.prod_actions

  (*let mk_undef_unless
               ((s_opt, constr): string option * CatFile.constraint_expr)
               (model: z3_memory_model)
               : string option * (Expr.expr list) =
    match constr with
    | Irreflexive expr ->
        failwith "TODO: undefined_unless irreflexive currently not supported"
    | Acyclic expr ->
        failwith "TODO: undefined_unless acyclic currently not supported"
    | Empty expr ->
        (s_opt, mk_constraint (s_opt, constr) model)
  *)

  let mk_decls_and_fnapps (events: Sort.sort) =
    List.fold_left (fun (decls, fnapps) id ->
      let decl = (mk_decl id [events;events] boolean_sort) in
      let fnapp = (fun (e1,e2) -> apply decl [e1;e2]) in
      (Pmap.add (CatFile.Id id) decl decls,
       Pmap.add (CatFile.Id id) fnapp fnapps)
    ) (Pmap.empty compare, Pmap.empty compare)
      (List.map (fun (s,_,_) -> s) M.bindings)

  let compute_executions (exec: preexec) (file: unit typed_file) =
    let common        = initialise exec file in
    let (decls,fns)   = mk_decls_and_fnapps common.event_sort in
    let actions = exec.initial_actions @ exec.actions in
    let event_map = common.event_map in
    let action_map =
      List.fold_left (fun acc a ->
        Pmap.add (aid_of_bmcaction a) (get_action a) acc)
        (Pmap.empty Pervasives.compare) actions in

    let model : z3_memory_model =
      { event_sort    = common.event_sort
      ; events        = Enumeration.get_consts common.event_sort
      ; actions       = actions
      ; prod_actions  = cartesian_product actions actions
      ; event_map     = event_map
      ; action_map    = action_map

      ; z3action      = (fun a -> Pmap.find (aid_of_bmcaction a) event_map)
      ; builtin_decls = common.decls
      ; builtin_fns   = common.fns
      ; decls         = decls
      ; fns           = fns
      ; assertions    = None
      (*; undefs        = []*)
      } in
    let assertions =
      gen_all_assertions common
      @ List.concat (List.map
          (fun constr -> mk_constraint constr model) M.constraints)
      @ List.concat (List.map
          (fun binding -> mk_assertion binding model) M.bindings)
    in
    (*let undefs =
      (List.map (fun constr -> mk_undef_unless constr model) M.undefs) in*)
    (*List.iter (fun e -> print_endline (Expr.to_string e)) assertions;*)
    {model with assertions = Some assertions;
                (*undefs     = M.undefs*)}

  (* TODO: code duplication here with C11MemoryModel *)
  let extract_execution (model: Model.model)
                        (mem: z3_memory_model)
                        (ret_value: Expr.expr)
                        (metadata_opt: (alloc, allocation_metadata) Pmap.map option)=
    let interp (expr: Expr.expr) = Option.get (Model.eval model expr false) in
    let fns = mem.builtin_fns in
    let proj_fst = (fun (p1,p2) -> (fst p1, fst p2))  in
    let get_bool (b: Expr.expr) = match Boolean.get_bool_value b with
       | L_TRUE -> true
       | L_FALSE -> false
       | _ -> false in
    let get_relation rel (p1,p2) = get_bool (interp (rel (snd p1, snd p2))) in

    let ranges =
      if is_some metadata_opt then
        MemoryModelCommon.get_address_ranges
            (Pmap.bindings_list (Option.get metadata_opt))
            (fun expr -> Model.eval model expr false)
      else
        []
    in

    let action_events = List.fold_left (fun acc (aid, action) ->
      let event = Pmap.find aid mem.event_map in
      (*if tid_of_action action = initial_tid then acc*)
      if (Boolean.get_bool_value (interp (fns.getGuard event)) = L_TRUE) then
        let new_action = match action with
          | Load (aid,tid,memorder,loc,rval,ctype) ->
              let loc = interp (fns.getAddr event) in
              let rval = interp (fns.getRval event) in
              Load(aid,tid,memorder,loc,rval,ctype)
          | Store(aid,tid,memorder,loc,wval,ctype) ->
              let loc = interp (fns.getAddr event) in
              let wval = interp (fns.getWval event) in
              Store(aid,tid,memorder,loc,wval,ctype)
          | RMW (aid,tid,memorder,loc,rval,wval,ctype) ->
              let loc = interp (fns.getAddr event) in
              let rval = interp (fns.getRval event) in
              let wval = interp (fns.getWval event) in
              RMW(aid,tid,memorder,loc,rval,wval,ctype)
          | Fence _ ->
              action
        in (new_action, event) :: acc
      else acc
    ) [] (Pmap.bindings_list mem.action_map) in

    let loc_pprinting = List.fold_left (fun base (action,_) ->
      match action with
      | Load (_,_,_,loc,_,_) (* fall through *)
      | Store(_,_,_,loc,_,_) (* fall through *)
      | RMW(_,_,_,loc,_,_,_) ->
          Pmap.add loc (MemoryModelCommon.loc_to_string loc ranges) base
      | Fence _ ->
          base
      ) (Pmap.empty Expr.compare) (action_events) in

    let not_initial action = (tid_of_action action <> initial_tid) in
    let remove_initial rel =
      List.filter (fun (x,y) -> not_initial x && not_initial y) rel in

    let actions = List.map fst action_events in
    let noninitial_actions = List.filter not_initial actions in
    let events = List.map snd action_events in
    let prod = cartesian_product action_events action_events in
    let threads = Pset.elements (
        List.fold_left (fun acc a -> Pset.add (tid_of_action a) acc)
                       (Pset.empty compare) noninitial_actions) in
    let po = List.filter (get_relation fns.po) prod in
    let asw = List.filter (get_relation fns.asw) prod in

    let preexec : preexec2 =
      { actions = noninitial_actions
      ; threads = threads
      ; sb      = remove_initial (List.map proj_fst po)
      ; asw     = remove_initial (List.map proj_fst asw)
      } in

    let rf = List.filter (get_relation fns.rf) prod in
    let co = List.filter (get_relation fns.co) prod in
    (*let sc = List.filter (get_relation fns.sc) prod in*)

    let witness : witness =
      { rf = remove_initial (List.map proj_fst rf)
      ; mo = remove_initial (List.map proj_fst co)
      ; sc = []
      } in

    let derived_relations =
      List.map (fun s ->
        let fn = lookup_id (CatFile.Id s) mem.fns in
        let rel = List.filter (get_relation fn) prod in
        (s, remove_initial (List.map proj_fst rel))
      ) M.to_output in

    let ubs_unless_empty =
      List.map (fun s ->
        let fn = lookup_id (CatFile.Id s) mem.fns in
        let rel = List.filter (get_relation fn) prod in
        (s, remove_initial (List.map proj_fst rel))
      ) M.undefs_unless_empty in

    (*let sw = List.filter (get_relation fns.sw) prod in *)
    let execution_derived_data =
      { derived_relations =  derived_relations
      ; undefined_behaviour =
          List.map (fun (s, rel) -> (s, Two rel)) ubs_unless_empty
            (*[("dr",Two (List.map (fun (e1,e2) -> (fst e1, fst e2)) data_race))
            ;("ur",Two (List.map (fun (e1,e2) -> (fst e1, fst e2)) unseq_race))
            ]*)
      } in
    let guard_asserts = List.map (fun event ->
         mk_eq (fns.getGuard event) (interp (fns.getGuard event))
      ) events in
    let rf_asserts = List.map (fun ((_,e1),(_,e2)) ->
        mk_eq (fns.rf (e1,e2)) mk_true
      ) rf in
    let co_asserts = List.map (fun ((_,e1),(_,e2)) ->
        mk_eq (fns.co (e1,e2)) mk_true
      ) co in

    let ret = interp ret_value in
    bmc_debug_print 4 (sprintf "RET_VALUE: %s\n" (Expr.to_string ret));

    let race_free = List.fold_left (fun acc (_, rel) ->
        acc && (List.length rel = 0)) true ubs_unless_empty in

    { z3_asserts = mk_and (List.concat [guard_asserts; rf_asserts; co_asserts])
    ; ret = ret

    ; preexec = preexec
    ; witness = witness
    ; exdd    = execution_derived_data

    ; race_free = race_free

    (*race_free = (List.length data_race = 0) && (List.length unseq_race =
      0)*)
    ; loc_pprinting = loc_pprinting
    }

  (* TODO: fix api *)
  let extract_executions (solver   : Solver.solver)
                         (mem      : z3_memory_model)
                         (ret_value: Expr.expr)
                         (metadata_opt : (alloc, allocation_metadata) Pmap.map option)
                         : string * string list * bool =
    MemoryModelCommon.extract_executions
      solver mem extract_execution ret_value metadata_opt
end

(*module BmcMem = C11MemoryModel*)
(*module BmcMem = GenericModel(Partial_RC11Model)*)

(* TODO: figure out syntax *)
(*let cat_model =
  CatParser.load_file g_model_file
module BmcMem = GenericModel (val cat_model)*)
