(* kevin.ml - a C11 candidate execution layout tool *)
(* (C) J Pichon 2019 *)
(* call "neato" on the output *)
(* this assumes 'asw' is pretty simple *)

(* thanks to Stella Lau for a bug fix *)

module Int = struct
  type t = int
  let compare (x : t) y = Pervasives.compare x y
end

module Int_map = Map.Make(Int)

module Aid = struct
  type t = Bmc_types.aid
  let compare (x : t) y =
    Pervasives.compare x y
  let string_of (a : t) =
    String.make 1 (Char.chr ((Char.code 'a') + a))
end

module Tid = struct
  type t = Bmc_types.tid
  let compare (x : t) y =
    Pervasives.compare x y
end

module Memory_order2 = struct
  type t = Bmc_types.memory_order
  let compare (x : t) y =
    Pervasives.compare x y
end

module Z3_location = struct
  type t = Bmc_types.z3_location
  let compare (x : t) y =
    Pervasives.compare x y
end

module Z3_value = struct
  type t = Bmc_types.z3_value
  let compare (x : t) y =
    Pervasives.compare x y
end

module Action = struct
  let action_rank = function
  | Bmc_types.Load _ -> 0
  | Bmc_types.Store _ -> 1
  | Bmc_types.RMW _ -> 2
  | Bmc_types.Fence _ -> 3

  type t = Bmc_types.action
  (* TODO: do we care about types at this point? *)
  let compare (x : t) y =
    Functors.(
    match x, y with
    | Bmc_types.Load (a1, t1, m1, l1, v1, ty1), Bmc_types.Load (a2, t2, m2, l2, v2, ty2) ->
      pair_compare Aid.compare (pair_compare Tid.compare (pair_compare Memory_order2.compare (pair_compare Z3_location.compare Z3_value.compare)))  (a1, (t1, (m1, (l1, v1)))) (a2, (t2, (m2, (l2, v2))))
    | Bmc_types.Store (a1, t1, m1, l1, v1, ty1), Bmc_types.Store (a2, t2, m2, l2, v2, ty2) ->
      pair_compare Aid.compare (pair_compare Aid.compare (pair_compare Memory_order2.compare (pair_compare Z3_location.compare Z3_value.compare)))  (a1, (t1, (m1, (l1, v1)))) (a2, (t2, (m2, (l2, v2))))
    | Bmc_types.RMW (a1, t1, m1, l1, v11, v21, ty1), Bmc_types.RMW (a2, t2, m2, l2, v12, v22, ty2) ->
      pair_compare Aid.compare (pair_compare Tid.compare (pair_compare Memory_order2.compare (pair_compare Z3_location.compare (pair_compare Z3_value.compare Z3_value.compare))))  (a1, (t1, (m1, (l1, (v11, v21))))) (a2, (t2, (m2, (l2, (v12, v22)))))
    | Bmc_types.Fence (a1, t1, m1), Bmc_types.Fence (a2, t2, m2) ->
      pair_compare Aid.compare (pair_compare Tid.compare Memory_order2.compare)  (a1, (t1, m1)) (a2, (t2, m2))
    | _, _ -> Pervasives.compare (action_rank x) (action_rank y))
end

module Action_set = Set.Make(Action)

module Aid_set = Set.Make(Aid)
module String_map = Map.Make(String)

module Aid_times_aid = Functors.Ord_pair(Aid)(Aid)
module Aid_times_aid_set = Set.Make(Aid_times_aid)
module Aid_times_aid_map = Map.Make(Aid_times_aid)

module Pos = struct
  type t = Rational_ml.t * int
  let compare (x : t) y =
    Pervasives.compare x y
end

module Action_times_pos = Functors.Ord_pair(Action)(Pos)

module Action_times_pos_set = Set.Make(Action_times_pos)

let tid_of_action = function
| Bmc_types.Load (_, t, _, _, _, _) -> t
| Bmc_types.Store (_, t, _, _, _, _) -> t
| Bmc_types.RMW (_, t, _, _, _, _, _) -> t
| Bmc_types.Fence (_, t, _) -> t

let aid_of_action = function
| Bmc_types.Load (a, _, _, _, _, _) -> a
| Bmc_types.Store (a, _, _, _, _, _) -> a
| Bmc_types.RMW (a, _, _, _, _, _, _) -> a
| Bmc_types.Fence (a, _, _) -> a

module Bmc_types_pp = struct

let string_of_c_memory_order = function
| Cmm_csem.NA -> "na"
| Cmm_csem.Seq_cst -> "sc"
| Cmm_csem.Relaxed -> "rlx"
| Cmm_csem.Release -> "rel"
| Cmm_csem.Acquire -> "acq"
| Cmm_csem.Consume -> "con"
| Cmm_csem.Acq_rel -> "acqrel"

let string_of_linux_memory_order = function
| Linux.Once -> "once"
| Linux.Acquire0 -> "acq"
| Linux.Release0 -> "rel"
| Linux.Rmb -> "rmb"
| Linux.Wmb -> "wmb"
| Linux.Mb -> "mb"
| Linux.RbDep -> "rbdep"
| Linux.RcuLock -> "rculock"
| Linux.RcuUnlock -> "rcuunlock"
| Linux.SyncRcu -> "syncrcu"

let string_of_memory_order = function
| Bmc_types.C_mem_order mo -> string_of_c_memory_order mo
| Bmc_types.Linux_mem_order mo -> string_of_linux_memory_order mo

(* TODO: change? *)
let string_of_location loc_map loc =
  let default =
    begin match Z3.Expr.get_args loc with
    | [a] ->
        Printf.sprintf "(%s)" (Z3.Expr.to_string a)
    | [a1;a2] -> Printf.sprintf "(%s.%s)" (Z3.Expr.to_string a1) (Z3.Expr.to_string a2)
    | _ -> Z3.Expr.to_string loc
    end in
  match Pmap.lookup loc loc_map with
  | Some s -> s (*^ default*)
  | None -> default

(* TODO: change? *)
let string_of_value expr =
  let open Z3 in
  let open Bmc_sorts in
  assert (Expr.get_num_args expr = 1);
  let arg = List.hd (Expr.get_args expr) in
  if (Sort.equal (Expr.get_sort arg) (LoadedInteger.mk_sort)) then
    begin
      if (Boolean.is_true
        (Expr.simplify (LoadedInteger.is_unspecified arg) None)) then
        "?"
      else
      Expr.to_string (List.hd (Expr.get_args arg))
    end
  else if (Sort.equal (Expr.get_sort arg) (LoadedPointer.mk_sort)) then
    begin
      if (Boolean.is_true
        (Expr.simplify (LoadedPointer.is_unspecified arg) None)) then
        "?"
      else begin
        PointerSort.pp (List.hd (Expr.get_args arg))
      end
    end
  else
    Expr.to_string arg

let string_of_action loc_map = function
| Bmc_types.Load (a, t, mo, x, v, ty) -> Aid.string_of a ^ ":R" ^ string_of_memory_order mo ^ " " ^ string_of_location loc_map x ^ "=" ^ string_of_value v
| Bmc_types.Store (a, t, mo, x, v, ty) -> Aid.string_of a ^ ":W" ^ string_of_memory_order mo ^ " " ^ string_of_location loc_map x ^ "=" ^ string_of_value v
| Bmc_types.RMW (a, t, mo, x, v1, v2, ty) -> Aid.string_of a ^ ":RMW" ^ string_of_memory_order mo ^ " " ^ string_of_location loc_map x ^ " " ^ string_of_value v1 ^ "->" ^ string_of_value v2
| Bmc_types.Fence (a, t, mo) -> Aid.string_of a ^ ":F" ^ string_of_memory_order mo

end

let aid_times_aid_set_of_rel rel =
  Aid_times_aid_set.of_list (List.map (fun (a, a') -> (aid_of_action a, aid_of_action a')) rel)

module Layout = struct

let make_line sb laid_out_aids to_lay_out =
  let line =
    Action_set.filter
      (fun a ->
        Aid_times_aid_set.for_all (fun (aid, aid') -> not (aid' = aid_of_action a) || Aid_set.mem aid laid_out_aids ) sb)
      to_lay_out in
  let line_aids =
    Aid_set.of_list (List.map aid_of_action (Action_set.elements line)) in
  (line, line_aids, Action_set.diff to_lay_out line)

let vertical_layout sb acts =
  let rec f (laid_out, laid_out_aids, to_lay_out) =
    if Action_set.is_empty to_lay_out then laid_out
    else let (line, line_aids, rest) = make_line sb laid_out_aids to_lay_out in
      f (laid_out @ [line], Aid_set.union laid_out_aids line_aids, rest) in
  f ([], Aid_set.empty, acts)

module Aid_map = Map.Make(Aid)

module Aid_list = Functors.Ord_list(Aid)

module Aid_list_set = Set.Make(Aid_list)

module Real_map_action_set_aid_list_set = Functors.Real_map(Action_set)(Aid_list_set)

module Aid_times_aid_list = Functors.Ord_pair(Aid)(Aid_list)

module Aid_times_aid_list_set = Set.Make(Aid_times_aid_list)

module Option_bind_aid_list_set_aid_times_aid_list_set = Functors.Option_set_bind(Aid_list_set)(Aid_times_aid_list_set)

type reduction_mode =
| RM_no_reduction
| RM_transitive_reduction
| RM_transitive_reduction_over_sb

type colour = string

type edge_display_mode =
| ED_hide
| ED_show of reduction_mode * colour

type layout =
| L_naive
| L_frac

type display_info = {
  repulsion_factor : Rational_ml.t;
  mask : edge_display_mode String_map.t;
  layout : layout;
  step_div : int;
  iterations : int;
  margin : Rational_ml.t;
  x_factor : Rational_ml.t;
  y_factor : Rational_ml.t;
}

let rec last = function
| [] -> assert false
| [x] -> x
| _ :: xs -> last xs

let columns_of sb acts =
  let next columns =
    Aid_list_set.map
      (fun column ->
        let bot = List.hd column in
        let top = last column in
        let preds = Aid_times_aid_set.filter (fun (aid, aid') -> aid' = bot && Aid_times_aid_set.cardinal (Aid_times_aid_set.filter (fun (aid'', _) -> aid'' = aid) sb) = 1) sb in
        let succs = Aid_times_aid_set.filter (fun (aid, aid') -> aid = top && Aid_times_aid_set.cardinal (Aid_times_aid_set.filter (fun (_, aid'') -> aid'' = aid') sb) = 1) sb in
        (if Aid_times_aid_set.cardinal preds = 1 then match Aid_times_aid_set.choose_opt preds with None -> assert false | Some (aid, _) -> [aid] else [])
        @ column
        @ (if Aid_times_aid_set.cardinal succs = 1 then match Aid_times_aid_set.choose_opt succs with None -> assert false| Some (_, aid) -> [aid] else []))
      columns in
  let rec f columns =
    let columns' = next columns in
    if Aid_list_set.equal columns columns' then columns
    else f columns' in
  let columns = f (Real_map_action_set_aid_list_set.map (fun a -> [aid_of_action a]) acts) in
  let non_singleton_columns =
    Option_bind_aid_list_set_aid_times_aid_list_set.bind
      (function
      | [] -> assert false
      | [_] -> None
      | hd :: tail -> Some (hd, tail)) columns in
  let columns_map =
    List.fold_left
      (fun columns_map column ->
        let bot = List.hd column in
        let top = last column in
        List.fold_left (fun m x -> Aid_map.add x (bot, top) m) columns_map column)
      Aid_map.empty
      (Aid_list_set.elements columns) in
  (non_singleton_columns, columns_map)

module Formula = Rational_function.Make(Aid)

module Formula_set = Set.Make(Formula)

let width_of_action loc_map act =
  String.length (Bmc_types_pp.string_of_action loc_map act)

let repulse repulsion_factor a_rep a'_rep width =
  Formula.(F_times (F_div (F_const repulsion_factor, f_square (F_minus (F_var a_rep, F_var a'_rep))), F_const (width, 7)))

let attract a a' =
  Formula.f_square (F_minus (F_var a, F_var a'))

module Real_map_aid_times_aid_to_formula_set = Functors.Option_set_bind(Aid_times_aid_set)(Formula_set)

let equation_of_act display_info loc_map sb columns_map line act =
  let trans a =
    match Aid_map.find_opt a columns_map with
    | None -> assert false
    | Some v -> v in
  let a = aid_of_action act in
  let (a_top, a_bot) = trans a in
  let a_w = width_of_action loc_map act in
  assert (a = a_top);
  let repulsion =
    Functors.option_map
      (fun act' ->
        let a' = aid_of_action act' in
        let a'_w = width_of_action loc_map act' in
        if a' = a then None
        else
          let a'_rep = fst (trans a') in
          Some (repulse display_info.repulsion_factor a_top a'_rep (a_w + a'_w)))
      (Action_set.elements line) in
  let attraction_up =
    Real_map_aid_times_aid_to_formula_set.bind
      (fun (a1, a2) -> if a2 = a_top then let (a1', _) = trans a1 in Some (attract a1' a_top) else None)
      sb in
  let attraction_down =
    Real_map_aid_times_aid_to_formula_set.bind
      (fun (a1, a2) -> if a1 = a_bot then Some (attract a_bot a2) else None)
      sb in
  let attraction = (Formula_set.elements attraction_up) @ (Formula_set.elements attraction_down) in
  let f = Formula.F_plus (repulsion @ attraction) in
  let f' = Formula.simplify_formula (Formula.derivative a_top f) in
  Formula.simplify_formula Formula.(F_minus (F_const (0, 1), f'))

module Aid_map_of_list = Functors.Map_of_list(Aid_map)

let equations_map_of display_info loc_map sb columns_map lines =
  let x =
    Aid_map_of_list.of_list
      (List.concat
        (List.map
          (fun line ->
            Functors.option_map
              (fun act ->
                let aid = aid_of_action act in
                let (aid', _) = Aid_map.find aid columns_map in
                if Aid.compare aid aid' <> 0 then None
                else
                  let eqn = equation_of_act display_info loc_map sb columns_map line act in
                  Some (aid, eqn))
                (Action_set.elements line))
          lines)) in
  match x with
  | None -> assert false
  | Some map -> map

module Aid_times_pos = Functors.Ord_pair(Aid)(Pos)

module Aid_times_pos_set = Set.Make(Aid_times_pos)

module Real_map_action_times_pos_set_to_aid_times_pos_set = Functors.Real_map(Action_times_pos_set)(Aid_times_pos_set)

let obstruction_set_of actposs columns =
  let aidposs0 = Real_map_action_times_pos_set_to_aid_times_pos_set.map (fun (act, pos) -> (aid_of_action act, pos)) actposs in
  match Aid_map_of_list.of_list (Aid_times_pos_set.elements aidposs0) with
  | None -> assert false
  | Some aid_map ->
    Aid_times_aid_list_set.fold
      (fun (e, xs) aidposs ->
        match Aid_map.find_opt e aid_map with
        | None -> aidposs
        | Some (x, y) ->
          let (aidposs', _) =
            List.fold_left
              (fun (aidposs, y) aid -> (Aid_times_pos_set.add (aid, (x, y)) aidposs, y + 1) )
              (aidposs, y + 1)
              xs in
          aidposs')
      columns
      aidposs0

let obstruction obstruction_set pos =
  match Aid_times_pos_set.choose_opt (Aid_times_pos_set.filter (fun (_, pos') -> Pos.compare pos pos' = 0) obstruction_set) with
  | None -> None
  | Some (aid, _) -> Some aid

module Rational_ml_map = Map.Make(Rational_ml)

module Action_times_int = Functors.Ord_pair(Action)(Int)

module Action_times_int_set = Set.Make(Action_times_int)

module Real_map_action_times_int_set_to_action_times_pos = Functors.Real_map(Action_times_int_set)(Action_times_pos_set)

module Action_times_pos_set_union = Functors.Union(Action_times_pos_set)

module Collect_actions = Functors.Collect_in_map_fun(Rational_ml_map)(Action_times_pos_set)(Action_times_int_set)

let make_unit_spacing actposs =
  let act_map = Collect_actions.set_map_of (fun (act, (x, y)) -> (x, (act, y))) actposs in
  let actss =
    List.mapi
      (fun x (_, acts) ->
        Real_map_action_times_int_set_to_action_times_pos.map (fun (act, y) -> (act, ((x, 1), y))) acts)
      (Rational_ml_map.bindings act_map) in
  Action_times_pos_set_union.union actss

let init_var_map_frac sb (columns, columns_map) lines =
  let add_line actposs y line =
    let obstruction_set = obstruction_set_of actposs columns in
    let (actposs', _) =
      List.fold_left
        (fun (actposs, x) act ->
          let aid = aid_of_action act in
          let x' = Rational_ml.add (1, 1) x in
          match obstruction obstruction_set (x', y) with
          | None ->
            (match Aid_map.find_opt aid columns_map with
            | None -> (Action_times_pos_set.add (act, (x', y)) actposs, x')
            | Some (bot_aid, _) ->
              if aid = bot_aid then (Action_times_pos_set.add (act, (x', y)) actposs, x')
              else
                let (x'', _) = snd (Action_times_pos_set.choose (Action_times_pos_set.filter (fun (act, _) -> aid_of_action act = bot_aid) actposs)) in
                (Action_times_pos_set.add (act, (x'', y)) actposs, x''))
          | Some aid ->
            if (aid = aid_of_action act) then (Action_times_pos_set.add (act, (x', y)) actposs, x')
            else
              let x'' = Rational_ml.div_int (Rational_ml.add x x') 2 in
              (Action_times_pos_set.add (act, (x'', y)) actposs, x''))
          (actposs, (0, 1))
          (Action_set.elements line) in
    actposs' in
  let (actposs, _) =
    List.fold_left
      (fun (actposs, y) line -> (add_line actposs y line, y + 1))
      (Action_times_pos_set.empty, 0)
      lines in
  make_unit_spacing actposs

let init_var_map_naive sb columns lines =
  let rec add_line actposs columns y (n, d) = function
  | [] -> actposs
  | act :: line ->
    let actposs' = Action_times_pos_set.add (act, ((n, d), y)) actposs in
    add_line actposs' columns y (n + 1, d) line in
  let (actposs, _) =
    List.fold_left
      (fun (actposs, y) line ->
        (add_line actposs columns y (0, 1) (Action_set.elements line), y + 1))
      (Action_times_pos_set.empty, 0)
      lines in
  actposs

module Formula_evaluator = Rational_function.Make_evaluator(Formula)(Aid_map)

let step_aux display_info map eqn x =
  let deltax = Rational_ml.div_int (Formula_evaluator.evaluate map x eqn) display_info.step_div in
  Rational_ml.add x deltax

let step display_info columns_map eqns var_map =
  let map =
    Action_times_pos_set.fold
      (fun (act, (x, _)) m -> Aid_map.add (aid_of_action act) x m)
      var_map
      Aid_map.empty in
  Action_times_pos_set.map
    (fun (act, (x, y)) ->
      let (var, _) = Aid_map.find (aid_of_action act) columns_map in
      let x' = step_aux display_info map (Aid_map.find var eqns) x in
      (act, (x', y)))
    var_map

let iterate display_info columns_map eqns init_var_map =
  let rec f var_map n =
    if n <= 0 then var_map
    else f (step display_info columns_map eqns init_var_map) (n - 1) in
  f init_var_map display_info.iterations

module String_map_of_list = Functors.Map_of_list(String_map)

let default_display_info = {
  repulsion_factor = (1, 1);
  mask =
    (let l = [
      ("rf", ED_show (RM_no_reduction, "red"));
      ("sb", ED_show (RM_no_reduction, "black"));
      ("asw", ED_show (RM_transitive_reduction_over_sb, "deeppink4"));
      ("mo", ED_show (RM_no_reduction, "blue"));
      ("sc", ED_show (RM_no_reduction, "orange"));
      ("sw", ED_show (RM_no_reduction, "deeppink4"));
      ("hb", ED_show (RM_transitive_reduction, "forestgreen"));
      ("ithb", ED_show (RM_transitive_reduction, "forestgreen"))
      ] in
    match String_map_of_list.of_list l with | None -> assert false | Some m -> m);
  layout = L_frac;
  step_div = 10;
  iterations = 1000;
  margin = (2, 1);
  x_factor = (3, 2);
  y_factor = (1, 1);
}

let layout_thread display_info loc_map sb acts =
  let lines = vertical_layout sb acts in
  let (columns, columns_map) = columns_of sb acts in
  match display_info.layout with
  | L_naive -> init_var_map_naive sb columns lines
  | L_frac ->
     let eqns = equations_map_of display_info loc_map sb columns_map lines in
    iterate display_info columns_map eqns (init_var_map_frac sb (columns, columns_map) lines)

(* TODO: take label size into account *)
let bounds_of acts =
  match Action_times_pos_set.elements acts with
  | [] -> ((0, 1), (0, 1))
  | (_, (xpos, _)) :: acts' ->
    List.fold_left
      (fun (min, max) (_, (xpos, _)) -> (Rational_ml.min min xpos, Rational_ml.max max xpos))
      (xpos, xpos)
      acts'

let shift offset acts =
  Action_times_pos_set.map
    (fun (act, (x, y)) -> (act, (Rational_ml.add x offset, y)))
    acts

module Powerset_bind_aid_set_aid_set = Functors.Powerset_bind(Aid_set)(Aid_set)

module Aid_times_aid_set_to_aid_set_map = Functors.Real_map(Aid_times_aid_set)(Aid_set)

let down_closure rel n =
  let next s =
    let nx =
      Powerset_bind_aid_set_aid_set.bind
        (fun aid ->
          let outgoing = Aid_times_aid_set.filter (fun (src, _) -> src = aid) rel in
          Aid_times_aid_set_to_aid_set_map.map (fun (_, tgt) -> tgt) outgoing)
        s in
    Aid_set.union s nx in
  let rec f s =
    let s' = next s in
    if Aid_set.equal s s' then s
    else f s' in
  f (Aid_set.singleton n)

(* this assumes asw is pretty simple *)
let asw_surgery sb asw actposs =
  let level_map_of actposs =
    List.fold_left
      (fun m (act, (_, y)) -> Int_map.add (aid_of_action act) y m)
      Int_map.empty
      (Action_times_pos_set.elements actposs) in
  let min_asw excluded level_map =
    match
    List.fold_left
      (fun int_times_asws_opt (src, tgt) ->
        if Aid_times_aid_set.mem (src, tgt) excluded then int_times_asws_opt
        else
        match Int_map.find_opt src level_map with
        | None -> assert false
        | Some lvl ->
          (match int_times_asws_opt with
           | None -> Some (lvl, [(src, tgt)])
           | Some (lvl', edges) ->
             if lvl < lvl' then Some (lvl', [(src, tgt)])
             else if lvl > lvl' then Some (lvl', edges)
             else Some (lvl, edges @ [(src, tgt)])))
      None
      (Aid_times_aid_set.elements asw) with
      | None -> assert false
      | Some (_, edges) -> List.hd edges in
  let vertical_move_sb_down_closure y_offset tgt actposs =
    let aids = down_closure sb tgt in
    Action_times_pos_set.map
      (fun (act, (x, y)) -> if Aid_set.mem (aid_of_action act) aids then (act, (x, y + y_offset)) else (act, (x, y)))
      actposs in
  let step (excluded, actposs) =
    let level_map = level_map_of actposs in
    let (src, tgt) = min_asw excluded level_map in
    let lvl_tgt = Int_map.find tgt level_map in
    let lvl_src = Int_map.find src level_map in
    if lvl_tgt > lvl_src then (Aid_times_aid_set.add (src, tgt) excluded, actposs)
    else
      let offset = max (lvl_tgt - lvl_src) 1 in
      let actposs' = vertical_move_sb_down_closure offset tgt actposs in
      (Aid_times_aid_set.add (src, tgt) excluded, actposs') in
  let rec f (excluded, actposs) =
    if Aid_times_aid_set.equal excluded asw then actposs
    else f (step (excluded, actposs)) in
  f (Aid_times_aid_set.empty, actposs)

let juxtapose_threads display_info ths =
  let (actposs, _) =
    List.fold_left
      (fun (actposs, offset) th ->
        let (min, max) = bounds_of th in
        (Action_times_pos_set.union actposs (shift (Rational_ml.sub offset min) th), Rational_ml.add offset (Rational_ml.add (Rational_ml.sub max min) display_info.margin) ))
      (Action_times_pos_set.empty, (0, 1))
      ths in
  actposs

module Collect_tid = Functors.Collect_in_map(Int_map)(Action_set)

let collect_threads ex =
  Collect_tid.collect (tid_of_action) (Action_set.of_list ex.Bmc_types.actions)

(* TODO: space threads out depending on width *)
let layout_threads display_info loc_map ex =
  let thread_map = collect_threads ex in
  let sb' = aid_times_aid_set_of_rel ex.Bmc_types.sb in
  let ths =
    List.map
      (fun (tid, acts) -> layout_thread display_info loc_map sb' acts)
      (Int_map.bindings thread_map) in
  let actposs = juxtapose_threads display_info ths in
  asw_surgery sb' (aid_times_aid_set_of_rel ex.Bmc_types.asw) actposs

end

module Display = struct

let transitive_reduction s =
  Aid_times_aid_set.filter
    (fun (n, n'') ->
      not (Aid_times_aid_set.exists (fun (n1, n2) ->
        n = n1 &&
        Aid_times_aid_set.exists (fun (n3, n4) -> n2 = n3 && n4 = n'') s) s))
    s

let transitive_reduction_over_right s link =
  Aid_times_aid_set.filter
    (fun (s_src, s_tgt) ->
      not (Aid_times_aid_set.exists (fun (s'_src, s'_tgt) ->
        s_src = s'_src &&
        Aid_times_aid_set.exists (fun (l_src, l_tgt) -> s'_tgt = l_src && l_tgt = s_tgt) link) s))
    s

let transitive_reduction_over_left s link =
  Aid_times_aid_set.filter
    (fun (s_src, s_tgt) ->
      not (Aid_times_aid_set.exists (fun (s'_src, s'_tgt) ->
        s_tgt = s'_tgt &&
        Aid_times_aid_set.exists (fun (l_src, l_tgt) -> s'_src = l_tgt && l_src = s_src) link) s))
    s

let transitive_reduction_over s link =
  transitive_reduction_over_left (transitive_reduction_over_right s link) link

let repr n = "n" ^ string_of_int n

let make_edges display_info ex ew d =
  let add_edges name col rel edges =
    List.fold_left
      (fun edges (src, tgt) ->
        match Aid_times_aid_map.find_opt (src, tgt) edges with
        | None -> Aid_times_aid_map.add (src, tgt) [(name, col)] edges
        | Some l -> Aid_times_aid_map.add (src, tgt) (l @ [(name, col)]) edges)
      edges
      (Aid_times_aid_set.elements rel) in
  let sb' = transitive_reduction @@ aid_times_aid_set_of_rel ex.Bmc_types.sb in
  let asw' = aid_times_aid_set_of_rel ex.Bmc_types.asw in
  let rf' = aid_times_aid_set_of_rel ew.Bmc_types.rf in
  let mo' = transitive_reduction (aid_times_aid_set_of_rel ew.Bmc_types.mo) in
  let sc = aid_times_aid_set_of_rel ew.Bmc_types.sc in
  let transform rm edges =
    match rm with
    | Layout.RM_no_reduction -> edges
    | Layout.RM_transitive_reduction -> transitive_reduction edges
    | Layout.RM_transitive_reduction_over_sb -> transitive_reduction_over edges sb' in
  let add_edges_mask mask name rel edges =
    match String_map.find_opt name mask with
    | None -> edges
    | Some Layout.ED_hide -> edges
    | Some (Layout.ED_show (rm, col)) -> add_edges name col (transform rm rel) edges in
  let add_edges_mask2 mask name rel edges = add_edges_mask mask name (aid_times_aid_set_of_rel rel) edges in
  let base_edges =
    Aid_times_aid_map.empty |>
    add_edges_mask display_info.Layout.mask "sb" sb' |>
    add_edges_mask display_info.Layout.mask "asw" asw' |>
    add_edges_mask display_info.Layout.mask "rf" rf' |>
    add_edges_mask display_info.Layout.mask "mo" mo' |>
    add_edges_mask display_info.Layout.mask "sc" sc in
  let edges_with_derived = List.fold_left (fun edges (name, rel) -> add_edges_mask2 display_info.Layout.mask name rel edges) base_edges d.Bmc_types.derived_relations in
  let all_edges =
    List.fold_left
      (fun edges (name, fault) ->
        match fault with
        | Bmc_types.One x -> edges
        | Bmc_types.Two rel -> add_edges "undef" "darkorange" (aid_times_aid_set_of_rel rel) edges)
      edges_with_derived
      d.Bmc_types.undefined_behaviour in
  all_edges

let dot_of_edge attrs (n1, n2) =
  Dot.Edge { Dot.src = repr n1; Dot.tgt = repr n2; Dot.eattrs = attrs }

let display_nodes loc_map display_info d g =
  List.map
    (fun (act, (x, y)) ->
      let aid = aid_of_action act in
      (* TODO: is this the best way to display undef? *)
      let undefs =
        if List.exists
          (fun (name, fault) ->
            match fault with
              Bmc_types.One set -> List.mem act set
            | Bmc_types.Two _ -> false)
          d.Bmc_types.undefined_behaviour then [Dot.NColor "orange"]
        else [] in
      Dot.Node { Dot.nname = repr aid; Dot.nattrs = [Dot.NLabel (Bmc_types_pp.string_of_action loc_map act); Dot.NPos (Rational_ml.float_of (Rational_ml.mult display_info.Layout.x_factor x), -. Rational_ml.float_of (Rational_ml.mult (y, 1) display_info.Layout.y_factor)); Dot.NShape "none";] @ undefs })
    (Action_times_pos_set.elements g)

let display_edges display_info ex ew d =
  List.map
    (fun ((src, tgt), info) ->
      dot_of_edge
        [Dot.EColor (String.concat ":" (List.map snd info));
          Dot.ELabel (String.concat "," (List.map (fun (name, col) -> "<font color=\"" ^ col ^ "\">" ^ name ^ "</font>") info))] (src, tgt))
    (Aid_times_aid_map.bindings (make_edges display_info ex ew d))

let digraph_of_execution_aux loc_map display_info (ex, ew, d) g =
  [Dot.Graph_attr (Dot.Overlap false); Dot.Graph_attr (Dot.Splines true)] @ display_nodes loc_map display_info d g @ display_edges display_info ex ew d

let digraph_of_execution loc_map display_info (ex, ew, d) =
  let ths = Layout.layout_threads display_info loc_map ex in
  digraph_of_execution_aux loc_map display_info (ex, ew, d) ths

end

let pp_dot loc_map exec =
  Dot.string_of_digraph (Display.digraph_of_execution loc_map Layout.default_display_info exec)
