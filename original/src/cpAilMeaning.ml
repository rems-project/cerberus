module S = BatSet
module M = BatMap
module AC = CpAilConstraint

type id = CpSymbol.t
type action = CpAilAction.t

type 'a set = 'a BatSet.t
type ('a, 'b) map = ('a, 'b) BatMap.t

type denotation = {
  actions : action set;
  constraints : AC.t;
  seq_before : (action * action) set;
  fs_actions : (action, action set) map
}

module Denotation = struct
  type t = denotation
  let compare d1 d2 =
    let (++) n p = if n = 0 then p else n in
    S.compare d1.actions d2.actions
    ++ AC.compare d1.constraints d2.constraints
    ++ S.compare d1.seq_before d2.seq_before
    ++ M.compare S.compare d1.fs_actions d2.fs_actions
end

module DS = S.Make(Denotation)

let set_product_map f s1 s2 =
  S.fold (fun e1 x2 -> S.fold (fun e2 x2 -> S.add(f e1 e2) x2) s2 x2) s1 S.empty
let set_product s1 s2 = set_product_map (fun x y -> (x, y)) s1 s2

let list_product_map f s1 s2 =
  List.fold_left (fun x2 e1 -> List.fold_left (fun x2 e2 -> (f e1 e2) :: x2) s2 x2) s1 []
let list_product s1 s2 = list_product_map (fun x y -> (x, y)) s1 s2

let map_of_list ls =
  List.fold_left (fun m (k, d) -> M.add k d m) M.empty ls

type t = DS.t
(*type t = denotation S.t*)

type func = {
  break : t;
  continue : t;
  normal : t;
  return : t
}

let empty =
  (* Lexicographic ordering. *)
  (* let cmp d1 d2 = *)
  (*   let (++) n p = if n = 0 then p else n in *)
  (*   S.compare d1.actions d2.actions *)
  (*   ++ AC.compare d1.constraints d2.constraints *)
  (*   ++ S.compare d1.seq_before d2.seq_before *)
  (*   ++ S.compare d1.fs_actions d2.fs_actions *)
  (*   ++ S.compare d1.comp_actions d2.comp_actions in *)
  DS.singleton (*~cmp:cmp*) {
    actions = S.empty;
    constraints = AC.empty;
    seq_before = S.empty;
    fs_actions = M.empty
  }

let none = DS.empty

let and_denotations d1 d2 = {
  actions = S.union d1.actions d2.actions;
  constraints = AC.union d1.constraints d2.constraints;
  seq_before = S.union d1.seq_before d2.seq_before;
  fs_actions = M.union d1.fs_actions d2.fs_actions
}

let and_denotations_sb d1 d2 = {
  actions = S.union d1.actions d2.actions;
  constraints = AC.union d1.constraints d2.constraints;
  seq_before =
    begin
      let sb = set_product d1.actions d2.actions in
      S.union sb (S.union d1.seq_before d2.seq_before)
    end;
  fs_actions = M.union d1.fs_actions d2.fs_actions
}

let product_map pair s1 s2 =
  let fold_inner a s_init =
    DS.fold (fun b s -> DS.add (pair a b) s) s2 s_init in
  DS.fold (fun a s -> fold_inner a s) s1 DS.empty

let conj m1 m2 = product_map and_denotations m1 m2
let conj_seq_before m1 m2 = product_map and_denotations_sb m1 m2
let disj m1 m2 = DS.union m1 m2

let add_constraint m constr =
  let c = AC.make constr in
  DS.map (fun d -> {d with constraints = AC.union d.constraints c}) m

let add_constraint_set m c =
  DS.map (fun d -> {d with constraints = AC.union d.constraints c}) m

let add_action m a =
  DS.map (fun d -> {d with actions = S.add a d.actions}) m

module Operators = struct
  (* OCaml won't allow us to define (\/) and (/\). *sniff* *)
  let (<&>) = conj
  let (&>>) = conj_seq_before
  let (<|>) = disj
  let (<&-) = add_constraint
  let (<@-) = add_action
end

let empty_func = {
  break = DS.empty;
  continue = DS.empty;
  normal = empty;
  return = DS.empty
}

let break m = {
  break = m;
  continue = DS.empty;
  normal = DS.empty;
  return = DS.empty
}

let continue m = {
  break = DS.empty;
  continue = m;
  normal = DS.empty;
  return = DS.empty
}

let normal m = {
  break = DS.empty;
  continue = DS.empty;
  normal = m;
  return = DS.empty
}

let return m = {
  break = DS.empty;
  continue = DS.empty;
  normal = DS.empty;
  return = m
}

let collect_fs_actions =
  let module Action = CpAilAction in
  DS.map (fun d ->
    let call = Action.call () in
    {d with
      actions = S.singleton call;
      fs_actions = M.add call d.actions d.fs_actions
    }
  )

let flatten_func {break; continue; normal; return} =
  let open Operators in
      assert (DS.is_empty break);
      assert (DS.is_empty continue);
      collect_fs_actions (normal <&- AC.undef <|> return)

let enter_loop m_pos m_neg {break; continue; normal; return} =
  let open Operators in
      let m = continue <|> normal in {
        break = break <|> (m &>> m_neg);
        continue = DS.empty;
        normal = m &>> m_pos;
        return = return
      }

let exit_loop m_neg {break; continue; normal; return} =
  let open Operators in {empty_func with
    normal = break <|> ((continue <|> normal) &>> m_neg);
    return = return
  }

let conj_seq_before_func ml1 ml2 =
  let open Operators in {
    break = ml1.break <|> (ml1.normal &>> ml2.break);
    continue = ml1.continue <|> (ml1.normal &>> ml2.continue);
    normal = ml1.normal &>> ml2.normal;
    return = ml1.return <|> (ml1.normal &>> ml2.return)
  }

let disj_func ml1 ml2 =
  let open Operators in {
    break = ml1.break <|> ml2.break;
    continue = ml1.continue <|> ml2.continue;
    normal = ml1.normal <|> ml2.normal;
    return = ml1.return <|> ml2.return
  }

let add_constraint_func ml c =
  let open Operators in
      {ml with normal = ml.normal <&- c}

let add_action_func ml a =
  let open Operators in
      {ml with normal = ml.normal <@- a}

let add_action_entire_func {break; continue; normal; return} a =
  let open Operators in {
    break = break <@- a;
    continue = continue <@- a;
    normal = normal <@- a;
    return = return <@- a
  }

let add_actions_entire_func_sb {break; continue; normal; return} actions =
  let open Operators in
  let m = DS.map (fun d -> {d with actions = actions} ) empty in {
    break = break &>> m;
    continue = continue &>> m;
    normal = normal &>> m;
    return = return &>> m
  }

let add_constraint_entire_func {break; continue; normal; return} c =
  let open Operators in {
    break = break <&- c;
    continue = continue <&- c;
    normal = normal <&- c;
    return = return <&- c
  }

module StatementOperators = struct
  (* OCaml won't allow us to define (\/) and (/\). *sniff* *)
  let (&>>) = conj_seq_before_func
  let (<|>) = disj_func
  let (<&-) = add_constraint_entire_func
  let (<@-) = add_action_func
end

module Print = struct
  module P = Pprint
  module U = Pprint.Unicode

  open P.Operators

  let nbraces d = P.lbrace ^^ P.group2 (P.break0 ^^ d) ^/^ P.rbrace

  let pp_set pp s  =
    nbraces (P.comma_list pp (S.elements  s))
  let pp_dset pp s =
    let sep = P.comma ^^ P.break1 in
    let pp_b e = nbraces (pp e) in
    P.sepmap sep pp_b (DS.elements s)

  let pp_actions = pp_set CpAilAction.Print.pp
  let pp_contraints = AC.Print.pp
  let pp_action_id = CpAilAction.Print.pp_uid
  let pp_seq_before =
    let pp_a = pp_action_id in
    pp_set (fun (a1, a2) -> pp_a a1 ^^^ U.implies ^^^ pp_a a2)
  let pp_fs_actions m =
    let pp_a = pp_action_id in
    nbraces (
      P.comma_list
        (fun (a, b) -> pp_a a ^^^ U.mapsto ^^^ pp_actions b)
        (M.bindings m)
    )

  let pp_denot {actions; constraints; seq_before; fs_actions} =
    let line name pp p = !^ name ^^^ P.equals ^^^ P.group (pp p) ^^ P.semi in
    line "actions" pp_actions actions
    ^/^ line "constraints" pp_contraints constraints
    ^/^ line "sequenced_before" pp_seq_before seq_before
    ^/^ line "function_actions" pp_fs_actions fs_actions

  let pp m = nbraces (pp_dset pp_denot m) ^^ P.break0
end

module Solve = struct
  module Action = CpAilAction

  type trace = AC.t * action list

  let schedule pre s =
    match pre with
    | [] -> [S.fold (fun a ls -> a :: ls) s []]
    | _ ->
        let pre_f a ls = ls @ [a] in
        S.fold (fun a pre -> List.map (pre_f a) pre) s pre

  let partition_sb d u =
    let sa a u = S.exists (fun a' -> S.mem (a', a) d.seq_before) u in
    S.partition (fun a -> not (sa a u)) u

  let permute sb ts =
    let rec p t lls front tail =
      match tail with
      | [] -> (front @ [t]) :: lls
      | a::rest -> p t ((front @ (t :: tail)) :: lls) (front @ [a]) rest in
    let combine t lls ls =
      let rec split p front tail =
        match tail with
        | [] -> front, []
        | a::rest ->
            if p a then
              front, tail
            else
              split p (front @ [a]) rest in
      let split_sb = split (fun a -> S.mem (a, t) sb) in
      let split_sa = split (fun a -> S.mem (t, a) sb) in
      let rest, sa = split_sa [] ls in
      let nu, bs = split_sb [] (List.rev rest) in
      let sb = List.rev bs in
      let un = List.rev nu in
      let sb_un = List.map ((@) sb) (p t lls [] un) in
      List.map ((@) sa) sb_un in
    let step t lls = List.fold_left (combine t) [] lls in
    S.fold step ts [[]]

  let partition sb cs es =
    let rec f e lls cs front tail =
      match cs, tail with
      | [], [a] -> (front @ [e :: a]) :: lls
      | c::cs', a::rest ->
          let lls' = (front @ ((e :: a) :: rest)) :: lls in
          if S.mem (e, c) sb || List.exists (fun t -> S.mem (e, t) sb) a then
            lls'
          else
            if Action.is_access e && not (Action.is_fn_store e) then
              f e lls' cs' (front @ [a]) rest
            else
              f e lls  cs' (front @ [a]) rest in
    let step lls e =
      List.fold_left (fun lls ls -> f e lls cs [] ls) [] lls in
    List.fold_left step [BatList.make (1 + List.length cs) []] es
(*
  let rec merge d pre perm part =
    match perm, part with
    | [], [ts] -> schedule pre ts
    | c::cs, ts::tss ->
        let combine_pres (c1, ls1) (c2, ls2) = AC.union c1 c2, ls1 @ ls2 in
        merge d (schedule (BatList.product_map combine_pres pre c) ts) cs tss
    | _ -> assert (false)
*)

  let rec seq d pre future =
    let () = print_endline ("future: " ^ string_of_int (S.cardinal future)) in
    if S.is_empty future then
      pre
    else
      let sb, sa = partition_sb d future in
      let () = print_endline ("sb: " ^ string_of_int (S.cardinal sb)) in
      let sb_calls, sb_rest = S.partition Action.is_call sb in
      let sa_ucalls, sa_rest =
        S.partition
          (fun a -> Action.is_call a
            && S.exists (fun a' -> not (S.mem (a',a) d.seq_before)) sb)
          sa in
      let calls = S.union sb_calls sa_ucalls in
      if S.is_empty calls then
        seq d (schedule pre sb) sa
      else
        let sb_accesses, sb_other = S.partition Action.is_access sb_rest in
        let pre = schedule pre sb_other in
        let sa_rest_todo, sa_rest_rest = S.partition
          (fun a -> S.exists
            (fun c -> S.mem (a, c) d.seq_before
              || not (S.mem (c, a) d.seq_before)) calls)
          sa_rest in
        let todo_list =
          let rec f ls t =
            if S.is_empty t then
              ls
            else
              let sb, sa = S.partition
                (fun a -> S.for_all
                  (fun a' -> not (S.mem (a', a) d.seq_before)) t) t in
              f (S.elements sb @ ls) sa in
          f [] (S.union sb_accesses sa_rest_todo) in
        let call_map =
          let seq_call c =
            let () = print_endline ("c: " ^ string_of_int (S.cardinal (M.find c d.fs_actions))) in
            seq d [] (M.find c d.fs_actions) in
          map_of_list (List.map (fun c -> c, seq_call c) (S.elements calls)) in
        let perm = permute d.seq_before calls in
        let rec interleave pre cs ts =
          match cs, ts with
          | [], [t] -> List.map (fun p -> p @ t) pre
          | c::cs', t::ts ->
              let pre = List.map (fun p -> p @ t) pre in
              let pre = list_product_map (@) pre (M.find c call_map) in
              interleave pre cs' ts in
        let merge lls cs =
          let part = partition d.seq_before cs todo_list in
          List.fold_left (fun lls ts -> interleave pre cs ts @ lls) lls part in
        seq d (List.fold_left merge [] perm) sa_rest_rest

  let linearise d = seq d [] d.actions

  let simplify d c =
    let module P = AC.Process in
    let conflicts =
      M.fold
        (fun ts c -> AC.union c (Action.conflicts d.seq_before ts))
        d.fs_actions AC.empty in
    try
      let p = P.make d.constraints in
      let p = P.union p conflicts in
      let f c trace =
        try
(*
          S.add (Action.Memory.replay p trace) c
*)
          (Action.Memory.replay p trace) :: c
        with
        | P.Partial _ -> assert (false)
        | P.Invalid -> c in
      List.fold_left f c (linearise d)
    with P.Invalid -> c
(*
      List.fold_left f (S.create AC.compare) traces
    with P.Invalid -> S.create AC.compare
*)
  let set_of_list cmp ls = List.fold_left (fun a x -> S.add x a) (S.create cmp) ls

  let simplify_all t = set_of_list AC.compare (DS.fold simplify t [])

  let simplify_result = function
    | CpAil.Program t -> CpAil.Program (simplify_all t)
    | CpAil.Invalid -> CpAil.Invalid
    | CpAil.Undefined -> CpAil.Undefined
end

module Graph = struct
  let dot n t =
    DS.fold
      (fun d i ->
        let name = n ^ "." ^ (BatInt.to_string i) ^ ".dot" in
        let doc = CpAilAction.Print.pp_dot d.seq_before in
        let str = CpDocument.to_plain_string doc in
        let () = CpOutput.write str (CpOutput.file name) in
        i + 1
      ) t 0
  let dot_result n = function
    | CpAil.Program t -> ignore (dot n t)
    | _ -> ()
end
