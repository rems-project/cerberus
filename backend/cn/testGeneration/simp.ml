module BT = BaseTypes
module IT = IndexTerms
open Constraints
open Utils
module CF = Cerb_frontend
open CF

let subst_goal (x : Symbol.sym) (v : IT.t) ((vars, ms, locs, cs) : goal) : goal =
  let vars =
    List.map (fun (x', (ty, e)) -> (x', (ty, IT.subst (IT.make_subst [ (x, v) ]) e))) vars
  in
  let locs = List.map (fun (e, y) -> (IT.subst (IT.make_subst [ (x, v) ]) e, y)) locs in
  let cs = List.map (fun e -> IT.subst (IT.make_subst [ (x, v) ]) e) cs in
  (vars, ms, locs, cs)


let rec inline_constants' (g : goal) (iter : constraints) : goal =
  match iter with
  | IT (Binop (EQ, IT (Const c, bt, loc), IT (Sym x, _, _)), _, _) :: iter'
  | IT (Binop (EQ, IT (Sym x, _, _), IT (Const c, bt, loc)), _, _) :: iter' ->
    let g = subst_goal x (IT (Const c, bt, loc)) g in
    inline_constants' g iter'
  | _ :: iter' ->
    inline_constants' g iter'
  | [] ->
    g


let inline_constants (g : goal) : goal =
  let _, _, _, cs = g in
  inline_constants' g cs


let eval_term (it : IT.t) : IT.const option =
  let g = Global.empty in
  let m = Solver.empty_model in
  match Solver.eval g m it with
  | Some (IT (Const c, _, _)) ->
    Some c
  | _ ->
    None


let rec remove_tautologies ((vars, ms, locs, cs) : goal) : goal =
  match cs with
  | IT (Binop (EQ, IT (Sym x, _, _), IT (Sym y, _, _)), _, _) :: cs
    when sym_codified_equal x y ->
    remove_tautologies (vars, ms, locs, cs)
  | c :: cs ->
    (match eval_term c with
     | Some (Bool b) ->
       if b then
         remove_tautologies (vars, ms, locs, cs)
       else
         failwith "Inconsistent constraints"
     | Some _ ->
       failwith "unreachable"
     | None ->
       let vars, ms, locs, cs = remove_tautologies (vars, ms, locs, cs) in
       (vars, ms, locs, c :: cs))
  | [] ->
    (vars, ms, locs, cs)


let rec cnf_ (e : BT.t IT.term_) : BT.t IT.term_ =
  match e with
  (* Double negation elimination *)
  | Unop (Not, IT (Unop (Not, IT (e, _, _)), _, _)) ->
    e
  (* Flip inequalities *)
  | Unop (Not, IT (Binop (LT, e1, e2), _, _)) ->
    Binop (LE, e2, e1)
  | Unop (Not, IT (Binop (LE, e1, e2), _, _)) ->
    Binop (LT, e2, e1)
  (* De Morgan's Law *)
  | Unop (Not, IT (Binop (And, e1, e2), info, loc)) ->
    Binop (Or, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
  | Unop (Not, IT (Binop (Or, e1, e2), info, loc)) ->
    Binop (And, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
  (* Distribute disjunction *)
  | Binop (Or, e1, IT (Binop (And, e2, e3), info, loc))
  | Binop (Or, IT (Binop (And, e2, e3), info, loc), e1) ->
    Binop (And, IT (Binop (Or, e1, e2), info, loc), IT (Binop (Or, e1, e3), info, loc))
  | _ ->
    e


and cnf (e : IT.t) : IT.t =
  let (IT (e, info, loc)) = e in
  IT (cnf_ e, info, loc)


let rec inline_aliasing' (g : goal) (iter : constraints) : goal =
  match iter with
  | IT (Binop (EQ, IT (Sym x, info_x, loc_x), IT (Sym y, _, _)), info_y, loc_y) :: iter'
    ->
    let vars, _, _, _ = g in
    let g =
      match List.assoc sym_codified_equal x vars with
      | _, IT (Sym x', _, _) when sym_codified_equal x x' ->
        subst_goal x (IT (Sym y, info_y, loc_y)) g
      | _ ->
        subst_goal y (IT (Sym x, info_x, loc_x)) g
    in
    inline_aliasing' g iter'
  | _ :: iter' ->
    inline_aliasing' g iter'
  | [] ->
    g


let inline_aliasing (g : goal) : goal =
  let _, _, _, cs = g in
  inline_aliasing' g cs


let rec remove_nonnull_for_locs ((vars, ms, locs, cs) : goal) : goal =
  match cs with
  | IT (Unop (Not, IT (Binop (EQ, e, IT (Const Null, _, _)), _, _)), _, _) :: cs
    when List.assoc_opt Stdlib.( = ) e locs |> Option.is_some ->
    remove_nonnull_for_locs (vars, ms, locs, cs)
  | IT (Unop (Not, IT (Binop (EQ, IT (Const Null, _, _), e), _, _)), _, _) :: cs
    when List.assoc_opt Stdlib.( = ) e locs |> Option.is_some ->
    remove_nonnull_for_locs (vars, ms, locs, cs)
  | c :: cs ->
    let vars, ms, locs, cs = remove_nonnull_for_locs (vars, ms, locs, cs) in
    (vars, ms, locs, c :: cs)
  | [] ->
    (vars, ms, locs, [])


let rec indirect_members_expr_ (ms : members) (e : BT.t IT.term_) : BT.t IT.term_ =
  match e with
  | StructMember (IT (Sym x, _, _), Symbol.Identifier (_, y)) ->
    let new_sym =
      (List.assoc sym_codified_equal x ms |> List.find (fun m -> String.equal m.name y))
        .carrier
    in
    Sym new_sym
  | Unop (op, e') ->
    Unop (op, indirect_members_expr ms e')
  | Binop (op, e1, e2) ->
    Binop (op, indirect_members_expr ms e1, indirect_members_expr ms e2)
  | ITE (e_if, e_then, e_else) ->
    ITE
      ( indirect_members_expr ms e_if,
        indirect_members_expr ms e_then,
        indirect_members_expr ms e_else )
  | EachI ((min, (x', bt), max), e') ->
    EachI ((min, (x', bt), max), indirect_members_expr ms e')
  | Tuple es ->
    Tuple (List.map (indirect_members_expr ms) es)
  | NthTuple (i, e') ->
    NthTuple (i, indirect_members_expr ms e')
  | Struct (x', xes) ->
    Struct (x', List.map (fun (x', e') -> (x', indirect_members_expr ms e')) xes)
  | StructMember (e', x') ->
    StructMember (indirect_members_expr ms e', x')
  | StructUpdate ((e', x'), e'') ->
    StructUpdate ((indirect_members_expr ms e', x'), indirect_members_expr ms e'')
  | Record xes ->
    Record (List.map (fun (x', e') -> (x', indirect_members_expr ms e')) xes)
  | RecordMember (e', x') ->
    RecordMember (indirect_members_expr ms e', x')
  | RecordUpdate ((e', x'), e'') ->
    RecordUpdate ((indirect_members_expr ms e', x'), indirect_members_expr ms e'')
  | Constructor (x', xes) ->
    Constructor (x', List.map (fun (x', e') -> (x', indirect_members_expr ms e')) xes)
  | MemberShift (e', x', x'') ->
    MemberShift (indirect_members_expr ms e', x', x'')
  | ArrayShift { base; ct; index } ->
    ArrayShift
      { base = indirect_members_expr ms base; ct; index = indirect_members_expr ms index }
  | CopyAllocId { addr; loc } ->
    CopyAllocId
      { addr = indirect_members_expr ms addr; loc = indirect_members_expr ms loc }
  | Cons (e1, e2) ->
    Cons (indirect_members_expr ms e1, indirect_members_expr ms e2)
  | Head e' ->
    Head (indirect_members_expr ms e')
  | Tail e' ->
    Tail (indirect_members_expr ms e')
  | NthList (e1, e2, e3) ->
    NthList
      ( indirect_members_expr ms e1,
        indirect_members_expr ms e2,
        indirect_members_expr ms e3 )
  | ArrayToList (e1, e2, e3) ->
    ArrayToList
      ( indirect_members_expr ms e1,
        indirect_members_expr ms e2,
        indirect_members_expr ms e3 )
  | Representable (ty, e') ->
    Representable (ty, indirect_members_expr ms e')
  | Good (ty, e') ->
    Good (ty, indirect_members_expr ms e')
  | Aligned { t; align } ->
    Aligned { t = indirect_members_expr ms t; align = indirect_members_expr ms align }
  | WrapI (ty, e') ->
    WrapI (ty, indirect_members_expr ms e')
  | MapConst (bt, e') ->
    MapConst (bt, indirect_members_expr ms e')
  | MapSet (e1, e2, e3) ->
    MapSet
      ( indirect_members_expr ms e1,
        indirect_members_expr ms e2,
        indirect_members_expr ms e3 )
  | MapGet (e1, e2) ->
    MapGet (indirect_members_expr ms e1, indirect_members_expr ms e2)
  | MapDef (xbt, e') ->
    MapDef (xbt, indirect_members_expr ms e')
  | Apply (x', es) ->
    Apply (x', List.map (indirect_members_expr ms) es)
  | Let ((x', e1), e2) ->
    Let ((x', indirect_members_expr ms e1), indirect_members_expr ms e2)
  | Match (e', pes) ->
    Match
      ( indirect_members_expr ms e',
        List.map (fun (p, e') -> (p, indirect_members_expr ms e')) pes )
  | Cast (bt, e') ->
    Cast (bt, indirect_members_expr ms e')
  | Sym _
  | Const _
  | SizeOf _
  | OffsetOf _
  | Nil _ ->
    e


and indirect_members_expr (ms : members) (e : IT.t) : IT.t =
  let (IT (e, info, loc)) = e in
  IT (indirect_members_expr_ ms e, info, loc)


let indirect_members ((vars, ms, locs, cs) : goal) : goal =
  ( List.map (fun (x, (ty, e)) -> (x, (ty, indirect_members_expr ms e))) vars,
    ms,
    List.map (fun (e, x) -> (indirect_members_expr ms e, x)) locs,
    List.map (fun e -> indirect_members_expr ms e) cs )


let listify_constraints (cs : constraints) : constraints =
  let rec loop (c : IT.t) : constraints =
    match c with
    | IT (Binop (And, e1, e2), _, _) ->
      loop e1 @ loop e2
    | _ ->
      [ c ]
  in
  List.map loop cs |> List.flatten


let remove_good (cs : constraints) : constraints =
  List.filter
    (fun (c : IT.t) ->
      match c with
      | IT (Good _, _, _) ->
        false
      | _ ->
        true)
    cs


let simplify (g : goal) : goal =
  let g = indirect_members g in
  let vars, ms, locs, cs = g in
  let g = (vars, ms, locs, List.map cnf cs) in
  let g = remove_nonnull_for_locs g in
  let rec loop (g : goal) : goal =
    let og = g in
    let g = inline_constants g in
    let g = inline_aliasing g in
    let vars, ms, locs, cs = remove_tautologies g in
    let cs = listify_constraints cs in
    let cs = remove_good cs in
    let g = (vars, ms, locs, cs) in
    if Stdlib.( <> ) og g then loop g else g
  in
  loop g
