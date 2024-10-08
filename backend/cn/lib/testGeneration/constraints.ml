module AT = ArgumentTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
open Utils
module CF = Cerb_frontend

type variables = (Sym.sym * (CF.Ctype.ctype * IT.t)) list

let pp_variables (vars : variables) : Pp.document =
  let open Pp in
  group
    (lbrace
     ^^ nest
          2
          (break 1
           ^^ separate_map
                (semi ^^ break 1)
                (fun (x, (ty, it)) ->
                  string (codify_sym x)
                  ^^ string " -> ("
                  ^^ CF.Pp_ail.pp_ctype CF.Ctype.no_qualifiers ty
                  ^^ string ", "
                  ^^ IT.pp it
                  ^^ string ")")
                vars)
     ^^ break 1
     ^^ rbrace)


type locations = (IT.t * Sym.sym) list

let pp_locations (locs : locations) : Pp.document =
  let open Pp in
  group
    (lbrace
     ^^ nest
          2
          (break 1
           ^^ separate_map
                (semi ^^ break 1)
                (fun (it, x) ->
                  string "(*" ^^ IT.pp it ^^ string ") -> " ^^ string (codify_sym x))
                locs)
     ^^ break 1
     ^^ rbrace)


(** Tracks indirection for a struct's member [name],
    where [carrier] carries its value of type [cty].
    **)
type member =
  { name : string; (** The name of the member *)
    carrier : Sym.sym; (** The name of the carrier*)
    cty : CF.Ctype.ctype (** The type of the member *)
  }

let pp_member (m : member) : Pp.document =
  let open Pp in
  dot
  ^^ string m.name
  ^^ string ": "
  ^^ CF.Pp_ail.pp_ctype CF.Ctype.no_qualifiers m.cty
  ^^ string " = "
  ^^ string (codify_sym m.carrier)


type members = (Sym.sym * member list) list

let pp_members (ms : members) : Pp.document =
  let open Pp in
  let pp_members' (ml : member list) : Pp.document =
    nest 2 (break 1 ^^ separate_map (comma ^^ break 1) (fun m -> pp_member m) ml)
    ^^ break 1
  in
  group
    (lbrace
     ^^ nest
          2
          (break 1
           ^^ separate_map
                (semi ^^ break 1)
                (fun (x, m) ->
                  string (codify_sym x)
                  ^^ string " -> "
                  ^^ lbrace
                  ^^ pp_members' m
                  ^^ string "}")
                ms)
     ^^ break 1
     ^^ rbrace)


type constraints = IT.t list

let pp_constraints (cs : constraints) : Pp.document =
  let open Pp in
  group
    (lbrace
     ^^ nest 2 (break 1 ^^ separate_map (semi ^^ break 1) IT.pp cs)
     ^^ break 1
     ^^ rbrace)


type goal = variables * members * locations * constraints

let pp_goal ((vars, ms, locs, cs) : goal) : Pp.document =
  let open Pp in
  group
    (string "Vars: "
     ^^ pp_variables vars
     ^^ semi
     ^^ break 1
     ^^ string "Ms: "
     ^^ pp_members ms
     ^^ break 1
     ^^ string "Locs: "
     ^^ pp_locations locs
     ^^ break 1
     ^^ string "Cs: "
     ^^ pp_constraints cs)


module Collect = struct
  let bt_of_ctype (loc : Locations.t) (ty : CF.Ctype.ctype) : BT.t =
    Memory.bt_of_sct (Sctypes.of_ctype_unsafe loc ty)


  let add_to_vars_ms
    (sigma : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma)
    (sym : Sym.sym)
    (ty : CF.Ctype.ctype)
    (vars : variables)
    (ms : members)
    : variables * members
    =
    match ty with
    | Ctype (_, Struct n) ->
      (match List.assoc sym_codified_equal n sigma.tag_definitions with
       | _, _, StructDef (membs, _) ->
         let f (Sym.Identifier (_, id), (_, _, _, cty)) =
           let sym' = Sym.fresh () in
           ( ( sym',
               ( cty,
                 IT.sym_
                   ( sym',
                     bt_of_ctype (Locations.other __FUNCTION__) cty,
                     Locations.other __FUNCTION__ ) ) ),
             { name = id; carrier = sym'; cty } )
         in
         let vars', member_data = List.split (List.map f membs) in
         ( (( sym,
              ( ty,
                IT.sym_
                  ( sym,
                    bt_of_ctype (Locations.other __FUNCTION__) ty,
                    Locations.other __FUNCTION__ ) ) )
            :: vars)
           @ vars',
           (sym, member_data) :: ms )
       | _ -> failwith ("No struct '" ^ codify_sym n ^ "' defined"))
    | _ ->
      ( ( sym,
          ( ty,
            IT.fresh_named
              (bt_of_ctype (Locations.other __FUNCTION__) ty)
              (codify_sym sym)
              (Locations.other __FUNCTION__)
            |> snd ) )
        :: vars,
        ms )


  let ( let@ ) (x : 'a list) (f : 'a -> 'b list) : 'b list = List.flatten (List.map f x)

  let return (x : 'a) : 'a list = [ x ]

  let collect_lc (vars : variables) (ms : members) (lc : LC.t)
    : (variables * members * locations * constraints) list
    =
    match lc with
    | T it -> return (vars, ms, [], [ it ])
    | Forall _ -> failwith "`each` not supported"


  let rec collect_clauses
    (max_unfolds : int)
    (sigma : _ CF.AilSyntax.sigma)
    (prog5 : unit Mucore.file)
    (vars : variables)
    (ms : members)
    (cs : RP.clause list)
    : (IT.t * variables * members * locations * constraints) list
    =
    match cs with
    | cl :: cls' ->
      let rest =
        List.map
          (fun (v, vars, ms, locs, cs) ->
            (v, vars, ms, locs, IT.not_ cl.guard (Locations.other __FUNCTION__) :: cs))
          (collect_clauses max_unfolds sigma prog5 vars ms cls')
      in
      let@ v, vars, ms, locs, cs =
        collect_lat_it max_unfolds sigma prog5 vars ms cl.packing_ft
      in
      (v, vars, ms, locs, cl.guard :: cs) :: rest
    | [] -> []


  and collect_ret
    (max_unfolds : int)
    (sigma : _ CF.AilSyntax.sigma)
    (prog5 : unit Mucore.file)
    (vars : variables)
    (ms : members)
    (ret : RET.t)
    : (IT.t * variables * members * locations * constraints) list
    =
    match ret with
    | P { name = Owned (ty, _); pointer; iargs = [] } ->
      let sym = Sym.fresh () in
      let ty = Sctypes.to_ctype ty in
      let vars, ms = add_to_vars_ms sigma sym ty vars ms in
      let l = Locations.other __FUNCTION__ in
      return (IT.sym_ (sym, bt_of_ctype l ty, l), vars, ms, [ (pointer, sym) ], [])
    | P { name = Owned (_, _); _ } ->
      failwith "unreachable: Incorrect number of arguments for `Owned`"
    | P { name = PName psym; pointer; iargs } ->
      if max_unfolds <= 0 then
        []
      else (
        let pred = List.assoc sym_codified_equal psym prog5.resource_predicates in
        let args = List.combine (List.map fst pred.iargs) iargs in
        let clauses =
          Option.get pred.clauses
          |> List.map (RP.subst_clause (IT.make_subst [ (pred.pointer, pointer) ]))
          |> List.map
               (List.fold_right
                  (fun (x, v) acc -> RP.subst_clause (IT.make_subst [ (x, v) ]) acc)
                  args)
        in
        collect_clauses (max_unfolds - 1) sigma prog5 vars ms clauses)
    | Q _ -> failwith "`each` not supported"


  and collect_lat_it
    (max_unfolds : int)
    (sigma : _ CF.AilSyntax.sigma)
    (prog5 : unit Mucore.file)
    (vars : variables)
    (ms : members)
    (lat : IT.t LAT.t)
    : (IT.t * variables * members * locations * constraints) list
    =
    let lat_subst x v e = LAT.subst IT.subst (IT.make_subst [ (x, v) ]) e in
    match lat with
    | Define ((x, tm), _, lat') ->
      collect_lat_it max_unfolds sigma prog5 vars ms (lat_subst x tm lat')
    | Resource ((x, (ret, _)), _, lat') ->
      let@ v, vars, ms, locs, cs = collect_ret max_unfolds sigma prog5 vars ms ret in
      let@ v', vars, ms, locs', cs' =
        collect_lat_it max_unfolds sigma prog5 vars ms (lat_subst x v lat')
      in
      return (v', vars, ms, locs @ locs', cs @ cs')
    | Constraint (lc, _, lat') ->
      let@ vars, ms, locs, cs = collect_lc vars ms lc in
      let@ v, vars, ms, locs', cs' =
        collect_lat_it max_unfolds sigma prog5 vars ms lat'
      in
      return (v, vars, ms, locs @ locs', cs @ cs')
    | I it -> return (it, vars, ms, [], [])


  let rec collect_lat
    (max_unfolds : int)
    (sigma : _ CF.AilSyntax.sigma)
    (prog5 : unit Mucore.file)
    (vars : variables)
    (ms : members)
    (lat : unit LAT.t)
    : (variables * members * locations * constraints) list
    =
    let lat_subst x v e = LAT.subst (fun _ x -> x) (IT.make_subst [ (x, v) ]) e in
    match lat with
    | Define ((x, tm), _, lat') ->
      collect_lat max_unfolds sigma prog5 vars ms (lat_subst x tm lat')
    | Resource ((x, (ret, _)), _, lat') ->
      let@ v, vars, ms, locs, cs = collect_ret max_unfolds sigma prog5 vars ms ret in
      let@ vars, ms, locs', cs' =
        collect_lat max_unfolds sigma prog5 vars ms (lat_subst x v lat')
      in
      return (vars, ms, locs @ locs', cs @ cs')
    | Constraint (lc, _, lat') ->
      let@ vars, ms, locs, cs = collect_lc vars ms lc in
      let@ vars, ms, locs', cs' = collect_lat max_unfolds sigma prog5 vars ms lat' in
      return (vars, ms, locs @ locs', cs @ cs')
    | I _ -> return (vars, ms, [], [])


  let collect
    ~(max_unfolds : int)
    (sigma : _ CF.AilSyntax.sigma)
    (prog5 : unit Mucore.file)
    (args : (Sym.sym * CF.Ctype.ctype) list)
    (lat : unit LAT.t)
    : (variables * members * locations * constraints) list
    =
    let vars, ms =
      List.fold_left
        (fun (vars, ms) (x, ty) -> add_to_vars_ms sigma x ty vars ms)
        ([], [])
        args
    in
    collect_lat max_unfolds sigma prog5 vars ms lat
end

let collect = Collect.collect

module Simplify = struct
  let subst_goal (x : Sym.sym) (v : IT.t) ((vars, ms, locs, cs) : goal) : goal =
    let subst (it : IT.t) : IT.t =
      (IT.free_vars it
       |> LAT.SymSet.filter (sym_codified_equal x)
       |> LAT.SymSet.to_seq
       |> List.of_seq
       |> List.map (fun x' -> (x', v))
       |> IT.make_subst
       |> IT.subst)
        it
    in
    let vars = List.map (fun (x', (ty, e)) -> (x', (ty, subst e))) vars in
    let locs = List.map (fun (e, y) -> (subst e, y)) locs in
    let cs = List.map (fun e -> subst e) cs in
    (vars, ms, locs, cs)


  let rec inline_constants' (g : goal) (iter : constraints) : goal =
    match iter with
    | IT (Binop (EQ, IT (Const c, bt, loc), IT (Sym x, _, _)), _, _) :: iter'
    | IT (Binop (EQ, IT (Sym x, _, _), IT (Const c, bt, loc)), _, _) :: iter' ->
      let g = subst_goal x (IT (Const c, bt, loc)) g in
      inline_constants' g iter'
    | _ :: iter' -> inline_constants' g iter'
    | [] -> g


  let inline_constants (g : goal) : goal =
    let _, _, _, cs = g in
    inline_constants' g cs


  let eval_term (it : IT.t) : IT.const option =
    let g = Global.empty in
    let m = Solver.empty_model in
    match Solver.eval g m it with Some (IT (Const c, _, _)) -> Some c | _ -> None


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
       | Some _ -> failwith "unreachable"
       | None ->
         let vars, ms, locs, cs = remove_tautologies (vars, ms, locs, cs) in
         (vars, ms, locs, c :: cs))
    | [] -> (vars, ms, locs, cs)


  let rec cnf_ (e : IT.t') : IT.t' =
    match e with
    (* Double negation elimination *)
    | Unop (Not, IT (Unop (Not, IT (e, _, _)), _, _)) -> e
    (* Flip inequalities *)
    | Unop (Not, IT (Binop (LT, e1, e2), _, _)) -> Binop (LE, e2, e1)
    | Unop (Not, IT (Binop (LE, e1, e2), _, _)) -> Binop (LT, e2, e1)
    (* De Morgan's Law *)
    | Unop (Not, IT (Binop (And, e1, e2), info, loc)) ->
      Binop (Or, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
    | Unop (Not, IT (Binop (Or, e1, e2), info, loc)) ->
      Binop (And, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
    (* Distribute disjunction *)
    | Binop (Or, e1, IT (Binop (And, e2, e3), info, loc))
    | Binop (Or, IT (Binop (And, e2, e3), info, loc), e1) ->
      Binop (And, IT (Binop (Or, e1, e2), info, loc), IT (Binop (Or, e1, e3), info, loc))
    | _ -> e


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
        | _ -> subst_goal y (IT (Sym x, info_x, loc_x)) g
      in
      inline_aliasing' g iter'
    | _ :: iter' -> inline_aliasing' g iter'
    | [] -> g


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
    | [] -> (vars, ms, locs, [])


  let rec indirect_members_expr_ (ms : members) (e : IT.t') : IT.t' =
    match e with
    | StructMember (IT (Sym x, _, _), Sym.Identifier (_, y)) ->
      let new_sym =
        (List.assoc sym_codified_equal x ms |> List.find (fun m -> String.equal m.name y))
          .carrier
      in
      Sym new_sym
    | Unop (op, e') -> Unop (op, indirect_members_expr ms e')
    | Binop (op, e1, e2) ->
      Binop (op, indirect_members_expr ms e1, indirect_members_expr ms e2)
    | ITE (e_if, e_then, e_else) ->
      ITE
        ( indirect_members_expr ms e_if,
          indirect_members_expr ms e_then,
          indirect_members_expr ms e_else )
    | EachI ((min, (x', bt), max), e') ->
      EachI ((min, (x', bt), max), indirect_members_expr ms e')
    | Tuple es -> Tuple (List.map (indirect_members_expr ms) es)
    | NthTuple (i, e') -> NthTuple (i, indirect_members_expr ms e')
    | Struct (x', xes) ->
      Struct (x', List.map (fun (x', e') -> (x', indirect_members_expr ms e')) xes)
    | StructMember (e', x') -> StructMember (indirect_members_expr ms e', x')
    | StructUpdate ((e', x'), e'') ->
      StructUpdate ((indirect_members_expr ms e', x'), indirect_members_expr ms e'')
    | Record xes ->
      Record (List.map (fun (x', e') -> (x', indirect_members_expr ms e')) xes)
    | RecordMember (e', x') -> RecordMember (indirect_members_expr ms e', x')
    | RecordUpdate ((e', x'), e'') ->
      RecordUpdate ((indirect_members_expr ms e', x'), indirect_members_expr ms e'')
    | Constructor (x', xes) ->
      Constructor (x', List.map (fun (x', e') -> (x', indirect_members_expr ms e')) xes)
    | MemberShift (e', x', x'') -> MemberShift (indirect_members_expr ms e', x', x'')
    | ArrayShift { base; ct; index } ->
      ArrayShift
        { base = indirect_members_expr ms base;
          ct;
          index = indirect_members_expr ms index
        }
    | CopyAllocId { addr; loc } ->
      CopyAllocId
        { addr = indirect_members_expr ms addr; loc = indirect_members_expr ms loc }
    | HasAllocId loc -> HasAllocId (indirect_members_expr ms loc)
    | Cons (e1, e2) -> Cons (indirect_members_expr ms e1, indirect_members_expr ms e2)
    | Head e' -> Head (indirect_members_expr ms e')
    | Tail e' -> Tail (indirect_members_expr ms e')
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
    | Representable (ty, e') -> Representable (ty, indirect_members_expr ms e')
    | Good (ty, e') -> Good (ty, indirect_members_expr ms e')
    | Aligned { t; align } ->
      Aligned { t = indirect_members_expr ms t; align = indirect_members_expr ms align }
    | WrapI (ty, e') -> WrapI (ty, indirect_members_expr ms e')
    | MapConst (bt, e') -> MapConst (bt, indirect_members_expr ms e')
    | MapSet (e1, e2, e3) ->
      MapSet
        ( indirect_members_expr ms e1,
          indirect_members_expr ms e2,
          indirect_members_expr ms e3 )
    | MapGet (e1, e2) -> MapGet (indirect_members_expr ms e1, indirect_members_expr ms e2)
    | MapDef (xbt, e') -> MapDef (xbt, indirect_members_expr ms e')
    | Apply (x', es) -> Apply (x', List.map (indirect_members_expr ms) es)
    | Let ((x', e1), e2) ->
      Let ((x', indirect_members_expr ms e1), indirect_members_expr ms e2)
    | Match (e', pes) ->
      Match
        ( indirect_members_expr ms e',
          List.map (fun (p, e') -> (p, indirect_members_expr ms e')) pes )
    | Cast (bt, e') -> Cast (bt, indirect_members_expr ms e')
    | Sym _ | Const _ | SizeOf _ | OffsetOf _ | Nil _ -> e


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
      match c with IT (Binop (And, e1, e2), _, _) -> loop e1 @ loop e2 | _ -> [ c ]
    in
    List.map loop cs |> List.flatten


  let remove_good (cs : constraints) : constraints =
    List.filter
      (fun (c : IT.t) -> match c with IT (Good _, _, _) -> false | _ -> true)
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
end

let simplify = Simplify.simplify
