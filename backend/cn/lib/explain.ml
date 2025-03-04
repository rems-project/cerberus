module Rp = Report
module BT = BaseTypes
module IT = IndexTerms
module Def = Definition
module Req = Request
module Res = Resource
module LF = Definition.Function
module LAT = LogicalArgumentTypes
module LC = LogicalConstraints
module Loc = Locations
module C = Context
open Pp

(* perhaps somehow unify with above *)
type action =
  | Read of IndexTerms.t * IndexTerms.t
  | Write of IndexTerms.t * IndexTerms.t
  | Create of IndexTerms.t
  | Kill of IndexTerms.t
  | Call of Sym.t * IndexTerms.t list
  | Return of IndexTerms.t

type log_entry =
  | Action of action * Locations.t
  | State of Context.t

type log = log_entry list (* most recent first *)

(** Infrastructure for checking if a countermodel satisfies a predicate **)
module CheckPreds = struct
  open ResultWithData

  type check_result = (LC.t list, Pp.document) result_with_data

  (* let pp_check_result =
     pp_result_with_data (Pp.list (fun lc -> !^"\n" ^^^ LC.pp lc)) (fun d -> d) *)


  (* Gives a single canonical result *)
  let combine_results (results : check_result list) : check_result =
    match results with
    | [] -> Error !^"Empty result list"
    | h :: t ->
      let combine acc res =
        match (acc, res) with
        | Yes l, _ -> Yes l
        | _, Yes l -> Yes l
        | Error s, _ -> Error s
        | _, Error s -> Error s
        | Unknown s, _ -> Unknown s
        | _, Unknown s -> Unknown s
        | No s, _ -> No s
      in
      List.fold_left combine h t


  (* Type of nonterminal lines in a predicate clause.
     Corresponds to packing_ft *)
  type def_line =
    | DefineL of (Sym.t * IT.t) * Loc.info
    | ResourceL of (Sym.t * (Req.t * BT.t)) * Loc.info

  (* Optionally zip two lists, returning None if the lists have different lengths *)
  let rec zip (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list option =
    match (l1, l2) with
    | [], [] -> Some []
    | h1 :: tl1, h2 :: tl2 ->
      (match zip tl1 tl2 with Some zs -> Some ((h1, h2) :: zs) | None -> None)
    | _, _ -> None


  (* Take the union of two symbol maps,
     removing any key that is in both maps but has a different value in each *)
  let merge_eq (eq : 'a -> 'a -> bool) (m1 : 'a Sym.Map.t) (m2 : 'a Sym.Map.t)
    : 'a Sym.Map.t
    =
    let merge _ v1 v2 = if eq v1 v2 then Some v1 else None in
    Sym.Map.union merge m1 m2


  (* Build a map by using f to develop a map for each
     pair of elements in the two lists, failing
     if they produce different results for any symbol or if
     the lists have different lengths *)
  let map_from_lists f eq exps exps' =
    let merge_r_maps r_acc (exp1, exp1') =
      let@ acc = r_acc in
      let@ combined = f exp1 exp1' in
      Yes (merge_eq eq acc combined)
    in
    match zip exps exps' with
    | Some zipped -> List.fold_left merge_r_maps (Yes Sym.Map.empty) zipped
    | None -> Error !^"Could not zip lists of expressions." (* should never happen *)


  (* Match an expression with free variables against a candidate returned by the solver to
     get candidates for each of those free variables *)
  let rec get_var_cands (exp : IT.t) (candidate : IT.t)
    : (IT.t Sym.Map.t, Pp.document) result_with_data
    =
    let map_from_IT_lists = map_from_lists get_var_cands IT.equal in
    let sort_by_discard_fst compare l =
      List.map snd (List.sort (fun p1 p2 -> compare (fst p1) (fst p2)) l)
    in
    let sort_by_id = sort_by_discard_fst Id.compare in
    let sort_by_pattern = sort_by_discard_fst (Terms.compare_pattern BT.compare) in
    let map_with_guard_unknown g l1 l1' =
      if g then map_from_IT_lists l1 l1' else Unknown (Pp.bool g ^^^ !^" not satisfied")
    in
    let map_with_guard_no g l1 l1' =
      if g then map_from_IT_lists l1 l1' else No (Pp.bool g ^^^ !^" not satisfied")
    in
    let default =
      Unknown
        (!^"Different CN constructors for "
         ^^^ IT.pp exp
         ^^^ !^" and "
         ^^^ IT.pp candidate)
    in
    match (IT.get_term exp, IT.get_term candidate) with
    | Const c, Const c' -> map_with_guard_no (IT.equal_const c c') [] []
    | Sym v, _' -> Yes (Sym.Map.add v candidate Sym.Map.empty)
    | Unop (op, exp1), Unop (op', exp1') ->
      map_with_guard_unknown (IT.equal_unop op op') [ exp1 ] [ exp1' ]
    | Binop (op, exp1, exp2), Binop (op', exp1', exp2') ->
      map_with_guard_unknown (IT.equal_binop op op') [ exp1; exp2 ] [ exp1'; exp2' ]
    | ITE (exp1, exp2, exp3), ITE (exp1', exp2', exp3') ->
      map_from_IT_lists [ exp1; exp2; exp3 ] [ exp1'; exp2'; exp3' ]
    | EachI ((z1, (v, bty), z2), exp1), EachI ((z1', (v', bty'), z2'), exp1') ->
      map_with_guard_unknown
        (z1 = z1' && Sym.equal v v' && BT.equal bty bty' && z2 = z2')
        [ exp1 ]
        [ exp1' ]
    | Tuple exps, Tuple exps' -> map_from_IT_lists exps exps'
    | NthTuple (n, exp1), NthTuple (n', exp1') ->
      map_with_guard_unknown (n = n') [ exp1 ] [ exp1' ]
    | Struct (name, fields), Struct (name', fields') ->
      map_with_guard_no (Sym.equal name name') (sort_by_id fields) (sort_by_id fields')
    | StructMember (exp1, id), StructMember (exp1', id') ->
      map_with_guard_unknown (Id.equal id id') [ exp1 ] [ exp1' ]
    | StructUpdate ((exp1, id), exp2), StructUpdate ((exp1', id'), exp2') ->
      map_with_guard_unknown (Id.equal id id') [ exp1; exp2 ] [ exp1'; exp2' ]
    | Record fields, Record fields' ->
      map_from_IT_lists (sort_by_id fields) (sort_by_id fields')
    | RecordMember (exp1, id), RecordMember (exp1', id') ->
      map_with_guard_unknown (Id.equal id id') [ exp1 ] [ exp1' ]
    | RecordUpdate ((exp1, id), exp2), RecordUpdate ((exp1', id'), exp2') ->
      map_with_guard_unknown (Id.equal id id') [ exp1; exp2 ] [ exp1'; exp2' ]
    | Constructor (name, args), Constructor (name', args') ->
      map_with_guard_no (Sym.equal name name') (sort_by_id args) (sort_by_id args')
    | MemberShift (exp1, v, id), MemberShift (exp1', v', id') ->
      map_with_guard_unknown (Sym.equal v v' && Id.equal id id') [ exp1 ] [ exp1' ]
    | ( ArrayShift { base; ct; index },
        ArrayShift { base = base'; ct = ct'; index = index' } ) ->
      map_with_guard_unknown (Sctypes.equal ct ct') [ base; index ] [ base'; index' ]
    | CopyAllocId { addr = exp1; loc = exp2 }, CopyAllocId { addr = exp1'; loc = exp2' }
      ->
      map_from_IT_lists [ exp1; exp2 ] [ exp1'; exp2' ]
    | HasAllocId exp1, HasAllocId exp1' -> get_var_cands exp1 exp1'
    | SizeOf cty, SizeOf cty' -> map_with_guard_unknown (Sctypes.equal cty cty') [] []
    | OffsetOf (v, id), OffsetOf (v', id') ->
      map_with_guard_unknown (Sym.equal v v' && Id.equal id id') [] []
    | Nil bty, Nil bty' -> map_with_guard_no (BT.equal bty bty') [] []
    | Cons (h, tl), Cons (h', tl') -> map_from_IT_lists [ h; tl ] [ h'; tl' ]
    | Head l, Head l' -> get_var_cands l l'
    | Tail l, Tail l' -> get_var_cands l l'
    | NthList (exp1, exp2, exp3), NthList (exp1', exp2', exp3') ->
      map_from_IT_lists [ exp1; exp2; exp3 ] [ exp1'; exp2'; exp3' ]
    | ArrayToList (exp1, exp2, exp3), ArrayToList (exp1', exp2', exp3') ->
      map_from_IT_lists [ exp1; exp2; exp3 ] [ exp1'; exp2'; exp3' ]
    | Representable (cty, exp1), Representable (cty', exp1') ->
      map_with_guard_unknown (Sctypes.equal cty cty') [ exp1 ] [ exp1' ]
    | Good (cty, exp1), Good (cty', exp1') ->
      map_with_guard_unknown (Sctypes.equal cty cty') [ exp1 ] [ exp1' ]
    | Aligned { t = exp1; align = exp2 }, Aligned { t = exp1'; align = exp2' } ->
      map_from_IT_lists [ exp1; exp2 ] [ exp1'; exp2' ]
    | WrapI (ity, exp1), WrapI (ity', exp1') ->
      map_with_guard_unknown
        (Cerb_frontend.IntegerType.integerTypeEqual ity ity')
        [ exp1 ]
        [ exp1' ]
    | MapConst (bty, exp1), MapConst (bty', exp1') ->
      map_with_guard_unknown (BT.equal bty bty') [ exp1 ] [ exp1' ]
    | MapSet (exp1, exp2, exp3), MapSet (exp1', exp2', exp3') ->
      map_from_IT_lists [ exp1; exp2; exp3 ] [ exp1'; exp2'; exp3' ]
    | MapGet (exp1, exp2), MapGet (exp1', exp2') ->
      map_from_IT_lists [ exp1; exp2 ] [ exp1'; exp2' ]
    | MapDef ((v, bty), exp1), MapDef ((v', bty'), exp1') ->
      map_with_guard_unknown (Sym.equal v v' && BT.equal bty bty') [ exp1 ] [ exp1' ]
    | Apply (v, exps), Apply (v', exps') ->
      map_with_guard_unknown (Sym.equal v v') exps exps'
    | Let ((v, exp1), exp2), Let ((v', exp1'), exp2') ->
      map_with_guard_unknown (Sym.equal v v') [ exp1; exp2 ] [ exp1'; exp2' ]
    | Match (exp1, pats), Match (exp1', pats') ->
      map_from_IT_lists (exp1 :: sort_by_pattern pats) (exp1' :: sort_by_pattern pats')
    | Cast (bt, exp1), Cast (bt', exp1') ->
      map_with_guard_unknown (BT.equal bt bt') [ exp1 ] [ exp1' ]
    (* included so the compiler will catch any missing new constructors *)
    | Const _, _ -> default
    | Unop _, _ -> default
    | Binop _, _ -> default
    | ITE _, _ -> default
    | EachI _, _ -> default
    | Tuple _, _ -> default
    | NthTuple _, _ -> default
    | Struct _, _ -> default
    | StructMember _, _ -> default
    | StructUpdate _, _ -> default
    | Record _, _ -> default
    | RecordMember _, _ -> default
    | RecordUpdate _, _ -> default
    | Constructor _, _ -> default
    | MemberShift _, _ -> default
    | ArrayShift _, _ -> default
    | CopyAllocId _, _ -> default
    | HasAllocId _, _ -> default
    | SizeOf _, _ -> default
    | OffsetOf _, _ -> default
    | Nil _, _ -> default
    | Cons _, _ -> default
    | Head _, _ -> default
    | Tail _, _ -> default
    | NthList _, _ -> default
    | ArrayToList _, _ -> default
    | Representable _, _ -> default
    | Good _, _ -> default
    | Aligned _, _ -> default
    | WrapI _, _ -> default
    | MapConst _, _ -> default
    | MapSet _, _ -> default
    | MapGet _, _ -> default
    | MapDef _, _ -> default
    | Apply _, _ -> default
    | Let _, _ -> default
    | Match _, _ -> default
    | Cast _, _ -> default


  let rec organize_lines_aux
    (lines : LAT.packing_ft)
    (defs : def_line Sym.Map.t)
    (lcs : LC.t list)
    : IT.t * def_line Sym.Map.t * LC.t list
    =
    match lines with
    | Define ((v, it), i, next) ->
      let ln = DefineL ((v, it), i) in
      let new_defs = Sym.Map.add v ln defs in
      organize_lines_aux next new_defs lcs
    | Resource ((v, (rt, bt)), i, next) ->
      let ln = ResourceL ((v, (rt, bt)), i) in
      let new_defs = Sym.Map.add v ln defs in
      organize_lines_aux next new_defs lcs
    | Constraint (lc, _, next) -> organize_lines_aux next defs (lc :: lcs)
    | I it -> (it, defs, lcs)


  (* Sort lines into the returned expression, a map of variables to their defining lines, and a list of constraints *)
  let organize_lines (lines : LAT.packing_ft) : IT.t * def_line Sym.Map.t * LC.t list =
    organize_lines_aux lines Sym.Map.empty []


  (* ask the solver if the given set of constraints is satisfiable *)
  let ask_solver g lcs =
    match Solver.ask_solver (Solver.make g) lcs with
    | Unsat -> No !^"Solver returned No."
    | Unknown -> Unknown !^"Solver returned Unknown."
    | Sat -> Yes lcs


  let pair_to_lc (ps : IT.t * IT.t) : LogicalConstraints.t =
    let here = Locations.other __LOC__ in
    LC.T (IT.eq_ (fst ps, snd ps) here)


  (* convert a list of variable assignments to equality constraints *)
  let convert_symmap_to_lcs (m : IT.t Sym.Map.t) : LogicalConstraints.t list =
    let here = Locations.other __LOC__ in
    let kvs = Sym.Map.bindings m in
    List.map (fun (k, v) -> pair_to_lc (IT.IT (IT.Sym k, IT.get_bt v, here), v)) kvs


  (* check if a candidate term could have been the output of a given predicate *)
  let rec check_pred
    (name : Sym.t)
    (def : Def.Predicate.t)
    (candidate : IT.t)
    (ctxt : C.t)
    (iarg_vals : IT.t list)
    (term_vals : (IT.t * IT.t) list)
    : check_result
    =
    (* ensure candidate type matches output type of predicate *)
    assert (BT.equal (IT.get_bt candidate) def.oarg_bt);
    match def.clauses with
    | None -> Unknown (!^"Predicate" ^^^ Sym.pp name ^^^ !^"is uninterpreted. ")
    | Some clauses ->
      (* add negation of previous clauses' guards into each clause's guard*)
      let clauses_with_guards = Def.Clause.explicit_negative_guards clauses in
      (* for each clause, check if candidate could have been its output *)
      let checked =
        List.map
          (fun c -> check_clause c candidate ctxt def.iargs iarg_vals term_vals)
          clauses_with_guards
      in
      combine_results checked


  (* check if a candidate term could have been the output of a predicate clause *)
  and check_clause
    (c : Def.Clause.t)
    (candidate : IT.t)
    (ctxt : C.t)
    (iargs : (Sym.t * BT.t) list)
    (iarg_vals : IT.t list)
    (term_vals : (IT.t * IT.t) list)
    =
    match Base.List.zip (List.map fst iargs) iarg_vals with
    | Unequal_lengths -> Unknown !^"Wrong number of predicate arguments provided"
    | Ok zipped ->
      (* get constraints on iarg values *)
      let toMap xs =
        List.fold_left (fun acc (k, v) -> Sym.Map.add k v acc) Sym.Map.empty xs
      in
      let ics = convert_symmap_to_lcs (toMap zipped) in
      (* (Sym.Map.of_seq (List.to_seq zipped)) in *)
      (* get other constraints on terms *)
      let tcs = List.map pair_to_lc term_vals in
      (* get returned expression of c and variable dependency graph *)
      let exp, var_def_locs, lcs = organize_lines c.packing_ft in
      (* get constraints on whether candidate could have come from this clause *)
      let@ cs, vs =
        get_body_constraints exp var_def_locs candidate ctxt iargs term_vals
      in
      (* add guard and variable assignments to constraints list *)
      let cs' =
        List.concat
          [ LC.Set.elements ctxt.constraints;
            lcs;
            cs;
            ics;
            tcs;
            convert_symmap_to_lcs vs;
            [ LC.T c.guard ]
          ]
      in
      (* query solver *)
      ask_solver ctxt.global (Base.List.dedup_and_sort ~compare:LC.compare cs')


  (* get a list of constraints that are satisfiable iff candidate could have come from this clause body *)
  and get_body_constraints
    (exp : IT.t)
    (var_def_locs : def_line Sym.Map.t)
    (candidate : IT.t)
    (ctxt : C.t)
    (iargs : (Sym.t * BT.t) list)
    (term_vals : (IT.t * IT.t) list)
    =
    let f var_cands =
      (* find constraints from checking each variable one at a time *)
      let accumulate_results acc (v, v_cand) =
        let@ acc_lcs, acc_var_cands = acc in
        let@ v_lcs, v_var_cands =
          get_var_constraints v v_cand acc_var_cands var_def_locs ctxt iargs term_vals
        in
        Yes (List.append v_lcs acc_lcs, v_var_cands)
      in
      List.fold_left accumulate_results (Yes ([], var_cands)) (Sym.Map.bindings var_cands)
    in
    (* use candidate to get terms for FVs in exp *)
    match get_var_cands exp candidate with
    | Yes var_cands -> f var_cands
    | No e -> No e
    | Error e -> Error e
    | Unknown e ->
      let s = Solver.make ctxt.global in
      let here = Locations.other __LOC__ in
      let th = !Solver.try_hard in
      let _ = Solver.try_hard := true in
      let res =
        match Solver.ask_solver s [ LC.T (IT.eq_ (exp, candidate) here) ] with
        | Sat ->
          (* not using model to get var cands because it may overconstrain *)
          Yes ([], Sym.Map.empty)
        | Unsat -> No !^"Solver returned no at variable assignment stage."
        | Unknown -> Unknown e
      in
      let _ = Solver.try_hard := th in
      res


  and get_var_constraints
    (v : Sym.t)
    (v_cand : IT.t)
    (var_cands : IT.t Sym.Map.t)
    (var_def_locs : def_line Sym.Map.t)
    (ctxt : C.t)
    (iargs : (Sym.t * BT.t) list)
    (term_vals : (IT.t * IT.t) list)
    =
    (* find def of x *)
    match Sym.Map.find_opt v var_def_locs with
    | None ->
      (match (Sym.Map.find_opt v ctxt.logical, Sym.Map.find_opt v ctxt.computational) with
       | Some (Value it, _), _ ->
         get_body_constraints it var_def_locs v_cand ctxt iargs term_vals
       | _, Some (Value it, _) ->
         get_body_constraints it var_def_locs v_cand ctxt iargs term_vals
       (* TODO: BaseType case *)
       | _ ->
         let f (s, _) = Sym.equal s v in
         (match List.find_opt f iargs with
          | Some _ -> Yes ([], var_cands)
          | _ -> Unknown (!^"Could not find variable definition line for" ^^^ Sym.pp v)))
    | Some line ->
      (match line with
       (* recurse with x's definition *)
       | DefineL ((_, t), _) ->
         get_body_constraints t var_def_locs v_cand ctxt iargs term_vals
       | ResourceL ((_, (p, _)), _) ->
         (match p with
          | P { name = Owned _; pointer = _; iargs = _ } ->
            (* if the predicate is Owned, get restrictions on pointer *)
            let owned_lcs = Res.derived_lc1 (p, O v_cand) in
            Yes (List.map (fun it -> LC.T it) owned_lcs, var_cands)
          | P { name = PName name; pointer = _; iargs } ->
            (* search for predicate definition *)
            (match Sym.Map.find_opt name ctxt.global.resource_predicates with
            | Some pdef ->
              (match check_pred name pdef v_cand ctxt iargs term_vals with
                | Yes cs -> Yes (cs, var_cands)
                | No e -> No e
                | Unknown e -> Unknown e
                | Error e -> Error e)
            | None ->
              Unknown (!^"Could not find definition of predicate" ^^^ Sym.pp name))
          | Q _ ->
            Unknown !^"Quantified predicates are out of scope for now."))
end

let clause_has_resource req c =
  let open LogicalArgumentTypes in
  let rec f = function
    | Resource ((_, (r, _)), _, c) -> Req.same_name req r || f c
    | Constraint (_, _, c) -> f c
    | Define (_, _, c) -> f c
    | I _ -> false
  in
  f c.Def.Clause.packing_ft


let relevant_predicate_clauses global name req =
  let open Global in
  let clauses =
    let defs = Sym.Map.bindings global.resource_predicates in
    List.concat_map
      (fun (nm, (def : Def.Predicate.t)) ->
        match def.clauses with
        | Some clauses -> List.map (fun c -> (nm, c)) clauses
        | None -> [])
      defs
  in
  List.filter (fun (nm, c) -> Sym.equal nm name || clause_has_resource req c) clauses


type state_extras =
  { request : Req.t option;
    unproven_constraint : LC.t option
  }

let no_ex = { request = None; unproven_constraint = None }

module ITSet = struct
  include Simplify.ITSet

  let rec bigunion_map f = function
    | [] -> empty
    | x :: xs -> union (f x) (bigunion_map f xs)
end

let subterms_without_bound_variables bindings =
  IT.fold_subterms
    ~bindings
    (fun bindings acc t ->
      let pats = List.map fst bindings in
      let bound = List.concat_map IT.bound_by_pattern pats in
      let bound = Sym.Set.of_list (List.map fst bound) in
      if Sym.Set.(is_empty (inter bound (IT.free_vars t))) then
        ITSet.add t acc
      else
        acc)
    ITSet.empty


(** Simplify a constraint in the context of a model. *)
let simp_constraint eval lct =
  let eval_to_bool it =
    match eval it with Some (IT.IT (Const (Bool b1), _, _)) -> Some b1 | _ -> None
  in
  let is b it = match eval_to_bool it with Some b1 -> Bool.equal b b1 | _ -> false in
  let rec go (IT.IT (term, bt, loc)) =
    let mk x = IT.IT (x, bt, loc) in
    let ands xs = IT.and_ xs loc in
    let go1 t = ands (go t) in
    match term with
    | Const (Bool true) -> []
    | Binop (Or, lhs, rhs) when is false lhs -> go rhs
    | Binop (Or, lhs, rhs) when is false rhs -> go lhs
    | Binop (And, lhs, rhs) -> List.append (go lhs) (go rhs)
    | Binop (Implies, lhs, rhs) ->
      (match eval_to_bool lhs with
       | Some b -> if b then go rhs else []
       | None -> [ mk (Binop (Implies, go1 lhs, go1 rhs)) ])
    | ITE (cond, ifT, ifF) ->
      (match eval_to_bool cond with
       | Some b -> if b then go ifT else go ifF
       | None -> [ mk (ITE (go1 cond, go1 ifT, go1 ifF)) ])
    | _ -> [ mk term ]
  in
  match lct with LC.Forall _ -> [ lct ] | LC.T ct -> List.map (fun x -> LC.T x) (go ct)


(** Simplify a resource clause in the context of a model. *)
let rec simp_resource eval r =
  match r with
  | LAT.Constraint (ct, info, more) ->
    let is_true =
      match ct with
      | LC.T ct ->
        (match eval ct with Some (IT.IT (Const (Bool b), _, _)) -> b | _ -> false)
      | _ -> false
    in
    if is_true then
      simp_resource eval more
    else
      LAT.Constraint (ct, info, simp_resource eval more)
  | LAT.Define (x, i, more) -> LAT.Define (x, i, simp_resource eval more)
  | LAT.Resource ((x, (rt, bt)), i, more) ->
    let rt1 = Interval.Solver.simp_rt eval rt in
    LAT.Resource ((x, (rt1, bt)), i, simp_resource eval more)
  | I i -> I i


let state (ctxt : C.t) log model_with_q extras =
  let where =
    let cur_colour = !Cerb_colour.do_colour in
    Cerb_colour.do_colour := false;
    let head_pos prfx loc =
      let head, pos = Loc.head_pos_of_location loc in
      (prfx ^ " " ^ head, pos)
    in
    let loc_cartesian, (loc_head, _loc_pos) =
      match (ctxt.where.statement, ctxt.where.expression) with
      | _, Some loc -> (Cerb_location.to_cartesian loc, head_pos "expr" loc)
      | Some loc, None -> (Cerb_location.to_cartesian loc, head_pos "stmt" loc)
      | None, None -> (None, ("", "\n"))
    in
    let fnction = Option.map Sym.pp_string ctxt.where.fnction in
    let section =
      Option.map (fun s -> Pp.plain (Where.pp_section s)) ctxt.where.section
    in
    let result = Report.{ fnction; section; loc_cartesian; loc_head } in
    Cerb_colour.do_colour := cur_colour;
    result
  in
  let model, quantifier_counter_model = model_with_q in
  let evaluate it = Solver.eval model it in
  (* let _mevaluate it = *)
  (*   match evaluate it with *)
  (*   | Some v -> IT.pp v *)
  (*   | None -> parens !^"not evaluated" *)
  (* in *)
  let render_constraints c =
    Rp.{ original = LC.pp c; simplified = List.map LC.pp (simp_constraint evaluate c) }
  in
  let render_sympair p =
    Rp.{ original = Sym.pp (fst p); simplified = [ Sym.pp (fst p) ] }
    (*Symbols do not need simplification*)
  in
  let interesting, uninteresting =
    List.partition
      (fun lc ->
        match lc with
        (* | LC.T (IT (Aligned _, _, _)) -> false *)
        | LC.T (IT (Representable _, _, _)) -> false
        | LC.T (IT (Good _, _, _)) -> false
        | _ -> true)
      (LC.Set.elements ctxt.constraints)
  in
  let not_given_to_solver =
    (* get predicates from past steps of trace not given to solver *)
    let log_preds =
      let log_comb acc entry =
        match entry with
        | State ctxt ->
          let _, _, ps = C.not_given_to_solver ctxt in
          List.append ps acc
        | Action _ -> acc
      in
      List.fold_left log_comb [] log
    in
    let forall_constraints, funs, ctxt_preds = C.not_given_to_solver ctxt in
    let preds =
      let pred_compare (s1, _) (s2, _) = Sym.compare s1 s2 in
      Base.List.dedup_and_sort (List.append log_preds ctxt_preds) ~compare:pred_compare
    in
    let interesting_constraints, uninteresting_constraints =
      List.partition LC.is_interesting forall_constraints
    in
    let interesting_funs, uninteresting_funs =
      List.partition (fun (_, v) -> LF.is_interesting v) funs
    in
    let interesting_preds, uninteresting_preds =
      List.partition (fun (_, v) -> Def.is_interesting v) preds
    in
    Rp.add_labeled
      Rp.lab_interesting
      (List.concat
         [ List.map render_sympair interesting_preds;
           List.map render_sympair interesting_funs;
           List.map render_constraints interesting_constraints
         ])
      (Rp.add_labeled
         Rp.lab_uninteresting
         (List.concat
            [ List.map render_sympair uninteresting_preds;
              List.map render_sympair uninteresting_funs;
              List.map render_constraints uninteresting_constraints
            ])
         Rp.labeled_empty)
  in
  let terms, vals =
    let variables =
      let make s ls = IT.sym_ (s, ls, Locations.other __LOC__) in
      let basetype_binding (s, (binding, _)) =
        match binding with C.Value _ -> None | BaseType ls -> Some (make s ls)
      in
      ITSet.of_list
        (List.map (fun (s, ls) -> make s ls) quantifier_counter_model
         @ List.filter_map basetype_binding (Sym.Map.bindings ctxt.computational)
         @ List.filter_map basetype_binding (Sym.Map.bindings ctxt.logical))
    in
    let unproven =
      match extras.unproven_constraint with
      | Some (T lc) -> subterms_without_bound_variables [] lc
      | Some (Forall ((s, bt), lc)) ->
        let binder = IT.(Pat (PSym s, bt, Loc.other __LOC__), None) in
        subterms_without_bound_variables [ binder ] lc
      | None -> ITSet.empty
    in
    let request =
      match extras.request with
      | Some (P ret) ->
        ITSet.bigunion_map (subterms_without_bound_variables []) (ret.pointer :: ret.iargs)
      | Some (Q ret) ->
        let binder = IT.(Pat (PSym (fst ret.q), snd ret.q, Loc.other __LOC__), None) in
        ITSet.union
          (ITSet.bigunion_map
             (subterms_without_bound_variables [])
             [ ret.pointer; ret.step ])
          (ITSet.bigunion_map
             (subterms_without_bound_variables [ binder ])
             (ret.permission :: ret.iargs))
      | None -> ITSet.empty
    in
    let subterms =
      List.fold_left ITSet.union ITSet.empty [ variables; unproven; request ]
    in
    let filtered =
      List.filter_map
        (fun it ->
          match evaluate it with
          | Some value when not (IT.equal value it) -> Some (it, value)
          | Some _ -> None
          | None -> None)
        (ITSet.elements subterms)
    in
    let pretty_printed =
      List.map
        (fun (it, value) -> (it, Rp.{ term = IT.pp it; value = IT.pp value }))
        filtered
    in
    let interesting, uninteresting =
      List.partition
        (fun (it, _entry) ->
          match IT.get_bt it with BT.Unit -> false | BT.Loc () -> false | _ -> true)
        pretty_printed
    in
    ( Rp.add_labeled
        Rp.lab_interesting
        (List.map snd interesting)
        (Rp.add_labeled
           Rp.lab_uninteresting
           (List.map snd uninteresting)
           Rp.labeled_empty),
      filtered )
  in
  let constraints =
    Rp.add_labeled
      Rp.lab_interesting
      (List.map render_constraints interesting)
      (Rp.add_labeled
         Rp.lab_uninteresting
         (List.map render_constraints uninteresting)
         Rp.labeled_empty)
  in
  let resources =
    let same_res, diff_res =
      match extras.request with
      | None -> ([], C.get_rs ctxt)
      | Some req -> List.partition (fun (r, _) -> Req.same_name req r) (C.get_rs ctxt)
    in
    let interesting_diff_res, uninteresting_diff_res =
      List.partition
        (fun (ret, _o) ->
          match ret with
          | Req.P ret when Req.equal_name ret.name Req.Predicate.alloc -> false
          | _ -> true)
        diff_res
    in
    let with_suff mb x = match mb with None -> x | Some d -> d ^^^ x in
    let pp_res mb_suff (rt, args) =
      Rp.
        { original = with_suff mb_suff (Res.pp (rt, args));
          simplified =
            [ with_suff mb_suff (Res.pp (Interval.Solver.simp_rt evaluate rt, args)) ]
        }
    in
    let interesting =
      List.map (fun re -> pp_res (Some (parens !^"same type")) re) same_res
      @ List.map (pp_res None) interesting_diff_res
    in
    let uninteresting = List.map (pp_res None) uninteresting_diff_res in
    Rp.add_labeled
      Rp.lab_interesting
      interesting
      (Rp.add_labeled Rp.lab_uninteresting uninteresting Rp.labeled_empty)
  in
  let invalid_resources =
    let g = ctxt.global in
    let defs = g.resource_predicates in
    let check (rt, o) =
      match (rt, o) with
      | Req.Q _, _ -> None
      | Req.P { name = Owned _; pointer = _; iargs = _ }, _ -> None
      | Req.P { name = PName s; pointer = _; iargs }, Resource.O it ->
        (match (Sym.Map.find_opt s defs, evaluate it) with
         | Some def, Some cand ->
           let here = Locations.other __LOC__ in
           let ptr_val = Req.get_pointer rt in
           let ptr_def =
             (IT.sym_ (def.pointer, IT.get_bt ptr_val, here), ptr_val)
           in
           Some (CheckPreds.check_pred s def cand ctxt iargs (ptr_def :: vals), rt, it)
         | Some _, None ->
           Some (Error (!^"Could not locate definition of variable" ^^^ IT.pp it), rt, it)
         | None, _ ->
           Some (Error (!^"Could not locate definition of predicate" ^^^ Sym.pp s), rt, it))
    in
    let checked = List.filter_map check (C.get_rs ctxt) in
    let nos, _ = List.partition (fun (r, _, _) -> ResultWithData.is_no r) checked in
    (* let yeses, unknown = List.partition (fun (r, _, _) -> is_yes r) rest in *)
    let pp_checked_res (p, req, cand) =
      let _ = p in
      let rslt = Req.pp req ^^^ !^"(" ^^^ IT.pp cand ^^^ !^")" in
      Rp.
        { original = rslt;
          (*original = ^^^ !^"\n"^^^ LAT.pp_check_result p; *)
          simplified = [ rslt ]
        }
    in
    Rp.add_labeled Rp.lab_invalid (List.map pp_checked_res nos) Rp.labeled_empty
    (* Currently only displays invalid predicates *)
    (* (Rp.add_labeled
       Rp.lab_unknown
       (List.map pp_checked_res unknown)
       (Rp.add_labeled Rp.lab_valid (List.map pp_checked_res yeses) Rp.labeled_empty)) *)
  in
  Rp.{ where; invalid_resources; not_given_to_solver; terms; resources; constraints }


let trace (ctxt, log) (model_with_q : Solver.model_with_q) (extras : state_extras) =
  let prev = !Pp.html_escapes in
  Pp.html_escapes := true;
  (* let req_cmp = Option.bind extras.request (Spans.spans_compare_for_pp model
     ctxt.global) in *)
  (* let req_entry req_cmp req = { *)
  (*     res = Req.pp req; *)
  (*     res_span = Spans.pp_model_spans model ctxt.global req_cmp req *)
  (*   } *)
  (* in *)
  (* let res_entry req_cmp same res = { *)
  (*     res = Res.pp res; *)
  (*     res_span = Spans.pp_model_spans model ctxt.global req_cmp (Res.request res) *)
  (*       ^^ (if same then !^" - same-type" else !^"") *)
  (*   } *)
  (* in *)
  let req_entry ret = Req.pp ret in
  let trace =
    let statef ctxt = state ctxt log model_with_q extras in
    List.rev
      (statef ctxt
       :: List.filter_map (function State ctxt -> Some (statef ctxt) | _ -> None) log)
  in
  let model, _quantifier_counter_model = model_with_q in
  let evaluate it = Solver.eval model it in
  let predicate_hints =
    match extras.request with
    | None -> []
    | Some req ->
      (match Req.get_name req with
       | Owned _ -> []
       | PName pname ->
         let doc_clause (_name, (c : Def.Clause.t)) =
           Rp.
             { cond = IT.pp c.guard;
               clause =
                 LogicalArgumentTypes.pp IT.pp (simp_resource evaluate c.packing_ft)
             }
         in
         List.map doc_clause (relevant_predicate_clauses ctxt.global pname req))
  in
  let requested = Option.map req_entry extras.request in
  let unproven =
    match extras.unproven_constraint with
    | Some lc ->
      let lc_simp = Simplify.LogicalConstraints.simp (Simplify.default ctxt.global) lc in
      Some (LC.pp lc_simp)
    | None -> None
  in
  Pp.html_escapes := prev;
  Rp.{ requested; unproven; predicate_hints; trace }
