open Report
module IT = IndexTerms
module BT = BaseTypes
module RE = Resources
module REP = ResourcePredicates
module RET = ResourceTypes
module LC = LogicalConstraints
module LF = LogicalFunctions
module LAT = LogicalArgumentTypes
module LS = LogicalSorts
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)
module StringMap = Map.Make (String)
module C = Context
module Loc = Locations
module S = Solver
open ResourceTypes
open IndexTerms
open Pp
open C
open Resources

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
open ResultWithData

(* ask the solver if the given set of constraints is satisfiable *)
let ask_solver g lcs = match (Solver.ask_solver g lcs) with
| Unsat -> No !^"Solver returned No."
| Unknown -> Unknown !^"Solver returned Unknown."
| Sat -> Yes lcs

(* convert a list of variable assignments to equality constraints *)
let convert_symmap_to_lc (m : IT.t SymMap.t) : LogicalConstraints.t list =
  let loc = Cerb_location.unknown in
  let kvs = SymMap.bindings m in
  let to_lc (k, v) =
    LC.T (IT.eq_ (IT.IT (IT.Sym k, basetype v, loc) , v) loc) in
  List.map to_lc kvs

(* check if a candidate term could have been the output of a given predicate *)
let rec check_pred (name : Sym.t) (def : ResourcePredicates.definition) (candidate : IT.t) (ctxt : C.t) : LAT.check_result =
  (* ensure candidate type matches output type of predicate *)
  if (not (BT.equal (IT.basetype candidate) (def.oarg_bt)))
  then
    No (!^"Candidate" ^^^ IT.pp candidate ^^^ !^"has different type from
      predicate output:" ^^^ BT.pp (IT.basetype candidate) ^^^  !^" versus" ^^^ BT.pp def.oarg_bt ^^^ !^".")
  else
    match def.clauses with
    | None -> Unknown (!^"Predicate" ^^^ Sym.pp name ^^^ !^"is uninterpreted. ")
    | Some clauses ->
        let clauses_with_guards = REP.explicit_negative_guards clauses in
        (* for each clause, check if candidate could have been its output *)
        let checked = List.map (fun c -> check_clause c candidate  ctxt def.iargs) clauses_with_guards
        in
        LAT.combine_results checked

(* check if a candidate term could have been the output of a predicate clause *)
and check_clause (c : ResourcePredicates.clause) (candidate : IT.t) (ctxt : C.t)  (iargs : (Sym.t * BT.t) list) =
  (* get returned expression of c and variable dependency graph *)
  let exp, var_def_locs, lcs = LAT.organize_lines c.packing_ft in
  (* get constraints on whether candidate could have come from this clause *)
  let@ (cs, vs) = get_body_constraints exp var_def_locs candidate ctxt iargs in
  (* add guard and variable assignments to constraints list *)
  let cs' = List.concat [lcs; cs; convert_symmap_to_lc vs; [LC.t_ c.guard]] in
  (* query solver *)
  ask_solver ctxt.global cs'

(* get a list of constraints that are satisfiable iff candidate could have come from this clause body *)
and get_body_constraints (exp : IT.t) (var_def_locs : LAT.def_line SymMap.t) (candidate : IT.t) (ctxt : C.t) (iargs : (Sym.t * BT.t) list) =
  (* use candidate to get terms for FVs in exp *)
  let@ var_cands = LAT.get_var_cands exp candidate in
  (* find constraints from checking each variable one at a time*)
  let accumulate_results acc (v, v_cand) =
    let@ (acc_lcs, acc_var_cands) = acc in
    let@ (v_lcs, v_var_cands) = get_var_constraints v v_cand acc_var_cands var_def_locs ctxt iargs in
    Yes (List.append v_lcs acc_lcs, v_var_cands)
  in
  List.fold_left accumulate_results (Yes ([], var_cands)) (SymMap.bindings var_cands)

and get_var_constraints (v : Sym.t) (v_cand : IT.t) (var_cands : IT.t SymMap.t) (var_def_locs : LAT.def_line SymMap.t) (ctxt : C.t) (iargs : (Sym.t * BT.t) list)=
  let loc = Cerb_location.unknown in
  match (SymMap.find_opt v var_def_locs) with
  | None -> (match (SymMap.find_opt v ctxt.logical, SymMap.find_opt v ctxt.computational) with
    | (Some (Value it, _), _) -> get_body_constraints it var_def_locs v_cand ctxt iargs
    | (_, Some (Value it, _)) -> get_body_constraints it var_def_locs v_cand ctxt iargs
    (* TODO: logical vs computational *)
    (* TODO: BaseType case? *)
    | _ -> (let f = fun (s, _) -> Sym.equal s v in
      if (Base.List.exists iargs ~f)
      then Yes ([], var_cands)
      else Unknown (!^"Could not find variable definition line for" ^^^ (Sym.pp v))))
  | Some line ->
    match line with
      (* recurse with x's definition *)
    | DefineL ((_, t), _) -> get_body_constraints t var_def_locs v_cand ctxt iargs (*TODO: variable conflicts?*)
    | ResourceL ((_, (p, _)), _) ->
      match p with
      | P psig -> (match psig.name with
        | Owned (_, _) ->
          (* if the predicate is Owned, its pointer argument should not be null *)
          let neq = IT.ne__ psig.pointer (IT.null_ loc) loc in
          Yes ([LC.t_ neq], var_cands)
        | PName name ->
          (* search for predicate definition *)
          match SymMap.find_opt name ctxt.global.resource_predicates with
          | Some pdef ->
            (* TODO: this doesn't account for looking up args of the predicate further up in the graph.
                Adding that will require dealing with scoping issues, e.g. if
                a candidate or line definition for one of the arguments includes a variable with a
                different usage within the predicate *)
            (match check_pred name pdef v_cand ctxt with
            | Yes cs -> Yes (cs, var_cands)
            | No e -> No e
            | Unknown e -> Unknown e
            | Error e -> Error e)
          | None -> Unknown (!^"Could not find definition of predicate" ^^^ Sym.pp name)
        )
      | Q qsig -> let _ = qsig in Unknown (!^"Quantified predicates are out of scope for now.")

(** End section: Infrastructure for checking if a countermodel satisfies a predicate **)

let clause_has_resource req c =
  let open LogicalArgumentTypes in
  let rec f = function
    | Resource ((_, (r, _)), _, c) -> RET.same_predicate_name req r || f c
    | Constraint (_, _, c) -> f c
    | Define (_, _, c) -> f c
    | I _ -> false
  in
  let open ResourcePredicates in
  f c.packing_ft


let relevant_predicate_clauses global name req =
  let open Global in
  let open ResourcePredicates in
  let clauses =
    let defs = SymMap.bindings global.resource_predicates in
    List.concat_map
      (fun (nm, def) ->
        match def.clauses with
        | Some clauses -> List.map (fun c -> (nm, c)) clauses
        | None -> [])
      defs
  in
  List.filter (fun (nm, c) -> Sym.equal nm name || clause_has_resource req c) clauses


type state_extras =
  { request : RET.t option;
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
  fold_subterms
    ~bindings
    (fun bindings acc t ->
      let pats = List.map fst bindings in
      let bound = List.concat_map bound_by_pattern pats in
      let bound = SymSet.of_list (List.map fst bound) in
      if SymSet.(is_empty (inter bound (IT.free_vars t))) then
        ITSet.add t acc
      else
        acc)
    ITSet.empty


(** Simplify a constraint in the context of a model. *)
let simp_constraint eval lct =
  let eval_to_bool it =
    match eval it with Some (IT (Const (Bool b1), _, _)) -> Some b1 | _ -> None
  in
  let is b it = match eval_to_bool it with Some b1 -> Bool.equal b b1 | _ -> false in
  let rec go (IT (term, bt, loc)) =
    let mk x = IT (x, bt, loc) in
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
        (match eval ct with Some (IT (Const (Bool b), _, _)) -> b | _ -> false)
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


let state ctxt log model_with_q extras =
  let model, quantifier_counter_model = model_with_q in
  let evaluate it = Solver.eval ctxt.global model it in
  let with_suff mb x = match mb with None -> x | Some d -> d ^^^ x in
  let pp_res mb_suff (rt, args) =
    { original = with_suff mb_suff (RE.pp (rt, args));
      simplified =
        [ with_suff mb_suff (RE.pp (Interval.Solver.simp_rt evaluate rt, args)) ]
    }
  in
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
  (* let _mevaluate it = *)
  (*   match evaluate it with *)
  (*   | Some v -> IT.pp v *)
  (*   | None -> parens !^"not evaluated" *)
  (* in *)
  let render_constraints c =
    { original = LC.pp c; simplified = List.map LC.pp (simp_constraint evaluate c) }
  in
  let render_sympair p =
    { original = Sym.pp (fst p); simplified = [ Sym.pp (fst p) ] }
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
      (LCSet.elements ctxt.constraints)
  in
  let invalid_resources =
    let g = ctxt.global in
    let defs = g.resource_predicates in
    let check (rt, o) =
      match predicate_name rt, o with
      | Owned _, _ -> None
      | PName s, O it ->
        match (SymMap.find_opt s defs), evaluate it with
        | Some def, Some cand -> Some (check_pred s def cand ctxt)
        | Some _, None -> Some (Error (!^"Could not locate definition of variable" ^^^ IT.pp it))
        | None, _ -> Some (Error (!^"Could not locate definition of predicate" ^^^ Sym.pp s))
        in
    let checked =
      let f r = match check r with
      | None -> None
      | Some res -> Some (r, res) in
      LAT.filter_map_some f (get_rs ctxt) in
    let (nos, rest) = List.partition (fun p -> is_no (snd p)) checked in
    let (yeses, unknown) = List.partition (fun p -> is_yes (snd p)) rest in
    let pp_checked_res (p : resource * (LC.logical_constraint list, document) result_with_data) =
      let r = fst p in
      { original =  LAT.pp_check_result (snd p) ;
        simplified = [RE.pp r] } in
      (* {original = LAT.pp_check_result (snd r); simplified= [LAT.pp_check_result (snd r)]} in *)
    add_labeled
      lab_invalid
      (List.map pp_checked_res nos)
      (add_labeled lab_unknown (List.map pp_checked_res unknown)
        (add_labeled lab_valid (List.map pp_checked_res yeses)
          labeled_empty))
      in
  let not_given_to_solver =
    (* get predicates from past steps of trace not given to solver *)
    let log_preds =
      let log_comb acc entry =
        match entry with
        | State ctxt ->
          let _, _, ps = not_given_to_solver ctxt in
          List.append ps acc
        | Action _ -> acc
      in
      List.fold_left log_comb [] log
    in
    let forall_constraints, funs, ctxt_preds = not_given_to_solver ctxt in
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
      List.partition (fun (_, v) -> REP.is_interesting v) preds
    in
    add_labeled
      lab_interesting
      (List.concat
         [ List.map render_sympair interesting_preds;
           List.map render_sympair interesting_funs;
           List.map render_constraints interesting_constraints
         ])
      (add_labeled
         lab_uninteresting
         (List.concat
            [ List.map render_sympair uninteresting_preds;
              List.map render_sympair uninteresting_funs;
              List.map render_constraints uninteresting_constraints
            ])
         labeled_empty)
  in
  let terms =
    let variables =
      let make s ls = sym_ (s, ls, Locations.other __FUNCTION__) in
      let basetype_binding (s, (binding, _)) =
        match binding with Value _ -> None | BaseType ls -> Some (make s ls)
      in
      ITSet.of_list
        (List.map (fun (s, ls) -> make s ls) quantifier_counter_model
         @ List.filter_map basetype_binding (SymMap.bindings ctxt.computational)
         @ List.filter_map basetype_binding (SymMap.bindings ctxt.logical))
    in
    let unproven =
      match extras.unproven_constraint with
      | Some (T lc) -> subterms_without_bound_variables [] lc
      | Some (Forall ((s, bt), lc)) ->
        let binder = (Pat (PSym s, bt, Loc.other __FUNCTION__), None) in
        subterms_without_bound_variables [ binder ] lc
      | None -> ITSet.empty
    in
    let request =
      match extras.request with
      | Some (P ret) ->
        ITSet.bigunion_map (subterms_without_bound_variables []) (ret.pointer :: ret.iargs)
      | Some (Q ret) ->
        let binder = (Pat (PSym (fst ret.q), snd ret.q, Loc.other __FUNCTION__), None) in
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
          | Some value when not (IT.equal value it) ->
            Some (it, { term = IT.pp it; value = IT.pp value })
          | Some _ -> None
          | None -> None)
        (ITSet.elements subterms)
    in
    let interesting, uninteresting =
      List.partition
        (fun (it, _entry) ->
          match IT.bt it with BT.Unit -> false | BT.Loc () -> false | _ -> true)
        filtered
    in
    add_labeled
      lab_interesting
      (List.map snd interesting)
      (add_labeled lab_uninteresting (List.map snd uninteresting) labeled_empty)
  in
  let constraints =
    add_labeled
      lab_interesting
      (List.map render_constraints interesting)
      (add_labeled
         lab_uninteresting
         (List.map render_constraints uninteresting)
         labeled_empty)
  in
  let resources =
    let same_res, diff_res =
      match extras.request with
      | None -> ([], get_rs ctxt)
      | Some req ->
        List.partition (fun r -> RET.same_predicate_name req (RE.request r)) (get_rs ctxt)
    in
    let interesting_diff_res, uninteresting_diff_res =
      List.partition
        (fun (ret, _o) ->
          match ret with
          | P ret when equal_predicate_name ret.name ResourceTypes.alloc -> false
          | _ -> true)
        diff_res
    in
    let interesting =
      List.map (fun re -> pp_res (Some (parens !^"same type")) re) same_res
      @ List.map (pp_res None) interesting_diff_res
    in
    let uninteresting = List.map (pp_res None) uninteresting_diff_res in
    add_labeled
      lab_interesting
      interesting
      (add_labeled lab_uninteresting uninteresting labeled_empty)
  in
  { where; invalid_resources; not_given_to_solver; terms; resources; constraints }


let trace (ctxt, log) (model_with_q : Solver.model_with_q) (extras : state_extras) =
  let prev = !Pp.html_escapes in
  Pp.html_escapes := true;
  (* let req_cmp = Option.bind extras.request (Spans.spans_compare_for_pp model
     ctxt.global) in *)
  (* let req_entry req_cmp req = { *)
  (*     res = RET.pp req; *)
  (*     res_span = Spans.pp_model_spans model ctxt.global req_cmp req *)
  (*   } *)
  (* in *)
  (* let res_entry req_cmp same res = { *)
  (*     res = RE.pp res; *)
  (*     res_span = Spans.pp_model_spans model ctxt.global req_cmp (RE.request res) *)
  (*       ^^ (if same then !^" - same-type" else !^"") *)
  (*   } *)
  (* in *)
  let req_entry ret = RET.pp ret in
  let trace =
    let statef ctxt = state ctxt log model_with_q extras in
    List.rev
      (statef ctxt
       :: List.filter_map (function State ctxt -> Some (statef ctxt) | _ -> None) log)
  in
  let model, _quantifier_counter_model = model_with_q in
  let evaluate it = Solver.eval ctxt.global model it in
  let predicate_hints =
    match extras.request with
    | None -> []
    | Some req ->
      let open ResourcePredicates in
      (match predicate_name req with
       | Owned _ -> []
       | PName pname ->
         let doc_clause (_name, c) =
           { cond = IT.pp c.guard;
             clause = LogicalArgumentTypes.pp IT.pp (simp_resource evaluate c.packing_ft)
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
  { requested; unproven; predicate_hints; trace }
