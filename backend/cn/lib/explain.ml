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
open Option

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


(** CHT: Infrastructure for checking if a countermodel satisfies a predicate **)

type ('a, 'b) result =
| Yes of 'a
| No
| Unknown of 'b
| Error of 'b

let is_no r = match r with No -> true | _ -> false

let is_yes r = match r with Yes _ -> true | _ -> false

type check_result = (LC.logical_constraint list, Pp.document) result

let filter_map_some (f : 'a -> 'b option) (l : 'a list) : 'b list =
  List.fold_left (fun acc elem -> match f elem with None -> acc | Some x -> x :: acc) [] l

(* Condenses list into "No" or a list of successes/timeouts/errors *)
let condense_results (results : check_result list) :
  check_result list =
  let filtered = List.filter (fun r -> r != No) results in
  if filtered == [] then [No] else filtered

(* Gives a single canonical result *)
let combine_results (results : check_result list)
  : check_result =
  match results with
  | [] -> Error !^"Empty result list"
  | h :: t ->
    let combine = fun acc res -> match acc, res with
      | Yes l, _ -> Yes l
      | _, Yes l -> Yes l
      | Error s, _ -> Error s
      | _, Error s -> Error s
      | Unknown s, _ -> Unknown s
      | _, Unknown s -> Unknown s
      | No, _ -> No
    in
    List.fold_left combine h t

let ask_solver g lcs = match (Solver.ask_solver g lcs) with
| Unsat -> No
| Unknown -> Unknown !^"Solver returned Unknown."
| Sat -> Yes lcs

let convert_symmap_to_lc (m : IT.t SymMap.t) : LogicalConstraints.t list =
  let kvs = SymMap.bindings m in
  let to_lc (k, v) =
    LC.T (IT.eq_ (IT.IT (IT.Sym k, basetype v, Cerb_location.unknown) , v) Cerb_location.unknown) in
  List.map to_lc kvs

let rec check_clause (g : Global.t) (c : ResourcePredicates.clause) (candidate : IT.t) =
  (*get variable dependency graph*)
  let graph = LAT.to_tree c.packing_ft in
  (*get constraints on whether candidate could have come from this clause*)
  let cs, vs = (getClauseConstraints graph candidate g) in
  let cs' = List.concat [cs; convert_symmap_to_lc vs; [LC.t_ c.guard]] in
  (*query solver*)
  ask_solver g cs'

and check_pred
  (def : ResourcePredicates.definition) (candidate : IT.t) (g : Global.t) : check_result list =
  (* ensure candidate type matches output type of predicate *)
  if (not (BT.equal (IT.basetype candidate) (def.oarg_bt)))
  then
    [Error (!^"Candidate " ^/^ IT.pp candidate ^/^ !^" has different type from
      predicate output: " ^/^ BT.pp (IT.basetype candidate) ^/^  !^" versus " ^/^ BT.pp def.oarg_bt ^/^ !^".")]
  else
    match def.clauses with
    | None -> [Unknown (!^"Predicate " ^/^ ResourcePredicates.pp_definition def ^/^ !^" is uninterpreted. ")]
    | Some clauses ->
        (* for each clause, check if candidate could have been its output *)
        let checked = List.map (fun c -> check_clause g c candidate) clauses
        in
        (* return either [No] or a list of positive/ambiguous results *)
        condense_results checked

and getClauseConstraints graph candidate globals =
  (*"false" constraint*)
  let default = ([LC.T (IT (Const (Bool false), BT.Bool, Cerb_location.unknown))], SymMap.empty) in
  match graph with
  | (exp, subgraphs) ->
    (* use candidate to get terms for FVs in exp. This may fail for valid expressions *)
    let ovs_ = LAT.get_assignment exp candidate in
    match ovs_ with
    | None -> failwith "Unknown"
    | Some vs_ ->
    (*CHT TODO: stateful*)
    (*CHT TODO: shortcut - guard could be var equality*)
    (* find definition of x, and for each fv in its def, recurse *)
    let foreachvar x' vs = match (SymMap.find_opt x' subgraphs) with
    | None -> failwith "CHT - could be known in ctxt? out of scope for now"
    | Some UndefinedLT -> failwith "CHT style - impossible"
    | Some (NodeLT (line, subgraphs')) -> match line with
      | DefineL ((x, t), _) ->
        (match (SymMap.find_opt x vs) with
        | None -> failwith "CHT style - impossible case, just rearrange"
        | Some v -> getClauseConstraints (t, subgraphs') v globals
        )
      | ResourceL ((x, (p, _)), _) ->
        (match (SymMap.find_opt x vs) with
        | None -> failwith "CHT style - impossible"
        | Some v -> match p with
          | P psig ->
            (match psig.name with
            | Owned (_, _) ->
              let neq = IT.ne__ psig.pointer (IT.null_ Cerb_location.unknown) Cerb_location.unknown in
                ([LC.t_ neq], vs)
            | PName name -> let opdef = SymMap.find_opt name globals.resource_predicates in
              match opdef with
              | Some pdef ->
                (*CHT TODO: this doesn't account for looking up args of the predicate further up in the graph*)
                (match combine_results (check_pred pdef v globals) with
                | Yes cs -> (cs, vs)
                | _ -> default (*CHT style - should separate checking and getting constraints*))
              | None -> default
            )
          | Q qsig -> let _ = qsig in failwith "CHT - quantified predicates are out of scope for now"
        )
      | ConstraintL (c, _) -> let _ = c in failwith "CHT - asserts are out of scope for now"
      in
    let comb (acc : LC.logical_constraint list * IT.t SymMap.t) (elem : Sym.t * IT.t) =
      let lcs, vs = acc in
      let k, _ = elem in
      let lcs', vs' = foreachvar k vs in
      (List.append lcs' lcs, vs') in
    List.fold_left comb ([], vs_) (SymMap.bindings vs_)

let rec getBodyConstraints (ctxt : Context.t) (lines : IT.t LAT.t) : IT.t =
  let loc = Cerb_location.unknown in
  match lines with
  | Define ((v, it), _, next) -> failwith "need bt for v"
  | Resource ((v, (rt, bt)), _, next)-> failwith "Main issue: need to be able to check that whatever value we give v works for rt"
  | Constraint (lc, _, next) -> (match lc with
    | T it -> and_ [it; getBodyConstraints ctxt next] loc
    | Forall _ -> failwith ""
    )
  | I it -> failwith ""

let getClauseConstraints' (ctxt : Context.t) (cl : REP.clause) : IT.t =
  IT.and_ [cl.guard; getBodyConstraints ctxt cl.packing_ft] Cerb_location.unknown

let checkPredNaive (ctxt : Context.t) (def : REP.definition) (candidate : IT.t) : check_result =
  let loc = Cerb_location.unknown in
  match def.clauses with
  | None -> Unknown (!^"Predicate " ^/^ ResourcePredicates.pp_definition def ^/^ !^" is uninterpreted.")
  | Some cls ->
    let cand_eq (cl : REP.clause) = IT.eq__ (LAT.get_return cl.packing_ft) candidate loc in
    let with_cand_eq (cl : REP.clause)  = LC.T (IT.and_ [getClauseConstraints' ctxt cl; cand_eq cl] loc) in
    let check_cl (cl : REP.clause)  = ask_solver ctxt.global [with_cand_eq cl] in
    combine_results (List.map check_cl cls)

(* End CHT *)

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
      match predicate_name rt with
      | Owned _ -> None
      | PName s ->
        match (SymMap.find_opt s defs), o with
        | Some def, O it -> Some (combine_results (check_pred def it g))
        | None, _ -> Some (Error (!^"Could not locate definition of predicate " ^/^ Sym.pp s))
        in
    let checked =
      let f r = match check r with
      | None -> None
      | Some res -> Some (r, res) in
      filter_map_some f (get_rs ctxt) in
    let (nos, rest) = List.partition (fun p -> is_no (snd p)) checked in
    let (yeses, unknown) = List.partition (fun p -> is_yes (snd p)) rest in
    add_labeled
      lab_invalid
      (List.map (fun r -> pp_res None (fst r)) nos)
      (add_labeled lab_unknown (List.map (fun r -> pp_res None (fst r)) unknown)
        (add_labeled lab_valid (List.map (fun r -> pp_res None (fst r)) yeses)
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
      (*CHT TODO: deriving this would require changing a lot of files *)
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
