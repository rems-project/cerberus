open Report
module IT = IndexTerms
module BT = BaseTypes
module RE = Resources
module RET = ResourceTypes
module LC = LogicalConstraints
module LS = LogicalSorts
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module StringMap = Map.Make(String)
module SymPairMap = Map.Make(SymRel.SymPair)
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

type log = log_entry list       (* most recent first *)




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
    List.concat_map (fun (nm, def) ->
        match def.clauses with
        | Some clauses -> List.map (fun c -> (nm, c)) clauses
        | None -> []
      ) defs
  in
  List.filter (fun (nm, c) -> 
      Sym.equal nm name
      || clause_has_resource req c
    ) clauses

type state_extras = {
    request : RET.t option;
    unproven_constraint : LC.t option;
  }

let no_ex = {request = None; unproven_constraint = None}


let state ctxt model_with_q extras = 

  let where = 
    let cur_colour = !Cerb_colour.do_colour in
    Cerb_colour.do_colour := false;
    let head_pos prfx loc = 
      let head,pos = Loc.head_pos_of_location loc in
      ((prfx^" "^head), pos)
    in
    let loc_head, loc_pos = 
      match ctxt.where.statement, ctxt.where.expression with
      | _, Some loc -> head_pos "expr" loc
      | Some loc, None -> head_pos "stmt" loc
      | None, None -> "", "\n"
    in
    let fnction = match ctxt.where.fnction with
      | None -> "(none)"
      | Some sym -> Sym.pp_string sym
    in
    let section = match ctxt.where.section with
      | None -> "(none)"
      | Some s -> Pp.plain (Where.pp_section s)
    in
    let result = Report.{ fnction; section; loc_head; loc_pos; } in
    Cerb_colour.do_colour := cur_colour;
    result
  in

  let model, quantifier_counter_model = model_with_q in

  let evaluate it = Solver.eval ctxt.global model it in

  let mevaluate it =
    match evaluate it with
    | Some v -> IT.pp v
    | None -> parens !^"not evaluated"
  in

  let variables =
    let make s ls =
      {term = Sym.pp s;
       value = mevaluate (sym_ (s, ls, Locations.other __FUNCTION__))}
    in
    let make_basetype_binding (s, (binding, _)) = 
      match binding with 
      | Value _ -> None 
      | BaseType ls -> Some (make s ls)
    in
    List.map (fun (s, ls) -> make s ls) quantifier_counter_model @
    List.filter_map make_basetype_binding (SymMap.bindings ctxt.computational) @
    List.filter_map make_basetype_binding (SymMap.bindings ctxt.logical)
  in

  let terms = 
    let subterms1 = match extras.unproven_constraint with
      | Some (T lc) -> 
         IT.subterms_without_bound_variables [] lc
      | Some (Forall ((s,bt), lc)) ->
         let binder = (Pat (PSym s, bt, Loc.other __FUNCTION__), None) in
         IT.subterms_without_bound_variables [binder] lc
      | None -> 
         []
    in
    let subterms2 = match extras.request with
      | Some (P ret) ->
         List.concat_map (IT.subterms_without_bound_variables []) 
           (ret.pointer :: ret.iargs)
      | Some (Q ret) ->
         List.concat_map (IT.subterms_without_bound_variables [])
           [ret.pointer; ret.step]
         @ 
         (let binder = (Pat (PSym (fst ret.q), snd ret.q, Loc.other __FUNCTION__), None) in
          List.concat_map (IT.subterms_without_bound_variables [binder])
           (ret.permission :: ret.iargs))
      | None -> 
         []
    in
    let subterms = 
      List.map (fun it -> 
          {term = IT.pp it; value = mevaluate it}
        (* deduplicate *)
        ) (Simplify.ITSet.(elements (of_list (subterms1 @ subterms2))))
    in
    variables @ subterms
  in

  let constraints = List.map LC.pp (LCSet.elements ctxt.constraints) in

  let resources =
    let (same_res, diff_res) = match extras.request with
      | None -> ([], get_rs ctxt)
      | Some req -> List.partition (fun r -> RET.same_predicate_name req (RE.request r)) (get_rs ctxt)
    in
    List.map (fun re -> RE.pp re ^^^ parens !^"same type") same_res 
    @ List.map RE.pp diff_res
  in

  { where;
    terms;
    resources;
    constraints }



let trace (ctxt,log) (model_with_q : Solver.model_with_q) (extras : state_extras) =

  let prev = ! Pp.html_escapes in
  Pp.html_escapes := true;


  (* let req_cmp = Option.bind extras.request (Spans.spans_compare_for_pp model ctxt.global) in *)
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
    let statef ctxt = state ctxt model_with_q extras in
    List.rev (statef ctxt :: List.filter_map (function State ctxt -> Some (statef ctxt) | _ -> None) log)
  in


  let predicate_hints = match extras.request with
    | None -> []
    | Some req ->
       let open ResourcePredicates in
       match predicate_name req with
       | Owned _ -> []
       | PName pname ->
          let doc_clause (nm, c) = {
              cond = IT.pp c.guard;
              clause = LogicalArgumentTypes.pp IT.pp c.packing_ft
            }
          in
          List.map doc_clause (relevant_predicate_clauses ctxt.global pname req)
  in
  let requested = Option.map req_entry extras.request in
  let pp_with_simp lc = 
    let lc_simp = Simplify.LogicalConstraints.simp (Simplify.default ctxt.global) lc in 
    (LC.pp lc, LC.pp lc_simp)
  in
  let unproven = Option.map pp_with_simp extras.unproven_constraint in

    

  Pp.html_escapes := prev;


  { requested;
    unproven;
    predicate_hints;
    trace }







