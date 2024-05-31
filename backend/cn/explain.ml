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

let relevant_predicate_clauses global oname req =
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
  List.filter (fun (nm, c) -> Option.equal Sym.equal (Some nm) oname
    || clause_has_resource req c) clauses

type state_extras = {
    request : RET.t option;
    unproven_constraint : LC.t option;
  }

let no_ex = {request = None; unproven_constraint = None}

let state ctxt (model_with_q : Solver.model_with_q) (extras : state_extras) =

  let prev = ! Pp.html_escapes in
  Pp.html_escapes := true;

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
    List.map (fun (s, ls) -> make s ls) quantifier_counter_model @
    List.filter_map (fun (s, (binding, _)) -> match binding with Value _ -> None | BaseType ls -> Some (make s ls)) (SymMap.bindings ctxt.computational) @
    List.filter_map (fun (s, (binding, _)) -> match binding with Value _ -> None | BaseType ls -> Some (make s ls)) (SymMap.bindings ctxt.logical)
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

  let req_cmp = Option.bind extras.request (Spans.spans_compare_for_pp model ctxt.global) in
  let req_entry req_cmp req = {
      res = RET.pp req;
      res_span = Spans.pp_model_spans model ctxt.global req_cmp req
    }
  in
  let res_entry req_cmp same res = {
      res = RE.pp res;
      res_span = Spans.pp_model_spans model ctxt.global req_cmp (RE.request res)
        ^^ (if same then !^" - same-type" else !^"")
    }
  in
(*
  begin match extras.request with
    | None -> ()
    | Some req -> Spans.diag_req (get_rs ctxt) req model ctxt.global
  end;*)


  let resources =
    let (same_res, diff_res) = match extras.request with
      | None -> ([], get_rs ctxt)
      | Some req -> List.partition (fun r -> RET.same_predicate_name req (RE.request r)) (get_rs ctxt)
    in
    List.map (res_entry req_cmp true) same_res @ List.map (res_entry req_cmp false) diff_res
  in

  let predicate_hints =
    let predicate_name = match Option.map predicate_name extras.request with
      | Some (PName sym) -> Some sym
      | _ -> None
    in
    let predicate_clauses = match extras.request with
      | None -> []
      | Some req -> relevant_predicate_clauses ctxt.global predicate_name req
    in
    let doc_clause (nm, c) =
      let open ResourcePredicates in
      {
        cond = IT.pp c.guard;
        clause = LogicalArgumentTypes.pp IT.pp c.packing_ft
      }
    in
    List.map doc_clause predicate_clauses
  in
  let requested = Option.map (req_entry None) extras.request in
  let pp_with_simp lc = 
    let lc_simp = Simplify.LogicalConstraints.simp (Simplify.default ctxt.global) lc in 
    (LC.pp lc, LC.pp lc_simp)
  in
  let unproven = Option.map pp_with_simp extras.unproven_constraint in

  let trace = 
    (*copying from above*)
    let print_location loc = Pp.string (Locations.to_string loc) in
    let print_label = function
      | None -> !^"function body"
      | Some (loc, label_kind) -> 
          let open CF.Annot in
          let prefix = match label_kind with
            | LAreturn -> "return"
            | LAloop_break _ -> "break"
            | LAloop_continue _ -> "loop continue"
            | LAloop_body _ -> "loop body"
            | LAloop_prebody _ -> "pre-loop condition"
            | LAactual_label -> "label"
            | LAswitch -> "switch"
            | LAcase -> "case"
            | LAdefault -> "default"
          in
          !^prefix ^^ colon ^^^ (print_location loc)
    in

    
    let print_trace_item (i, loc) = 
      match i with
      | Stmt -> 
         print_location loc ^^ Pp.empty
      | Expr -> 
         print_location loc ^^ Pp.empty
      | Read (p,v) -> 
         print_location loc ^^ colon ^^^ !^"read" ^^^ IT.pp v ^^^ parens (mevaluate v) ^^^ !^"for" ^^^ IT.pp p ^^^ parens (mevaluate p)
      | Write (p,v) -> 
         print_location loc ^^ colon ^^^ !^"wrote" ^^^ IT.pp v ^^^ parens (mevaluate v) ^^^ !^"to" ^^^ IT.pp p ^^^ parens (mevaluate p)
      | Create p -> 
         print_location loc ^^ colon ^^^ !^"allocated" ^^^ IT.pp p ^^^ parens (mevaluate p)
      | Kill p -> 
         print_location loc ^^ colon ^^^ !^"deallocated" ^^^ IT.pp p ^^^ parens (mevaluate p)
      | Call (s,[]) -> 
         print_location loc ^^ colon ^^^ !^"called" ^^^ Sym.pp s 
      | Call (s,args) -> 
         print_location loc ^^ colon ^^^ !^"called" ^^^ Sym.pp s ^^^ !^"with" ^^^
         separate_map (comma ^^ space) (fun arg -> IT.pp arg ^^^ parens (mevaluate arg)) args 
      | Return v ->
         print_location loc ^^ colon ^^^ !^"returned" ^^^
         IT.pp v ^^^ parens (mevaluate v)
    in

    let intra_label_trace_report (t: (trace_item * Locations.t) list) = 
      let t = List.rev t in
      let groups = List.separate_and_group (function (Stmt, l) -> Some l | _ -> None) t in
      List.map (fun (stmt, is) ->
        Report.{ 
          stmt = (match stmt with
             | Some l -> print_location l
             | None -> Pp.parens (!^"no statement"))
          ; 
          within = List.map print_trace_item is }
        ) groups
    in
    List.map (fun (l : Context.per_label_trace) ->
        Report.{ 
          label = print_label l.label;
          trace = intra_label_trace_report l.trace 
        }
      ) (List.rev ctxt.trace)
  in
    

  Pp.html_escapes := prev;

  { terms;
    requested;
    unproven;
    resources;
    predicate_hints;
    constraints;
    trace }







